theory CHERI_PCC_Properties
  imports
    "Sail-Morello.Morello_lemmas"
    CHERI_Instantiation
    CHERI_Lemmas
    Trace_Properties
begin

context Morello_ISA
begin

(* Helper functions for getting initial values of register/memory appearing in a trace
   before they get overwritten *)
definition trace_reads_initial_caps_from_gpr :: "int \<Rightarrow> register_value trace \<Rightarrow> Capability set" where
  "trace_reads_initial_caps_from_gpr n t \<equiv>
     {c. \<exists>i < length t. \<exists>r \<in> R_name n.
        t ! i = E_read_reg r (Regval_bitvector_129_dec c) \<and>
        (\<forall>r' \<in> R_name n. \<forall>v. E_write_reg r' v \<notin> set (take i t))}"

definition no_mem_writes_in_trace where
  "no_mem_writes_in_trace t \<equiv>
     (\<forall>wk addr sz v r. E_write_mem wk addr sz v r \<notin> set t) \<and>
     (\<forall>wk addr sz v tag r. E_write_memt wk addr sz v tag r \<notin> set t)"

(* Includes untagged capabilities *)
definition initial_mem_cap_vaddr_loads_of_trace where
  "initial_mem_cap_vaddr_loads_of_trace t \<equiv>
     {(vaddr, c) | vaddr c wk paddr bytes tag i.
        i < length t \<and>
        t ! i = E_read_memt wk paddr 16 (bytes, tag) \<and>
        cap_of_mem_bytes bytes tag = Some c \<and>
        translate_address vaddr = Some paddr \<and>
        no_mem_writes_in_trace (take i t)}"

(* "Other" instructions not denoted by an instruction AST node definitely won't perform an invocation *)
lemma instr_of_trace_None_instr_invokes_no_caps:
  assumes "instr_of_trace t = None"
  shows "instr_invokes_code_caps instr t = {}"
    and "instr_invokes_data_caps instr t = {}"
    and "instr_invokes_indirect_caps instr t = {}"
  using assms
  by (auto simp: trace_invoked_cap_defs)

(* TODO: Move *)
lemma mem_cap_loads_of_ev_reads_mem_cap:
  "mem_cap_loads_of_ev e = {(paddr, c) | paddr c. reads_mem_cap CC e = Some (paddr, 16, c)}"
  by (cases e rule: mem_cap_loads_of_ev.cases)
     (auto simp: reads_mem_cap_def no_cap_load_translation_events bind_eq_Some_conv cap_of_mem_bytes_def nth_ucast
           dest: test_bit_len split: option.splits if_splits)

(* Characterisation of the different cases of invocation for a given instruction trace *)
lemma hasTrace_instr_sem_invocation_cases:
  assumes "hasTrace t (instr_sem opcode)"
    and "instr_of_trace t = Some instr" \<comment> \<open>instruction AST, e.g. @{verbatim Instr_BRS_C_C}, not opcode\<close>
    and "\<not>hasException t (instr_sem opcode)"
    and "\<not>hasFailure t (instr_sem opcode)" \<comment> \<open>ignoring assertion failures\<close>
    and "translation_assms_trace t"
    and "cap_inv_trace t"
    \<comment> \<open>TODO: Add assumption that (at least) reads from GPRs behave sequentially, i.e. reading
        the same register more than once in a row gives the same value.  Needed in particular for
        the sealed pair invocation case when the two given source registers are the same.\<close>
  obtains (SealedPair) cc cd nc nd
    where "instr_invokes_code_cap_from_reg instr = Some nc"
    and "instr_invokes_data_cap_from_reg instr = Some nd"
    and "trace_reads_initial_caps_from_gpr nc t = {cc}"
    and "trace_reads_initial_caps_from_gpr nd t = {cd}"
    and "invokable CC cc cd"
    and "instr_invokes_code_caps opcode t = branch_caps (clear_lsb (CapUnseal cc))"
    and "instr_invokes_data_caps opcode t = {CapUnseal cd}"
    and "instr_invokes_indirect_caps opcode t = {}"
  | (DirectRegSentry) c n
    where "instr_invokes_code_cap_from_reg instr = Some n"
    and "trace_reads_initial_caps_from_gpr n t = {c}"
    and "instr_invokes_data_cap_from_reg instr = None"
    and "CapIsTagSet c" and "CapGetObjectType c = CAP_SEAL_TYPE_RB"
    and "instr_invokes_code_caps opcode t = branch_caps (clear_lsb (CapUnseal c))"
    and "instr_invokes_data_caps opcode t = {}"
    and "instr_invokes_indirect_caps opcode t = {}"
  | (DirectMemSentry) n c c' vaddr sentry_type
      \<comment> \<open>Using an indirect branching instruction with a register other than 29, or a capability
      that isn't an indirect sentry, can still load a direct sentry from memory and invoke it\<close>
    where "instr_load_auth instr = Some (RegAuth n)"
    and "trace_reads_initial_caps_from_gpr n t = {c}"
    and "instr_indirect_sentry_type instr = Some sentry_type"
    and "\<not>CapIsSealed c"
    and "set (address_range (bounds_address AccType_NORMAL vaddr) 16) \<subseteq> get_mem_region CC c"
    and "initial_mem_cap_vaddr_loads_of_trace t = {(vaddr, c')}"
    and "CapGetObjectType c' = CAP_SEAL_TYPE_RB"
    and "instr_invokes_code_caps opcode t = branch_caps (clear_lsb (CapUnseal c'))"
    and "instr_invokes_data_caps opcode t = {}"
    and "instr_invokes_indirect_caps opcode t = {}"
  | (IndirectPointsToPCC) c c' vaddr
    where "instr_invokes_indirect_cap_from_reg instr = Some 29"
    and "instr_indirect_sentry_type instr = Some Points_to_PCC"
    and "trace_reads_initial_caps_from_gpr 29 t = {c}"
    and "CapIsTagSet c"
    and "CapGetObjectType c = CAP_SEAL_TYPE_LB"
    and "instr_invokes_indirect_caps opcode t = {CapUnseal c}"
    and "initial_mem_cap_vaddr_loads_of_trace t = {(vaddr, c')}"
    and "set (address_range (bounds_address AccType_NORMAL vaddr) 16) \<subseteq> get_mem_region CC c"
    and "instr_invokes_code_caps opcode t = (if CapIsTagSet c' \<and> cap_permits CAP_PERM_LOAD_CAP c then mem_branch_caps (clear_lsb c') else {})"
    and "instr_invokes_data_caps opcode t = {CapUnseal c}"
  | (IndirectPointsToPair) n c cc cd
    where "instr_invokes_indirect_cap_from_reg instr = Some n"
    and "instr_indirect_sentry_type instr = Some Points_to_Pair"
    and "trace_reads_initial_caps_from_gpr n t = {c}"
    and "CapIsTagSet c"
    and "CapGetObjectType c = CAP_SEAL_TYPE_LPB"
    and "instr_invokes_indirect_caps opcode t = {CapUnseal c}"
    and "initial_mem_cap_vaddr_loads_of_trace t = {(unat (CapGetValue c), cd), (unat (CapGetValue c + 16), cc)}"
    and "instr_invokes_code_caps opcode t = (if CapIsTagSet cc \<and> cap_permits CAP_PERM_LOAD_CAP c then mem_branch_caps (clear_lsb cc) else {})"
    and "instr_invokes_data_caps opcode t = (if CapIsTagSet cd \<and> cap_permits CAP_PERM_LOAD_CAP c then mem_data_caps cd else {})"
    and "set (address_range (bounds_address AccType_NORMAL (unat (CapGetValue c))) 32) \<subseteq> get_mem_region CC c"
  | (NoInvocation) "instr_invokes_code_caps opcode t = {}"
    and "instr_invokes_data_caps opcode t = {}"
    and "instr_invokes_indirect_caps opcode t = {}"
  oops

end

(* In the case of an invocation, PSTATE.C64 will be set to the LSB of the invoked code capability *)
(* TODO: Could maybe be merged into another property, like the lemma above *)

definition pstate_c64_writes :: "register_value trace \<Rightarrow> bool set" where
  "pstate_c64_writes t \<equiv> {test_bit (ProcState_C64 ps) 0 | ps. E_write_reg ''PSTATE'' (Regval_ProcState ps) \<in> set t}"

context Morello_ISA
begin

definition invocation_writes_pstate_c64 :: "(register_value, instr) isa_trace \<Rightarrow> bool" where
  "invocation_writes_pstate_c64 t \<equiv>
     (\<forall>c' \<in> trace_invokes_code_caps ISA t \<inter> trace_writes_pcc_caps ISA t.
       \<exists>c. original_code_caps_invoked_in_trace (trace t) = {c} \<and>
            c' \<in> clear_lsb ` (branch_caps (CapUnseal c) \<union> mem_branch_caps c) \<and>
            pstate_c64_writes (trace t) = {lsb c})"

end

definition idc_write_axiom''  :: \<open> 'cap Capability_class \<Rightarrow>('cap,'regval,'instr,'e)isa \<Rightarrow> 'cap set \<Rightarrow> nat \<Rightarrow> ('regval,'instr)isa_trace \<Rightarrow> bool \<close>  where
     \<open> idc_write_axiom'' CC ISA initial_caps n t = (
  ((\<forall> i. \<forall> c. \<forall> idc.
     (i < n \<and> (writes_to_reg_at_idx i t = Some idc) \<and> ((idc \<in>(IDC   ISA)) \<and> (c \<in> (writes_reg_caps_at_idx
  CC ISA i t))) \<and> is_invoked_data_cap_at_idx CC ISA c t i)
     \<longrightarrow>
     (((\<exists> cc.  trace_writes_pcc_caps ISA t = {cc} \<and> (is_tagged_method CC cc \<longrightarrow> cc \<in> trace_invokes_code_caps ISA t)))))))\<close>
  for  "CC"  :: " 'cap Capability_class "
  and  "ISA"  :: "('cap,'regval,'instr,'e)isa "
  and  "initial_caps"  :: " 'cap set "
  and  "t"  :: "('regval,'instr)isa_trace "

lemma idc_write_axiom'_idc_write_axiom:
  assumes "store_cap_reg_axiom CC ISA initial_caps n t"
    and "idc_write_axiom'' CC ISA initial_caps n t"
    and "disjnt (PCC ISA) (IDC ISA)"
  shows "idc_write_axiom' CC ISA initial_caps n t"
proof (unfold idc_write_axiom'_def, intro allI impI)
  fix i c idc
  assume *: "i < n \<and> writes_to_reg_at_idx i t = Some idc \<and> idc \<in> IDC ISA \<and> c \<in> writes_reg_caps_at_idx CC ISA i t"
  then have c: "cap_derivable CC (initial_caps \<union> available_caps CC ISA i t) c \<or> is_invoked_data_cap_at_idx CC ISA c t i"
    using assms
    unfolding store_cap_reg_axiom_def
    by (elim allE[where x = i] allE[where x = c] allE[where x = idc]) (auto simp: disjnt_iff)
  then show "cap_derivable CC (initial_caps \<union> available_caps CC ISA i t) c \<or>
             (\<exists>cc. trace_writes_pcc_caps ISA t = {cc} \<and> (is_tagged_method CC cc \<longrightarrow> cc \<in> trace_invokes_code_caps ISA t))"
    using assms *
    by (auto simp: idc_write_axiom''_def)
qed

lemma no_invoked_data_caps_idc_write_axiom:
  assumes "store_cap_reg_axiom CC ISA initial_caps n t"
    and "trace_invokes_data_caps ISA t = {}"
    and "disjnt (PCC ISA) (IDC ISA)"
  shows "idc_write_axiom' CC ISA initial_caps n t"
proof (unfold idc_write_axiom'_def, intro allI impI)
  fix i c idc
  assume *: "i < n \<and> writes_to_reg_at_idx i t = Some idc \<and> idc \<in> IDC ISA \<and> c \<in> writes_reg_caps_at_idx CC ISA i t"
  have "\<not>is_invoked_data_cap_at_idx CC ISA c t i"
    using assms
    unfolding  is_invoked_data_cap_at_idx_def is_invoked_pair_data_cap_at_idx_def
    unfolding is_indirectly_invoked_single_data_cap_at_idx_def is_indirectly_invoked_pair_data_cap_at_idx_def
    by auto
  then show "cap_derivable CC (initial_caps \<union> available_caps CC ISA i t) c \<or>
             (\<exists>cc. trace_writes_pcc_caps ISA t = {cc} \<and> (is_tagged_method CC cc \<longrightarrow> cc \<in> trace_invokes_code_caps ISA t))"
    using assms *
    unfolding store_cap_reg_axiom_def
    by (elim allE[where x = i] allE[where x = c] allE[where x = idc]) (auto simp: disjnt_iff)
qed

fun wellformed_reg_read where
  "wellformed_reg_read (E_read_reg r v) =
     (\<exists>valid_rv set_rv get_rv. map_of registers r = Some (valid_rv, set_rv, get_rv) \<and> valid_rv v)"
| "wellformed_reg_read _ = True"

locale Morello_IDC_Write_Automaton = Morello_Axiom_Automaton +
  assumes wellformed_reg_reads: "\<And>e. wellformed_ev e \<Longrightarrow> wellformed_reg_read e"
begin

definition "pcc_regvals_of_trace t \<equiv> {v. \<exists>e \<in> set t. e = E_write_reg ''PCC'' v}"

abbreviation "add_pcc_regvals_of_trace s t \<equiv> s \<union> pcc_regvals_of_trace t"

lemma pcc_regvals_of_trace_Nil[simp]:
  "pcc_regvals_of_trace [] = {}"
  by (auto simp: pcc_regvals_of_trace_def)

lemma pcc_regvals_of_trace_append[simp]:
  "pcc_regvals_of_trace (t1 @ t2) = pcc_regvals_of_trace t1 \<union> pcc_regvals_of_trace t2"
  by (auto simp: pcc_regvals_of_trace_def)

definition idc_write_axiom_from where
  "idc_write_axiom_from s t \<equiv>
   (s = {} \<and>
    (\<forall>cd. E_write_reg ''_R29'' (Regval_bitvector_129_dec cd) \<in> set t \<and> cd \<in> invoked_data_caps \<longrightarrow>
       (\<exists>cc. pcc_regvals_of_trace t = {Regval_bitvector_129_dec cc} \<and> (CapIsTagSet cc \<longrightarrow> cc \<in> invoked_code_caps))))"
   (*((\<exists>c. s \<union> pcc_regvals_of_trace t \<subseteq> {Regval_bitvector_129_dec c}) \<and>
    (\<forall>cd. E_write_reg ''_R29'' (Regval_bitvector_129_dec cd) \<in> set t \<and> cd \<in> invoked_data_caps \<longrightarrow>
       (\<exists>cc. s \<union> pcc_regvals_of_trace t = {Regval_bitvector_129_dec cc} \<and> cc \<in> invoked_code_caps)))"*)
   (*(s = {} \<and>
    (\<forall>cd. E_read_reg ''_R29'' (Regval_bitvector_129_dec cd) \<in> set t \<and> cd \<in> invoked_data_caps \<longrightarrow>
       (\<exists>cc. pcc_regvals_of_trace t = {Regval_bitvector_129_dec cc} \<and> CapIsTagSet cc \<and> cc \<in> invoked_code_caps)))"*)
   (*(''PCC'' \<notin> written_regs s \<and>
    (\<forall>cd. E_read_reg ''_R29'' (Regval_bitvector_129_dec cd) \<in> set t \<and> cd \<in> invoked_data_caps \<longrightarrow>
       (\<exists>cc. pcc_regvals_of_trace t = {Regval_bitvector_129_dec cc} \<and> CapIsTagSet cc \<and> cc \<in> invoked_code_caps)))"*)
   (*((pcc_regvals_of_trace t = {} \<or> (\<exists>cc. pcc_regvals_of_trace t = {Regval_bitvector_129_dec cc} \<and> ''PCC'' \<notin> written_regs s)) \<and>
    (\<forall>cd. E_read_reg ''_R29'' (Regval_bitvector_129_dec cd) \<in> set t \<and> cd \<in> invoked_data_caps \<longrightarrow>
       (\<exists>cc. pcc_regvals_of_trace t = {Regval_bitvector_129_dec cc} \<and> CapIsTagSet cc \<and> cc \<in> invoked_code_caps)))"*)
  (*"idc_write_axiom_from s t \<equiv>
   (if ''PCC'' \<in> written_regs s then pcc_regvals_of_trace t = {}
    else (\<forall>cd. E_read_reg ''_R29'' (Regval_bitvector_129_dec cd) \<in> set t \<and> cd \<in> invoked_data_caps \<longrightarrow>
           (\<exists>cc. pcc_regvals_of_trace t = {Regval_bitvector_129_dec cc} \<and> CapIsTagSet cc \<and> cc \<in> invoked_code_caps)))"*)

(* abbreviation "idc_write_axiom_from_assms s t \<equiv> invocation_trace_assms t \<and> wellformed_trace t \<longrightarrow> idc_write_axiom_from s t" *)

(*lemma member_written_regs_run_iff:
  "r \<in> written_regs (run s t) \<longleftrightarrow> r \<in> written_regs s \<or> (\<exists>c. E_write_reg r (Regval_bitvector_129_dec c) \<in> set t \<and> CapIsTagSet c)"
  by (induction t arbitrary: s) auto

lemma member_written_regs_run_imp:
  "r \<in> written_regs s \<Longrightarrow> r \<in> written_regs (run s t)"
  by (auto simp: member_written_regs_run_iff)

lemma PCC_in_written_regs_run_iff:
  "''PCC'' \<in> written_regs (run s t) \<longleftrightarrow> ''PCC'' \<in> written_regs s \<or> (\<exists>c. Regval_bitvector_129_dec c \<in> pcc_regvals_of_trace t \<and> CapIsTagSet c)"
  by (auto simp: member_written_regs_run_iff pcc_regvals_of_trace_def)*)

(*lemma idc_write_axiom_from_append:
  assumes "idc_write_axiom_from s t1"
    and "idc_write_axiom_from (add_pcc_regvals_of_trace s t1) t2"
  shows "idc_write_axiom_from s (t1 @ t2)"
  using assms
  by (auto simp: idc_write_axiom_from_def)*)
  (* apply (auto simp: idc_write_axiom_from_def PCC_in_written_regs_run_iff) *)

lemma idc_write_axiom_from_Nil[intro, simp]:
  "idc_write_axiom_from {} []"
  by (auto simp: idc_write_axiom_from_def)

sublocale IDC_Property: Stateful_Full_Trace_Property
  where pred = idc_write_axiom_from and ev_assms = "\<lambda>e. invocation_ev_assms e \<and> translation_assms e \<and> wellformed_ev e"
    and update_state = add_pcc_regvals_of_trace
  by standard (auto simp: idc_write_axiom_from_def)

lemma fold_un_map_eq_Un:
  "foldl (\<union>) xs (map f ys) = xs \<union> (\<Union>(f ` set ys))"
  by (induction ys arbitrary: xs) auto

lemma trace_writes_pcc_caps_alt_def:
  "trace_writes_pcc_caps ISA t = {c. \<exists>e \<in> set (trace t). e = E_write_reg ''PCC'' (Regval_bitvector_129_dec c)}"
  by (auto simp: trace_writes_pcc_caps_def ev_writes_pcc_caps_def fold_un_map_eq_Un split: event.splits if_splits)

(*lemma
  "pcc_regvals_of_trace (trace t) = Regval_bitvector_129_dec ` trace_writes_pcc_caps ISA t"
  apply (auto simp: pcc_regvals_of_trace_def trace_writes_pcc_caps_alt_def image_iff)
  find_theorems "_ \<in> _ ` _"
  oops*)

lemma trace_writes_pcc_caps_pcc_regvals_of_trace:
  "trace_writes_pcc_caps ISA t = {c. Regval_bitvector_129_dec c \<in> pcc_regvals_of_trace (trace t)}"
  by (auto simp: trace_writes_pcc_caps_alt_def pcc_regvals_of_trace_def)

lemma is_invoked_data_cap_at_idx_in_trace_invokes_data_caps:
  assumes "is_invoked_data_cap_at_idx CC ISA c t i"
  shows "c \<in> trace_invokes_data_caps ISA t"
  using assms
  unfolding is_invoked_data_cap_at_idx_def is_invoked_pair_data_cap_at_idx_def
    is_indirectly_invoked_single_data_cap_at_idx_def is_indirectly_invoked_pair_data_cap_at_idx_def
  by auto

lemma idc_write_axiom_from_idc_write_axiom':
  assumes "idc_write_axiom_from s t"
    and "invoked_code_caps \<subseteq> trace_invokes_code_caps ISA (instr_trace instr t)"
    and "trace_invokes_data_caps ISA (instr_trace instr t) \<subseteq> invoked_data_caps"
  shows "idc_write_axiom'' CC ISA UNKNOWN_caps n (instr_trace instr t)"
  using assms
  apply (auto simp: idc_write_axiom_from_def idc_write_axiom''_def trace_writes_pcc_caps_pcc_regvals_of_trace
              dest!: is_invoked_data_cap_at_idx_in_trace_invokes_data_caps)
  subgoal for i c
    by (erule allE[where x = c]) (use nth_mem[of i t] in auto)
  done

lemma (in Stateful_Full_Trace_Property) hasTrace_traces_satisfy_pred_fromE:
  assumes "hasTrace t m" and "trace_assms t" and "traces_satisfy_pred_from s m"
  shows "pred s t"
  using assms
  by (auto simp: traces_satisfy_pred_from_def hasTrace_iff_Traces_final)

lemma no_reg_writes_to_R29_traces_satisfy_pred_from:
  assumes "no_reg_writes_to Rs m" and "{''_R29''} \<subseteq> Rs" and "s = {}"
  shows "IDC_Property.traces_satisfy_pred_from s m"
  using assms
  unfolding IDC_Property.traces_satisfy_pred_from_def
  by (auto simp: no_reg_writes_to_def idc_write_axiom_from_def hasTrace_iff_Traces_final)

lemma no_reg_writes_to_PCC_no_pcc_regvals_of_trace:
  assumes "no_reg_writes_to Rs m" and "{''PCC''} \<subseteq> Rs"
    and "(m, t, m') \<in> Traces"
  shows "pcc_regvals_of_trace t = {}"
  by (use assms in \<open>auto simp: pcc_regvals_of_trace_def no_reg_writes_to_def\<close>)

lemma runs_no_reg_writes_to_PCC_no_pcc_regvals_of_trace:
  assumes "runs_no_reg_writes_to Rs m" and "{''PCC''} \<subseteq> Rs"
    and "Run m t a"
  shows "pcc_regvals_of_trace t = {}"
  by (use assms in \<open>auto simp: pcc_regvals_of_trace_def runs_no_reg_writes_to_def\<close>)

lemma no_reg_writes_to_traces_satisfy_pred_from_bind_left:
  assumes "no_reg_writes_to {''_R29''} m"
    and "runs_no_reg_writes_to {''PCC''} m"
    and "\<And>t a. Run m t a \<Longrightarrow> IDC_Property.trace_assms t \<Longrightarrow> IDC_Property.traces_satisfy_pred_from {} (f a)"
  shows "IDC_Property.traces_satisfy_pred_from {} (bind m f)"
  using assms
  by (intro IDC_Property.traces_satisfy_pred_from_bind no_reg_writes_to_R29_traces_satisfy_pred_from[OF assms(1)])
     (auto simp: runs_no_reg_writes_to_PCC_no_pcc_regvals_of_trace)

lemma idc_write_axiom_append_no_reg_writes_right:
  assumes "\<forall>v. E_write_reg ''_R29'' v \<notin> set t2"
    and "\<forall>v. E_write_reg ''PCC'' v \<notin> set t2"
  shows "idc_write_axiom_from s (t1 @ t2) \<longleftrightarrow> idc_write_axiom_from s t1"
  using assms
  by (auto simp: idc_write_axiom_from_def pcc_regvals_of_trace_def)

lemma no_reg_writes_to_traces_satisfy_pred_from_bind_right:
  assumes "IDC_Property.traces_satisfy_pred_from {} m"
    and "\<And>t a. Run m t a \<Longrightarrow> IDC_Property.trace_assms t \<Longrightarrow> no_reg_writes_to {''PCC'', ''_R29''} (f a)"
  shows "IDC_Property.traces_satisfy_pred_from {} (bind m f)"
  using assms
  by (fastforce simp: IDC_Property.traces_satisfy_pred_from_def idc_write_axiom_append_no_reg_writes_right no_reg_writes_to_def hasTrace_iff_Traces_final final_bind_iff IDC_Property.trace_assms_def
                elim!: bind_Traces_cases)

definition
  "trace_writes_invoked_code_cap s t \<equiv>
     (\<exists>cc. s \<union> pcc_regvals_of_trace t = {Regval_bitvector_129_dec cc} \<and> (CapIsTagSet cc \<longrightarrow> cc \<in> invoked_code_caps))"

(* abbreviation "trace_writes_invoked_code_cap_assms s t \<equiv> invocation_trace_assms t \<and> wellformed_trace t \<longrightarrow> trace_writes_invoked_code_cap s t" *)

sublocale PCC_Writes: Stateful_Full_Trace_Property
  where pred = trace_writes_invoked_code_cap and ev_assms = "\<lambda>e. invocation_ev_assms e \<and> translation_assms e \<and> wellformed_ev e"
    and update_state = add_pcc_regvals_of_trace
  by standard (auto simp: trace_writes_invoked_code_cap_def)

(* TODO: Move *)
lemma atLeastAtMost_int_if_insert:
  fixes m n :: int
  shows "{m..n} = (if m \<le> n then insert m {m+1..n} else {})"
  by auto

lemma R_set_Traces_cases:
  assumes "(R_set n c, t, m') \<in> Traces"
  obtains (Write) r where "t = [E_write_reg r (Regval_bitvector_129_dec c)]" and "r \<in> R_name n" and "m' = Done ()"
  | (Fail) msg where "t = []" and "n \<notin> {0..30}" and "m' = Fail msg"
  | (Nil) r where "t = []" and "r \<in> R_name n" and "m' = Write_reg r (Regval_bitvector_129_dec c) (Done ())"
  using assms
  unfolding R_set_def write_reg_def assert_exp_def
  by (auto simp: register_defs R_name_def hasTrace_iff_Traces_final atLeastAtMost_int_if_insert
           simp del: atLeastAtMost_iff elim!: Write_reg_TracesE elim: final_cases split: if_splits)

lemma final_Write_reg[simp]:
  "final (Write_reg r v k) \<longleftrightarrow> False"
  by (auto simp: final_def)

lemma hasTrace_R_set_cases:
  assumes "hasTrace t (R_set n c)"
  obtains (Write) r where "t = [E_write_reg r (Regval_bitvector_129_dec c)]" and "r \<in> R_name n"
  | (Nil) "t = []" and "n \<notin> {0..30}"
  using assms
  by (auto simp: hasTrace_iff_Traces_final elim!: R_set_Traces_cases)

lemma hasTrace_Fail_iff[simp]:
  "hasTrace t (Fail msg) \<longleftrightarrow> t = []"
  by (auto simp: hasTrace_iff_Traces_final)

lemma pcc_regvals_of_trace_Cons:
  "pcc_regvals_of_trace (E_write_reg r v # t) = (if r = ''PCC'' then insert v (pcc_regvals_of_trace t) else pcc_regvals_of_trace t)"
  by (auto simp: pcc_regvals_of_trace_def)

lemma pcc_regvals_of_trace_Cons_other_reg:
  "r \<noteq> ''PCC'' \<Longrightarrow> pcc_regvals_of_trace (E_write_reg r v # t) = pcc_regvals_of_trace t"
  by (auto simp: pcc_regvals_of_trace_def)

lemma
  "idc_write_axiom_from s (E_write_reg r (Regval_bitvector_129_dec c) # t) \<longleftrightarrow>
   (if r = ''_R29'' \<and> c \<in> invoked_data_caps then trace_writes_invoked_code_cap s t
    else (r = ''PCC'' \<and> c \<in> invoked_code_caps) \<or> idc_write_axiom_from s t) \<and> s = {}"
  (* apply (auto simp: idc_write_axiom_from_def) *)
  apply (cases "r = ''_R29'' \<and> c \<in> invoked_data_caps"; simp add: idc_write_axiom_from_def trace_writes_invoked_code_cap_def pcc_regvals_of_trace_Cons)
   apply auto[]
  apply (cases "r = ''_R29''"; simp)
   apply auto[]
  apply (cases "c \<in> invoked_code_caps"; simp)
  apply (cases "r = ''PCC''"; simp)
  oops

lemma R_name_29_PCC:
  assumes "r \<in> R_name n"
  shows "r = ''_R29'' \<longleftrightarrow> n = 29" and "r \<noteq> ''PCC''"
  by (use assms in \<open>auto simp: R_name_def split: if_splits\<close>)

lemma R_name_29_simp[simp]:
  "R_name 29 = {''_R29''}"
  "''_R29'' \<in> R_name n \<longleftrightarrow> n = 29"
  by (auto simp: R_name_def)

lemma idc_write_axiom_from_Cons_write_reg_if:
  assumes "r \<in> R_name n"
  shows "idc_write_axiom_from s (E_write_reg r (Regval_bitvector_129_dec c) # t) =
         (if n = 29 \<and> c \<in> invoked_data_caps then s = {} \<and> trace_writes_invoked_code_cap s t else idc_write_axiom_from s t)"
  using assms
  by (auto simp: idc_write_axiom_from_def trace_writes_invoked_code_cap_def pcc_regvals_of_trace_Cons R_name_29_PCC)

lemma hasFailure_R_set_Nil:
  "hasFailure t (R_set n c) \<Longrightarrow> t = []"
  by (auto simp: hasFailure_iff_Traces_Fail elim!: R_set_Traces_cases)

lemma hasException_R_set[simp]:
  "hasException t (R_set n c) \<longleftrightarrow> False"
  by (auto simp: R_set_def write_reg_def assert_exp_def hasException_iff_Traces_Exception elim!: Write_reg_TracesE)

lemma traces_satisfy_pred_from_bind_C_set:
  assumes "n = 29 \<and> c \<in> invoked_data_caps \<longrightarrow> PCC_Writes.traces_satisfy_pred_from {} m"
    and "no_reg_writes_to {''_R29''} m"
  shows "IDC_Property.traces_satisfy_pred_from {} (bind (C_set n c) (\<lambda>_. m))"
  using assms
  using IDC_Property.hasTrace_traces_satisfy_pred_fromE[OF _ _ no_reg_writes_to_R29_traces_satisfy_pred_from[OF assms(2)], where s = "{}"]
  unfolding IDC_Property.traces_satisfy_pred_from_def PCC_Writes.traces_satisfy_pred_from_def C_set_def assert_exp_def
  by (auto simp: idc_write_axiom_from_Cons_write_reg_if invocation_trace_assms_def IDC_Property.trace_assms_def dest: hasFailure_R_set_Nil
           elim!: hasTrace_bind_cases R_set_Traces_cases split: if_splits)

(* TODO: Use definition from Wellformed_Traces *)
(* definition exp_succeeds where "exp_succeeds m \<equiv> \<not>(\<exists>t. hasFailure t m \<or> hasException t m)" *)
(* definition exp_succeeds where "exp_succeeds m \<equiv> (\<forall>t. wellformed_trace t \<longrightarrow> \<not>hasFailure t m \<and> \<not>hasException t m)" *)

(*lemma exp_succeeds_no_failure_or_exception:
  assumes "exp_succeeds m"
    and "wellformed_trace t"
  shows "hasFailure t m \<longleftrightarrow> False" and "hasException t m \<longleftrightarrow> False"
  using assms
  by (auto simp: exp_ends_with_def hasFailure_def hasException_def split: option.splits monad.splits)*)

(* TODO: Move *)
lemma hasFailure_bind_iff:
  "hasFailure t (bind m f) \<longleftrightarrow> hasFailure t m \<or> (\<exists>tm a tf. t = tm @ tf \<and> Run m tm a \<and> hasFailure tf (f a))"
proof -
  have "(bind m f, t, Fail msg) \<in> Traces" if "(m, t, Fail msg) \<in> Traces" for msg
    using that
    apply (induction m arbitrary: t) apply (auto elim: Traces_cases)
    apply (erule Traces_cases; auto)+
    done
  moreover have "Fail msg = (bind m'' f) \<longleftrightarrow> m'' = Fail msg \<or> (\<exists>a. m'' = Done a \<and> f a = Fail msg)" for m'' msg
    by (cases m''; auto)
  ultimately show ?thesis
    by (auto simp: hasFailure_iff_Traces_Fail intro: Traces_bindI elim!: bind_Traces_cases; fastforce)
qed

lemma hasException_bind_iff:
  "hasException t (bind m f) \<longleftrightarrow> hasException t m \<or> (\<exists>tm a tf. t = tm @ tf \<and> Run m tm a \<and> hasException tf (f a))"
proof -
  have "(bind m f, t, Exception e) \<in> Traces" if "(m, t, Exception e) \<in> Traces" for e
    using that
    apply (induction m arbitrary: t) apply (auto elim: Traces_cases)
    apply (erule Traces_cases; auto)+
    done
  moreover have "Exception e = (bind m'' f) \<longleftrightarrow> m'' = Exception e \<or> (\<exists>a. m'' = Done a \<and> f a = Exception e)" for m'' e
    by (cases m''; auto)
  ultimately show ?thesis
    by (auto simp: hasException_iff_Traces_Exception intro: Traces_bindI elim!: bind_Traces_cases; fastforce)
qed

lemma bind_eq_Fail_iff:
  "bind m f = Fail msg \<longleftrightarrow> m = Fail msg \<or> (\<exists>a. m = Done a \<and> f a = Fail msg)"
  by (cases m) auto

lemma bind_eq_Exception_iff:
  "bind m f = Exception e \<longleftrightarrow> m = Exception e \<or> (\<exists>a. m = Done a \<and> f a = Exception e)"
  by (cases m) auto

lemma exp_succeeds_bind_iff:
  "exp_succeeds (bind m f) \<longleftrightarrow> exp_succeeds m \<and> (\<forall>t a. Run m t a \<and> wellformed_trace t \<longrightarrow> exp_succeeds (f a))"
  (* by (auto simp: exp_ends_with_def hasFailure_bind_iff hasException_bind_iff) *)
  using Traces_bindI[where m = m and f = f] Traces_bind_leftI[where f = f]
  apply (auto simp: exp_ends_with_def runTrace_iff_Traces bind_eq_Fail_iff bind_eq_Exception_iff elim!: bind_Traces_cases final_cases)
           apply fastforce
          apply fastforce
         apply (drule Traces_bindI[where m = m and f = f], fastforce, fastforce)
        apply (drule Traces_bindI[where m = m and f = f], fastforce, fastforce)
       apply fastforce
      apply fastforce
     apply fastforce
    apply fastforce
   apply fastforce
  apply fastforce
  done

lemmas exp_succeeds_bindI[intro] = exp_succeeds_bind_iff[THEN iffD2]

lemma exp_succeeds_return[intro, simp]:
  "exp_ends_with (return a) P \<longleftrightarrow> P (Done a)"
  by (auto simp: exp_ends_with_def runTrace_iff_Traces)

lemma exp_succeeds_assert_exp[simp]:
  "exp_ends_with (assert_exp e msg) P \<longleftrightarrow> (if e then P (Done ()) else P (Fail msg))"
  by (auto simp: assert_exp_def exp_ends_with_def runTrace_iff_Traces)

lemma exp_succeeds_and_boolM[intro]:
  assumes "exp_succeeds m1" and "exp_succeeds m2"
  shows "exp_succeeds (and_boolM m1 m2)"
  by (use assms in \<open>auto simp: and_boolM_def exp_succeeds_bind_iff\<close>)

lemma exp_succeeds_or_boolM[intro]:
  assumes "exp_succeeds m1" and "exp_succeeds m2"
  shows "exp_succeeds (or_boolM m1 m2)"
  by (use assms in \<open>auto simp: or_boolM_def exp_succeeds_bind_iff\<close>)

lemma exp_succeeds_write_reg[simp]:
  "exp_succeeds (write_reg r v)"
  by (auto simp: write_reg_def exp_ends_with_def runTrace_iff_Traces elim!: Write_reg_TracesE)
  (*"exp_ends_with (write_reg r v :: unit M) P \<longleftrightarrow> P (Done ())"*)
  (* apply (auto simp: write_reg_def exp_ends_with_def runTrace_iff_Traces elim!: Write_reg_TracesE allE[where x = "[E_write_reg (name r) (regval_of r v)]"] allE[where x = "Done () :: unit M"]) *)

abbreviation "known_reg r \<equiv> (map_of registers (name r) = Some (register_ops_of r))"

lemma known_regs:
  "known_reg PCC_ref"
  "known_reg PSTATE_ref"
  "known_reg SCR_EL3_ref"
  "known_reg TCR_EL1_ref"
  "known_reg TCR_EL2_ref"
  "known_reg TCR_EL3_ref"
  "known_reg CCTLR_EL0_ref"
  "known_reg CCTLR_EL1_ref"
  "known_reg CCTLR_EL2_ref"
  "known_reg CCTLR_EL3_ref"
  "known_reg HCR_EL2_ref"
  "known_reg EDSCR_ref"
  by (auto simp: register_defs)

lemma exp_succeeds_read_reg:
  assumes "map_of registers (name r) = Some (register_ops_of r)"
  shows "exp_succeeds (read_reg r)"
  using assms
  by (auto simp: read_reg_def exp_ends_with_def runTrace_iff_Traces register_ops_of_def
           elim!: Read_reg_TracesE final_cases split: option.splits dest!: wellformed_reg_reads (*map_of_SomeD*))

lemmas exp_succeeds_read_regs[intro, simp] = known_regs[THEN exp_succeeds_read_reg]

lemma exp_succeeds_UsingAArch32[intro, simp]:
  "exp_succeeds (UsingAArch32 u)"
  unfolding UsingAArch32_def Let_def
  apply (auto simp: exp_succeeds_bind_iff HaveAnyAArch32_def HighestELUsingAArch32_def)
  (* TODO: ProcState_nRW, PSTATE *)
  sorry

lemma exp_succeeds_choose_convert_default:
  "exp_succeeds (choose_convert_default of_rv d msg)"
  unfolding choose_convert_default_def exp_ends_with_def runTrace_iff_Traces
  by (auto elim: Traces_cases final_cases)

lemma exp_succeeds_undefined_bool[intro, simp]:
  "exp_succeeds (undefined_bool RV u)"
  by (auto simp: undefined_bool_def choose_bool_def exp_succeeds_choose_convert_default)

lemma exp_succeeds_foreachM:
  assumes "\<And>x vars. x \<in> set xs \<Longrightarrow> exp_succeeds (body x vars)"
  shows "exp_succeeds (foreachM xs vars body)"
  using assms
  by (induction xs arbitrary: vars) (auto simp: exp_succeeds_bind_iff)

lemma exp_succeeds_undefined_bitvector[intro, simp]:
  "exp_succeeds (undefined_bitvector BC RV u)"
  unfolding undefined_bitvector_def choose_bitvector_def choose_bools_def genlistM_def choose_bool_def
  by (auto simp: exp_succeeds_bind_iff intro!: exp_succeeds_foreachM exp_succeeds_choose_convert_default)

lemma exp_succeeds_IsSecureBelowEL3[intro, simp]:
  "exp_succeeds (IsSecureBelowEL3 u)"
  unfolding IsSecureBelowEL3_def SCR_GEN_read_def
  by auto

lemma exp_succeeds_ELUsingAArch32[intro, simp]:
  "exp_succeeds (ELUsingAArch32 el)"
  unfolding ELUsingAArch32_def ELStateUsingAArch32_def ELStateUsingAArch32K_def
  by (auto simp: exp_succeeds_bind_iff)

lemma exp_succeeds_ELIsInHost[intro, simp]:
  "exp_succeeds (ELIsInHost el)"
  by (auto simp: ELIsInHost_def exp_succeeds_bind_iff intro!: exp_succeeds_and_boolM exp_succeeds_or_boolM)

lemma exp_succeeds_IsInHost[intro, simp]:
  "exp_succeeds (IsInHost u)"
  by (auto simp: IsInHost_def)

lemma exp_succeeds_AddrTop[intro, simp]:
  "exp_succeeds (AddrTop c el)"
  unfolding AddrTop_def
  by (auto simp: exp_succeeds_bind_iff S1TranslationRegime_def EL0_def EL1_def EL2_def EL3_def)

lemma exp_succeeds_BranchAddr[intro, simp]:
  "exp_succeeds (BranchAddr c el)"
  unfolding BranchAddr_def Let_def
  by (auto simp: exp_succeeds_bind_iff intro: exp_succeeds_UsingAArch32 dest!: AddrTop_63_or_55
           intro!: exp_succeeds_and_boolM exp_succeeds_or_boolM)

lemma exp_succeeds_AArch64_BranchAddr[intro, simp]:
  "exp_succeeds (AArch64_BranchAddr addr)"
  by (auto simp: AArch64_BranchAddr_def exp_succeeds_bind_iff intro!: exp_succeeds_and_boolM exp_succeeds_or_boolM)

lemma exp_succeeds_Halted[intro, simp]:
  "exp_succeeds (Halted u)"
  by (auto simp: Halted_def exp_succeeds_bind_iff)

lemma exp_succeeds_IsInRestricted[intro, simp]:
  "exp_succeeds (IsInRestricted u)"
  by (auto simp: IsInRestricted_def PCC_read_def exp_succeeds_bind_iff)

lemma hasFailure_iff_runTrace:
  "hasFailure t m \<longleftrightarrow> (\<exists>msg. runTrace t m = Some (Fail msg))"
  by (auto simp: hasFailure_def split: option.splits monad.splits)

lemma hasException_iff_runTrace:
  "hasException t m \<longleftrightarrow> (\<exists>e. runTrace t m = Some (Exception e))"
  by (auto simp: hasException_def split: option.splits monad.splits)

lemma PCC_Writes_traces_satisfy_pred_from_bind_right:
  assumes "\<And>t a. Run m t a \<Longrightarrow> PCC_Writes.trace_assms t \<Longrightarrow> PCC_Writes.traces_satisfy_pred_from {} (f a)"
    and "no_reg_writes_to {''PCC''} m"
    and "exp_succeeds m"
  shows "PCC_Writes.traces_satisfy_pred_from {} (bind m f)"
  using assms no_reg_writes_to_PCC_no_pcc_regvals_of_trace[OF assms(2)]
  unfolding PCC_Writes.traces_satisfy_pred_from_def
  unfolding trace_writes_invoked_code_cap_def
  by (fastforce elim!: hasTrace_bind_cases simp: exp_ends_with_def hasFailure_iff_runTrace hasException_iff_runTrace PCC_Writes.trace_assms_def)

lemma PCC_Writes_traces_satisfy_pred_from_bind_left:
  assumes "PCC_Writes.traces_satisfy_pred_from {} m"
    and "\<And>a. no_reg_writes_to {''PCC''} (f a)"
  shows "PCC_Writes.traces_satisfy_pred_from {} (bind m f)"
  using assms no_reg_writes_to_PCC_no_pcc_regvals_of_trace[OF assms(2)]
  unfolding PCC_Writes.traces_satisfy_pred_from_def
  unfolding trace_writes_invoked_code_cap_def
  by (auto simp: hasTrace_iff_Traces_final hasFailure_iff_Traces_Fail hasException_iff_Traces_Exception final_bind_iff PCC_Writes.trace_assms_def
           elim!: bind_Traces_cases;
      fastforce)

lemma PCC_Writes_write_reg_PCC:
  assumes "CapIsTagSet c \<longrightarrow> c \<in> invoked_code_caps"
  shows "PCC_Writes.traces_satisfy_pred_from {} (write_reg PCC_ref c)"
  using assms
  unfolding PCC_Writes.traces_satisfy_pred_from_def
  unfolding trace_writes_invoked_code_cap_def pcc_regvals_of_trace_def
  by (auto simp: write_reg_def hasTrace_iff_Traces_final register_defs elim!: Write_reg_TracesE)

lemmas PCC_Writes_bind_write_reg_PCC =
  PCC_Writes_write_reg_PCC[THEN PCC_Writes_traces_satisfy_pred_from_bind_left]

lemma PCC_Write_BranchToCapability:
  assumes "CapIsTagSet c \<and> \<not>CapIsSealed c \<longrightarrow> branch_caps c \<subseteq> invoked_code_caps"
  shows "PCC_Writes.traces_satisfy_pred_from {} (BranchToCapability c branch_type)"
  unfolding BranchToCapability_def bind_assoc Let_def
  apply (intro PCC_Writes_bind_write_reg_PCC PCC_Writes_traces_satisfy_pred_from_bind_right exp_succeeds_UsingAArch32)
  subgoal
    by (use assms in \<open>auto elim!: BranchAddr_branch_caps_tagged_unsealed read_reg_PSTATE_translation_el simp: PCC_Writes.trace_assms_def\<close>)
  by (no_reg_writes_toI
      | intro exp_succeeds_write_reg exp_succeeds_read_regs exp_succeeds_bindI conjI allI impI
      | (auto)[])+

lemma PCC_Write_BranchXToCapability:
  assumes "CapIsTagSet c \<and> \<not>CapIsSealed c \<longrightarrow> branch_caps c \<subseteq> invoked_code_caps"
  shows "PCC_Writes.traces_satisfy_pred_from {} (BranchXToCapability c branch_type)"
  unfolding BranchXToCapability_def Let_def
  apply (intro PCC_Writes_traces_satisfy_pred_from_bind_right PCC_Write_BranchToCapability)
  subgoal
    by (use assms branch_caps_set_bit_0_subset[of c] in \<open>auto simp: test_bit_set_gen\<close>)
  by (no_reg_writes_toI | intro exp_succeeds_write_reg exp_succeeds_read_regs exp_succeeds_bindI conjI allI impI)+

lemma IDC_Property_BranchXToCapability:
  "IDC_Property.traces_satisfy_pred_from {} (BranchXToCapability c branch_type)"
  by (rule no_reg_writes_to_R29_traces_satisfy_pred_from[where Rs = "{''_R29''}"]) auto

(* lemmas traces_satisfy_pred_from_bind_if_split = if_split[where P = "\<lambda>m. traces_satisfy_pred_from s (bind m f)" for f s] *)

lemmas branch_caps_if_sentry_invoked_code_caps = if_split[where P = "\<lambda>c. branch_caps c \<subseteq> invoked_code_caps", THEN iffD2]

lemma branch_caps_unseal_if_tag_clear_invoked_code_caps:
  assumes "CapIsTagSet (if b then CapWithTagClear c else c)"
    and "branch_caps (CapUnseal c) \<subseteq> invoked_code_caps"
  shows "branch_caps (CapUnseal (if b then CapWithTagClear c else c)) \<subseteq> invoked_code_caps"
  by (use assms in auto)

lemma branch_caps_if_tag_clear_invoked_code_caps:
  assumes "CapIsTagSet (if b then CapWithTagClear c else c)"
    and "branch_caps c \<subseteq> invoked_code_caps"
  shows "branch_caps (if b then CapWithTagClear c else c) \<subseteq> invoked_code_caps"
  by (use assms in auto)

lemma sealed_branch_caps_singleton:
  "CapIsSealed c \<Longrightarrow> branch_caps c = {c}"
  by (auto simp: branch_caps_def)

lemma CapSquashPostLoadCap_branch_caps_invoked_code_caps:
  assumes "Run (CapSquashPostLoadCap c base) t c'"
    and "CapIsTagSet c'"
    and "CapGetObjectType c' \<noteq> CAP_SEAL_TYPE_RB \<or> \<not>CapIsSealed c'"
    and "CapIsTagSet c \<longrightarrow> mem_branch_caps c \<subseteq> invoked_code_caps"
  shows "branch_caps c' \<subseteq> invoked_code_caps"
  using assms sealed_branch_caps_singleton[of c]
  by (elim CapSquashPostLoadCap_cases) (auto simp: mem_branch_caps_def CapIsSealed_def split: if_splits)

lemma CapSquashPostLoadCap_branch_caps_unseal_invoked_code_caps:
  assumes "Run (CapSquashPostLoadCap c base) t c'"
    and "CapGetObjectType c' = CAP_SEAL_TYPE_RB"
    and "CapIsTagSet c'"
    and "CapIsTagSet c \<longrightarrow> mem_branch_caps c \<subseteq> invoked_code_caps"
  shows "branch_caps (CapUnseal c') \<subseteq> invoked_code_caps"
  using assms
  by (elim CapSquashPostLoadCap_cases) (auto simp: mem_branch_caps_def CapIsSealed_def)

lemma IDC_Property_trace_assmsE:
  assumes "IDC_Property.trace_assms t"
  shows "invocation_trace_assms t" and "translation_assms_trace t"
  using assms
  by (auto simp: invocation_trace_assms_def IDC_Property.trace_assms_def)

lemma MemC_read_invoked_code_caps:
  assumes "Run (MemC_read vaddr acctype) t c"
    and "IDC_Property.trace_assms t"
    and "is_indirect_branch"
    and "CapIsTagSet c"
    and "\<exists>sentry \<in> invoked_indirect_caps. indirect_sentry_type = Some Points_to_Pair \<longrightarrow> vaddr = CapGetValue sentry + 16"
        (is "\<exists>sentry \<in> invoked_indirect_caps. ?P sentry")
  shows "mem_branch_caps c \<subseteq> invoked_code_caps"
proof -
  from assms obtain sentry where "sentry \<in> invoked_indirect_caps" and "?P sentry"
    by blast
  then show ?thesis
    using assms
    by (elim MemC_read_mem_cap_vaddr_loaded_in_trace_if_tagged[THEN mem_cap_vaddr_loaded_in_trace_if_tagged_invoked_code_cap, where sentry = sentry])
       (auto simp: invocation_trace_assms_def IDC_Property.trace_assms_def)
qed

(*lemma CapGetObjectType_if_CapWithTagClear_eq:
  "CapGetObjectType (if b then CapWithTagClear c else c) = CapGetObjectType c"
  apply (intro word_eqI)
  apply (auto simp: CapGetObjectType_def CapWithTagClear_def)
  oops*)

lemma CapIsTagSet_if_CapWithTagClear_iff[simp]:
  "(if b then CapWithTagClear c else c) !! 128 \<longleftrightarrow> \<not>b \<and> CapIsTagSet c"
  by auto

(* TODO: Move out of Write_Cap context in CHERI_Lemmas *)
lemma CapGetObjectType_CapWithTagClear_eq[simp]:
  "CapGetObjectType (CapWithTagClear c) = CapGetObjectType c"
  by (auto simp: CapGetObjectType_def CapWithTagClear_def slice_set_bit_above)

lemma CapGetObjectType_if_CapWithTagClear_eq[simp]:
  "CapGetObjectType (if clear then CapWithTagClear c else c) = CapGetObjectType c"
  by auto

lemma CapIsSealed_if_CapWithTagClear_iff[simp]:
  "CapIsSealed (if b then CapWithTagClear c else c) \<longleftrightarrow> CapIsSealed c"
  by (auto simp: CapIsSealed_def)

named_theorems traces_satisfy_predI
named_theorems traces_satisfy_predE

method traces_satisfy_predI_step uses intro elim =
  (rule intro traces_satisfy_predI allI impI conjI
    | erule elim traces_satisfy_predE FalseE
    | (rule no_reg_writes_to_traces_satisfy_pred_from_bind_left, no_reg_writes_toI intro: intro, no_reg_writes_toI)
    | (rule PCC_Writes_traces_satisfy_pred_from_bind_right[rotated], no_reg_writes_toI intro: intro, solves \<open>simp add: exp_succeeds_bind_iff\<close>)
    | rule IDC_Property.traces_satisfy_pred_from_if
    | assumption
    | no_reg_writes_toI intro: intro)

method traces_satisfy_predI_with methods s uses intro elim =
  (traces_satisfy_predI_step intro: intro elim: elim | solves s)+

method traces_satisfy_predI uses intro elim assms =
  (traces_satisfy_predI_with \<open>use assms in auto\<close> intro: intro elim: elim)

declare PCC_Write_BranchXToCapability[traces_satisfy_predI]
declare IDC_Property_BranchXToCapability[traces_satisfy_predI]
lemmas branch_caps_invoked_code_capsI[traces_satisfy_predI] =
  branch_caps_unseal_if_tag_clear_invoked_code_caps branch_caps_if_tag_clear_invoked_code_caps branch_caps_if_sentry_invoked_code_caps
declare CapSquashPostLoadCap_branch_caps_unseal_invoked_code_caps[traces_satisfy_predE]
declare CapSquashPostLoadCap_branch_caps_invoked_code_caps[traces_satisfy_predE]
declare MemC_read_invoked_code_caps[traces_satisfy_predE]
declare C_read_branch_caps_invoked_code_cap[traces_satisfy_predE]
declare IDC_Property_trace_assmsE[traces_satisfy_predE]

lemma IDC_Property_execute_BR_CI_C:
  assumes "indirect_sentry_type = Some Points_to_PCC" and "invoked_indirect_caps = invoked_data_caps"
  shows "IDC_Property.traces_satisfy_pred_from {} (execute_BR_CI_C branch_type n offset)"
  unfolding execute_BR_CI_C_def Let_def if_distrib[where f = "\<lambda>m. Sail2_prompt_monad.bind m f" and c = "n = 29" for f] bind_assoc bind_return
  by (traces_satisfy_predI assms: assms intro: traces_satisfy_pred_from_bind_C_set[where n = 29])

lemma IDC_Property_decode_BR_CI_C:
  assumes "indirect_sentry_type = Some Points_to_PCC" and "invoked_indirect_caps = invoked_data_caps"
  shows "IDC_Property.traces_satisfy_pred_from {} (decode_BR_CI_C imm7 Cn)"
  unfolding decode_BR_CI_C_def Let_def
  by (intro IDC_Property_execute_BR_CI_C assms)

lemma IDC_Property_execute_BRS_C_C_C:
  assumes "invoked_code_reg = Some n"
  shows "IDC_Property.traces_satisfy_pred_from {} (execute_BRS_C_C_C branch_type m n)"
  unfolding execute_BRS_C_C_C_def bind_assoc Let_def if_distrib[where f = "\<lambda>m. Sail2_prompt_monad.bind m f" for f] bind_return
  by (traces_satisfy_predI assms: assms intro: traces_satisfy_pred_from_bind_C_set[where n = 29])

lemma IDC_Property_decode_BRS_C_C_C:
  assumes "invoked_code_reg = Some (uint Cn)"
  shows "IDC_Property.traces_satisfy_pred_from {} (decode_BRS_C_C_C Cm opc Cn)"
  unfolding decode_BRS_C_C_C_def bind_assoc Let_def
  by (intro IDC_Property_execute_BRS_C_C_C assms)

lemma exp_succeeds_IsInC64[intro, simp]:
  "exp_succeeds (IsInC64 u)"
  by (auto simp: IsInC64_def)

lemma exp_succeeds_PCC_read[intro, simp]:
  "exp_succeeds (PCC_read u)"
  by (auto simp: PCC_read_def)

lemma exp_succeeds_CapIsRepresentableFast[intro, simp]:
  "exp_succeeds (CapIsRepresentableFast c n)"
  by (auto simp: CapIsRepresentableFast_def Let_def exp_succeeds_bind_iff)

lemma exp_succeeds_CapAdd[intro, simp]:
  "exp_succeeds (CapAdd c n)"
  by (auto simp: CapAdd_def Let_def exp_succeeds_bind_iff)

lemma exp_succeeds_CapAdd__1[intro, simp]:
  "exp_succeeds (CapAdd__1 c n)"
  by (auto simp: CapAdd__1_def Let_def)

lemma exp_succeeds_CCTLR_read__1[intro, simp]:
  "exp_succeeds (CCTLR_read__1 u)"
  using EL_exhaust_disj[where el = "ProcState_EL ps" for ps]
  by (auto simp: CCTLR_read__1_def CCTLR_read_def Let_def exp_succeeds_bind_iff EL0_def EL1_def EL2_def EL3_def)

lemma exp_succeeds_R_set[intro, simp]:
  "n \<in> {0..30} \<Longrightarrow> exp_succeeds (R_set n c)"
  using exp_succeeds_write_reg[where v = c]
  unfolding R_set_def Let_def
  by (auto simp add: atLeastAtMost_int_if_insert simp del: atLeastAtMost_iff)

abbreviation "unit_exp_succeeds m \<equiv> exp_ends_with m (\<lambda>m'. m' = Done ())"

lemma exp_succeeds_C_set[intro, simp]:
  "n \<in> {0..30} \<Longrightarrow> unit_exp_succeeds (C_set n c)"
  by (use exp_succeeds_R_set in \<open>auto simp: C_set_def\<close>)

lemma no_reg_writes_to_R29_C_set:
  "n \<noteq> 29 \<Longrightarrow> no_reg_writes_to {''_R29''} (C_set n c)"
  by (auto simp: C_set_def R_set_def register_defs)

lemma IDC_Property_execute_BLRS_C_C_C:
  assumes "invoked_code_reg = Some n"
  shows "IDC_Property.traces_satisfy_pred_from {} (execute_BLRS_C_C_C branch_type m n)"
  unfolding execute_BLRS_C_C_C_def bind_assoc Let_def if_distrib[where f = "\<lambda>m. Sail2_prompt_monad.bind m f" for f] bind_return
  by (traces_satisfy_predI assms: assms intro: traces_satisfy_pred_from_bind_C_set[where n = 29] no_reg_writes_to_R29_C_set)

lemma IDC_Property_decode_BLRS_C_C_C:
  assumes "invoked_code_reg = Some (uint Cn)"
  shows "IDC_Property.traces_satisfy_pred_from {} (decode_BLRS_C_C_C Cm opc Cn)"
  unfolding decode_BLRS_C_C_C_def bind_assoc Let_def
  by (intro IDC_Property_execute_BLRS_C_C_C assms)

lemma IDC_Property_execute_RETS_C_C_C:
  assumes "invoked_code_reg = Some n"
  shows "IDC_Property.traces_satisfy_pred_from {} (execute_RETS_C_C_C branch_type m n)"
  unfolding execute_RETS_C_C_C_def bind_assoc Let_def if_distrib[where f = "\<lambda>m. Sail2_prompt_monad.bind m f" for f] bind_return
  by (traces_satisfy_predI assms: assms intro: traces_satisfy_pred_from_bind_C_set[where n = 29] no_reg_writes_to_R29_C_set)

lemma IDC_Property_decode_RETS_C_C_C:
  assumes "invoked_code_reg = Some (uint Cn)"
  shows "IDC_Property.traces_satisfy_pred_from {} (decode_RETS_C_C_C Cm opc Cn)"
  unfolding decode_RETS_C_C_C_def bind_assoc Let_def
  by (intro IDC_Property_execute_RETS_C_C_C assms)

lemma IDC_Property_execute_BLR_CI_C:
  assumes "indirect_sentry_type = Some Points_to_PCC" and "invoked_indirect_caps = invoked_data_caps"
  shows "IDC_Property.traces_satisfy_pred_from {} (execute_BLR_CI_C branch_type n offset)"
  unfolding execute_BLR_CI_C_def Let_def if_distrib[where f = "\<lambda>m. Sail2_prompt_monad.bind m f" and c = "n = 29" for f] bind_assoc bind_return
  by (traces_satisfy_predI assms: assms intro: traces_satisfy_pred_from_bind_C_set[where n = 29] no_reg_writes_to_R29_C_set)

lemma IDC_Property_decode_BLR_CI_C:
  assumes "indirect_sentry_type = Some Points_to_PCC" and "invoked_indirect_caps = invoked_data_caps"
  shows "IDC_Property.traces_satisfy_pred_from {} (decode_BLR_CI_C imm7 Cn)"
  unfolding decode_BLR_CI_C_def Let_def
  by (intro IDC_Property_execute_BLR_CI_C assms)

lemma CSP_or_C_read_unseal_invoked_indirect_caps_cases:
  assumes "Run (if n = 31 then seq (CheckSPAlignment u) (CSP_read u') else C_read n) t c"
    and "invocation_trace_assms t"
    and "invoked_indirect_reg = Some n"
    and "indirect_sentry_type = Some sentry_type"
  obtains (Invocation) "CapUnseal c \<in> invoked_indirect_caps" and "CapIsTagSet c" and "get_indirect_sentry_type c = Some sentry_type"
  | (NoInvocation) "invoked_indirect_caps = {}" and "\<not>CapIsTagSet c \<or> get_indirect_sentry_type c \<noteq> Some sentry_type"
  using assms
  by (elim Run_ifE Run_bindE C_read_unseal_invoked_indirect_caps_cases[where sentry_type = sentry_type] CSP_read_invoked_indirect_caps_cases[where sentry_type = sentry_type])
     auto

declare CapUnseal_get_bounds_helpers_eq[simp]

lemma CSP_or_C_read_exists_invoked_indirect_Points_to_Pair_cap:
  assumes "Run (if n = 31 then seq (CheckSPAlignment u) (CSP_read u') else C_read n) t c"
    and "invocation_trace_assms t"
    and "invoked_indirect_reg = Some n"
    and "indirect_sentry_type = Some Points_to_Pair"
    and "invoked_indirect_caps \<noteq> {}"
    and "CapGetValue c = addr"
  shows "\<exists>sentry\<in>invoked_indirect_caps. indirect_sentry_type = Some Points_to_Pair \<longrightarrow>
          add_vec_int addr CAPABILITY_DBYTES = CapGetValue sentry + 16"
  using assms
  by (elim CSP_or_C_read_unseal_invoked_indirect_caps_cases[where sentry_type = Points_to_Pair]; fastforce)

lemma Run_VAddress_CapabilityE:
  assumes "Run (VAddress va) t a"
    and "VirtualAddress_vatype va = VA_Capability"
  obtains "a = CapGetValue (VirtualAddress_base va)"
  using assms
  by (auto simp: VAddress_def VAIsBits64_def elim!: Run_bindE)

lemma IDC_Property_execute_LDPBR_C_C_C:
  assumes "indirect_sentry_type = Some Points_to_Pair" and "t = 29 \<longrightarrow> invoked_indirect_reg = Some n" and "invoked_indirect_caps = {} \<longrightarrow> invoked_data_caps = {}"
  shows "IDC_Property.traces_satisfy_pred_from {} (execute_LDPBR_C_C_C branch_type n t)"
  unfolding execute_LDPBR_C_C_C_def Let_def if_distrib[where f = "\<lambda>m. Sail2_prompt_monad.bind m f" and c = "t = 29" for f] bind_assoc bind_return
  by (traces_satisfy_predI assms: assms intro: traces_satisfy_pred_from_bind_C_set[where n = 29] no_reg_writes_to_R29_C_set elim: CSP_or_C_read_exists_invoked_indirect_Points_to_Pair_cap Run_VAddress_CapabilityE)

lemma IDC_Property_decode_LDPBR_C_C_C:
  assumes "indirect_sentry_type = Some Points_to_Pair" and "uint Ct = 29 \<longrightarrow> invoked_indirect_reg = Some (uint Cn)" and "invoked_indirect_caps = {} \<longrightarrow> invoked_data_caps = {}"
  shows "IDC_Property.traces_satisfy_pred_from {} (decode_LDPBR_C_C_C opc Cn Ct)"
  unfolding decode_LDPBR_C_C_C_def Let_def
  by (intro IDC_Property_execute_LDPBR_C_C_C assms)

lemma IDC_Property_execute_LDPBLR_C_C_C:
  assumes "indirect_sentry_type = Some Points_to_Pair" and "t = 29 \<longrightarrow> invoked_indirect_reg = Some n" and "invoked_indirect_caps = {} \<longrightarrow> invoked_data_caps = {}"
  shows "IDC_Property.traces_satisfy_pred_from {} (execute_LDPBLR_C_C_C branch_type n t)"
  unfolding execute_LDPBLR_C_C_C_def Let_def if_distrib[where f = "\<lambda>m. Sail2_prompt_monad.bind m f" and c = "t = 29" for f] bind_assoc bind_return
  by (traces_satisfy_predI assms: assms intro: traces_satisfy_pred_from_bind_C_set[where n = 29] no_reg_writes_to_R29_C_set elim: CSP_or_C_read_exists_invoked_indirect_Points_to_Pair_cap Run_VAddress_CapabilityE)

lemma IDC_Property_decode_LDPBLR_C_C_C:
  assumes "indirect_sentry_type = Some Points_to_Pair" and "uint Ct = 29 \<longrightarrow> invoked_indirect_reg = Some (uint Cn)" and "invoked_indirect_caps = {} \<longrightarrow> invoked_data_caps = {}"
  shows "IDC_Property.traces_satisfy_pred_from {} (decode_LDPBLR_C_C_C opc Cn Ct)"
  unfolding decode_LDPBLR_C_C_C_def Let_def
  by (intro IDC_Property_execute_LDPBLR_C_C_C assms)

lemmas IDC_Property_data_invocation_instrs =
  IDC_Property_decode_BLR_CI_C
  IDC_Property_decode_BR_CI_C
  IDC_Property_decode_LDPBLR_C_C_C
  IDC_Property_decode_LDPBR_C_C_C
  IDC_Property_decode_BRS_C_C_C
  IDC_Property_decode_BLRS_C_C_C
  IDC_Property_decode_RETS_C_C_C

lemma Points_to_PCC_invoked_data_caps_eq_indirect_sentries:
  assumes "trace_indirect_sentry_type t = Some Points_to_PCC"
  shows "instr_invokes_data_caps instr t = trace_invokes_indirect_sentries t"
  using assms
  by (auto simp: trace_indirect_sentry_type_def instr_invokes_data_caps_def trace_indirectly_invokes_data_caps_def bind_eq_Some_conv
           elim!: instr_indirect_sentry_type.elims)

lemma Points_to_Pair_no_invoked_data_caps_without_indirect_sentries:
  assumes "trace_indirect_sentry_type t = Some Points_to_Pair"
    and "trace_invokes_indirect_sentries t = {}"
  shows "instr_invokes_data_caps instr t = {}"
  using assms
  by (auto simp: trace_indirect_sentry_type_def instr_invokes_data_caps_def trace_indirectly_invokes_data_caps_def bind_eq_Some_conv
           elim!: instr_indirect_sentry_type.elims)

(*lemma no_indirect_or_data_regs_no_invoked_data_caps:
  assumes "trace_invokes_indirect_cap_from_reg t = None"
    and "trace_invokes_data_cap_from_reg t = None"
  shows "instr_invokes_data_caps instr t = {}"
  using assms
  by (auto simp: instr_invokes_data_caps_def trace_indirectly_invokes_data_caps_def split: option.splits indirect_sentry_type.splits)*)

end

(*lemma idc_write_axiom'_fetch_trace:
  "idc_write_axiom' CC ISA initial_caps n (fetch_trace t)"
  unfolding idc_write_axiom'_def is_invoked_data_cap_at_idx_def is_invoked_pair_data_cap_at_idx_def
  unfolding is_indirectly_invoked_single_data_cap_at_idx_def is_indirectly_invoked_pair_data_cap_at_idx_def
  by auto*)

locale Morello_IDC_Write_Instr_Trace_Automaton = Morello_Instr_Trace_Axiom_Automaton +
  assumes wellformed_reg_reads: "\<And>e. wellformed_ev e \<Longrightarrow> wellformed_reg_read e"
begin

sublocale Morello_IDC_Write_Automaton
  where ex_traces = "isa.trace_raises_ex ISA (instr_trace instr t)"
    and instr_opt = "instr_of_trace (trace (instr_trace instr t))"
    and invoked_code_caps = "trace_invokes_code_caps ISA (instr_trace instr t)"
    and invoked_data_caps = "trace_invokes_data_caps ISA (instr_trace instr t)"
    and invoked_indirect_caps = "trace_invokes_indirect_caps ISA (instr_trace instr t)"
    and load_auth = "trace_load_auths (trace (instr_trace instr t))"
    and load_caps_permitted = "isa.trace_uses_mem_caps ISA (instr_trace instr t)"
    and no_system_reg_access = "\<not>trace_has_system_reg_access (trace (instr_trace instr t))"
    and is_in_c64 = "trace_is_in_c64 (trace (instr_trace instr t))"
    and is_fetch = "is_fetch_trace (instr_trace instr t)"
  by standard (rule wellformed_reg_reads)

lemma instr_exp_assms_IDC_Property_ifE:
  assumes "instr_exp_assms (if c then m1 else m2)"
    and "instr_exp_assms m1 \<Longrightarrow> IDC_Property.traces_satisfy_pred_from {} m1"
    and "instr_exp_assms m2 \<Longrightarrow> IDC_Property.traces_satisfy_pred_from {} m2"
  shows "IDC_Property.traces_satisfy_pred_from {} (if c then m1 else m2)"
  using assms
  by auto

lemma instr_exp_assms_IDC_Property_letE:
  assumes "instr_exp_assms (let x = y in f x)"
    and "instr_exp_assms (f y) \<Longrightarrow> IDC_Property.traces_satisfy_pred_from {} (f y)"
  shows "IDC_Property.traces_satisfy_pred_from {} (let x = y in f x)"
  using assms
  by auto

lemma IDC_Property_bind_write_ThisInstrAbstract:
  assumes "instr_exp_assms (seq (write_reg ThisInstrAbstract_ref i) m)"
    and "instr_of_trace (trace (instr_trace instr t)) = Some i \<Longrightarrow> IDC_Property.traces_satisfy_pred_from {} m"
  shows "IDC_Property.traces_satisfy_pred_from {} (seq (write_reg ThisInstrAbstract_ref i) m)"
  using assms
  unfolding instr_exp_assms_def invocation_instr_exp_assms_write_ThisInstrAbstract_iff
  by (intro no_reg_writes_to_traces_satisfy_pred_from_bind_left)
     (auto simp: register_defs no_reg_writes_to_write_reg[THEN no_reg_writes_runs_no_reg_writes])

lemma IDC_Property_without_data_invocation:
  assumes "invoked_data_reg = None"
    and "indirect_sentry_type = None"
  shows "IDC_Property.traces_satisfy_pred_from {} m"
  using assms
  unfolding IDC_Property.traces_satisfy_pred_from_def idc_write_axiom_from_def
  by (auto simp: instr_invokes_data_caps_def trace_invokes_data_cap_from_reg_def
                 trace_indirectly_invokes_data_caps_def trace_indirect_sentry_type_def)

lemma IDC_Property_no_ThisInstrAbstract:
  assumes "instr_exp_assms m"
    and "no_reg_writes_to {''__ThisInstrAbstract''} m"
  shows "IDC_Property.traces_satisfy_pred_from {} m"
  using assms(1) no_reg_writes_to_instr_of_exp[OF assms(2)]
  unfolding instr_exp_assms_def invocation_instr_exp_assms_def
  by (intro IDC_Property_without_data_invocation) auto

lemma IDC_Property_DecodeA64:
  assumes "instr_exp_assms (DecodeA64 pc opcode)"
  shows "IDC_Property.traces_satisfy_pred_from {} (DecodeA64 pc opcode)"
  using assms
  by (unfold DecodeA64_def, elim instr_exp_assms_IDC_Property_ifE instr_exp_assms_IDC_Property_letE)
     ((erule IDC_Property_bind_write_ThisInstrAbstract,
       solves \<open>(rule IDC_Property_data_invocation_instrs, auto simp: Points_to_PCC_invoked_data_caps_eq_indirect_sentries Points_to_Pair_no_invoked_data_caps_without_indirect_sentries instr_invokes_indirect_caps_def)
              | (rule IDC_Property_without_data_invocation, solves \<open>simp\<close>, solves \<open>simp\<close>)\<close>)
      | (erule IDC_Property_no_ThisInstrAbstract, solves \<open>no_reg_writes_toI\<close>))+

(* TODO: BranchTaken *)

end

end
