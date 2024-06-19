theory CHERI_PCC_Properties
  imports
    "Sail-Morello.Morello_lemmas"
    CHERI_Instantiation
    CHERI_Lemmas
    Trace_Properties
begin

definition idc_write_axiom'  :: \<open> 'cap Capability_class \<Rightarrow>('cap,'regval,'instr,'e)isa \<Rightarrow> 'cap set \<Rightarrow> nat \<Rightarrow> ('regval,'instr)isa_trace \<Rightarrow> bool \<close>  where
     \<open> idc_write_axiom' CC ISA initial_caps n t = (
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
    and "idc_write_axiom' CC ISA initial_caps n t"
    and "disjnt (PCC ISA) (IDC ISA)"
  shows "idc_write_axiom CC ISA initial_caps n t"
proof (unfold idc_write_axiom_def, intro allI impI)
  fix i c idc
  assume *: "i < n \<and> writes_to_reg_at_idx i t = Some idc \<and> idc \<in> IDC ISA \<and> c \<in> writes_reg_caps_at_idx CC ISA i t"
  then have c: "cap_derivable CC (initial_caps \<union> available_caps CC ISA i t) c \<or> is_invoked_data_cap_at_idx CC ISA c t i"
    using assms
    unfolding store_cap_reg_axiom_def
    by (elim allE[where x = i] allE[where x = c] allE[where x = idc]) (auto simp: disjnt_iff)
  then show "cap_derivable CC (initial_caps \<union> available_caps CC ISA i t) c \<or>
             (\<exists>cc. trace_writes_pcc_caps ISA t = {cc} \<and> (is_tagged_method CC cc \<longrightarrow> cc \<in> trace_invokes_code_caps ISA t))"
    using assms *
    by (auto simp: idc_write_axiom'_def)
qed

lemma no_invoked_data_caps_idc_write_axiom:
  assumes "store_cap_reg_axiom CC ISA initial_caps n t"
    and "trace_invokes_data_caps ISA t = {}"
    and "disjnt (PCC ISA) (IDC ISA)"
  shows "idc_write_axiom CC ISA initial_caps n t"
proof (unfold idc_write_axiom_def, intro allI impI)
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
  where pred = idc_write_axiom_from and ev_assms = "\<lambda>e. invocation_ev_assms e \<and> wellformed_ev e"
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
  shows "idc_write_axiom' CC ISA UNKNOWN_caps n (instr_trace instr t)"
  using assms
  apply (auto simp: idc_write_axiom_from_def idc_write_axiom'_def trace_writes_pcc_caps_pcc_regvals_of_trace
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
  by (fastforce simp: IDC_Property.traces_satisfy_pred_from_def idc_write_axiom_append_no_reg_writes_right no_reg_writes_to_def hasTrace_iff_Traces_final final_bind_iff
                elim!: bind_Traces_cases)

definition
  "trace_writes_invoked_code_cap s t \<equiv>
     (\<exists>cc. s \<union> pcc_regvals_of_trace t = {Regval_bitvector_129_dec cc} \<and> (CapIsTagSet cc \<longrightarrow> cc \<in> invoked_code_caps))"

(* abbreviation "trace_writes_invoked_code_cap_assms s t \<equiv> invocation_trace_assms t \<and> wellformed_trace t \<longrightarrow> trace_writes_invoked_code_cap s t" *)

sublocale PCC_Writes: Stateful_Full_Trace_Property
  where pred = trace_writes_invoked_code_cap and ev_assms = "\<lambda>e. invocation_ev_assms e \<and> wellformed_ev e"
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
  by (auto simp: idc_write_axiom_from_Cons_write_reg_if invocation_trace_assms_def dest: hasFailure_R_set_Nil
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

abbreviation "wellformed_reg r \<equiv> (map_of registers (name r) = Some (register_ops_of r))"

lemma wellformed_regs:
  "wellformed_reg PCC_ref"
  "wellformed_reg PSTATE_ref"
  "wellformed_reg SCR_EL3_ref"
  "wellformed_reg TCR_EL1_ref"
  "wellformed_reg TCR_EL2_ref"
  "wellformed_reg TCR_EL3_ref"
  "wellformed_reg HCR_EL2_ref"
  "wellformed_reg EDSCR_ref"
  by (auto simp: register_defs)

lemma exp_succeeds_read_reg:
  assumes "map_of registers (name r) = Some (register_ops_of r)"
  shows "exp_succeeds (read_reg r)"
  using assms
  by (auto simp: read_reg_def exp_ends_with_def runTrace_iff_Traces register_ops_of_def
           elim!: Read_reg_TracesE final_cases split: option.splits dest!: wellformed_reg_reads (*map_of_SomeD*))

lemmas exp_succeeds_read_regs[intro, simp] = wellformed_regs[THEN exp_succeeds_read_reg]

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
  by (fastforce elim!: hasTrace_bind_cases simp: exp_ends_with_def hasFailure_iff_runTrace hasException_iff_runTrace)

lemma PCC_Writes_traces_satisfy_pred_from_bind_left:
  assumes "PCC_Writes.traces_satisfy_pred_from {} m"
    and "\<And>a. no_reg_writes_to {''PCC''} (f a)"
  shows "PCC_Writes.traces_satisfy_pred_from {} (bind m f)"
  using assms no_reg_writes_to_PCC_no_pcc_regvals_of_trace[OF assms(2)]
  unfolding PCC_Writes.traces_satisfy_pred_from_def
  unfolding trace_writes_invoked_code_cap_def
  by (auto simp: hasTrace_iff_Traces_final hasFailure_iff_Traces_Fail hasException_iff_Traces_Exception final_bind_iff
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
  unfolding BranchToCapability_def Let_def
  apply (intro PCC_Writes_bind_write_reg_PCC PCC_Writes_traces_satisfy_pred_from_bind_right exp_succeeds_UsingAArch32)
  subgoal
    apply (use assms in \<open>auto elim!: BranchAddr_branch_caps_tagged_unsealed\<close>)
    done
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

(* lemmas traces_satisfy_pred_from_bind_if_split = if_split[where P = "\<lambda>m. traces_satisfy_pred_from s (bind m f)" for f s] *)

lemma
  shows "IDC_Property.traces_satisfy_pred_from {} (execute_BR_CI_C branch_type n offset)"
  unfolding execute_BR_CI_C_def Let_def if_distrib[where f = "\<lambda>m. Sail2_prompt_monad.bind m f" and c = "n = 29" for f] bind_assoc bind_return
  (* apply (intro traces_satisfy_pred_from_if no_reg_writes_to_traces_satisfy_pred_from_bind_left) *)
  apply (rule no_reg_writes_to_traces_satisfy_pred_from_bind_left, no_reg_writes_toI, no_reg_writes_toI)
  apply (rule no_reg_writes_to_traces_satisfy_pred_from_bind_left, no_reg_writes_toI, no_reg_writes_toI)
  apply (rule no_reg_writes_to_traces_satisfy_pred_from_bind_left, no_reg_writes_toI, no_reg_writes_toI)
  apply (rule no_reg_writes_to_traces_satisfy_pred_from_bind_left, no_reg_writes_toI, no_reg_writes_toI)
  (* apply (rule traces_satisfy_pred_from_bind_if_split[where Q = "n = 29", THEN iffD2], (rule conjI; rule impI)) *)
  apply (rule IDC_Property.traces_satisfy_pred_from_if)
  apply (rule no_reg_writes_to_traces_satisfy_pred_from_bind_left, no_reg_writes_toI, no_reg_writes_toI)
  apply (rule no_reg_writes_to_traces_satisfy_pred_from_bind_left, no_reg_writes_toI, no_reg_writes_toI)
  apply (rule no_reg_writes_to_traces_satisfy_pred_from_bind_left, no_reg_writes_toI, no_reg_writes_toI)
  apply (rule no_reg_writes_to_traces_satisfy_pred_from_bind_left, no_reg_writes_toI, no_reg_writes_toI)
  apply (rule no_reg_writes_to_traces_satisfy_pred_from_bind_left, no_reg_writes_toI, no_reg_writes_toI)
  apply (rule traces_satisfy_pred_from_bind_C_set[where n = 29])
  subgoal
    apply (intro impI PCC_Writes_traces_satisfy_pred_from_bind_right PCC_Write_BranchXToCapability)
    subgoal
      sorry
     apply (no_reg_writes_toI)
    apply auto
    done
  apply (no_reg_writes_toI)
  apply (rule no_reg_writes_to_traces_satisfy_pred_from_bind_left, no_reg_writes_toI, no_reg_writes_toI)+
  apply (rule no_reg_writes_to_R29_traces_satisfy_pred_from[where Rs = "{''_R29''}"], no_reg_writes_toI, auto)
  done

lemma Points_to_PCC_invoked_data_caps_eq_indirect_sentries:
  assumes "trace_indirect_sentry_type t = Some Points_to_PCC"
  shows "instr_invokes_data_caps instr t = trace_invokes_indirect_sentries t"
  using assms
  by (auto simp: trace_indirect_sentry_type_def instr_invokes_data_caps_def trace_indirectly_invokes_data_caps_def bind_eq_Some_conv
           elim!: instr_indirect_sentry_type.elims)

end

end
