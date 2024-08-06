theory CHERI_PCC_Properties
  imports
    "Sail-Morello.Morello_lemmas"
    CHERI_Instantiation
    CHERI_Lemmas
    Trace_Properties
    "Sail-T-CHERI.Trace_Subset"
    "Sail-T-CHERI.No_Exception"
begin

(* In the case of an invocation, PSTATE.C64 will be set to the LSB of the invoked code capability *)

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
definition initial_mem_cap_loads_of_trace where
  "initial_mem_cap_loads_of_trace t \<equiv>
     {(paddr, c) | paddr c wk bytes tag i.
        i < length t \<and>
        t ! i = E_read_memt wk paddr 16 (bytes, tag) \<and>
        cap_of_mem_bytes bytes tag = Some c \<and>
        no_mem_writes_in_trace (take i t)}"

definition initial_mem_cap_vaddr_loads_of_trace where
  "initial_mem_cap_vaddr_loads_of_trace t \<equiv>
     {(vaddr, c) | vaddr c wk paddr bytes tag i.
        i < length t \<and>
        t ! i = E_read_memt wk paddr 16 (bytes, tag) \<and>
        cap_of_mem_bytes bytes tag = Some c \<and>
        translate_address vaddr = Some paddr \<and>
        no_mem_writes_in_trace (take i t)}"

abbreviation instr_trace_may_invoke where
  "instr_trace_may_invoke opcode t \<equiv> trace_invokes_code_cap_from_reg t \<noteq> None \<or> trace_indirect_sentry_type t \<noteq> None \<or> trace_invokes_data_cap_from_reg t \<noteq> None"

definition branch_instr_run_has_expected_gpr_reads where
  "branch_instr_run_has_expected_gpr_reads t \<equiv>
     (\<forall>n. trace_invokes_code_cap_from_reg t = Some n \<or> trace_invokes_data_cap_from_reg t = Some n \<or>
          trace_load_auths t = Some (RegAuth n) \<longrightarrow>
           (\<exists>c. trace_reads_caps_from_gpr n t = {c} \<and> trace_reads_initial_caps_from_gpr n t = {c}))"

definition branch_instr_run_has_expected_pstate_writes where
  "branch_instr_run_has_expected_pstate_writes opcode t \<equiv>
     (\<forall>cc' \<in> instr_invokes_code_caps opcode t.
         CapIsTagSet cc' \<longrightarrow>
           (\<exists>cc \<in> original_code_caps_invoked_in_trace t. pstate_c64_writes t = {lsb cc}))"

definition branch_instr_run_performs_expected_invocation where
  "branch_instr_run_performs_expected_invocation opcode t \<equiv>
     instr_trace_may_invoke opcode t \<longrightarrow>
     (\<exists>cc. trace_writes_pcc_caps ISA (instr_trace opcode t) = {cc} \<and>
           (CapIsTagSet cc \<longrightarrow> cc \<in> instr_invokes_code_caps opcode t)) \<and>
     (instr_invokes_data_caps opcode t = {} \<or>
        (\<exists>cd. trace_writes_idc_caps ISA (instr_trace opcode t) = {cd} \<and> cd \<in> instr_invokes_data_caps opcode t))"

definition trace_has_reg_load_auth_for_addr where
  "trace_has_reg_load_auth_for_addr t auth vaddr sz \<equiv>
     (\<exists>n. trace_load_auths t = Some (RegAuth n) \<and>
          auth \<in> trace_reads_caps_from_gpr n t \<and>
          CapIsTagSet auth \<and>
          set (address_range (bounds_address AccType_NORMAL vaddr) sz) \<subseteq> get_mem_region CC auth)"

definition branch_instr_run_has_expected_invocation_loads where
  "branch_instr_run_has_expected_invocation_loads t \<equiv>
     (case trace_indirect_sentry_type t of
        Some Points_to_PCC \<Rightarrow>
          (\<exists>auth paddr vaddr c.
              trace_has_reg_load_auth_for_addr t auth vaddr 16 \<and>
              (get_indirect_sentry_type auth = Some Points_to_PCC \<and> CapUnseal auth \<in> trace_invokes_indirect_sentries t \<or> \<not>CapIsSealed auth) \<and>
              \<comment> \<open>initial_mem_cap_vaddr_loads_of_trace t = {(vaddr, c)} \<and>
              mem_cap_vaddr_loads_of_trace t \<subseteq> initial_mem_cap_vaddr_loads_of_trace t \<and>\<close>
              translate_address vaddr = Some paddr \<and>
              initial_mem_cap_loads_of_trace t = {(paddr, c)} \<and>
              mem_cap_loads_of_trace t = {(paddr, c) | paddr c. (paddr, c) \<in> initial_mem_cap_loads_of_trace t \<and> CapIsTagSet c})
      | Some Points_to_Pair \<Rightarrow>
          (\<exists>auth paddr_cc paddr_cd cc cd.
              trace_has_reg_load_auth_for_addr t auth (unat (CapGetValue auth)) 32 \<and>
              (get_indirect_sentry_type auth = Some Points_to_Pair \<and> CapUnseal auth \<in> trace_invokes_indirect_sentries t \<or> \<not>CapIsSealed auth) \<and>
              \<comment> \<open>initial_mem_cap_vaddr_loads_of_trace t = {(unat (CapGetValue auth), cd), (unat (CapGetValue auth) + 16, cc)} \<and>
              mem_cap_vaddr_loads_of_trace t \<subseteq> initial_mem_cap_vaddr_loads_of_trace t \<and>\<close>
              translate_address (unat (CapGetValue auth)) = Some paddr_cd \<and>
              translate_address (unat (CapGetValue auth) + 16) = Some paddr_cc \<and>
              initial_mem_cap_loads_of_trace t = {(paddr_cd, cd), (paddr_cc, cc)} \<and>
              mem_cap_loads_of_trace t = {(paddr, c) | paddr c. (paddr, c) \<in> initial_mem_cap_loads_of_trace t \<and> CapIsTagSet c} \<and>
              unat (CapGetValue auth + 16) = unat (CapGetValue auth) + 16 \<and>
              bounds_address AccType_NORMAL (unat (CapGetValue auth) + 16) = bounds_address AccType_NORMAL (unat (CapGetValue auth)) + 16)
      | None \<Rightarrow> True)"

definition branch_instr_trace_has_expected_exceptions where
  "branch_instr_trace_has_expected_exceptions opcode t \<equiv>
     (\<forall>e. (instr_sem opcode, t, Exception e) \<in> Traces \<longrightarrow>
          trace_writes_idc_caps ISA (instr_trace opcode t) = {} \<and>
          is_singleton (trace_writes_pcc_caps ISA (instr_trace opcode t)) \<and>
          e = Error_ExceptionTaken ())"

definition branch_instr_trace_has_expected_invocations where
  "branch_instr_trace_has_expected_invocations opcode t \<longleftrightarrow>
     (Run (instr_sem opcode) t () \<longrightarrow>
        branch_instr_run_performs_expected_invocation opcode t \<and>
        branch_instr_run_has_expected_gpr_reads t \<and>
        branch_instr_run_has_expected_invocation_loads t \<and>
        branch_instr_run_has_expected_pstate_writes opcode t)
     \<and>
     branch_instr_trace_has_expected_exceptions opcode t"

(* "Other" instructions not denoted by an instruction AST node definitely won't perform an invocation *)
lemma instr_of_trace_None_instr_invokes_no_caps:
  assumes "instr_of_trace t = None"
  shows "instr_invokes_code_caps instr t = {}"
    and "instr_invokes_data_caps instr t = {}"
    and "instr_invokes_indirect_caps instr t = {}"
  using assms
  by (auto simp: trace_invoked_cap_defs)

end

text \<open>Helper definitions - TODO: Move\<close>

lemmas monad_trace_subset_datatype_splits[monad_trace_subset_intro] =
  datatype_splits[where P="monad_trace_subset _", THEN iffD2]

lemma monad_trace_subset_ConstrainUnpredictable[monad_trace_subset]:
  "monad_trace_subset {} (ConstrainUnpredictable u)"
  by (cases u) (auto simp: monad_trace_subset_return)

setup \<open>Monad_Trace_Subset_Exploration.install_recs
  ["Morello_bindings", "Morello"]
  @{thms execute_LDPBLR_C_C_C_def}
\<close>

find_theorems monad_trace_subset execute_LDPBLR_C_C_C
find_theorems monad_trace_subset VACheckAddress

lemmas monad_no_exception_datatype_splits[monad_no_exception_intro] =
  datatype_splits[where P="monad_no_exception _", THEN iffD2]

lemma monad_no_exception_ConstrainUnpredictable[monad_no_exception]:
  "monad_no_exception {} (ConstrainUnpredictable u)"
  by (cases u) (auto simp: monad_no_exception_return)

lemma monad_no_exception_IsSecureBelowEL3[monad_no_exception]:
  "monad_no_exception {} (IsSecureBelowEL3 el)"
  by (auto simp: IsSecureBelowEL3_def SCR_GEN_read_def HaveEL_def
           intro: monad_no_exception_bind_simple monad_no_exception)

lemma monad_no_exception_HaveRASExt[monad_no_exception]:
  "monad_no_exception {} (HaveRASExt u)"
  by (auto simp: HaveRASExt_def intro: monad_no_exception)

lemma monad_no_exception_HaveIESB[monad_no_exception]:
  "monad_no_exception {} (HaveIESB u)"
  by (auto simp: HaveIESB_def HaveRASExt_def IMPDEF_boolean_def IMPDEF_boolean_map_def intro: monad_no_exception)

lemma monad_no_exception_HaveSSBSExt[monad_no_exception]:
  "monad_no_exception {} (HaveSSBSExt u)"
  by (auto simp: HaveSSBSExt_def IMPDEF_boolean_def IMPDEF_boolean_map_def intro: monad_no_exception)

lemma monad_no_exception_HaveMPAMExt[monad_no_exception]:
  "monad_no_exception {} (HaveMPAMExt u)"
  by (auto simp: HaveMPAMExt_def IMPDEF_boolean_def IMPDEF_boolean_map_def intro: monad_no_exception)

lemma monad_no_exception_Have16bitVMID[monad_no_exception]:
  "monad_no_exception {} (Have16bitVMID u)"
  (* FIXME *)
  (* by (auto simp: Have16bitVMID_def IMPDEF_boolean_def IMPDEF_boolean_map_def intro: monad_no_exception) *)
  sorry

setup \<open>Monad_No_Exception_Exploration.install_recs
  ["Morello_bindings", "Morello"]
  @{thms execute_LDPBLR_C_C_C_def}
\<close>

text \<open>Yet another Hoare logic\<close>

locale Hoare_Logic =
  fixes ev_assms :: "'state \<Rightarrow> 'regval event \<Rightarrow> bool"
    and step_state :: "'state \<Rightarrow> 'regval event \<Rightarrow> 'state"
begin

abbreviation run_state :: "'state \<Rightarrow> 'regval trace \<Rightarrow> 'state" where
  "run_state \<equiv> foldl step_state"

fun trace_assms :: "'state \<Rightarrow> 'regval trace \<Rightarrow> bool" where
  "trace_assms s (e # t) \<longleftrightarrow> ev_assms s e \<and> trace_assms (step_state s e) t"
| "trace_assms s [] \<longleftrightarrow> True"

lemma trace_assms_append[simp]:
  "trace_assms s (t1 @ t2) \<longleftrightarrow> trace_assms s t1 \<and> trace_assms (run_state s t1) t2"
  by (induction t1 arbitrary: s) auto

definition
  "pre_post P m Q E F \<equiv>
     (\<forall>s t m'. (m, t, m') \<in> Traces \<and> trace_assms s t \<and> P s
               \<longrightarrow>
               (case m' of
                  Done a \<Rightarrow> Q a (run_state s t)
                | Exception e \<Rightarrow> E e (run_state s t)
                | Fail msg \<Rightarrow> F msg (run_state s t)
                | _ \<Rightarrow> True))"

abbreviation "pre_post_ignore_fail P m Q E \<equiv> pre_post P m Q E (\<lambda>_ _. True)"

lemma pre_postI:
  assumes "\<And>s t a. Run m t a \<Longrightarrow> P s \<Longrightarrow> trace_assms s t \<Longrightarrow> Q a (run_state s t)"
    and "\<And>s t e. (m, t, Exception e) \<in> Traces \<Longrightarrow> P s \<Longrightarrow> trace_assms s t \<Longrightarrow> E e (run_state s t)"
    and "\<And>s t d. (m, t, Fail d) \<in> Traces \<Longrightarrow> P s \<Longrightarrow> trace_assms s t \<Longrightarrow> F d (run_state s t)"
  shows "pre_post P m Q E F"
  using assms
  by (auto simp: pre_post_def split: monad.split)

lemma pre_post_RunE:
  assumes "pre_post P m Q E F" and "Run m t a" and "P s" and "trace_assms s t"
  shows "Q a (run_state s t)"
  using assms
  by (fastforce simp: pre_post_def)

lemma pre_post_ExceptionE:
  assumes "pre_post P m Q E F" and "(m, t, Exception e) \<in> Traces" and "P s" and "trace_assms s t"
  shows "E e (run_state s t)"
  using assms
  by (fastforce simp: pre_post_def)

lemma pre_post_FailE:
  assumes "pre_post P m Q E F" and "(m, t, Fail d) \<in> Traces" and "P s" and "trace_assms s t"
  shows "F d (run_state s t)"
  using assms
  by (fastforce simp: pre_post_def)

lemma pre_post_consequence:
  assumes "pre_post P' m Q' E' F'"
    and "\<And>s. P s \<Longrightarrow> P' s"
    and "\<And>a s. Q' a s \<Longrightarrow> Q a s"
    and "\<And>e s. E' e s \<Longrightarrow> E e s"
    and "\<And>msg s. F' msg s \<Longrightarrow> F msg s"
  shows "pre_post P m Q E F"
  using assms
  by (fastforce simp: pre_post_def split: monad.split)

lemma pre_post_strengthen_pre:
  assumes "pre_post P' m Q F E"
    and "\<And>s. P s \<Longrightarrow> P' s"
  shows "pre_post P m Q F E"
  using assms
  by (rule pre_post_consequence)

lemma pre_post_return:
  "pre_post (Q a) (return a) Q E F"
  by (auto simp: pre_post_def)

lemma pre_post_bind:
  assumes f: "\<And>s t a. Run m t a \<Longrightarrow> P s \<Longrightarrow> trace_assms s t \<Longrightarrow> pre_post (R a) (f a) Q E F"
    and m: "pre_post P m R E F"
  shows "pre_post P (bind m f) Q E F"
  by (intro pre_postI;
      fastforce elim!: Run_bindE bind_Exception_cases bind_Fail_cases
                elim: m[THEN pre_post_ExceptionE] f[THEN pre_post_ExceptionE, rotated 3]
                      m[THEN pre_post_FailE] f[THEN pre_post_FailE, rotated 3]
                      m[THEN pre_post_RunE] f[THEN pre_post_RunE, rotated 3])

lemma pre_post_read_reg:
  "pre_post
     (\<lambda>s. \<forall>e v a. e = E_read_reg (name r) v \<and> ev_assms s e
            \<longrightarrow>
          (case of_regval r v of
             Some a \<Rightarrow> Q a (step_state s e)
           | None \<Rightarrow> F ''read_reg: unrecognised value'' (step_state s e)))
     (read_reg r) Q E F"
  by (intro pre_postI; fastforce simp: read_reg_def elim: Traces_cases split: option.splits)

lemma pre_post_write_reg:
  "pre_post
     (\<lambda>s. \<forall>e. e = E_write_reg (name r) (regval_of r v) \<and> ev_assms s e \<longrightarrow> Q () (step_state s e))
     (write_reg r v) Q E F"
  by (intro pre_postI) (auto simp: write_reg_def elim: Traces_cases)

lemma pre_post_read_memt_BC:
  "pre_post
     (\<lambda>s. case nat_of_bv BCa addr of
            Some addr' \<Rightarrow>
              (\<forall>e bytes tag.
                 e = E_read_memt rk addr' (nat sz) (bytes, tag) \<and> ev_assms s e \<longrightarrow>
                 (case of_bits_method BCb (bits_of_mem_bytes bytes) of
                    Some v \<Rightarrow> Q (v, tag) (step_state s e)
                  | None \<Rightarrow> F ''bits_of_mem_bytes'' (step_state s e)))
          | None \<Rightarrow> F ''nat_of_bv'' s)
     (read_memt BCa BCb rk addr sz) Q E F"
  by (intro pre_postI;
      fastforce simp: read_memt_def read_memt_bytes_def maybe_fail_def elim: Traces_cases split: option.splits)

lemma pre_post_read_memt:
  "pre_post
     (\<lambda>s. (\<forall>e bytes tag.
             e = E_read_memt rk (unat addr) (nat sz) (bytes, tag) \<and> ev_assms s e \<longrightarrow>
             (case of_bits_method BC_mword (bits_of_mem_bytes bytes) of
                Some v \<Rightarrow> Q (v, tag) (step_state s e)
              | None \<Rightarrow> F ''bits_of_mem_bytes'' (step_state s e))))
     (read_memt BC_mword BC_mword rk addr sz) Q E F"
  by (intro pre_post_read_memt_BC[THEN pre_post_strengthen_pre]) auto

lemma pre_post_throw:
  "pre_post (E e) (throw e) Q E F"
  by (intro pre_postI; auto simp: throw_def)

lemma pre_post_ignore_fail_assert_exp:
  "pre_post_ignore_fail (\<lambda>s. b \<longrightarrow> Q () s) (assert_exp b msg) Q E"
  by (rule pre_postI) (auto simp: assert_exp_def split: if_splits)

definition "no_state_update m \<equiv> (\<forall>s t m'. (m, t, m') \<in> Traces \<and> trace_assms s t \<longrightarrow> run_state s t = s)"

lemma pre_post_no_state_update:
  assumes "no_state_update m"
  shows "pre_post
           (\<lambda>s. \<forall>t m'. runTrace t m = Some m' \<and> trace_assms s t \<longrightarrow>
                         (case m' of Done a \<Rightarrow> Q a s | Exception e \<Rightarrow> E e s | Fail d \<Rightarrow> F d s | _ \<Rightarrow> True))
           m Q E F"
  by (intro pre_postI)
     (use assms in \<open>auto simp add: no_state_update_def simp flip: runTrace_iff_Traces split: monad.splits\<close>)

lemma monad_no_exceptionD':
  assumes "monad_no_exception S m"
  shows "\<forall>t e. e \<notin> S \<longrightarrow> (m, t, Exception e) \<notin> Traces"
  by (use assms in \<open>auto simp: monad_no_exception_def\<close>)

lemma pre_post_no_state_update_no_exception:
  assumes "no_state_update m"
    and "monad_no_exception {} m"
  shows "pre_post
           (\<lambda>s. \<forall>t m'. runTrace t m = Some m' \<and> trace_assms s t \<longrightarrow>
                         (case m' of Done a \<Rightarrow> Q a s | Fail d \<Rightarrow> F d s | _ \<Rightarrow> True))
           m Q E F"
  by (intro pre_post_no_state_update[THEN pre_post_strengthen_pre])
     (use assms in \<open>auto simp: runTrace_iff_Traces dest: monad_no_exceptionD' split: monad.splits\<close>)

lemma pre_post_ignore_fail_no_state_update_no_exception:
  assumes "no_state_update m"
    and "monad_no_exception {} m"
  shows "pre_post_ignore_fail (\<lambda>s. \<forall>t a. Run m t a \<and> trace_assms s t \<longrightarrow> Q a s) m Q E"
  by (intro pre_post_no_state_update_no_exception[THEN pre_post_strengthen_pre])
     (use assms in \<open>auto simp: runTrace_iff_Traces split: monad.split\<close>)

lemma pre_post_ignore_fail_no_state_update_no_exception_ignore_result:
  assumes "no_state_update m"
    and "monad_no_exception {} m"
  shows "pre_post_ignore_fail Q m (\<lambda>_ s. Q s) E"
  by (rule pre_post_strengthen_pre,
      rule pre_post_ignore_fail_no_state_update_no_exception[OF assms])
     auto

lemma pre_post_if:
  assumes "b \<Longrightarrow> pre_post P1 m1 Q E F" and "\<not>b \<Longrightarrow> pre_post P2 m2 Q E F"
  shows "pre_post (\<lambda>s. if b then P1 s else P2 s) (if b then m1 else m2) Q E F"
  by (use assms in auto)

lemma pre_post_if_common_pre:
  assumes "b \<Longrightarrow> pre_post P m1 Q E F" and "\<not>b \<Longrightarrow> pre_post P m2 Q E F"
  shows "pre_post P (if b then m1 else m2) Q E F"
  by (use assms in auto)

lemma pre_post_if_post_collapse:
  assumes "pre_post P m Q E F"
  shows "pre_post P m (\<lambda>a s. if b then Q a s else Q a s) E F"
  by (use assms in auto)

end

definition no_reads_from_gpr where
  "no_reads_from_gpr n m \<equiv> (\<forall>t m' r v. (m, t, m') \<in> Traces \<and> r \<in> R_name n \<longrightarrow> E_read_reg r v \<notin> set t)"

definition no_reads_from_any_gpr where
  "no_reads_from_any_gpr m \<equiv> (\<forall>n. no_reads_from_gpr n m)"

definition no_writes_to_gpr where
  "no_writes_to_gpr n m \<equiv> (\<forall>t m' r v. (m, t, m') \<in> Traces \<and> r \<in> R_name n \<longrightarrow> E_write_reg r v \<notin> set t)"

definition no_writes_to_any_gpr where
  "no_writes_to_any_gpr m \<equiv> (\<forall>n. no_writes_to_gpr n m)"

definition no_accesses_to_gpr where
  "no_accesses_to_gpr n m \<equiv> no_reads_from_gpr n m \<and> no_writes_to_gpr n m"

definition no_accesses_to_any_gpr where
  "no_accesses_to_any_gpr m \<equiv> no_reads_from_any_gpr m \<and> no_writes_to_any_gpr m"

definition no_mem_cap_reads where
  "no_mem_cap_reads m \<equiv> (\<forall>t m' rk addr sz val. (m, t, m') \<in> Traces \<longrightarrow> E_read_memt rk addr sz val \<notin> set t)"

definition no_gpr_accesses_or_mem_cap_reads where
  "no_gpr_accesses_or_mem_cap_reads m \<equiv> no_accesses_to_any_gpr m \<and> no_mem_cap_reads m"

definition "all_R_names \<equiv> {''_R00'', ''_R01'', ''_R02'', ''_R03'', ''_R04'', ''_R05'', ''_R06'',
  ''_R07'', ''_R08'', ''_R09'', ''_R10'', ''_R11'', ''_R12'', ''_R13'', ''_R14'', ''_R15'', ''_R16'',
  ''_R17'', ''_R18'', ''_R19'', ''_R20'', ''_R21'', ''_R22'', ''_R23'', ''_R24'', ''_R25'',  ''_R26'',
  ''_R27'', ''_R28'', ''_R29'', ''_R30'', ''RSP_EL0'', ''SP_EL0'', ''SP_EL1'', ''SP_EL2'', ''SP_EL3''}"

lemma R_name_in_all_R_names:
  "r \<in> R_name n \<Longrightarrow> r \<in> all_R_names"
  by (auto simp: R_name_def all_R_names_def split: if_splits)

lemma all_R_names_R_name:
  assumes "r \<in> all_R_names"
  shows "\<exists>n. r \<in> R_name n"
  sorry

lemma all_R_names_iff_R_name:
  "r \<in> all_R_names \<longleftrightarrow> (\<exists>n. r \<in> R_name n)"
  by (auto intro: R_name_in_all_R_names elim: all_R_names_R_name)

lemma R29_all_R_names:
  "''_R29'' \<in> all_R_names"
  by (auto simp: all_R_names_def)

lemma monad_trace_subset_no_reads_from_gpr:
  assumes "monad_trace_subset S m"
    and "\<forall>r \<in> R_name n. disjnt (range (E_read_reg r)) S"
  shows "no_reads_from_gpr n m"
  using assms
  by (fastforce simp: no_reads_from_gpr_def monad_trace_subset_def disjnt_def)

lemma monad_trace_subset_no_reads_from_any_gpr:
  assumes "monad_trace_subset S m"
    and "\<forall>r \<in> all_R_names. disjnt (range (E_read_reg r)) S"
  shows "no_reads_from_any_gpr m"
  using assms
  unfolding no_reads_from_any_gpr_def
  by (intro allI monad_trace_subset_no_reads_from_gpr[of S m]) (auto dest: R_name_in_all_R_names)

lemma monad_trace_subset_no_writes_to_gpr:
  assumes "monad_trace_subset S m"
    and "\<forall>r \<in> R_name n. disjnt (range (E_write_reg r)) S"
  shows "no_writes_to_gpr n m"
  using assms
  by (fastforce simp: no_writes_to_gpr_def monad_trace_subset_def disjnt_def)

lemma monad_trace_subset_no_writes_to_any_gpr:
  assumes "monad_trace_subset S m"
    and "\<forall>r \<in> all_R_names. disjnt (range (E_write_reg r)) S"
  shows "no_writes_to_any_gpr m"
  using assms
  unfolding no_writes_to_any_gpr_def
  by (intro allI monad_trace_subset_no_writes_to_gpr[of S m]) (auto dest: R_name_in_all_R_names)

lemma monad_trace_subset_no_accesses_to_gpr:
  assumes "monad_trace_subset S m"
    and "\<forall>r \<in> R_name n. disjnt (range (E_read_reg r) \<union> range (E_write_reg r)) S"
  shows "no_accesses_to_gpr n m"
  using assms
  by (auto simp: no_accesses_to_gpr_def intro: monad_trace_subset_no_reads_from_gpr monad_trace_subset_no_writes_to_gpr)

lemma monad_trace_subset_no_accesses_to_any_gpr:
  assumes "monad_trace_subset S m"
    and "\<forall>r \<in> all_R_names. disjnt (range (E_read_reg r) \<union> range (E_write_reg r)) S"
  shows "no_accesses_to_any_gpr m"
  using assms
  by (auto simp: no_accesses_to_any_gpr_def intro: monad_trace_subset_no_reads_from_any_gpr monad_trace_subset_no_writes_to_any_gpr)

lemma monad_trace_subset_no_mem_cap_reads:
  assumes "monad_trace_subset S m"
    and "disjnt (range (\<lambda>(rk, addr, val, sz). E_read_memt rk addr sz val)) S"
  shows "no_mem_cap_reads m"
  using assms
  by (fastforce simp: no_mem_cap_reads_def monad_trace_subset_def disjnt_def)

lemma monad_trace_subset_no_gpr_accesses_or_mem_cap_reads:
  assumes "monad_trace_subset S m"
    and "disjnt (range (\<lambda>(rk, addr, val, sz). E_read_memt rk addr sz val)) S \<and> (\<forall>r \<in> all_R_names. disjnt (range (E_read_reg r) \<union> range (E_write_reg r)) S)"
  shows "no_gpr_accesses_or_mem_cap_reads m"
  using assms
  by (auto simp: no_gpr_accesses_or_mem_cap_reads_def intro: monad_trace_subset_no_mem_cap_reads monad_trace_subset_no_accesses_to_any_gpr)

lemma disjnt_range_event:
  "r \<noteq> r' \<Longrightarrow> disjnt (range (E_read_reg r)) (range (E_read_reg r'))"
  "disjnt (range (E_read_reg r)) (range (E_write_reg r'))"
  "disjnt (range (E_read_reg r)) (range (E_choose msg))"
  "disjnt (range (E_read_reg r)) (range (\<lambda>(rk, addr, val, sz). E_read_memt rk addr sz val))"
  "r \<noteq> r' \<Longrightarrow> disjnt (range (E_write_reg r)) (range (E_write_reg r'))"
  "disjnt (range (E_write_reg r)) (range (E_read_reg r'))"
  "disjnt (range (E_write_reg r)) (range (E_choose msg))"
  "disjnt (range (E_write_reg r)) (range (\<lambda>(rk, addr, val, sz). E_read_memt rk addr sz val))"
  "disjnt (range (\<lambda>(rk, addr, val, sz). E_read_memt rk addr sz val)) (range (E_read_reg r'))"
  "disjnt (range (\<lambda>(rk, addr, val, sz). E_read_memt rk addr sz val)) (range (E_write_reg r'))"
  "disjnt (range (\<lambda>(rk, addr, val, sz). E_read_memt rk addr sz val)) (range (E_choose msg))"
  by (auto simp: disjnt_def)

method no_reads_from_any_gpr =
  (rule monad_trace_subset[THEN monad_trace_subset_no_reads_from_any_gpr]
        monad_trace_subset[THEN monad_trace_subset_no_writes_to_any_gpr]
        monad_trace_subset[THEN monad_trace_subset_no_accesses_to_any_gpr]
        monad_trace_subset[THEN monad_trace_subset_no_gpr_accesses_or_mem_cap_reads];
   unfold all_R_names_def ball_simps disjnt_Un1 disjnt_Un2;
   intro conjI disjnt_empty2 disjnt_range_event;
   simp add: register_defs)

lemma no_reads_from_gpr_invocation_helper_functions:
  "\<And>u. no_gpr_accesses_or_mem_cap_reads (CheckCapabilitiesEnabled u)"
  by no_reads_from_any_gpr

fun ev_reads_from_reg_state :: "(register_name \<rightharpoonup> 'regval) \<Rightarrow> 'regval event \<Rightarrow> bool" where
  "ev_reads_from_reg_state s (E_read_reg r v) \<longleftrightarrow>
     (case s r of Some v' \<Rightarrow> v = v' | _ \<Rightarrow> True)"
| "ev_reads_from_reg_state s _ \<longleftrightarrow> True"

fun regs_sequential_in_trace :: "(register_name \<rightharpoonup> 'regval) \<Rightarrow> 'regval trace \<Rightarrow> bool" where
  "regs_sequential_in_trace s (E_read_reg r v # t) \<longleftrightarrow>
     (case s r of Some v' \<Rightarrow> v = v' | _ \<Rightarrow> True) \<and> regs_sequential_in_trace s t"
| "regs_sequential_in_trace s (E_write_reg r v # t) \<longleftrightarrow>
     regs_sequential_in_trace (if r \<in> dom s then s(r\<mapsto>v) else s) t"
| "regs_sequential_in_trace s (_ # t) \<longleftrightarrow> regs_sequential_in_trace s t"
| "regs_sequential_in_trace s [] \<longleftrightarrow> True"

record invocation_state =
  code_reg_caps :: "Capability set"
  data_reg_caps :: "Capability set"
  load_auth_caps :: "Capability set"
  mem_caps :: "(nat * Capability) set"
  reg_state :: "register_name \<rightharpoonup> register_value"
  pcc_writes :: "register_value list"
  idc_writes :: "register_value list"
  pstate_writes :: "register_value list"
  branch_taken_writes :: "register_value list"
  gprs_written :: bool
  gpr_reads_after_write :: bool

definition
  "initial_invocation_state regs \<equiv>
     \<lparr>code_reg_caps = {}, data_reg_caps = {}, load_auth_caps = {}, mem_caps = {},
      reg_state = regs, pcc_writes = [], idc_writes = [], pstate_writes = [],
      branch_taken_writes = [], gprs_written = False, gpr_reads_after_write = False\<rparr>"

locale Morello_Instr_Invocation_Property = Morello_ISA +
  fixes instr :: instr_ast
begin

definition is_code_reg :: "register_name \<Rightarrow> bool" where
  "is_code_reg r \<equiv> (\<exists>n. instr_invokes_code_cap_from_reg instr = Some n \<and> r \<in> R_name n)"

definition is_data_reg :: "register_name \<Rightarrow> bool" where
  "is_data_reg r \<equiv> (\<exists>n. instr_invokes_data_cap_from_reg instr = Some n \<and> r \<in> R_name n)"

definition is_indirect_reg :: "register_name \<Rightarrow> bool" where
  "is_indirect_reg r \<equiv> (\<exists>n. instr_invokes_indirect_cap_from_reg instr = Some n \<and> r \<in> R_name n)"

definition is_load_auth_reg :: "register_name \<Rightarrow> bool" where
  "is_load_auth_reg r \<equiv> (\<exists>n. instr_load_auth instr = Some (RegAuth n) \<and> r \<in> R_name n)"

definition "invocation_regs = all_R_names \<union> {''PCC'', ''PSTATE'', ''__BranchTaken''}"

fun step_state :: "invocation_state \<Rightarrow> register_value event \<Rightarrow> invocation_state" where
  "step_state s (E_read_reg r (Regval_bitvector_129_dec c)) =
    s\<lparr>code_reg_caps := (if is_code_reg r then insert c (code_reg_caps s) else code_reg_caps s),
      data_reg_caps := (if is_data_reg r then insert c (data_reg_caps s) else data_reg_caps s),
      load_auth_caps := (if is_load_auth_reg r then insert c (load_auth_caps s) else load_auth_caps s),
      gpr_reads_after_write := (if gprs_written s \<and> r \<in> all_R_names then True else gpr_reads_after_write s)\<rparr>"
| "step_state s (E_write_reg r v) =
    s\<lparr>\<comment> \<open>reg_state := (if r \<in> dom (reg_state s) \<inter> invocation_regs then (reg_state s)(r\<mapsto>v) else reg_state s),\<close>
      pcc_writes := (if r = ''PCC'' then v # pcc_writes s else pcc_writes s),
      idc_writes := (if r = ''_R29'' then v # idc_writes s else idc_writes s),
      pstate_writes := (if r = ''PSTATE'' then v # pstate_writes s else pstate_writes s),
      branch_taken_writes := (if r = ''__BranchTaken'' then v # branch_taken_writes s else branch_taken_writes s),
      gprs_written := (if r \<in> all_R_names then True else gprs_written s)\<rparr>"
| "step_state s (E_read_memt rk paddr sz (bytes, tag)) =
    (case cap_of_mem_bytes bytes tag of Some c \<Rightarrow> s\<lparr>mem_caps := insert (paddr, c) (mem_caps s)\<rparr> | None \<Rightarrow> s)"
| "step_state s e = s"

definition has_expected_gpr_reads :: "invocation_state \<Rightarrow> bool" where
  "has_expected_gpr_reads s \<longleftrightarrow>
     (instr_invokes_code_cap_from_reg instr \<noteq> None \<longrightarrow> is_singleton (code_reg_caps s)) \<and>
     (instr_invokes_data_cap_from_reg instr \<noteq> None \<longrightarrow> is_singleton (data_reg_caps s)) \<and>
     (\<forall>n. instr_load_auth instr = Some (RegAuth n) \<longrightarrow> is_singleton (load_auth_caps s)) \<and>
     \<not>gpr_reads_after_write s"

definition original_mem_code_caps :: "invocation_state \<Rightarrow> Capability set" where
  "original_mem_code_caps s \<equiv>
     {cc. \<exists>paddr.
             (paddr, cc) \<in> mem_caps s \<and>
             (instr_indirect_sentry_type instr = Some Points_to_Pair \<longrightarrow>
                (\<exists>auth \<in> load_auth_caps s. translate_address (unat (CapGetValue auth + 16)) = Some paddr))}"

definition "original_code_caps s \<equiv> code_reg_caps s \<union> original_mem_code_caps s"

definition invoked_code_caps :: "invocation_state \<Rightarrow> Capability set" where
  "invoked_code_caps s =
     \<Union>(branch_caps ` CapUnseal ` code_reg_caps s) \<union>
     \<Union>(mem_branch_caps ` original_mem_code_caps s)"

definition original_mem_data_caps :: "invocation_state \<Rightarrow> Capability set" where
  "original_mem_data_caps s \<equiv>
     {cc. \<exists>paddr.
             (paddr, cc) \<in> mem_caps s \<and>
             instr_indirect_sentry_type instr = Some Points_to_Pair \<and>
             (\<exists>auth \<in> load_auth_caps s. translate_address (unat (CapGetValue auth)) = Some paddr)}"

definition original_reg_data_caps :: "invocation_state \<Rightarrow> Capability set" where
  "original_reg_data_caps s \<equiv>
     (case instr_indirect_sentry_type instr of
        Some Points_to_PCC \<Rightarrow> load_auth_caps s
      | Some Points_to_Pair \<Rightarrow> {}
      | None \<Rightarrow> data_reg_caps s)"

definition invoked_data_caps :: "invocation_state \<Rightarrow> Capability set" where
  "invoked_data_caps s =
     (CapUnseal ` original_reg_data_caps s) \<union>
     \<Union>(mem_data_caps ` original_mem_data_caps s)"

definition has_expected_pstate_writes where
  "has_expected_pstate_writes s \<equiv>
     (\<forall>cc \<in> original_code_caps s.
        CapIsTagSet cc \<longrightarrow>
        (\<exists>pstate. pstate_writes s = [Regval_ProcState pstate] \<and> (test_bit (ProcState_C64 pstate) 0 = lsb cc)))"

definition has_expected_code_cap_invocation where
  "has_expected_code_cap_invocation s \<equiv>
     (\<exists>cc. pcc_writes s = [Regval_bitvector_129_dec cc] \<and> (CapIsTagSet cc \<longrightarrow> cc \<in> invoked_code_caps s))"

definition has_expected_data_cap_invocation where
  "has_expected_data_cap_invocation s \<equiv>
     (\<exists>cd. idc_writes s = [Regval_bitvector_129_dec cd] \<and>
           (invoked_data_caps s = {} \<or> cd \<in> invoked_data_caps s))"

abbreviation "has_expected_invocation s \<equiv> has_expected_code_cap_invocation s \<and> has_expected_data_cap_invocation s"

definition cap_authorises_load where
  "cap_authorises_load c vaddr sz \<equiv>
     CapIsTagSet c \<and> set (address_range (bounds_address AccType_NORMAL vaddr) sz) \<subseteq> get_mem_region CC c"

definition has_expected_loads where
  "has_expected_loads s \<equiv>
     (case instr_indirect_sentry_type instr of
        Some Points_to_PCC \<Rightarrow>
         \<exists>auth paddr vaddr c.
            auth \<in> load_auth_caps s \<and> cap_authorises_load auth vaddr 16 \<and>
            translate_address vaddr = Some paddr \<and>
            mem_caps s = {(paddr, c)} \<and>
            valid_address AccType_NORMAL vaddr \<and>
            bounds_address AccType_NORMAL vaddr + 16 \<le> 2^64
      | Some Points_to_Pair \<Rightarrow>
         \<exists>auth cc paddr_cc cd paddr_cd.
            auth \<in> load_auth_caps s \<and> cap_authorises_load auth (unat (CapGetValue auth)) 32 \<and>
            translate_address (unat (CapGetValue auth)) = Some paddr_cd \<and>
            translate_address (unat (CapGetValue auth) + 16) = Some paddr_cc \<and>
            mem_caps s = {(paddr_cd, cd), (paddr_cc, cc)} \<and>
            valid_address AccType_NORMAL (unat (CapGetValue auth)) \<and>
            bounds_address AccType_NORMAL (unat (CapGetValue auth)) + 32 \<le> 2^64
      | None \<Rightarrow> True)"

abbreviation ev_assms :: "invocation_state \<Rightarrow> register_value event \<Rightarrow> bool" where
  "ev_assms s e \<equiv> ev_reads_from_reg_state (reg_state s) e \<and> translation_assms e"

sublocale Hoare_Logic where ev_assms = ev_assms and step_state = step_state .

lemma trace_assms_translation_assms_trace:
  "trace_assms s t \<Longrightarrow> translation_assms_trace t"
  by (induction s t rule: trace_assms.induct) auto

lemma gprs_written_step_state:
  "gprs_written (step_state s e) \<longleftrightarrow> (\<exists>r v. e = E_write_reg r v \<and> r \<in> all_R_names) \<or> gprs_written s"
  by (induction s e rule: step_state.induct) (auto split: option.split)

lemma gprs_written_run_state:
  "gprs_written (run_state s t) \<longleftrightarrow> (\<exists>r v i. t ! i = E_write_reg r v \<and> i < length t \<and> r \<in> all_R_names) \<or> gprs_written s"
  by (induction t arbitrary: s) (auto simp: nth_Cons gprs_written_step_state gr0_conv_Suc split: nat.splits)

lemma gpr_reads_after_write_step_state:
  "gpr_reads_after_write (step_state s e) \<longleftrightarrow>
   (\<exists>r c. e = E_read_reg r (Regval_bitvector_129_dec c) \<and> r \<in> all_R_names \<and> gprs_written s) \<or> gpr_reads_after_write s"
  by (induction s e rule: step_state.induct) (auto split: option.split)

lemma gpr_reads_after_write_run_state:
  "gpr_reads_after_write (run_state s t) \<longleftrightarrow>
     (\<exists>r c i. t ! i = E_read_reg r (Regval_bitvector_129_dec c) \<and> r \<in> all_R_names \<and> i < length t \<and>
              gprs_written (run_state s (take i t)))
     \<or> gpr_reads_after_write s"
  by (induction t arbitrary: s)
     (auto simp: nth_Cons gpr_reads_after_write_step_state gr0_conv_Suc split: nat.splits)

lemma mem_caps_step_state:
  "mem_caps (step_state s e) =
     {(paddr, c) | paddr c. \<exists>rk sz bytes tag.
        e = E_read_memt rk paddr sz (bytes, tag) \<and> cap_of_mem_bytes bytes tag = Some c}
     \<union> mem_caps s"
  by (induction s e rule: step_state.induct) (auto split: option.splits)

lemma mem_caps_run_state:
  "mem_caps (run_state s t) =
     {(paddr, c) | paddr c. \<exists>rk sz bytes tag.
        E_read_memt rk paddr sz (bytes, tag) \<in> set t \<and> cap_of_mem_bytes bytes tag = Some c}
     \<union> mem_caps s"
  by (induction t arbitrary: s) (auto simp: mem_caps_step_state)

lemma pstate_writes_step_state:
  "pstate_writes (step_state s e) = (case e of E_write_reg r v \<Rightarrow> (if r = ''PSTATE'' then [v] else []) | _ \<Rightarrow> []) @ pstate_writes s"
  by (induction s e rule: step_state.induct) (auto split: option.splits)

lemma set_pstate_writes_run_state:
  "set (pstate_writes (run_state s t)) = {v. E_write_reg ''PSTATE'' v \<in> set t \<or> v \<in> set (pstate_writes s)}"
  by (induction t arbitrary: s) (auto simp add: pstate_writes_step_state)

lemma trace_reads_initial_caps_from_gpr_eq:
  assumes "\<not>gpr_reads_after_write (run_state s t)"
  shows "trace_reads_initial_caps_from_gpr n t = trace_reads_caps_from_gpr n t"
  using assms
  unfolding gpr_reads_after_write_run_state
  unfolding trace_reads_initial_caps_from_gpr_def trace_reads_caps_from_gpr_def
  by (auto simp: all_R_names_iff_R_name gprs_written_run_state in_set_conv_nth; blast)

lemma code_reg_caps_run_state_trace_reads_caps_from_gpr:
  assumes "instr_invokes_code_cap_from_reg instr = Some n"
  shows "code_reg_caps (run_state s t) = trace_reads_caps_from_gpr n t \<union> code_reg_caps s"
proof (induction t arbitrary: s)
  case (Cons e t)
  then show ?case
  proof (cases e)
    case (E_read_reg r v)
    then show ?thesis
      using Cons.prems Cons.IH[of "step_state s e"] assms
      by (cases v) (auto simp add: trace_reads_caps_from_gpr_def is_code_reg_def)
  qed (auto simp: trace_reads_caps_from_gpr_def split: option.splits)
qed (auto simp: trace_reads_caps_from_gpr_def)

lemma data_reg_caps_run_state_trace_reads_caps_from_gpr:
  assumes "instr_invokes_data_cap_from_reg instr = Some n"
  shows "data_reg_caps (run_state s t) = trace_reads_caps_from_gpr n t \<union> data_reg_caps s"
proof (induction t arbitrary: s)
  case (Cons e t)
  then show ?case
  proof (cases e)
    case (E_read_reg r v)
    then show ?thesis
      using Cons.prems Cons.IH[of "step_state s e"] assms
      by (cases v) (auto simp add: trace_reads_caps_from_gpr_def is_data_reg_def)
  qed (auto simp: trace_reads_caps_from_gpr_def split: option.splits)
qed (auto simp: trace_reads_caps_from_gpr_def)

lemma load_auth_caps_run_state_trace_reads_caps_from_gpr:
  assumes "instr_load_auth instr = Some (RegAuth n)"
  shows "load_auth_caps (run_state s t) = trace_reads_caps_from_gpr n t \<union> load_auth_caps s"
proof (induction t arbitrary: s)
  case (Cons e t)
  then show ?case
  proof (cases e)
    case (E_read_reg r v)
    then show ?thesis
      using Cons.prems Cons.IH[of "step_state s e"] assms
      by (cases v) (auto simp add: trace_reads_caps_from_gpr_def is_load_auth_reg_def)
  qed (auto simp: trace_reads_caps_from_gpr_def split: option.splits)
qed (auto simp: trace_reads_caps_from_gpr_def)

lemma instr_load_auth_if_indirect_sentry_type:
  assumes "instr_indirect_sentry_type instr = Some sentry_type"
  obtains n where "instr_load_auth instr = Some (RegAuth n)"
  using assms
  by (auto elim!: instr_indirect_sentry_type.elims)

lemma indirect_cap_reg_is_load_auth:
  assumes "instr_invokes_indirect_cap_from_reg instr = Some n"
  shows "instr_load_auth instr = Some (RegAuth n)"
  using assms
  by (cases instr) (auto split: if_splits)

lemma load_auth_caps_of_trace_trace_reads_caps_from_gpr:
  assumes "instr_load_auth instr = Some (RegAuth n)"
    and "instr_of_trace t = Some instr"
  shows "load_auth_caps_of_trace t = trace_reads_caps_from_gpr n t"
  using assms
  by (auto simp: load_auth_caps_of_trace_def trace_load_auths_def trace_reads_caps_from_gpr_def)

lemma load_auth_caps_run_eq_load_auth_caps_of_trace:
  assumes "instr_indirect_sentry_type instr = Some sentry_type"
    and "instr_of_trace t = Some instr"
  shows "load_auth_caps (run_state s t) = load_auth_caps_of_trace t \<union> load_auth_caps s"
  using assms
  by (elim instr_load_auth_if_indirect_sentry_type)
     (auto simp: load_auth_caps_run_state_trace_reads_caps_from_gpr load_auth_caps_of_trace_trace_reads_caps_from_gpr)

lemma branch_instr_run_has_expected_gpr_readsI:
  assumes "has_expected_gpr_reads (run_state (initial_invocation_state regs) t)"
    and "instr_of_trace t = Some instr"
  shows "branch_instr_run_has_expected_gpr_reads t"
  using assms
  unfolding branch_instr_run_has_expected_gpr_reads_def has_expected_gpr_reads_def
  by (auto simp: trace_invokes_code_cap_from_reg_def trace_invokes_data_cap_from_reg_def
                 trace_load_auths_def trace_reads_initial_caps_from_gpr_eq is_singleton_def
                 code_reg_caps_run_state_trace_reads_caps_from_gpr
                 data_reg_caps_run_state_trace_reads_caps_from_gpr
                 load_auth_caps_run_state_trace_reads_caps_from_gpr initial_invocation_state_def)

lemma original_reg_code_caps_invoked_in_trace_in_code_reg_caps:
  assumes "instr_of_trace t = Some instr"
  shows "original_reg_code_caps_invoked_in_trace t \<subseteq> code_reg_caps (run_state s t)"
  using assms
  unfolding original_reg_code_caps_invoked_in_trace_def original_cap_pairs_invoked_in_trace_def
    original_direct_reg_sentries_invoked_in_trace_def
  by (auto simp: trace_invokes_code_cap_from_reg_def code_reg_caps_run_state_trace_reads_caps_from_gpr)

lemma original_code_caps_indirectly_invoked_in_trace_in_original_mem_code_caps:
  assumes "instr_of_trace t = Some instr"
  shows "original_code_caps_indirectly_invoked_in_trace t \<subseteq> original_mem_code_caps (run_state s t)"
  using assms
  unfolding original_code_caps_indirectly_invoked_in_trace_def original_mem_code_caps_def
    trace_invokes_indirect_sentries_def trace_invokes_indirect_cap_from_reg_def
    trace_indirect_sentry_type_def
  apply (auto simp: mem_caps_run_state indirect_cap_reg_is_load_auth[THEN load_auth_caps_run_state_trace_reads_caps_from_gpr] CapUnseal_get_bounds_helpers_eq elim!: get_indirect_sentry_type_Some_cases)
  apply fastforce
  apply fastforce
  subgoal for c rk paddr bytes c' n
    apply (rule exI[where x = paddr])
    apply (auto)
    done
  done

lemma original_direct_mem_sentries_invoked_in_trace_in_original_mem_code_caps:
  assumes "instr_of_trace t = Some instr"
  shows "original_direct_mem_sentries_invoked_in_trace t \<subseteq> original_mem_code_caps (run_state s t)"
  using assms
  unfolding original_direct_mem_sentries_invoked_in_trace_def original_mem_code_caps_def
    trace_indirect_sentry_type_def
  by (fastforce simp: mem_caps_run_state load_auth_caps_run_eq_load_auth_caps_of_trace)

lemma original_code_caps_invoked_in_trace_in_original_code_caps:
  assumes "instr_of_trace t = Some instr"
  shows "original_code_caps_invoked_in_trace t \<subseteq> original_code_caps (run_state s t)"
  using original_reg_code_caps_invoked_in_trace_in_code_reg_caps[OF assms, THEN subsetD]
    original_code_caps_indirectly_invoked_in_trace_in_original_mem_code_caps[OF assms, THEN subsetD]
    original_direct_mem_sentries_invoked_in_trace_in_original_mem_code_caps[OF assms, THEN subsetD]
  by (auto simp: original_code_caps_invoked_in_trace_def original_code_caps_def)

lemma branch_instr_run_has_expected_pstate_writesI:
  assumes "has_expected_pstate_writes (run_state (initial_invocation_state regs) t)"
    and "instr_of_trace t = Some instr"
  shows "branch_instr_run_has_expected_pstate_writes opcode t"
proof (unfold branch_instr_run_has_expected_pstate_writes_def, intro ballI impI)
  fix cc'
  assume "cc' \<in> instr_invokes_code_caps opcode t" and tagged: "CapIsTagSet cc'"
  then obtain cc where cc: "cc \<in> original_code_caps_invoked_in_trace t"
    and "cc' \<in> branch_caps (clear_lsb (CapUnseal cc)) \<union> mem_branch_caps (clear_lsb cc)"
    by (cases rule: instr_of_trace_invocation_cases[OF assms(2), where opcode = opcode];
        auto simp: image_UN clear_lsb_image_branch_caps_eq clear_lsb_image_mem_branch_caps_eq reads_mem_cap_Some_iff;
        fastforce)
  then have "cc \<in> original_code_caps (run_state (initial_invocation_state regs) t)" and "CapIsTagSet cc"
    using original_code_caps_invoked_in_trace_in_original_code_caps[OF assms(2), where s = "initial_invocation_state regs"] tagged
    by (auto simp: branch_caps_128th_iff mem_branch_caps_128th_iff test_bit_set_gen)
  then obtain pstate where
    "set (pstate_writes (run_state (initial_invocation_state regs) t)) = {Regval_ProcState pstate}"
    "test_bit (ProcState_C64 pstate) 0 = lsb cc"
    using assms(1)
    by (auto simp: has_expected_pstate_writes_def)
  then show "\<exists>cc\<in>original_code_caps_invoked_in_trace t. pstate_c64_writes t = {lsb cc}"
    using cc
    by (intro bexI[where x = cc])
       (auto simp add: pstate_c64_writes_def set_pstate_writes_run_state initial_invocation_state_def set_eq_iff)
qed

lemma no_state_updateI:
  assumes "no_gpr_accesses_or_mem_cap_reads m"
    and "no_reg_writes_to {''PCC'', ''PSTATE'', ''__BranchTaken''} m"
  shows "no_state_update m"
proof (unfold no_state_update_def, intro allI impI, elim conjE)
  fix s t m'
  assume t: "(m, t, m') \<in> Traces" and "trace_assms s t"
  then have "\<forall>r v. r \<in> all_R_names \<longrightarrow> E_read_reg r v \<notin> set t"
    using assms
    by (auto simp: no_gpr_accesses_or_mem_cap_reads_def no_accesses_to_any_gpr_def no_reads_from_any_gpr_def
                   no_reads_from_gpr_def dest: all_R_names_R_name)
  moreover have "\<forall>r v. r \<in> invocation_regs \<longrightarrow> E_write_reg r v \<notin> set t"
    using t assms
    unfolding invocation_regs_def no_reg_writes_to_def no_gpr_accesses_or_mem_cap_reads_def
      no_accesses_to_any_gpr_def no_writes_to_any_gpr_def no_writes_to_gpr_def
    by (auto dest: all_R_names_R_name)
  moreover have "E_read_memt rk addr sz val \<notin> set t" for rk addr sz val
    using t assms
    unfolding no_gpr_accesses_or_mem_cap_reads_def no_mem_cap_reads_def
    by (cases val) auto
  ultimately show "run_state s t = s"
  proof (induction t)
    case (Cons e t)
    then show ?case
    proof (cases e)
      case (E_read_memt rk addr sz val)
      then show ?thesis
        using Cons.prems(3)[of rk addr sz val]
        by auto
    next
      case (E_read_reg r v)
      then have "r \<notin> all_R_names"
        using Cons.prems
        by auto
      moreover have "\<not>is_code_reg r" and "\<not>is_data_reg r" and "\<not>is_indirect_reg r" and "\<not>is_load_auth_reg r"
        using calculation
        by (auto simp: is_code_reg_def is_data_reg_def is_indirect_reg_def is_load_auth_reg_def dest: R_name_in_all_R_names)
      ultimately show ?thesis
        using E_read_reg Cons
        by (cases v) auto
    next
      case (E_write_reg r v)
      then have "r \<notin> invocation_regs"
        using Cons.prems
        by auto
      then have "r \<notin> invocation_regs \<union> all_R_names \<union> {''PCC'', ''PSTATE'', ''_R29'', ''__BranchTaken''}"
        using R29_all_R_names
        unfolding invocation_regs_def
        by auto
      then show ?thesis
        using E_write_reg Cons
        by auto
    qed auto
  qed auto
qed

definition "add_pcc_write c s \<equiv> s\<lparr>pcc_writes := Regval_bitvector_129_dec c # pcc_writes s\<rparr>"
definition "add_pstate_write ps s \<equiv> s\<lparr>pstate_writes := Regval_ProcState ps # pstate_writes s\<rparr>"
definition "add_branch_taken_write b s \<equiv> s\<lparr>branch_taken_writes := Regval_bool b # branch_taken_writes s\<rparr>"

lemma pre_post_write_reg_BranchTaken:
  "pre_post (\<lambda>s. Q () (add_branch_taken_write b s)) (write_reg BranchTaken_ref b) Q E F"
  by (rule pre_post_strengthen_pre, rule pre_post_write_reg)
     (simp add: add_branch_taken_write_def register_defs invocation_regs_def all_R_names_def)

lemma pre_post_write_reg_PCC:
  "pre_post (\<lambda>s. Q () (add_pcc_write c s)) (write_reg PCC_ref c) Q E F"
  by (rule pre_post_strengthen_pre, rule pre_post_write_reg)
     (simp add: add_pcc_write_def register_defs all_R_names_def)

lemma pre_post_write_reg_PSTATE:
  "pre_post (\<lambda>s. Q () (add_pstate_write ps s)) (write_reg PSTATE_ref ps) Q E F"
  by (rule pre_post_strengthen_pre, rule pre_post_write_reg)
     (simp add: add_pstate_write_def register_defs all_R_names_def)

lemma pre_post_read_reg_PSTATE:
  "pre_post_ignore_fail
     (\<lambda>s. \<forall>pstate. (\<forall>acctype. acctype \<noteq> AccType_UNPRIV \<longrightarrow> translation_el acctype = ProcState_EL pstate) \<longrightarrow> Q pstate s)
     (read_reg PSTATE_ref :: ProcState M) Q E"
  apply (rule pre_post_strengthen_pre)
   apply (rule pre_post_ignore_fail_no_state_update_no_exception)
    apply (rule no_state_updateI, no_reads_from_any_gpr, no_reg_writes_toI, rule monad_no_exception)
  apply (use read_reg_PSTATE_translation_el in \<open>auto dest!: trace_assms_translation_assms_trace\<close>)
  done

lemma pre_post_BranchAddr:
  "pre_post_ignore_fail
     (\<lambda>s. translation_el AccType_IFETCH = el \<and>
     (\<forall>c'. (CapIsTagSet c' \<longrightarrow> c' \<in> branch_caps c) \<longrightarrow> Q c' s))
     (BranchAddr c el) Q E"
  apply (rule pre_post_strengthen_pre, rule pre_post_ignore_fail_no_state_update_no_exception)
    apply (rule no_state_updateI)
     apply (no_reads_from_any_gpr)
    apply (no_reg_writes_toI)
   apply (rule monad_no_exception)
  apply (use BranchAddr_in_branch_caps in \<open>auto dest: trace_assms_translation_assms_trace\<close>)
  done

lemma pre_post_BranchToCapability:
  "pre_post_ignore_fail
     (\<lambda>s. (\<forall>c'. (CapIsTagSet c' \<longrightarrow> c' \<in> branch_caps c) \<longrightarrow>
                Q () (add_branch_taken_write True (add_pcc_write c' s))))
     (BranchToCapability c branch_type) Q E"
  unfolding BranchToCapability_def Let_def bind_assoc
  apply (rule pre_post_strengthen_pre)
   apply (rule pre_post_bind)+
          apply (rule pre_post_write_reg_BranchTaken)
         apply (rule pre_post_write_reg_PCC)
        apply (rule pre_post_BranchAddr)
       apply (rule pre_post_read_reg_PSTATE)
      apply (rule pre_post_write_reg)
     apply (rule pre_post_ignore_fail_no_state_update_no_exception, rule no_state_updateI, no_reads_from_any_gpr, no_reg_writes_toI, rule monad_no_exception)
    apply (rule pre_post_ignore_fail_assert_exp)
   apply (rule pre_post_ignore_fail_no_state_update_no_exception, rule no_state_updateI, no_reads_from_any_gpr, no_reg_writes_toI, rule monad_no_exception)
  apply (simp add: all_R_names_def register_defs)
  done

lemma pre_post_BranchXToCapability:
  "pre_post_ignore_fail
     (\<lambda>s. (\<forall>c' pstate.
              (CapIsTagSet c' \<longrightarrow> c' \<in> branch_caps (clear_lsb c)) \<and>
              ProcState_C64 pstate = of_bl [lsb c] \<longrightarrow>
              Q () (add_branch_taken_write True (add_pcc_write c' (add_pstate_write pstate s)))))
     (BranchXToCapability c branch_type) Q E"
  unfolding BranchXToCapability_def Let_def bind_assoc
  apply (rule pre_post_strengthen_pre)
   apply (rule pre_post_bind)+
     apply (rule pre_post_BranchToCapability)
    apply (rule pre_post_write_reg_PSTATE)
   apply (rule pre_post_read_reg)
  apply (auto simp: register_defs word_lsb_alt split: option.split)
  done

lemma pre_post_R_read:
  "pre_post_ignore_fail
     (\<lambda>s. \<forall>r c e.
            n \<in> {0..30} \<and> R_name n = {r} \<and> e = E_read_reg r (Regval_bitvector_129_dec c) \<and>
            (reg_state s r = Some (Regval_bitvector_129_dec c) \<or> reg_state s r = None)
            \<longrightarrow> Q c (step_state s e))
     (R_read n) Q E"
  unfolding R_read_def Let_def
  apply (intro pre_post_if_common_pre)
  apply (rule pre_post_strengthen_pre, rule pre_post_read_reg, simp add: register_defs R_name_def del: step_state.simps split: option.split)+
  apply (rule pre_post_bind, simp, rule pre_post_strengthen_pre, rule pre_post_ignore_fail_assert_exp, simp)
  done

end

context Morello_ISA
begin

(* TODO: Move *)
lemma mem_cap_loads_of_ev_reads_mem_cap:
  "mem_cap_loads_of_ev e = {(paddr, c) | paddr c. reads_mem_cap CC e = Some (paddr, 16, c)}"
  by (cases e rule: mem_cap_loads_of_ev.cases)
     (auto simp: reads_mem_cap_def no_cap_load_translation_events bind_eq_Some_conv cap_of_mem_bytes_def nth_ucast
           dest: test_bit_len split: option.splits if_splits)

lemma trace_has_cap_load_auth_iff_load_cap_perm:
  assumes "trace_load_auths t = Some (RegAuth n)"
    and "trace_reads_caps_from_gpr n t = {c}"
  shows "trace_has_cap_load_auth t \<longleftrightarrow> cap_permits CAP_PERM_LOAD_CAP c"
  using assms
  by (fastforce simp: trace_has_cap_load_auth_def instr_trace_load_auth_caps_def trace_reads_caps_from_gpr_def set_eq_iff)

lemma hasTrace_Run:
  assumes "hasTrace t m"
    and "\<not>hasException t m"
    and "\<not>hasFailure t m"
  shows "\<exists>a. Run m t a"
  using assms
  by (auto simp add: hasTrace_def hasException_def hasFailure_def final_def
           simp flip: runTrace_iff_Traces split: option.splits monad.splits)

(* Characterisation of the different cases of invocation for a given instruction trace *)
lemma hasTrace_instr_sem_invocation_cases:
  assumes "hasTrace t (instr_sem opcode)"
    and instr: "instr_of_trace t = Some instr" \<comment> \<open>instruction AST, e.g. @{verbatim Instr_BRS_C_C}, not opcode\<close>
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
    and "original_code_caps_invoked_in_trace t = {cc}"
    and "instr_invokes_code_caps opcode t = branch_caps (clear_lsb (CapUnseal cc))"
    and "instr_invokes_data_caps opcode t = {CapUnseal cd}"
    and "instr_invokes_indirect_caps opcode t = {}"
  | (DirectRegSentry) c n
    where "instr_invokes_code_cap_from_reg instr = Some n"
    and "trace_reads_initial_caps_from_gpr n t = {c}"
    and "instr_invokes_data_cap_from_reg instr = None"
    and "CapIsTagSet c" and "CapGetObjectType c = CAP_SEAL_TYPE_RB"
    and "original_code_caps_invoked_in_trace t = {c}"
    and "instr_invokes_code_caps opcode t = branch_caps (clear_lsb (CapUnseal c))"
    and "instr_invokes_data_caps opcode t = {}"
    and "instr_invokes_indirect_caps opcode t = {}"
  | (DirectMemSentry) n c c' paddr vaddr sentry_type
      \<comment> \<open>Using an indirect branching instruction with a register other than 29, or a capability
      that isn't an indirect sentry, can still load a direct sentry from memory and invoke it\<close>
    where "instr_load_auth instr = Some (RegAuth n)"
    and "trace_reads_initial_caps_from_gpr n t = {c}"
    and "instr_trace_load_auth_caps t = {c}"
    and "instr_indirect_sentry_type instr = Some sentry_type"
    and "\<not>CapIsSealed c"
    and "set (address_range (bounds_address AccType_NORMAL vaddr) 16) \<subseteq> get_mem_region CC c"
    and "translate_address vaddr = Some paddr"
    and "(paddr, c') \<in> initial_mem_cap_loads_of_trace t"
    and "CapIsTagSet c'" and "CapGetObjectType c' = CAP_SEAL_TYPE_RB"
    and "original_code_caps_invoked_in_trace t = {c'}"
    and "instr_invokes_code_caps opcode t = branch_caps (clear_lsb (CapUnseal c'))"
    and "instr_invokes_data_caps opcode t = {}"
    and "instr_invokes_indirect_caps opcode t = {}"
  | (IndirectPointsToPCC) c c' paddr vaddr
    where "instr_invokes_indirect_cap_from_reg instr = Some 29"
    and "instr_indirect_sentry_type instr = Some Points_to_PCC"
    and "trace_reads_initial_caps_from_gpr 29 t = {c}"
    and "instr_trace_load_auth_caps t = {c}"
    and "CapIsTagSet c"
    and "CapGetObjectType c = CAP_SEAL_TYPE_LB"
    and "instr_invokes_indirect_caps opcode t = {CapUnseal c}"
    and "translate_address vaddr = Some paddr"
    and "initial_mem_cap_loads_of_trace t = {(paddr, c')}"
    and "set (address_range (bounds_address AccType_NORMAL vaddr) 16) \<subseteq> get_mem_region CC c"
    and "original_code_caps_invoked_in_trace t = (if CapIsTagSet c' \<and> cap_permits CAP_PERM_LOAD_CAP c then {c'} else {})"
    and "instr_invokes_code_caps opcode t = (if CapIsTagSet c' \<and> cap_permits CAP_PERM_LOAD_CAP c then mem_branch_caps (clear_lsb c') else {})"
    and "instr_invokes_data_caps opcode t = {CapUnseal c}"
  | (IndirectPointsToPair) n c cc cd paddr_cc paddr_cd
    where "instr_invokes_indirect_cap_from_reg instr = Some n"
    and "instr_indirect_sentry_type instr = Some Points_to_Pair"
    and "trace_reads_initial_caps_from_gpr n t = {c}"
    and "instr_trace_load_auth_caps t = {c}"
    and "CapIsTagSet c"
    and "CapGetObjectType c = CAP_SEAL_TYPE_LPB"
    and "instr_invokes_indirect_caps opcode t = {CapUnseal c}"
    and "translate_address (unat (CapGetValue c)) = Some paddr_cd"
    and "translate_address (unat (CapGetValue c + 16)) = Some paddr_cc"
    and "initial_mem_cap_loads_of_trace t = {(paddr_cd, cd), (paddr_cc, cc)}"
    and "original_code_caps_invoked_in_trace t = (if CapIsTagSet cc \<and> cap_permits CAP_PERM_LOAD_CAP c then {cc} else {})"
    and "instr_invokes_code_caps opcode t = (if CapIsTagSet cc \<and> cap_permits CAP_PERM_LOAD_CAP c then mem_branch_caps (clear_lsb cc) else {})"
    and "instr_invokes_data_caps opcode t = (if CapIsTagSet cd \<and> cap_permits CAP_PERM_LOAD_CAP c then mem_data_caps cd else {})"
    and "set (address_range (bounds_address AccType_NORMAL (unat (CapGetValue c))) 32) \<subseteq> get_mem_region CC c"
  | (NoInvocation) "instr_invokes_code_caps opcode t = {}"
    and "instr_invokes_data_caps opcode t = {}"
    and "instr_invokes_indirect_caps opcode t = {}"
proof (use assms(2) in
       \<open>cases rule: instr_of_trace_invocation_cases[where opcode = opcode,
          case_names SealedPair' DirectRegSentry' DirectMemSentry' IndirectPointsToPCC' IndirectPointsToPair' NoInvocation']\<close>)
  case (SealedPair' nc nd)
  have *: "branch_instr_trace_has_expected_invocations opcode t"
    sorry
  obtain cc where cc: "trace_reads_caps_from_gpr nc t = {cc}" "trace_reads_initial_caps_from_gpr nc t = {cc}"
    using * SealedPair' hasTrace_Run[OF assms(1,3,4)] \<open>instr_of_trace t = Some instr\<close>
    by (auto simp: branch_instr_trace_has_expected_invocations_def branch_instr_run_has_expected_gpr_reads_def trace_invokes_code_cap_from_reg_def)
  obtain cd where cd: "trace_reads_caps_from_gpr nd t = {cd}" "trace_reads_initial_caps_from_gpr nd t = {cd}"
    using * SealedPair' hasTrace_Run[OF assms(1,3,4)] \<open>instr_of_trace t = Some instr\<close>
    by (auto simp: branch_instr_trace_has_expected_invocations_def branch_instr_run_has_expected_gpr_reads_def trace_invokes_data_cap_from_reg_def)
  show thesis
  proof (cases "invokable CC cc cd")
    case True
    then show ?thesis
      using SealedPair' cc cd
      by (intro SealedPair[of nc nd cc cd])
         (auto simp add: image_UN clear_lsb_image_branch_caps_eq)+
  next
    case False
    then show ?thesis
      using SealedPair' cc cd
      by (intro NoInvocation) auto
  qed
next
  case (DirectRegSentry' n)
  have *: "branch_instr_trace_has_expected_invocations opcode t"
    sorry
  obtain c where c: "trace_reads_caps_from_gpr n t = {c}" "trace_reads_initial_caps_from_gpr n t = {c}"
    using * DirectRegSentry' hasTrace_Run[OF assms(1,3,4)] \<open>instr_of_trace t = Some instr\<close>
    by (auto simp: branch_instr_trace_has_expected_invocations_def branch_instr_run_has_expected_gpr_reads_def trace_invokes_code_cap_from_reg_def)
  show ?thesis
  proof (cases "CapIsTagSet c \<and> is_sentry c")
    case True
    then show ?thesis
      using DirectRegSentry' c
      by (intro DirectRegSentry[of n c])
         (auto simp: is_sentry_def image_UN clear_lsb_image_branch_caps_eq)
  next
    case False
    then show ?thesis
      using DirectRegSentry' c
      by (intro NoInvocation) auto
  qed
next
  case (DirectMemSentry' sentry_type)
  obtain n where n: "instr_load_auth instr = Some (RegAuth n)"
    by (use \<open>instr_indirect_sentry_type instr = Some sentry_type\<close> in \<open>auto elim!: instr_indirect_sentry_type.elims\<close>)
  then have [simp]: "trace_indirect_sentry_type t = Some sentry_type"
    and [simp]: "trace_load_auths t = Some (RegAuth n)"
    using DirectMemSentry' instr
    by (auto simp: trace_indirect_sentry_type_def trace_load_auths_def)
  have *: "branch_instr_trace_has_expected_invocations opcode t"
    sorry
  then have **: "branch_instr_run_has_expected_invocation_loads t"
    using hasTrace_Run[OF assms(1,3,4)]
    by (auto simp: branch_instr_trace_has_expected_invocations_def)
  obtain c where c: "trace_reads_caps_from_gpr n t = {c}" "trace_reads_initial_caps_from_gpr n t = {c}"
                    "CapIsTagSet c" "\<not>CapIsSealed c"
    using * n DirectMemSentry'(9) hasTrace_Run[OF assms(1,3,4)] \<open>instr_of_trace t = Some instr\<close>
    by (cases sentry_type)
       (auto simp: branch_instr_trace_has_expected_invocations_def branch_instr_run_has_expected_invocation_loads_def
                   trace_has_reg_load_auth_for_addr_def branch_instr_run_has_expected_gpr_reads_def
                   instr_invokes_indirect_caps_def)
  then have [simp]: "instr_trace_load_auth_caps t = {c}"
    by (fastforce simp add: instr_trace_load_auth_caps_def trace_reads_caps_from_gpr_def set_eq_iff)
  show thesis
  proof (cases "instr_invokes_code_caps opcode t = {}")
    case True
    then show thesis
      using DirectMemSentry'
      by (intro NoInvocation) auto
  next
    case False
    show thesis
    proof (cases sentry_type)
      case Points_to_PCC
      then obtain cc vaddr paddr where paddr_cc: "initial_mem_cap_loads_of_trace t = {(paddr, cc)}"
        and vaddr: "translate_address vaddr = Some paddr"
        and bounds: "set (address_range (bounds_address AccType_NORMAL vaddr) 16) \<subseteq> get_mem_region CC c"
        using ** n c
        by (auto simp: branch_instr_run_has_expected_invocation_loads_def trace_has_reg_load_auth_for_addr_def)
      then have cap_loads: "mem_cap_loads_of_trace t = (if CapIsTagSet cc then {(paddr, cc)} else {})"
        using Points_to_PCC **
        by (intro set_eqI; simp add: branch_instr_run_has_expected_invocation_loads_def; fastforce)
      have original_code_caps: "original_code_caps_invoked_in_trace t = {cc. \<exists>paddr. (paddr, cc) \<in> mem_cap_loads_of_trace t \<and> is_sentry cc}"
        using DirectMemSentry'(6) Points_to_PCC
        by (auto simp: mem_cap_loads_of_trace_def mem_cap_loads_of_ev_reads_mem_cap reads_mem_cap_Some_iff)
      then have cc: "CapIsTagSet cc" "CapGetObjectType cc = CAP_SEAL_TYPE_RB"
        using DirectMemSentry'(7) False
        unfolding cap_loads
        by (auto simp: is_sentry_def split: if_splits)
      show thesis
        using DirectMemSentry'(1,7-9) n c cc False original_code_caps cap_loads Points_to_PCC paddr_cc vaddr bounds ** instr
        by (intro DirectMemSentry[of n c sentry_type vaddr paddr cc])
           (auto simp add: image_UN clear_lsb_image_branch_caps_eq)
    next
      case Points_to_Pair
      then obtain cc cd paddr_cc paddr_cd
        where initial_loads: "initial_mem_cap_loads_of_trace t = {(paddr_cd, cd), (paddr_cc, cc)}"
        and paddr_cd: "translate_address (unat (CapGetValue c)) = Some paddr_cd"
        and paddr_cc: "translate_address (unat (CapGetValue c) + 16) = Some paddr_cc"
        and bounds: "set (address_range (bounds_address AccType_NORMAL (unat (CapGetValue c) + 16)) 16) \<subseteq> get_mem_region CC c"
        using ** c
        by (auto simp: branch_instr_run_has_expected_invocation_loads_def trace_has_reg_load_auth_for_addr_def subset_eq)
      have paddr_distinct: "paddr_cd \<noteq> paddr_cc"
        using translate_address_vaddr_offset_paddr_different[OF paddr_cd, where offset = 16] paddr_cc
        by auto
      have "original_code_caps_invoked_in_trace t = {cc. (paddr_cc, cc) \<in> mem_cap_loads_of_trace t \<and> is_sentry cc}"
        using initial_loads paddr_cd paddr_cc ** c Points_to_Pair
        unfolding DirectMemSentry'(6)
        by (auto simp: mem_cap_loads_of_trace_def mem_cap_loads_of_ev_reads_mem_cap reads_mem_cap_Some_iff
                       branch_instr_run_has_expected_invocation_loads_def trace_has_reg_load_auth_for_addr_def set_eq_iff)
      then have "original_code_caps_invoked_in_trace t = (if CapIsTagSet cc \<and> is_sentry cc then {cc} else {})"
        using ** Points_to_Pair initial_loads c paddr_cd paddr_cc paddr_distinct
        by (auto simp: branch_instr_run_has_expected_invocation_loads_def)
      moreover have "instr_invokes_code_caps opcode t = branch_caps (clear_lsb (CapUnseal cc))"
        and "CapIsTagSet cc" and "is_sentry cc"
        using calculation False
        unfolding DirectMemSentry'(7)
        by (auto simp: image_UN clear_lsb_image_branch_caps_eq split: if_splits)
      ultimately show ?thesis
        using DirectMemSentry'(1,8,9) n c initial_loads paddr_cc bounds
        by (intro DirectMemSentry[of n c sentry_type "unat (CapGetValue c) + 16" paddr_cc cc])
           (auto simp: is_sentry_def)
    qed
  qed
next
  case IndirectPointsToPCC'
  then have load_auth: "instr_load_auth instr = Some (RegAuth 29)"
    by (auto elim!: instr_indirect_sentry_type.elims split: if_splits)
  then have [simp]: "trace_indirect_sentry_type t = Some Points_to_PCC"
    and [simp]: "trace_load_auths t = Some (RegAuth 29)"
    using IndirectPointsToPCC' instr
    by (auto simp: trace_indirect_sentry_type_def trace_load_auths_def)
  have *: "branch_instr_trace_has_expected_invocations opcode t"
    sorry
  then have **: "branch_instr_run_has_expected_invocation_loads t"
    using hasTrace_Run[OF assms(1,3,4)]
    by (auto simp: branch_instr_trace_has_expected_invocations_def)
  obtain c where c: "trace_reads_caps_from_gpr 29 t = {c}" "trace_reads_initial_caps_from_gpr 29 t = {c}"
                    "CapIsTagSet c" "CapGetObjectType c = CAP_SEAL_TYPE_LB"
    and indirect_sentries: "instr_invokes_indirect_caps opcode t = {CapUnseal c}"
    using IndirectPointsToPCC' * hasTrace_Run[OF assms(1,3,4)] instr
    by (auto simp: branch_instr_trace_has_expected_invocations_def branch_instr_run_has_expected_gpr_reads_def)
  then have load_cap: "trace_has_cap_load_auth t \<longleftrightarrow> cap_permits CAP_PERM_LOAD_CAP c"
    using load_auth \<open>instr_of_trace t = Some instr\<close>
    by (intro trace_has_cap_load_auth_iff_load_cap_perm) (auto simp: trace_load_auths_def)
  obtain cc vaddr paddr where paddr_cc: "initial_mem_cap_loads_of_trace t = {(paddr, cc)}"
    and vaddr: "translate_address vaddr = Some paddr"
    and authorised: "trace_has_reg_load_auth_for_addr t c vaddr 16"
    using ** load_auth c
    by (auto simp: branch_instr_run_has_expected_invocation_loads_def trace_has_reg_load_auth_for_addr_def)
  then have cap_loads: "mem_cap_loads_of_trace t = (if CapIsTagSet cc then {(paddr, cc)} else {})"
    using **
    by (intro set_eqI; simp add: branch_instr_run_has_expected_invocation_loads_def; fastforce)
  have "original_code_caps_invoked_in_trace t =
          {cc. \<exists>vaddr paddr. (paddr, cc) \<in> mem_cap_loads_of_trace t \<and> translate_address vaddr = Some paddr \<and>
                             cap_permits CAP_PERM_LOAD_CAP c \<and> trace_has_reg_load_auth_for_addr t c vaddr 16}"
    using c get_mem_region_CapUnseal_eq[of c]
    unfolding IndirectPointsToPCC'(4)
    by (auto simp: indirect_sentries load_cap mem_cap_loads_of_trace_def mem_cap_loads_of_ev_reads_mem_cap
                   reads_mem_cap_Some_iff trace_has_reg_load_auth_for_addr_def)
       blast+
  then have "original_code_caps_invoked_in_trace t = (if CapIsTagSet cc \<and> cap_permits CAP_PERM_LOAD_CAP c then {cc} else {})"
    using vaddr authorised
    unfolding cap_loads
    by auto
  moreover have
    "instr_invokes_code_caps opcode t = (if CapIsTagSet cc \<and> cap_permits CAP_PERM_LOAD_CAP c then mem_branch_caps (clear_lsb cc) else {})"
    using calculation IndirectPointsToPCC'(5)
    by (auto simp: clear_lsb_image_mem_branch_caps_eq)
  ultimately show thesis
    using IndirectPointsToPCC'(1,2,6) c indirect_sentries vaddr paddr_cc authorised
    by (intro IndirectPointsToPCC[of c vaddr paddr cc])
       (auto simp: trace_has_reg_load_auth_for_addr_def)
next
  case (IndirectPointsToPair' n)
  have [simp]: "trace_indirect_sentry_type t = Some Points_to_Pair"
    and [simp]: "trace_load_auths t = Some (RegAuth n)"
    using \<open>instr_invokes_indirect_cap_from_reg instr = Some n\<close> \<open>instr_indirect_sentry_type instr = Some Points_to_Pair\<close> instr
    by (auto simp: trace_indirect_sentry_type_def trace_load_auths_def
             elim!: instr_indirect_sentry_type.elims split: if_splits)
  have *: "branch_instr_trace_has_expected_invocations opcode t"
    sorry
  then have **: "branch_instr_run_has_expected_invocation_loads t"
    using hasTrace_Run[OF assms(1,3,4)]
    by (auto simp: branch_instr_trace_has_expected_invocations_def)
  obtain c where c: "trace_reads_caps_from_gpr n t = {c}" "trace_reads_initial_caps_from_gpr n t = {c}"
                    "CapIsTagSet c" "CapGetObjectType c = CAP_SEAL_TYPE_LPB"
    and indirect_sentries: "instr_invokes_indirect_caps opcode t = {CapUnseal c}"
    using IndirectPointsToPair'(1,3,7) * hasTrace_Run[OF assms(1,3,4)] instr
    by (auto simp: branch_instr_trace_has_expected_invocations_def branch_instr_run_has_expected_gpr_reads_def)
  then have load_cap: "trace_has_cap_load_auth t \<longleftrightarrow> cap_permits CAP_PERM_LOAD_CAP c"
    using \<open>trace_load_auths t = Some (RegAuth n)\<close> \<open>instr_of_trace t = Some instr\<close>
    by (intro trace_has_cap_load_auth_iff_load_cap_perm) (auto simp: trace_load_auths_def)
  obtain cc cd paddr_cc paddr_cd
    where initial_loads: "initial_mem_cap_loads_of_trace t = {(paddr_cd, cd), (paddr_cc, cc)}"
    and paddr_cd: "translate_address (unat (CapGetValue c)) = Some paddr_cd"
    and paddr_cc: "translate_address (unat (CapGetValue c) + 16) = Some paddr_cc"
    and authorised: "trace_has_reg_load_auth_for_addr t c (unat (CapGetValue c)) 32"
    and no_overflow[simp]:
      "unat (CapGetValue c + 16) = unat (CapGetValue c) + 16"
      "bounds_address AccType_NORMAL (unat (CapGetValue c) + 16) = bounds_address AccType_NORMAL (unat (CapGetValue c)) + 16"
    using ** c
    by (auto simp: branch_instr_run_has_expected_invocation_loads_def trace_has_reg_load_auth_for_addr_def subset_eq)
  then have cap_loads:
    "mem_cap_loads_of_trace t =
       (if CapIsTagSet cd then {(paddr_cd, cd)} else {}) \<union>
       (if CapIsTagSet cc then {(paddr_cc, cc)} else {})"
    using **
    by (intro set_eqI; simp add: branch_instr_run_has_expected_invocation_loads_def; fastforce)
  have paddr_distinct: "paddr_cd \<noteq> paddr_cc"
    using translate_address_vaddr_offset_paddr_different[OF paddr_cd, where offset = 16] paddr_cc
    by auto
  have "original_code_caps_invoked_in_trace t = {cc. \<exists>paddr.
          (paddr, cc) \<in> mem_cap_loads_of_trace t \<and> translate_address (unat (CapGetValue c + 16)) = Some paddr \<and>
          cap_permits CAP_PERM_LOAD_CAP c \<and> trace_has_reg_load_auth_for_addr t c (unat (CapGetValue c + 16)) 16}"
    using c
    unfolding IndirectPointsToPair'(4) indirect_sentries
    by (auto simp: mem_cap_loads_of_trace_def mem_cap_loads_of_ev_reads_mem_cap reads_mem_cap_Some_iff
                   get_mem_region_CapUnseal_eq CapUnseal_get_bounds_helpers_eq load_cap
                   trace_has_reg_load_auth_for_addr_def)
  then have original_code_caps:
    "original_code_caps_invoked_in_trace t = (if CapIsTagSet cc \<and> cap_permits CAP_PERM_LOAD_CAP c then {cc} else {})"
    using authorised paddr_distinct
    by (auto simp: cap_loads paddr_cc trace_has_reg_load_auth_for_addr_def)
  have code_caps:
    "instr_invokes_code_caps opcode t = (if CapIsTagSet cc \<and> cap_permits CAP_PERM_LOAD_CAP c then mem_branch_caps (clear_lsb cc) else {})"
    unfolding IndirectPointsToPair'(5) original_code_caps
    by (auto simp: clear_lsb_image_mem_branch_caps_eq)
  have "instr_invokes_data_caps opcode t =
          \<Union>{mem_data_caps cd | cd. \<exists>paddr.
              (paddr, cd) \<in> mem_cap_loads_of_trace t \<and> translate_address (unat (CapGetValue c)) = Some paddr \<and>
              cap_permits CAP_PERM_LOAD_CAP c \<and> trace_has_reg_load_auth_for_addr t c (unat (CapGetValue c)) 16}"
    using IndirectPointsToPair'(6) indirect_sentries c
    by (auto simp: mem_cap_loads_of_trace_def mem_cap_loads_of_ev_reads_mem_cap reads_mem_cap_Some_iff
                   get_mem_region_CapUnseal_eq trace_has_reg_load_auth_for_addr_def load_cap
                   CapUnseal_get_bounds_helpers_eq; fastforce)
  then have data_caps:
    "instr_invokes_data_caps opcode t = (if CapIsTagSet cd \<and> cap_permits CAP_PERM_LOAD_CAP c then mem_data_caps cd else {})"
    using authorised paddr_cd paddr_distinct
    by (simp add: cap_loads trace_has_reg_load_auth_for_addr_def; fastforce)
  show thesis
    using IndirectPointsToPair'(1,2) c indirect_sentries paddr_cd paddr_cc initial_loads original_code_caps code_caps data_caps authorised
    by (intro IndirectPointsToPair[of n c paddr_cd paddr_cc cd cc])
       (auto simp: trace_has_reg_load_auth_for_addr_def)
next
  case NoInvocation'
  then show ?thesis
    by (intro NoInvocation)
qed

lemma [simp]:
  "isa.trace_has_assertion_failure ISA t = trace_has_assertion_failure t"
  by (auto simp: ISA_def)

lemma branch_caps_empty_iff_sealed:
  "branch_caps c = {} \<longleftrightarrow> CapIsSealed c"
  by (auto simp: branch_caps_def)

lemma idc_write_axiom_if_trace_has_expected_invocations:
  assumes "hasTrace t (instr_sem opcode)"
    and "translation_assms_trace t"
    and "cap_inv_trace t"
    and "\<forall>instr. instr_of_trace t = Some instr \<longrightarrow> branch_instr_trace_has_expected_invocations opcode t"
  shows "idc_write_axiom CC ISA (instr_trace opcode t)"
proof (cases "instr_of_trace t")
  case None
  then show ?thesis
    using instr_of_trace_None_instr_invokes_no_caps[OF None, where instr = opcode]
    by (auto simp: idc_write_axiom_def)
next
  case (Some instr)
  then show ?thesis
  proof (use assms(1) in \<open>cases rule: hasTrace_cases\<close>)
    case (Run a)
    have [simp]:
      "trace_invokes_code_cap_from_reg t = instr_invokes_code_cap_from_reg instr"
      "trace_invokes_data_cap_from_reg t = instr_invokes_data_cap_from_reg instr"
      "trace_invokes_indirect_cap_from_reg t = instr_invokes_indirect_cap_from_reg instr"
      using Some
      by (auto simp: trace_invokes_code_cap_from_reg_def trace_invokes_data_cap_from_reg_def trace_invokes_indirect_cap_from_reg_def)
    from Run have no_ex: "\<not>hasException t (instr_sem opcode)"
      and no_fail: "\<not>hasFailure t (instr_sem opcode)"
      by (auto simp add: hasException_def hasFailure_def simp flip: runTrace_iff_Traces)
    then show ?thesis
      using Run Some assms(4)
      by (cases rule: hasTrace_instr_sem_invocation_cases[OF assms(1) Some no_ex no_fail assms(2,3)])
         (auto simp add: idc_write_axiom_def branch_instr_trace_has_expected_invocations_def
                         branch_instr_run_performs_expected_invocation_def)
  next
    case (Fail f)
    then show ?thesis
      by (auto simp: idc_write_axiom_def trace_has_assertion_failure_def runTrace_iff_Traces)
  next
    case (Ex e)
    then show ?thesis
      using Some assms(4)
      by (auto simp: idc_write_axiom_def branch_instr_trace_has_expected_invocations_def
                     branch_instr_trace_has_expected_exceptions_def is_singleton_def
                     trace_raises_ex_def runTrace_iff_Traces)
  qed
qed

lemma invocation_writes_pstate_c64_instr_trace:
  assumes "hasTrace t (instr_sem opcode)"
    and "\<not>hasException t (instr_sem opcode)"
    and "\<not>hasFailure t (instr_sem opcode)" \<comment> \<open>ignoring assertion failures\<close>
    and "translation_assms_trace t"
    and "cap_inv_trace t"
    and "\<forall>instr. instr_of_trace t = Some instr \<longrightarrow> branch_instr_trace_has_expected_invocations opcode t"
  shows "invocation_writes_pstate_c64 (instr_trace opcode t)"
proof (cases "instr_of_trace t")
  case None
  then show ?thesis
    using instr_of_trace_None_instr_invokes_no_caps[OF None, where instr = opcode]
    by (auto simp: invocation_writes_pstate_c64_def)
next
  case (Some instr)
  then have "branch_instr_run_has_expected_pstate_writes opcode t"
    using hasTrace_Run[OF assms(1-3)] assms(6)
    by (simp add: branch_instr_trace_has_expected_invocations_def)
  then show ?thesis
    using Some assms(6)
    by (cases rule: hasTrace_instr_sem_invocation_cases[OF assms(1) Some assms(2-5)])
       (auto simp add: invocation_writes_pstate_c64_def branch_instr_run_has_expected_pstate_writes_def
                       image_Un clear_lsb_image_branch_caps_eq clear_lsb_image_mem_branch_caps_eq
                       branch_caps_128th_iff mem_branch_caps_128th_iff test_bit_set_gen invokable_def)
qed

end

context Morello_ISA
begin

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
