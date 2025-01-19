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

fun mem_cap_of_event :: "register_value event \<Rightarrow> (nat \<times> Capability) option" where
  "mem_cap_of_event (E_read_memt rk paddr sz val) =
     (if sz = 16 then
        (case vec_of_bits_maybe (bits_of_mem_bytes (fst val)) of
           Some (data :: 128 word) \<Rightarrow>
             let tag = (if snd val = B1 then 1 else 0 :: 1 word) in
             Some (paddr, word_cat tag data)
         | None \<Rightarrow> None)
      else None)"
| "mem_cap_of_event (E_read_mem rk paddr sz val) =
     (if sz = 16 then
        (case vec_of_bits_maybe (bits_of_mem_bytes val) of
           Some (data :: 128 word) \<Rightarrow> Some (paddr, ucast data)
         | None \<Rightarrow> None)
      else None)"
| "mem_cap_of_event _ = None"

(* Includes untagged capabilities *)
definition initial_mem_cap_loads_of_trace where
  "initial_mem_cap_loads_of_trace t \<equiv>
     {(paddr, c) | paddr c i.
        i < length t \<and>
        mem_cap_of_event (t ! i) = Some (paddr, c) \<and>
        no_mem_writes_in_trace (take i t)}"

definition initial_mem_cap_vaddr_loads_of_trace where
  "initial_mem_cap_vaddr_loads_of_trace t \<equiv>
     {(vaddr, c) | vaddr c paddr i.
        i < length t \<and>
        mem_cap_of_event (t ! i) = Some (paddr, c) \<and>
        translate_address vaddr = Some paddr \<and>
        no_mem_writes_in_trace (take i t)}"

abbreviation instr_trace_may_invoke where
  "instr_trace_may_invoke opcode t \<equiv> trace_invokes_code_cap_from_reg t \<noteq> None \<or> trace_indirect_sentry_type t \<noteq> None \<or> trace_invokes_data_cap_from_reg t \<noteq> None"

definition trace_reads_caps_from_gpr_or_null :: "int \<Rightarrow> register_value trace \<Rightarrow> Capability set" where
  "trace_reads_caps_from_gpr_or_null n t \<equiv> trace_reads_caps_from_gpr n t \<union> (if n = 31 then {0} else {})"

definition trace_reads_initial_caps_from_gpr_or_null :: "int \<Rightarrow> register_value trace \<Rightarrow> Capability set" where
  "trace_reads_initial_caps_from_gpr_or_null n t \<equiv> trace_reads_initial_caps_from_gpr n t \<union> (if n = 31 then {0} else {})"

definition branch_instr_run_has_expected_gpr_reads where
  "branch_instr_run_has_expected_gpr_reads t \<equiv>
     (\<forall>n. (trace_invokes_code_cap_from_reg t = Some n \<or> trace_invokes_data_cap_from_reg t = Some n \<longrightarrow>
             (\<exists>c. trace_reads_caps_from_gpr_or_null n t = {c} \<and> trace_reads_initial_caps_from_gpr_or_null n t = {c})) \<and>
          (trace_load_auths t = Some (RegAuth n) \<longrightarrow>
             (\<exists>c. trace_reads_caps_from_gpr n t = {c} \<and> trace_reads_initial_caps_from_gpr n t = {c})))"

definition branch_instr_run_has_expected_pstate_writes where
  "branch_instr_run_has_expected_pstate_writes opcode t \<equiv>
     (\<forall>cc' \<in> instr_invokes_code_caps opcode t.
         CapIsTagSet cc' \<longrightarrow>
           (\<exists>cc \<in> original_code_caps_invoked_in_trace t. pstate_c64_writes t = {lsb cc}))"

definition branch_instr_run_performs_expected_data_invocation where
  "branch_instr_run_performs_expected_data_invocation opcode t \<equiv>
     instr_invokes_data_caps opcode t \<noteq> {} \<longrightarrow>
     (\<exists>cc cd. trace_writes_pcc_caps ISA (instr_trace opcode t) = {cc} \<and>
              trace_writes_idc_caps ISA (instr_trace opcode t) = {cd} \<and>
              (CapIsTagSet cc \<longrightarrow>
                 cc \<in> instr_invokes_code_caps opcode t \<and>
                 cd \<in> instr_invokes_data_caps opcode t))"

definition trace_has_reg_load_auth_for_addr where
  "trace_has_reg_load_auth_for_addr t auth \<comment> \<open>vaddr sz\<close> \<equiv>
     (\<exists>n. trace_load_auths t = Some (RegAuth n) \<and>
          auth \<in> trace_reads_caps_from_gpr n t \<and>
          CapIsTagSet auth
          \<comment> \<open>\<and> set (address_range (bounds_address AccType_NORMAL vaddr) sz) \<subseteq> get_mem_region CC auth\<close>)"

definition branch_instr_run_has_expected_invocation_loads where
  "branch_instr_run_has_expected_invocation_loads t \<equiv>
     (case trace_indirect_sentry_type t of
        Some Points_to_PCC \<Rightarrow>
          (\<exists>auth paddr vaddr c.
              trace_has_reg_load_auth_for_addr t auth \<comment> \<open>vaddr 16\<close> \<and>
              (get_indirect_sentry_type auth = Some Points_to_PCC \<and> CapUnseal auth \<in> trace_invokes_indirect_sentries t \<or> \<not>CapIsSealed auth) \<and>
              \<comment> \<open>initial_mem_cap_vaddr_loads_of_trace t = {(vaddr, c)} \<and>
              mem_cap_vaddr_loads_of_trace t \<subseteq> initial_mem_cap_vaddr_loads_of_trace t \<and>\<close>
              translate_address vaddr = Some paddr \<and>
              initial_mem_cap_loads_of_trace t = {(paddr, c)} \<and>
              mem_cap_loads_of_trace t = {(paddr, c) | paddr c. (paddr, c) \<in> initial_mem_cap_loads_of_trace t \<and> CapIsTagSet c})
      | Some Points_to_Pair \<Rightarrow>
          (\<exists>auth paddr_cc paddr_cd cc cd.
              trace_has_reg_load_auth_for_addr t auth \<comment> \<open>(unat (CapGetValue auth)) 32\<close> \<and>
              (get_indirect_sentry_type auth = Some Points_to_Pair \<and> CapUnseal auth \<in> trace_invokes_indirect_sentries t \<or> \<not>CapIsSealed auth) \<and>
              \<comment> \<open>initial_mem_cap_vaddr_loads_of_trace t = {(unat (CapGetValue auth), cd), (unat (CapGetValue auth) + 16, cc)} \<and>
              mem_cap_vaddr_loads_of_trace t \<subseteq> initial_mem_cap_vaddr_loads_of_trace t \<and>\<close>
              translate_address (unat (CapGetValue auth)) = Some paddr_cd \<and>
              translate_address (unat (CapGetValue auth + 16)) = Some paddr_cc \<and>
              initial_mem_cap_loads_of_trace t = {(paddr_cd, cd), (paddr_cc, cc)} \<and>
              mem_cap_loads_of_trace t = {(paddr, c) | paddr c. (paddr, c) \<in> initial_mem_cap_loads_of_trace t \<and> CapIsTagSet c} \<comment> \<open>\<and>
              unat (CapGetValue auth + 16) = unat (CapGetValue auth) + 16 \<and>
              bounds_address AccType_NORMAL (unat (CapGetValue auth) + 16) = bounds_address AccType_NORMAL (unat (CapGetValue auth)) + 16\<close>)
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
        \<comment> \<open>branch_instr_run_performs_expected_invocation opcode t \<and>\<close>
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

lemma fold_un_map_eq_Un:
  "foldl (\<union>) xs (map f ys) = xs \<union> (\<Union>(f ` set ys))"
  by (induction ys arbitrary: xs) auto

lemmas monad_trace_subset_datatype_splits[monad_trace_subset_intro] =
  datatype_splits[where P="monad_trace_subset _", THEN iffD2]

lemma monad_trace_subset_ConstrainUnpredictable[monad_trace_subset]:
  "monad_trace_subset {} (ConstrainUnpredictable u)"
  by (cases u) (auto simp: monad_trace_subset_return)

lemmas invocation_execute_defs =
  execute_BRS_C_C_C_def execute_BRS_C_C_def execute_BLRR_C_C_def execute_BLRS_C_C_def
  execute_BLRS_C_C_C_def execute_BLR_C_C_def execute_BRR_C_C_def execute_BR_C_C_def
  execute_RETR_C_C_def execute_RETS_C_C_def execute_RETS_C_C_C_def execute_RET_C_C_def
  execute_BLR_CI_C_def execute_BR_CI_C_def execute_LDPBLR_C_C_C_def execute_LDPBR_C_C_C_def

lemmas invocation_decode_defs[unfolded Let_def] =
  decode_BRS_C_C_C_def decode_BRS_C_C_def decode_BLRR_C_C_def decode_BLRS_C_C_def
  decode_BLRS_C_C_C_def decode_BLR_C_C_def decode_BRR_C_C_def decode_BR_C_C_def
  decode_RETR_C_C_def decode_RETS_C_C_def decode_RETS_C_C_C_def decode_RET_C_C_def
  decode_BLR_CI_C_def decode_BR_CI_C_def decode_LDPBLR_C_C_C_def decode_LDPBR_C_C_C_def

setup \<open>Monad_Trace_Subset_Exploration.install_recs
  ["Morello_bindings", "Morello"]
  @{thms invocation_execute_defs Step_PC_def}
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
  by (auto simp: Have16bitVMID_def IMPDEF_boolean_def IMPDEF_boolean_map_def intro: monad_no_exception)

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

lemma pre_post_False: "pre_post (\<lambda>_. False) m Q E F"
  by (auto simp: pre_post_def)

lemma pre_post_return:
  "pre_post (Q a) (return a) Q E F"
  by (auto simp: pre_post_def)

lemma pre_post_bind:
  assumes f: "\<And>s t a. Run m t a \<Longrightarrow> trace_assms s t \<Longrightarrow> pre_post (R a) (f a) Q E F"
    and m: "pre_post P m R E F"
  shows "pre_post P (bind m f) Q E F"
  (* Note: Could include \<open>P s\<close> in \<open>f\<close>, but then an uninstantiated precondition could appear
     in backwards reasoning; if we add it, need to adapt the \<open>rotated\<close> attributes below *)
  by (intro pre_postI;
      fastforce elim!: Run_bindE bind_Exception_cases bind_Fail_cases
                elim: m[THEN pre_post_ExceptionE] f[THEN pre_post_ExceptionE, rotated 2]
                      m[THEN pre_post_FailE] f[THEN pre_post_FailE, rotated 2]
                      m[THEN pre_post_RunE] f[THEN pre_post_RunE, rotated 2])

lemma pre_post_bind_ignore_trace:
  assumes f: "\<And>a. pre_post (R a) (f a) Q E F"
    and m: "pre_post P m R E F"
  shows "pre_post P (bind m f) Q E F"
  using assms
  by (auto intro: pre_post_bind)

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

lemma pre_post_read_mem_BC:
  "pre_post
     (\<lambda>s. case nat_of_bv BCa addr of
            Some addr' \<Rightarrow>
              (\<forall>e bytes tag.
                 e = E_read_mem rk addr' (nat sz) bytes \<and> ev_assms s e \<longrightarrow>
                 (case of_bits_method BCb (bits_of_mem_bytes bytes) of
                    Some v \<Rightarrow> Q v (step_state s e)
                  | None \<Rightarrow> F ''bits_of_mem_bytes'' (step_state s e)))
          | None \<Rightarrow> F ''nat_of_bv'' s)
     (read_mem BCa BCb rk addr_sz addr sz) Q E F"
  by (intro pre_postI;
      fastforce simp: read_mem_def read_mem_bytes_def maybe_fail_def elim: Traces_cases split: option.splits)

lemma pre_post_read_mem:
  "pre_post
     (\<lambda>s. (\<forall>e bytes tag.
             e = E_read_mem rk (unat addr) (nat sz) bytes \<and> ev_assms s e \<longrightarrow>
             (case of_bits_method BC_mword (bits_of_mem_bytes bytes) of
                Some v \<Rightarrow> Q v (step_state s e)
              | None \<Rightarrow> F ''bits_of_mem_bytes'' (step_state s e))))
     (read_mem BC_mword BC_mword rk addr_sz addr sz) Q E F"
  by (rule pre_post_read_mem_BC[THEN pre_post_strengthen_pre]) auto

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

named_theorems no_state_update

lemma no_state_update_bind[no_state_update]:
  assumes "no_state_update m" and "\<And>t a s. Run m t a \<Longrightarrow> trace_assms s t \<Longrightarrow> no_state_update (f a)"
  shows "no_state_update (bind m f)"
  using assms
  by (fastforce simp: no_state_update_def elim!: bind_Traces_cases)

lemma no_state_update_return[no_state_update, simp]:
  "no_state_update (return a)"
  by (auto simp: no_state_update_def)

lemma no_state_update_and_boolM[no_state_update]:
  "no_state_update m1 \<Longrightarrow> no_state_update m2 \<Longrightarrow> no_state_update (and_boolM m1 m2)"
  by (auto simp: and_boolM_def intro: no_state_update_bind)

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
  shows "pre_post P m (\<lambda>a s. if b a s then Q a s else Q a s) E F"
  by (use assms in auto)

lemma pre_post_if_False:
  "pre_post P m2 Q E F \<Longrightarrow> pre_post P (if False then m1 else m2) Q E F"
  by auto

lemma pre_post_if_True:
  "pre_post P m1 Q E F \<Longrightarrow> pre_post P (if True then m1 else m2) Q E F"
  by auto

lemma pre_post_case_prod:
  assumes "pre_post P (f (fst x) (snd x)) Q E F"
  shows "pre_post P (case x of (a, b) \<Rightarrow> f a b) Q E F"
  by (use assms in auto)

lemma pre_post_and_boolM:
  assumes "pre_post R m2 Q E F"
    and "pre_post P m1 (\<lambda>a s. if a then R s else Q False s) E F"
  shows "pre_post P (and_boolM m1 m2) Q E F"
  unfolding and_boolM_def
  apply (rule pre_post_bind, rule pre_post_if)
    apply (rule assms)
   apply (rule pre_post_return)
  apply (rule assms)
  done

lemma pre_post_or_boolM:
  assumes "pre_post R m2 Q E F"
    and "pre_post P m1 (\<lambda>a s. if a then Q True s else R s) E F"
  shows "pre_post P (or_boolM m1 m2) Q E F"
  unfolding or_boolM_def
  apply (rule pre_post_bind, rule pre_post_if)
    apply (rule pre_post_return)
   apply (rule assms)
  apply (rule assms)
  done

lemma pre_post_exit:
  "pre_post (F ''exit'') (exit0 u) Q E F"
  unfolding exit0_def
  by (rule pre_postI) auto

named_theorems pre_post_intro
named_theorems pre_post_elim
named_theorems pre_post_combinators

lemmas pre_post_builtins[pre_post_intro] =
  pre_post_return pre_post_ignore_fail_assert_exp pre_post_exit

lemmas pre_post_builtin_combinators[pre_post_combinators] =
  pre_post_bind_ignore_trace pre_post_if pre_post_and_boolM pre_post_or_boolM pre_post_case_prod

method pre_post_step uses intro elim =
  (erule elim pre_post_elim eqTrueE
   | rule intro pre_post_intro TrueI
   | rule pre_post_combinators TrueI)

method pre_postI_with methods preprocess solve uses intro elim =
  (rule pre_post_strengthen_pre,
   (preprocess?, (pre_post_step intro: intro elim: elim | solve))+)

method pre_postI uses intro elim simp = pre_postI_with \<open>-\<close> \<open>simp add: simp\<close> intro: intro elim: elim

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

definition no_accesses_to_gpr_in_trace where
  "no_accesses_to_gpr_in_trace n t \<equiv> (\<forall>r \<in> R_name n. \<forall>v. E_read_reg r v \<notin> set t \<and> E_write_reg r v \<notin> set t)"

definition no_mem_cap_reads where
  "no_mem_cap_reads m \<equiv>
     (\<forall>t m'. (m, t, m') \<in> Traces \<longrightarrow>
        (\<forall>rk addr sz val. E_read_memt rk addr sz val \<notin> set t) \<and>
        (\<forall>rk addr val. E_read_mem rk addr 16 val \<notin> set t))"

definition no_mem_cap_reads_in_trace where
  "no_mem_cap_reads_in_trace t \<equiv>
     ((\<forall>rk addr sz val. E_read_memt rk addr sz val \<notin> set t) \<and>
      (\<forall>rk addr val. E_read_mem rk addr 16 val \<notin> set t))"

definition no_gpr_accesses_or_mem_cap_reads where
  "no_gpr_accesses_or_mem_cap_reads m \<equiv> no_accesses_to_any_gpr m \<and> no_mem_cap_reads m"

lemma no_gpr_accesses_or_mem_cap_reads_trace_iff:
  "no_gpr_accesses_or_mem_cap_reads m
   \<longleftrightarrow> (\<forall>t m'. (m, t, m') \<in> Traces
           \<longrightarrow> no_mem_cap_reads_in_trace t \<and> (\<forall>n. no_accesses_to_gpr_in_trace n t))"
  unfolding no_gpr_accesses_or_mem_cap_reads_def no_accesses_to_any_gpr_def
    no_reads_from_any_gpr_def no_reads_from_gpr_def no_writes_to_any_gpr_def
    no_writes_to_gpr_def no_accesses_to_gpr_in_trace_def no_mem_cap_reads_def
    no_mem_cap_reads_in_trace_def
  by auto

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
proof -
  have ifI: "\<exists>n. n > n0 \<and> r \<in> (if n = m then Rs else Rs' n)"
    if "m > n0" and "Rs \<subseteq> all_R_names" and "r \<notin> Rs \<longrightarrow> (\<exists>n. n > m \<and> r \<in> Rs' n)" for Rs Rs' and n0 m :: int
    using that assms
    by (cases "r \<in> Rs") auto
  have "\<exists>n. n > (-1) \<and> r \<in> R_name n"
    using assms
    unfolding R_name_def
    by (intro ifI impI) (auto simp: all_R_names_def)
  then show ?thesis
    by auto
qed

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
    and "disjnt (range (\<lambda>(rk, addr, val, sz). E_read_memt rk addr sz val) \<union> range (\<lambda>(rk, addr, val, sz). E_read_mem rk addr sz val)) S"
  shows "no_mem_cap_reads m"
  using assms
  by (fastforce simp: no_mem_cap_reads_def monad_trace_subset_def disjnt_def)

lemma monad_trace_subset_no_gpr_accesses_or_mem_cap_reads:
  assumes "monad_trace_subset S m"
    and "disjnt (range (\<lambda>(rk, addr, val, sz). E_read_memt rk addr sz val) \<union> range (\<lambda>(rk, addr, val, sz). E_read_mem rk addr sz val)) S \<and> (\<forall>r \<in> all_R_names. disjnt (range (E_read_reg r) \<union> range (E_write_reg r)) S)"
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
  "disjnt (range (\<lambda>(rk, addr, val, sz). E_read_mem rk addr sz val)) (range (E_read_reg r'))"
  "disjnt (range (\<lambda>(rk, addr, val, sz). E_read_mem rk addr sz val)) (range (E_write_reg r'))"
  "disjnt (range (\<lambda>(rk, addr, val, sz). E_read_mem rk addr sz val)) (range (E_choose msg))"
  "disjnt (range (\<lambda>(wk, addr, val, sz, y). E_write_mem wk addr sz val y)) (range (E_read_reg r))"
  "disjnt (range (\<lambda>(wk, addr, val, sz, y). E_write_mem wk addr sz val y)) (range (E_write_reg r))"
  "disjnt (range (\<lambda>(wk, addr, val, sz, y). E_write_mem wk addr sz val y)) (range (E_choose msg))"
  "disjnt (range (\<lambda>(wk, addr, val, sz, y). E_write_mem wk addr sz val y))
          (range (\<lambda>(rk, addr, val, sz). E_read_mem rk addr sz val))"
  "disjnt (range (\<lambda>(wk, addr, val, sz, y). E_write_mem wk addr sz val y))
          (range (\<lambda>(rk, addr, val, sz). E_read_memt rk addr sz val))"
  "disjnt (range (\<lambda>(wk, addr, val, tag, sz, y). E_write_memt wk addr sz val tag y)) (range (E_read_reg r))"
  "disjnt (range (\<lambda>(wk, addr, val, tag, sz, y). E_write_memt wk addr sz val tag y)) (range (E_write_reg r))"
  "disjnt (range (\<lambda>(wk, addr, val, tag, sz, y). E_write_memt wk addr sz val tag y)) (range (E_choose msg))"
  "disjnt (range (\<lambda>(wk, addr, val, tag, sz, y). E_write_memt wk addr sz val tag y))
          (range (\<lambda>(rk, addr, val, sz). E_read_mem rk addr sz val))"
  "disjnt (range (\<lambda>(wk, addr, val, tag, sz, y). E_write_memt wk addr sz val tag y))
          (range (\<lambda>(rk, addr, val, sz). E_read_memt rk addr sz val))"
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
  invocation_regs_written :: bool
  gpr_reads_after_write :: bool

definition
  "initial_invocation_state regs \<equiv>
     \<lparr>code_reg_caps = {}, data_reg_caps = {}, load_auth_caps = {}, mem_caps = {},
      reg_state = regs, pcc_writes = [], idc_writes = [], pstate_writes = [],
      branch_taken_writes = [], invocation_regs_written = False, gpr_reads_after_write = False\<rparr>"

lemma initial_invocation_state_simps[simp]:
  "code_reg_caps (initial_invocation_state regs) = {}"
  "data_reg_caps (initial_invocation_state regs) = {}"
  "load_auth_caps (initial_invocation_state regs) = {}"
  "mem_caps (initial_invocation_state regs) = {}"
  "pcc_writes (initial_invocation_state regs) = []"
  "idc_writes (initial_invocation_state regs) = []"
  "pstate_writes (initial_invocation_state regs) = []"
  "branch_taken_writes (initial_invocation_state regs) = []"
  "invocation_regs_written (initial_invocation_state regs) = False"
  "gpr_reads_after_write (initial_invocation_state regs) = False"
  "reg_state (initial_invocation_state regs) = regs"
  by (auto simp: initial_invocation_state_def)

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

abbreviation
  "instr_may_invoke \<equiv>
     instr_invokes_code_cap_from_reg instr \<noteq> None \<or> instr_indirect_sentry_type instr \<noteq> None"

definition "invocation_regs = all_R_names \<union> {''PCC'', ''PSTATE'', ''__BranchTaken''}"

fun step_state :: "invocation_state \<Rightarrow> register_value event \<Rightarrow> invocation_state" where
  "step_state s (E_read_reg r (Regval_bitvector_129_dec c)) =
    s\<lparr>code_reg_caps := (if is_code_reg r then insert c (code_reg_caps s) else code_reg_caps s),
      data_reg_caps := (if is_data_reg r then insert c (data_reg_caps s) else data_reg_caps s),
      load_auth_caps := (if is_load_auth_reg r then insert c (load_auth_caps s) else load_auth_caps s),
      gpr_reads_after_write := (if invocation_regs_written s \<and> r \<in> all_R_names then True else gpr_reads_after_write s)\<rparr>"
| "step_state s (E_write_reg r v) =
    s\<lparr>\<comment> \<open>reg_state := (if r \<in> dom (reg_state s) \<inter> invocation_regs then (reg_state s)(r\<mapsto>v) else reg_state s),\<close>
      pcc_writes := (if r = ''PCC'' then v # pcc_writes s else pcc_writes s),
      idc_writes := (if r = ''_R29'' then v # idc_writes s else idc_writes s),
      pstate_writes := (if r = ''PSTATE'' then v # pstate_writes s else pstate_writes s),
      branch_taken_writes := (if r = ''__BranchTaken'' then v # branch_taken_writes s else branch_taken_writes s),
      invocation_regs_written := (if r \<in> invocation_regs then True else invocation_regs_written s)\<rparr>"
| "step_state s (E_read_memt rk paddr sz val) =
    (case mem_cap_of_event (E_read_memt rk paddr sz val) of Some (paddr, c) \<Rightarrow> s\<lparr>mem_caps := insert (paddr, c) (mem_caps s)\<rparr> | None \<Rightarrow> s)"
| "step_state s (E_read_mem rk paddr sz val) =
    (case mem_cap_of_event (E_read_mem rk paddr sz val) of Some (paddr, c) \<Rightarrow> s\<lparr>mem_caps := insert (paddr, c) (mem_caps s)\<rparr> | None \<Rightarrow> s)"
| "step_state s e = s"

definition init_null_caps where
  "init_null_caps s \<equiv>
     s\<lparr>code_reg_caps := (if instr_invokes_code_cap_from_reg instr = Some 31 then {0} else {}),
       data_reg_caps := (if instr_invokes_data_cap_from_reg instr = Some 31 then {0} else {})\<rparr>"

definition has_null_caps where
  "has_null_caps s \<equiv>
     code_reg_caps s = (if instr_invokes_code_cap_from_reg instr = Some 31 then {0} else {}) \<and>
     data_reg_caps s = (if instr_invokes_data_cap_from_reg instr = Some 31 then {0} else {})"

definition original_mem_code_caps :: "invocation_state \<Rightarrow> Capability set" where
  "original_mem_code_caps s \<equiv>
     {cc. \<exists>paddr.
             (paddr, cc) \<in> mem_caps s \<and>
             (instr_indirect_sentry_type instr = Some Points_to_Pair \<longrightarrow>
                (\<exists>auth \<in> load_auth_caps s. translate_address (unat (CapGetValue auth + 16)) = Some paddr))}"

definition "original_code_caps s \<equiv> code_reg_caps s \<union> original_mem_code_caps s"

definition invoked_code_caps :: "invocation_state \<Rightarrow> Capability set" where
  "invoked_code_caps s =
     \<Union>(branch_caps ` clear_lsb ` CapUnseal ` code_reg_caps s) \<union>
     \<Union>(mem_branch_caps ` clear_lsb ` original_mem_code_caps s)"

definition original_mem_data_caps :: "invocation_state \<Rightarrow> Capability set" where
  "original_mem_data_caps s \<equiv>
     {cc. \<exists>paddr.
             (paddr, cc) \<in> mem_caps s \<and>
             instr_indirect_sentry_type instr = Some Points_to_Pair \<and>
             instr_invokes_indirect_cap_from_reg instr \<noteq> None \<and>
             (\<exists>auth \<in> load_auth_caps s. translate_address (unat (CapGetValue auth)) = Some paddr)}"

definition original_reg_data_caps :: "invocation_state \<Rightarrow> Capability set" where
  "original_reg_data_caps s \<equiv>
     (case instr_indirect_sentry_type instr of
        Some Points_to_PCC \<Rightarrow>
          (if instr_invokes_indirect_cap_from_reg instr = None then {}
           else {c. c \<in> load_auth_caps s \<and> CapIsTagSet c \<and> get_indirect_sentry_type c = Some Points_to_PCC})
      | Some Points_to_Pair \<Rightarrow> {}
      | None \<Rightarrow> {cd. \<exists>cc \<in> code_reg_caps s. invokable CC cc cd \<and> cd \<in> data_reg_caps s})"

definition invoked_data_caps :: "invocation_state \<Rightarrow> Capability set" where
  "invoked_data_caps s =
     \<comment> \<open>original_reg_data_caps s \<union>\<close>
     (CapUnseal ` original_reg_data_caps s) \<union>
     \<Union>(mem_data_caps ` original_mem_data_caps s)"

definition has_expected_gpr_reads :: "invocation_state \<Rightarrow> bool" where
  "has_expected_gpr_reads s \<longleftrightarrow>
     (instr_invokes_code_cap_from_reg instr \<noteq> None \<longrightarrow> is_singleton (code_reg_caps s)) \<and>
     (instr_invokes_data_cap_from_reg instr \<noteq> None \<longrightarrow> is_singleton (data_reg_caps s)) \<and>
     (\<forall>n. instr_load_auth instr = Some (RegAuth n) \<longrightarrow> is_singleton (load_auth_caps s)) \<and>
     \<not>gpr_reads_after_write s"

definition has_expected_pstate_writes where
  "has_expected_pstate_writes s \<equiv>
     (\<exists>pstate cc.
         pstate_writes s = [Regval_ProcState pstate] \<and> cc \<in> original_code_caps s \<and>
         (CapIsTagSet cc \<longrightarrow> test_bit (ProcState_C64 pstate) 0 = lsb cc))"

definition has_load_cap_perm_if_needed where
  "has_load_cap_perm_if_needed pcc_tagged s \<equiv>
     pcc_tagged \<and> instr_invokes_indirect_cap_from_reg instr \<noteq> None \<longrightarrow>
     (\<exists>c \<in> load_auth_caps s. cap_permits CAP_PERM_LOAD_CAP c)"

definition has_expected_data_invocation where
  "has_expected_data_invocation s \<equiv>
     invoked_data_caps s \<noteq> {} \<longrightarrow>
     (\<exists>cc cd. pcc_writes s = [Regval_bitvector_129_dec cc] \<and>
              idc_writes s = [Regval_bitvector_129_dec cd] \<and>
              branch_taken_writes s = [Regval_bool True] \<and>
              (CapIsTagSet cc \<longrightarrow> cc \<in> invoked_code_caps s \<and> cd \<in> invoked_data_caps s \<and>
                                  has_load_cap_perm_if_needed True s))"

definition cap_authorises_load :: "Capability \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "cap_authorises_load c vaddr sz \<equiv>
     CapIsTagSet c \<and> \<comment> \<open>cap_permits CAP_PERM_LOAD_CAP c \<and>\<close>
     ((get_indirect_sentry_type c = instr_indirect_sentry_type instr \<and>
       instr_invokes_indirect_cap_from_reg instr \<noteq> None)
      \<or> \<not>CapIsSealed c) \<comment> \<open>\<and>
     valid_address AccType_NORMAL vaddr \<and>
     bounds_address AccType_NORMAL vaddr + sz \<le> 2^64
     \<and> set (address_range (bounds_address AccType_NORMAL vaddr) sz) \<subseteq> get_mem_region CC c\<close>"

definition has_expected_loads where
  "has_expected_loads s \<equiv>
     (case instr_indirect_sentry_type instr of
        Some Points_to_PCC \<Rightarrow>
         \<exists>auth paddr vaddr c.
            auth \<in> load_auth_caps s \<and> cap_authorises_load auth vaddr 16 \<and>
            translate_address vaddr = Some paddr \<and>
            mem_caps s = {(paddr, c)}
      | Some Points_to_Pair \<Rightarrow>
         \<exists>auth cc paddr_cc cd paddr_cd.
            auth \<in> load_auth_caps s \<and> cap_authorises_load auth (unat (CapGetValue auth)) 32 \<and>
            translate_address (unat (CapGetValue auth)) = Some paddr_cd \<and>
            translate_address (unat (CapGetValue auth + 16)) = Some paddr_cc \<and>
            mem_caps s = {(paddr_cd, cd), (paddr_cc, cc)}
      | None \<Rightarrow> (load_auth_caps s = {} \<longrightarrow> mem_caps s = {}))"

definition is_expected_exception where
  "is_expected_exception e s \<equiv>
     e = Error_ExceptionTaken () \<and> idc_writes s = [] \<and> (\<exists>c. pcc_writes s = [Regval_bitvector_129_dec c])"

abbreviation "pcc_cap_writes s \<equiv> \<Union>(caps_of_regval ` set (pcc_writes s))"
abbreviation "idc_cap_writes s \<equiv> \<Union>(caps_of_regval ` set (idc_writes s))"

definition
  "ev_reads_invocation_regs_from_initial_reg_state s e \<equiv>
     (\<not>invocation_regs_written s \<longrightarrow> ev_reads_from_reg_state (restrict_map (reg_state s) invocation_regs) e)"

definition (in Morello_ISA)
  "debug_disabled e \<equiv>
     (\<forall>v. e = E_read_reg ''DBGEN'' (Regval_signal v) \<longrightarrow> (v = LOW)) \<and>
     (\<forall>v. e = E_read_reg ''EDSCR'' (Regval_bitvector_32_dec v) \<longrightarrow> (ucast v :: 6 word) = 2) \<and>
     (\<forall>v. e = E_read_reg ''MDSCR_EL1'' (Regval_bitvector_32_dec v) \<longrightarrow> (\<not>v !! 15) \<and> (\<not>v !! 0))"

abbreviation ev_assms :: "invocation_state \<Rightarrow> register_value event \<Rightarrow> bool" where
  "ev_assms s e \<equiv> ev_reads_invocation_regs_from_initial_reg_state s e \<and> debug_disabled e \<and> translation_assms e"

sublocale Hoare_Logic where ev_assms = ev_assms and step_state = step_state .

lemma trace_assms_translation_assms_trace:
  "trace_assms s t \<Longrightarrow> translation_assms_trace t"
  by (induction s t rule: trace_assms.induct) auto

lemma invocation_regs_written_step_state:
  "invocation_regs_written (step_state s e) \<longleftrightarrow> (\<exists>r v. e = E_write_reg r v \<and> r \<in> invocation_regs) \<or> invocation_regs_written s"
  by (induction s e rule: step_state.induct) (auto split: option.split)

lemma invocation_regs_written_run_state:
  "invocation_regs_written (run_state s t) \<longleftrightarrow> (\<exists>r v i. t ! i = E_write_reg r v \<and> i < length t \<and> r \<in> invocation_regs) \<or> invocation_regs_written s"
  by (induction t arbitrary: s) (auto simp: nth_Cons invocation_regs_written_step_state gr0_conv_Suc split: nat.splits)

lemma gpr_reads_after_write_step_state:
  "gpr_reads_after_write (step_state s e) \<longleftrightarrow>
   (\<exists>r c. e = E_read_reg r (Regval_bitvector_129_dec c) \<and> r \<in> all_R_names \<and> invocation_regs_written s) \<or> gpr_reads_after_write s"
  by (induction s e rule: step_state.induct) (auto split: option.split)

lemma gpr_reads_after_write_run_state:
  "gpr_reads_after_write (run_state s t) \<longleftrightarrow>
     (\<exists>r c i. t ! i = E_read_reg r (Regval_bitvector_129_dec c) \<and> r \<in> all_R_names \<and> i < length t \<and>
              invocation_regs_written (run_state s (take i t)))
     \<or> gpr_reads_after_write s"
  by (induction t arbitrary: s)
     (auto simp: nth_Cons gpr_reads_after_write_step_state gr0_conv_Suc split: nat.splits)

lemma mem_caps_step_state:
  "mem_caps (step_state s e) =
     {(paddr, c) | paddr c. mem_cap_of_event e = Some (paddr, c)}
     \<union> mem_caps s"
  by (induction s e rule: step_state.induct) (auto split: option.splits)

lemma mem_caps_run_state:
  "mem_caps (run_state s t) =
     {(paddr, c) | paddr c. \<exists>e \<in> set t. mem_cap_of_event e = Some (paddr, c)}
     \<union> mem_caps s"
  by (induction t arbitrary: s) (auto simp: mem_caps_step_state)

lemma pstate_writes_step_state:
  "pstate_writes (step_state s e) = (case e of E_write_reg r v \<Rightarrow> (if r = ''PSTATE'' then [v] else []) | _ \<Rightarrow> []) @ pstate_writes s"
  by (induction s e rule: step_state.induct) (auto split: option.splits)

lemma set_pstate_writes_run_state:
  "set (pstate_writes (run_state s t)) = {v. E_write_reg ''PSTATE'' v \<in> set t \<or> v \<in> set (pstate_writes s)}"
  by (induction t arbitrary: s) (auto simp add: pstate_writes_step_state)

lemma pcc_cap_writes_run_state:
  "pcc_cap_writes (run_state s t) = pcc_cap_writes s \<union> \<Union>(ev_writes_pcc_caps ISA ` set t)"
proof (induction t arbitrary: s)
  case (Cons e t)
  have "ev_writes_pcc_caps ISA e = (case e of E_write_reg r v \<Rightarrow> if r = ''PCC'' then caps_of_regval v else {} | _ \<Rightarrow> {})"
    by (cases e) (auto simp: ev_writes_pcc_caps_def)
  then show ?case
    using Cons.IH[of "step_state s e"]
    by (induction e rule: step_state.induct) (auto split: option.splits)
qed auto

lemma idc_cap_writes_run_state:
  "idc_cap_writes (run_state s t) = idc_cap_writes s \<union> \<Union>(ev_writes_idc_caps ISA ` set t)"
proof (induction t arbitrary: s)
  case (Cons e t)
  have "ev_writes_idc_caps ISA e = (case e of E_write_reg r v \<Rightarrow> if r = ''_R29'' then caps_of_regval v else {} | _ \<Rightarrow> {})"
    by (cases e) (auto simp: ev_writes_idc_caps_def)
  then show ?case
    using Cons.IH[of "step_state s e"]
    by (induction e rule: step_state.induct) (auto split: option.splits)
qed auto

lemma trace_reads_initial_caps_from_gpr_eq:
  assumes "\<not>gpr_reads_after_write (run_state s t)"
  shows "trace_reads_initial_caps_from_gpr n t = trace_reads_caps_from_gpr n t"
  using assms
  unfolding gpr_reads_after_write_run_state
  unfolding trace_reads_initial_caps_from_gpr_def trace_reads_caps_from_gpr_def
  by (auto simp: all_R_names_iff_R_name invocation_regs_written_run_state in_set_conv_nth invocation_regs_def; blast)

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
  qed (auto simp: trace_reads_caps_from_gpr_def split: option.splits if_splits)
qed (auto simp: trace_reads_caps_from_gpr_def)

lemma no_code_reg_caps_run_state:
  assumes "instr_invokes_code_cap_from_reg instr = None"
  shows "code_reg_caps (run_state s t) = code_reg_caps s"
proof (induction t arbitrary: s)
  case (Cons e t)
  then show ?case
    using assms
    by (induction s e rule: step_state.induct) (auto simp: is_code_reg_def split: option.split)
qed auto

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
  qed (auto simp: trace_reads_caps_from_gpr_def split: option.splits if_splits)
qed (auto simp: trace_reads_caps_from_gpr_def)

lemma no_data_reg_caps_run_state:
  assumes "instr_invokes_data_cap_from_reg instr = None"
  shows "data_reg_caps (run_state s t) = data_reg_caps s"
proof (induction t arbitrary: s)
  case (Cons e t)
  then show ?case
    using assms
    by (induction s e rule: step_state.induct) (auto simp: is_data_reg_def split: option.split)
qed auto

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
  qed (auto simp: trace_reads_caps_from_gpr_def split: option.splits if_splits)
qed (auto simp: trace_reads_caps_from_gpr_def)

lemma no_load_auth_caps_run_state:
  assumes "instr_load_auth instr = None"
  shows "load_auth_caps (run_state s t) = load_auth_caps s"
proof (induction t arbitrary: s)
  case (Cons e t)
  then show ?case
    using assms
    by (induction s e rule: step_state.induct) (auto simp: is_load_auth_reg_def split: option.split)
qed auto

lemma no_load_auth_no_expected_mem_caps:
  assumes "has_expected_loads (run_state s t)"
    and "instr_load_auth instr = None"
    and "load_auth_caps s = {}"
  shows "mem_caps (run_state s t) = {}"
proof -
  from assms have "instr_indirect_sentry_type instr = None"
    by (cases instr) auto
  then show ?thesis
    using assms
    by (auto simp: has_expected_loads_def no_load_auth_caps_run_state)
qed

lemma instr_load_auth_if_indirect_sentry_type:
  assumes "instr_indirect_sentry_type instr = Some sentry_type"
  obtains n where "instr_load_auth instr = Some (RegAuth n)"
  using assms
  by (auto elim!: instr_indirect_sentry_type.elims)

lemma instr_indirect_sentry_type_if_load_auth:
  assumes "instr_load_auth instr = Some (RegAuth n)"
  obtains sentry_type where "instr_indirect_sentry_type instr = Some sentry_type"
  using assms
  by (auto elim!: instr_load_auth.elims)

lemma code_cap_reg_if_data_cap_reg:
  assumes "instr_invokes_data_cap_from_reg instr = Some n"
  obtains m where "instr_invokes_code_cap_from_reg instr = Some m"
  using assms
  by (auto elim!: instr_invokes_data_cap_from_reg.elims)

lemma indirect_cap_reg_is_load_auth:
  assumes "instr_invokes_indirect_cap_from_reg instr = Some n"
  shows "instr_load_auth instr = Some (RegAuth n)"
  using assms
  by (cases instr) (auto split: if_splits)

lemma load_auth_caps_of_trace_trace_reads_caps_from_gpr:
  assumes "instr_load_auth instr = Some (RegAuth n)"
    and "instr_of_trace t = Some instr"
  shows "instr_trace_load_auth_caps t = trace_reads_caps_from_gpr n t"
  using assms
  by (auto simp: instr_trace_load_auth_caps_def trace_load_auths_def trace_reads_caps_from_gpr_def)

lemma load_auth_caps_run_eq_load_auth_caps_of_trace:
  assumes "instr_indirect_sentry_type instr = Some sentry_type"
    and "instr_of_trace t = Some instr"
  shows "load_auth_caps (run_state s t) = instr_trace_load_auth_caps t \<union> load_auth_caps s"
  using assms
  by (elim instr_load_auth_if_indirect_sentry_type)
     (auto simp: load_auth_caps_run_state_trace_reads_caps_from_gpr load_auth_caps_of_trace_trace_reads_caps_from_gpr)

lemma branch_instr_run_has_expected_gpr_readsI:
  assumes "instr_may_invoke \<longrightarrow> has_expected_gpr_reads (run_state s t)"
    and "load_auth_caps s = {}" and "has_null_caps s" (* and "code_reg_caps s = {}" and "data_reg_caps s = {}"*)
    and "instr_of_trace t = Some instr"
  shows "branch_instr_run_has_expected_gpr_reads t"
  using assms
  unfolding branch_instr_run_has_expected_gpr_reads_def has_expected_gpr_reads_def
  by (auto simp: trace_invokes_code_cap_from_reg_def trace_invokes_data_cap_from_reg_def
                 trace_load_auths_def trace_reads_initial_caps_from_gpr_eq is_singleton_def
                 code_reg_caps_run_state_trace_reads_caps_from_gpr
                 data_reg_caps_run_state_trace_reads_caps_from_gpr
                 load_auth_caps_run_state_trace_reads_caps_from_gpr initial_invocation_state_def has_null_caps_def
                 trace_reads_caps_from_gpr_or_null_def trace_reads_initial_caps_from_gpr_or_null_def
           elim: instr_indirect_sentry_type_if_load_auth code_cap_reg_if_data_cap_reg split: if_splits)

lemma original_reg_code_caps_invoked_in_trace_in_code_reg_caps:
  assumes "instr_of_trace t = Some instr"
  shows "original_reg_code_caps_invoked_in_trace t \<subseteq> code_reg_caps (run_state s t)"
  using assms
  unfolding original_reg_code_caps_invoked_in_trace_def original_cap_pairs_invoked_in_trace_def
    original_direct_reg_sentries_invoked_in_trace_def
  by (auto simp: trace_invokes_code_cap_from_reg_def code_reg_caps_run_state_trace_reads_caps_from_gpr)

lemma nth_ucast_len:
  fixes w :: "'a::len word"
  defines "w' \<equiv> ucast w :: 'b::len word"
  shows "w' !! n = (w !! n \<and> n < LENGTH('a) \<and> n < LENGTH('b))"
  by (auto simp: w'_def nth_ucast dest: test_bit_len)

lemma mem_cap_of_event_Some_tagged_iff:
  assumes "CapIsTagSet c"
  shows "mem_cap_of_event e = Some (paddr, c) \<longleftrightarrow>
         (\<exists>rk bytes. e = E_read_memt rk paddr 16 (bytes, B1) \<and> cap_of_mem_bytes bytes B1 = Some c)"
  using assms
  by (cases e) (auto simp: cap_of_mem_bytes_def nth_ucast_len split: option.splits)

lemma original_code_caps_indirectly_invoked_in_trace_in_original_mem_code_caps:
  assumes "instr_of_trace t = Some instr"
  shows "original_code_caps_indirectly_invoked_in_trace t \<subseteq> original_mem_code_caps (run_state s t)"
  using assms
  unfolding original_code_caps_indirectly_invoked_in_trace_def original_mem_code_caps_def
    trace_invokes_indirect_sentries_def trace_invokes_indirect_cap_from_reg_def
    trace_indirect_sentry_type_def
  apply (auto simp: mem_caps_run_state indirect_cap_reg_is_load_auth[THEN load_auth_caps_run_state_trace_reads_caps_from_gpr] mem_cap_of_event_Some_tagged_iff CapUnseal_get_bounds_helpers_eq elim!: get_indirect_sentry_type_Some_cases)
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
  by (fastforce simp: mem_caps_run_state load_auth_caps_run_eq_load_auth_caps_of_trace mem_cap_of_event_Some_tagged_iff)

lemma original_code_caps_invoked_in_trace_in_original_code_caps:
  assumes "instr_of_trace t = Some instr"
  shows "original_code_caps_invoked_in_trace t \<subseteq> original_code_caps (run_state s t)"
  using original_reg_code_caps_invoked_in_trace_in_code_reg_caps[OF assms, THEN subsetD]
    original_code_caps_indirectly_invoked_in_trace_in_original_mem_code_caps[OF assms, THEN subsetD]
    original_direct_mem_sentries_invoked_in_trace_in_original_mem_code_caps[OF assms, THEN subsetD]
  by (auto simp: original_code_caps_invoked_in_trace_def original_code_caps_def)

lemma mem_cap_loads_of_ev_eq:
  "mem_cap_loads_of_ev e =
     {(paddr, c). \<exists>rk bytes tag. e = E_read_memt rk paddr 16 (bytes, tag) \<and>
                                 cap_of_mem_bytes bytes tag = Some c \<and> CapIsTagSet c}"
  by (cases e) (auto simp: no_cap_load_translation_events split: option.splits)

lemma mem_cap_loads_of_trace_eq:
  "mem_cap_loads_of_trace t =
     {(paddr, c). \<exists>rk bytes tag. E_read_memt rk paddr 16 (bytes, tag) \<in> set t \<and>
                                 cap_of_mem_bytes bytes tag = Some c \<and> CapIsTagSet c}"
  by (induction t; fastforce simp add: mem_cap_loads_of_trace_def mem_cap_loads_of_ev_eq)

lemma no_mem_writes_in_trace_take:
  "no_mem_writes_in_trace t \<Longrightarrow> no_mem_writes_in_trace (take i t)"
  by (auto simp add: no_mem_writes_in_trace_def dest: in_set_takeD)

lemma cap_of_mem_bytes_Some_tagged_iff:
  assumes "CapIsTagSet c"
  shows "cap_of_mem_bytes bytes tag = Some c \<longleftrightarrow>
         (\<exists>data :: 128 word. vec_of_bits_maybe (bits_of_mem_bytes bytes) = Some data \<and> tag = B1 \<and>
                             c = word_cat (1 :: 1 word) data)"
  using assms
  by (cases tag) (auto simp: cap_of_mem_bytes_def nth_ucast_len split: bind_splits)

lemma no_mem_writes_in_trace_mem_cap_loads_of_trace_eq:
  assumes "no_mem_writes_in_trace t"
  shows "mem_cap_loads_of_trace t = {(paddr, c). (paddr, c) \<in> initial_mem_cap_loads_of_trace t \<and> CapIsTagSet c}"
  using assms
  by (auto simp: mem_cap_loads_of_trace_eq initial_mem_cap_loads_of_trace_def in_set_conv_nth
                 no_mem_writes_in_trace_take mem_cap_of_event_Some_tagged_iff cap_of_mem_bytes_Some_tagged_iff;
      fastforce)

lemma mem_caps_initial_mem_cap_loads_of_trace:
  assumes "no_mem_writes_in_trace t"
  shows "mem_caps (run_state s t) = initial_mem_cap_loads_of_trace t \<union> mem_caps s"
  using assms
  unfolding mem_caps_run_state initial_mem_cap_loads_of_trace_def
  by (auto simp: no_mem_writes_in_trace_take in_set_conv_nth; fastforce)

lemma valid_address_no_overflow:
  fixes addr offset :: "64 word"
  assumes "valid_address acctype (unat addr)"
    and "unat offset < 2 ^ 52"
    and "bounds_address acctype (unat addr) + unat offset < 2 ^ 64"
  shows "unat (addr + offset) = unat addr + unat offset"
  using bounds_address_orig_address_no_overflow[OF assms]
  by (intro unat_add_lem[THEN iffD1]) auto

definition "no_mem_writes_in_exp m \<equiv> (\<forall>t m'. (m, t, m') \<in> Traces \<longrightarrow> no_mem_writes_in_trace t)"

abbreviation
  "write_mem_events \<equiv>
     range (\<lambda>(wk, addr, val, sz, k). E_write_mem wk addr sz val k) \<union>
     range (\<lambda>(wk, addr, val, tag, sz, k). E_write_memt wk addr sz val tag k)"

lemma monad_trace_subset_no_mem_writes_in_exp:
  assumes "monad_trace_subset S m"
    and "disjnt write_mem_events S"
  shows "no_mem_writes_in_exp m"
  using assms
  by (fastforce simp: monad_trace_subset_def no_mem_writes_in_exp_def no_mem_writes_in_trace_def subset_eq disjnt_iff)

lemma no_mem_writes_in_exp_bind:
  "no_mem_writes_in_exp m \<Longrightarrow> (\<And>a. no_mem_writes_in_exp (f a)) \<Longrightarrow> no_mem_writes_in_exp (bind m f)"
  by (fastforce simp: no_mem_writes_in_exp_def no_mem_writes_in_trace_def elim!: bind_Traces_cases)

lemma no_mem_writes_in_write_reg: "no_mem_writes_in_exp (write_reg r v)"
  by (auto simp: no_mem_writes_in_exp_def no_mem_writes_in_trace_def write_reg_def elim: Write_reg_TracesE)

lemma no_mem_writes_in_Step_PC: "no_mem_writes_in_exp (Step_PC u)"
  by (rule monad_trace_subset_no_mem_writes_in_exp, rule monad_trace_subset)
     (unfold disjnt_Un1 disjnt_Un2, intro conjI disjnt_empty2 disjnt_range_event)

lemma no_mem_writes_in_exp_DecodeA64_instr:
  assumes "instr_of_exp (DecodeA64 pc opcode) = Some instr"
    and "instr_may_invoke"
  shows "no_mem_writes_in_exp (DecodeA64 pc opcode)"
proof -
  have ifE: "no_mem_writes_in_exp (if b then m1 else m2)"
    if "instr_of_exp (if b then m1 else m2) = Some instr"
    and "instr_of_exp m1 = Some instr \<Longrightarrow> no_mem_writes_in_exp m1"
    and "instr_of_exp m2 = Some instr \<Longrightarrow> no_mem_writes_in_exp m2"
    for b and m1 m2 :: "unit M"
    by (use that in auto)
  have no_instr: "no_mem_writes_in_exp m"
    if instr: "instr_of_exp m = Some instr"
    and writes: "no_reg_writes_to {''__ThisInstrAbstract''} m"
    for m :: "unit M"
    using instr writes[THEN no_reg_writes_to_instr_of_exp]
    by auto
  from assms show ?thesis
    by -
       (unfold DecodeA64_def invocation_decode_defs Let_def, elim ifE,
        (erule no_instr, solves \<open>no_reg_writes_toI\<close>
         | solves \<open>rule no_mem_writes_in_write_reg[THEN no_mem_writes_in_exp_bind],
                   rule monad_trace_subset_no_mem_writes_in_exp,
                   rule monad_trace_subset,
                   unfold disjnt_Un1 disjnt_Un2,
                   intro conjI disjnt_empty2 disjnt_range_event\<close>
         | use \<open>instr_may_invoke\<close> in \<open>solves \<open>auto\<close>\<close>)+)
qed

lemma no_mem_writes_in_exp_instr_sem:
  assumes "instr_of_exp (instr_sem opcode) = Some instr"
    and "instr_may_invoke"
  shows "no_mem_writes_in_exp (instr_sem opcode)"
  using assms
  unfolding instr_sem_def
  by (intro no_mem_writes_in_exp_bind no_mem_writes_in_exp_DecodeA64_instr no_mem_writes_in_Step_PC)
     (auto simp: instr_of_exp_def instrs_of_exp_bind_no_writes split: if_splits)

lemma no_mem_writes_in_trace_of_exp:
  "no_mem_writes_in_exp m \<Longrightarrow> hasTrace t m \<Longrightarrow> no_mem_writes_in_trace t"
  by (auto simp: no_mem_writes_in_exp_def hasTrace_iff_Traces_final)

lemma branch_instr_run_has_expected_invocation_loadsI:
  assumes "instr_may_invoke \<longrightarrow> has_expected_loads (run_state s t)"
    and "instr_of_trace t = Some instr"
    and "instr_may_invoke \<longrightarrow> no_mem_writes_in_trace t"
    and "load_auth_caps s = {}" and "mem_caps s = {}"
  shows "branch_instr_run_has_expected_invocation_loads t"
proof (cases "instr_indirect_sentry_type instr" rule: indirect_sentry_type_cases)
  case No_Indirect_Sentry
  then show ?thesis
    using assms
    by (simp add: branch_instr_run_has_expected_invocation_loads_def trace_indirect_sentry_type_def)
next
  case Points_to_PCC
  then obtain n where "instr_load_auth instr = Some (RegAuth n)"
    and "instr_invokes_indirect_cap_from_reg instr \<in> {Some n, None}"
    by (cases instr) auto
  then show ?thesis
    using assms Points_to_PCC
    unfolding has_expected_loads_def branch_instr_run_has_expected_invocation_loads_def
    by (fastforce simp: trace_indirect_sentry_type_def load_auth_caps_run_eq_load_auth_caps_of_trace
                        trace_has_reg_load_auth_for_addr_def load_auth_caps_of_trace_trace_reads_caps_from_gpr
                        trace_load_auths_def cap_authorises_load_def trace_invokes_indirect_cap_from_reg_def
                        no_mem_writes_in_trace_mem_cap_loads_of_trace_eq
                        mem_caps_initial_mem_cap_loads_of_trace trace_invokes_indirect_sentries_def)
next
  case Points_to_Pair
  then obtain n where "instr_load_auth instr = Some (RegAuth n)"
    and "instr_invokes_indirect_cap_from_reg instr \<in> {Some n, None}"
    by (cases instr) auto
  then show ?thesis
    using assms Points_to_Pair
    unfolding has_expected_loads_def branch_instr_run_has_expected_invocation_loads_def
    by (fastforce simp: trace_indirect_sentry_type_def load_auth_caps_run_eq_load_auth_caps_of_trace
                        trace_has_reg_load_auth_for_addr_def load_auth_caps_of_trace_trace_reads_caps_from_gpr
                        trace_load_auths_def cap_authorises_load_def trace_invokes_indirect_cap_from_reg_def
                        no_mem_writes_in_trace_mem_cap_loads_of_trace_eq bounds_address_offset
                        mem_caps_initial_mem_cap_loads_of_trace trace_invokes_indirect_sentries_def
                        valid_address_no_overflow[where offset = 16 and acctype = AccType_NORMAL])
qed

(* TODO: Move *)
lemma expected_original_code_caps_cases:
  fixes s0 t
  defines "s \<equiv> run_state s0 t"
  assumes "has_expected_gpr_reads s"
    and "has_expected_loads s"
    and "instr_may_invoke"
    and "load_auth_caps s0 = {}"
    and "has_null_caps s0"
  obtains (Reg) cc where "code_reg_caps s = {cc}" and "original_mem_code_caps s = {}"
  | (Mem) cc where "code_reg_caps s = {}" and "original_mem_code_caps s = {cc}"
proof -
  from assms consider
    (CodeReg) n where "instr_invokes_code_cap_from_reg instr = Some n"
      and "instr_load_auth instr = None" and "instr_indirect_sentry_type instr = None"
  | (LoadAuth) n sentry_type where "instr_invokes_code_cap_from_reg instr = None"
      and "instr_load_auth instr = Some (RegAuth n)" and "instr_indirect_sentry_type instr = Some sentry_type"
    by (cases instr) auto
  then show ?thesis
  proof cases
    case CodeReg
    then show ?thesis
      using assms Reg no_load_auth_no_expected_mem_caps[OF assms(3)[unfolded s_def]]
      by (auto simp: has_expected_gpr_reads_def has_expected_loads_def original_mem_code_caps_def is_singleton_def)
  next
    case LoadAuth
    then obtain auth where auth: "load_auth_caps s = {auth}"
      using \<open>has_expected_gpr_reads s\<close>
      by (auto simp: has_expected_gpr_reads_def is_singleton_def)
    then show ?thesis
    proof (cases sentry_type)
      case Points_to_PCC
      then show ?thesis
        using assms LoadAuth Mem no_code_reg_caps_run_state[of s0 t]
        by (auto simp: has_expected_loads_def original_mem_code_caps_def has_null_caps_def)
    next
      case Points_to_Pair
      then obtain paddr_cd cd paddr_cc cc
        where "mem_caps s = {(paddr_cd, cd), (paddr_cc, cc)}"
        and "translate_address (unat (CapGetValue auth)) = Some paddr_cd"
        and "translate_address (unat (CapGetValue auth + 16)) = Some paddr_cc"
        (* and "unat (CapGetValue auth + 16) = unat (CapGetValue auth) + 16" *)
        using \<open>has_expected_loads s\<close> auth LoadAuth
        using valid_address_no_overflow[of AccType_NORMAL "CapGetValue auth" 16]
        by (auto simp: has_expected_loads_def cap_authorises_load_def)
      then show ?thesis
        using LoadAuth Points_to_Pair auth \<open>has_null_caps s0\<close> (*\<open>code_reg_caps s0 = {}\<close>*)
        using translate_address_unat_vaddr_offset_paddr_different[of "CapGetValue auth" paddr_cd 16]
        by (intro Mem[of cc]) (auto simp: original_mem_code_caps_def no_code_reg_caps_run_state s_def has_null_caps_def)
    qed
  qed
qed

lemma branch_instr_run_has_expected_pstate_writesI:
  assumes "instr_may_invoke \<longrightarrow> has_expected_pstate_writes (run_state s t)"
    and "instr_of_trace t = Some instr"
    and "instr_may_invoke \<longrightarrow> has_expected_gpr_reads (run_state s t)"
    and "instr_may_invoke \<longrightarrow> has_expected_loads (run_state s t)"
    and "load_auth_caps s = {}" and "has_null_caps s" and "pstate_writes s = []"
  shows "branch_instr_run_has_expected_pstate_writes opcode t"
proof (cases instr_may_invoke)
  case True
  then have gpr: "has_expected_gpr_reads (run_state s t)"
    and loads: "has_expected_loads (run_state s t)"
    using assms(3,4)
    by auto
  then show ?thesis
  proof (unfold branch_instr_run_has_expected_pstate_writes_def, intro ballI impI)
    fix cc'
    assume "cc' \<in> instr_invokes_code_caps opcode t" and tagged: "CapIsTagSet cc'"
    then obtain cc where cc: "cc \<in> original_code_caps_invoked_in_trace t"
      and "cc' \<in> branch_caps (clear_lsb (CapUnseal cc)) \<union> mem_branch_caps (clear_lsb cc)"
      by (cases rule: instr_of_trace_invocation_cases[OF assms(2), where opcode = opcode];
          auto simp: image_UN clear_lsb_image_branch_caps_eq clear_lsb_image_mem_branch_caps_eq reads_mem_cap_Some_iff;
          fastforce)
    then have "cc \<in> original_code_caps (run_state s t)" and "CapIsTagSet cc"
      using original_code_caps_invoked_in_trace_in_original_code_caps[OF assms(2), where s = s] tagged
      by (auto simp: branch_caps_128th_iff mem_branch_caps_128th_iff test_bit_set_gen)
    then obtain pstate where
      "set (pstate_writes (run_state s t)) = {Regval_ProcState pstate}"
      "test_bit (ProcState_C64 pstate) 0 = lsb cc"
      using assms(1) True
      by (cases rule: expected_original_code_caps_cases[OF gpr loads True assms(5,6)])
         (auto simp add: has_expected_pstate_writes_def original_code_caps_def)
    then show "\<exists>cc\<in>original_code_caps_invoked_in_trace t. pstate_c64_writes t = {lsb cc}"
      using cc assms(7)
      by (intro bexI[where x = cc])
         (auto simp add: pstate_c64_writes_def set_pstate_writes_run_state set_eq_iff)
  qed
next
  case False
  then have "instr_invokes_code_caps opcode t = {}"
    using assms(2)
    by (auto simp: instr_invokes_code_caps_def trace_invokes_reg_code_caps_def
                   original_reg_code_caps_invoked_in_trace_def original_cap_pairs_invoked_in_trace_def
                   trace_invokes_code_cap_from_reg_def original_direct_reg_sentries_invoked_in_trace_def
                   trace_indirectly_invokes_code_caps_def original_code_caps_indirectly_invoked_in_trace_def
                   trace_indirect_sentry_type_def trace_invokes_indirect_sentries_def
                   trace_invokes_direct_mem_sentries_def original_direct_mem_sentries_invoked_in_trace_def)
  then show ?thesis
    by (auto simp: branch_instr_run_has_expected_pstate_writes_def)
qed

lemma branch_instr_trace_has_expected_exceptionsI:
  assumes "\<forall>e. (instr_sem opcode, t, Exception e) \<in> Traces \<longrightarrow> is_expected_exception e (run_state s t)"
    and "pcc_writes s = []"
  shows "branch_instr_trace_has_expected_exceptions opcode t"
proof (unfold branch_instr_trace_has_expected_exceptions_def, intro allI impI conjI)
  fix e
  assume t: "(instr_sem opcode, t, Exception e) \<in> Traces"
  with assms(1) have e: "is_expected_exception e (run_state s t)"
    by blast
  then obtain c where "pcc_cap_writes (run_state s t) = {c}"
    and "idc_cap_writes (run_state s t) = {}"
    by (auto simp: is_expected_exception_def)
  then show "is_singleton (trace_writes_pcc_caps ISA (instr_trace opcode t))"
    and "trace_writes_idc_caps ISA (instr_trace opcode t) = {}"
    using assms(2)
    by (auto simp: trace_writes_pcc_caps_def trace_writes_idc_caps_def fold_un_map_eq_Un
                   pcc_cap_writes_run_state idc_cap_writes_run_state)
  from e show "e = Error_ExceptionTaken ()"
    by (auto simp: is_expected_exception_def)
qed

lemma traces_no_state_updateI:
  assumes "\<And>t m' s. (m, t, m') \<in> Traces \<Longrightarrow> trace_assms s t
             \<Longrightarrow> no_mem_cap_reads_in_trace t \<and> (\<forall>n. no_accesses_to_gpr_in_trace n t)
               \<and> (\<forall>r \<in> invocation_regs. \<forall>v. E_write_reg r v \<notin> set t)"
  shows "no_state_update m"
proof (unfold no_state_update_def, intro allI impI, elim conjE)
  fix s t m'
  assume t: "(m, t, m') \<in> Traces" "trace_assms s t"
  then have "\<forall>r v. r \<in> all_R_names \<longrightarrow> E_read_reg r v \<notin> set t"
    using assms[of t m' s]
    by (auto simp: all_R_names_iff_R_name no_accesses_to_gpr_in_trace_def)
  moreover have "\<forall>r v. r \<in> invocation_regs \<longrightarrow> E_write_reg r v \<notin> set t"
    using assms[of t m' s] t
    by blast
  moreover have "E_read_memt rk addr sz val \<notin> set t" for rk addr sz val
    using assms[of t m' s] t
    unfolding no_mem_cap_reads_in_trace_def
    by (cases val) auto
  moreover have "E_read_mem rk addr 16 val \<notin> set t" for rk addr val
    using assms[of t m' s] t
    unfolding no_mem_cap_reads_in_trace_def
    by auto
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
      case (E_read_mem rk addr sz val)
      then show ?thesis
        using Cons Cons.prems(4)[of rk addr val]
        by auto
    next
      case (E_read_reg r v)
      then have r: "r \<notin> all_R_names"
        using Cons.prems
        by auto
      moreover have "\<not>is_code_reg r \<and> \<not>is_data_reg r \<and> \<not>is_indirect_reg r \<and> \<not>is_load_auth_reg r"
        using r
        by (auto simp: is_code_reg_def is_data_reg_def is_indirect_reg_def is_load_auth_reg_def
                 dest: R_name_in_all_R_names)
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

lemma no_state_updateI:
  assumes "no_gpr_accesses_or_mem_cap_reads m"
    and "no_reg_writes_to {''PCC'', ''PSTATE'', ''__BranchTaken''} m"
  shows "no_state_update m"
  using assms
  by (intro traces_no_state_updateI)
     (fastforce simp: no_gpr_accesses_or_mem_cap_reads_trace_iff no_accesses_to_gpr_in_trace_def
                      no_reg_writes_to_def all_R_names_iff_R_name invocation_regs_def)

method pre_post_ignore_fail_no_state_update_no_exception =
  (rule pre_post_ignore_fail_no_state_update_no_exception_ignore_result pre_post_ignore_fail_no_state_update_no_exception,
   rule no_state_updateI,
   no_reads_from_any_gpr,
   no_reg_writes_toI,
   rule monad_no_exception)

definition "add_pcc_write c s \<equiv> s\<lparr>pcc_writes := Regval_bitvector_129_dec c # pcc_writes s, invocation_regs_written := True\<rparr>"
definition "add_idc_write c s \<equiv> s\<lparr>idc_writes := Regval_bitvector_129_dec c # idc_writes s, invocation_regs_written := True\<rparr>"
definition "add_pstate_write ps s \<equiv> s\<lparr>pstate_writes := Regval_ProcState ps # pstate_writes s, invocation_regs_written := True\<rparr>"
definition "add_branch_taken_write b s \<equiv> s\<lparr>branch_taken_writes := Regval_bool b # branch_taken_writes s, invocation_regs_written := True\<rparr>"

lemma pre_post_write_reg_BranchTaken:
  "pre_post (\<lambda>s. Q () (add_branch_taken_write b s)) (write_reg BranchTaken_ref b) Q E F"
  by (rule pre_post_strengthen_pre, rule pre_post_write_reg)
     (simp add: add_branch_taken_write_def register_defs invocation_regs_def all_R_names_def)

lemma pre_post_write_reg_PCC:
  "pre_post (\<lambda>s. Q () (add_pcc_write c s)) (write_reg PCC_ref c) Q E F"
  by (rule pre_post_strengthen_pre, rule pre_post_write_reg)
     (simp add: add_pcc_write_def register_defs all_R_names_def invocation_regs_def)

lemma pre_post_write_reg_PSTATE:
  "pre_post (\<lambda>s. Q () (add_pstate_write ps s)) (write_reg PSTATE_ref ps) Q E F"
  by (rule pre_post_strengthen_pre, rule pre_post_write_reg)
     (simp add: add_pstate_write_def register_defs all_R_names_def invocation_regs_def)

lemma pre_post_read_reg_PSTATE:
  "pre_post_ignore_fail
     (\<lambda>s. \<forall>pstate. (\<forall>acctype. acctype \<noteq> AccType_UNPRIV \<longrightarrow> translation_el acctype = ProcState_EL pstate) \<longrightarrow> Q pstate s)
     (read_reg PSTATE_ref :: ProcState M) Q E"
  apply (rule pre_post_strengthen_pre)
   apply (rule pre_post_ignore_fail_no_state_update_no_exception)
    apply (rule no_state_updateI, no_reads_from_any_gpr, no_reg_writes_toI, rule monad_no_exception)
  apply (use read_reg_PSTATE_translation_el in \<open>auto dest!: trace_assms_translation_assms_trace\<close>)
  done

lemma step_state_read_other_reg:
  "r \<notin> all_R_names \<Longrightarrow> step_state s (E_read_reg r v) = s"
  by (cases v) (auto simp: is_code_reg_def is_data_reg_def is_load_auth_reg_def dest: R_name_in_all_R_names)

lemma pre_post_read_other_reg:
  "name r \<notin> all_R_names \<Longrightarrow> pre_post_ignore_fail (\<lambda>s. \<forall>a. Q a s) (read_reg r :: 'a M) Q E"
  by (rule pre_post_strengthen_pre, rule pre_post_read_reg)
     (auto simp: step_state_read_other_reg split: option.splits)

lemma pre_post_read_other_reg_ignore_result:
  "name r \<notin> all_R_names \<Longrightarrow> pre_post_ignore_fail Q (read_reg r :: 'a M) (\<lambda>_. Q) E"
  by (rule pre_post_strengthen_pre, rule pre_post_read_reg)
     (auto simp: step_state_read_other_reg split: option.splits)

lemma pre_post_BranchAddr:
  "pre_post_ignore_fail
     (\<lambda>s. translation_el AccType_IFETCH = el \<and>
     (\<forall>c'. (CapIsTagSet c' \<longrightarrow> CapIsTagSet c \<and> \<not>CapIsSealed c \<and> c' \<in> branch_caps c) \<longrightarrow> Q c' s))
     (BranchAddr c el) Q E"
  apply (rule pre_post_strengthen_pre, rule pre_post_ignore_fail_no_state_update_no_exception)
    apply (rule no_state_updateI)
     apply (no_reads_from_any_gpr)
    apply (no_reg_writes_toI)
   apply (rule monad_no_exception)
  apply (use BranchAddr_in_branch_caps BranchAddr_not_sealed[of c el] in \<open>auto dest: trace_assms_translation_assms_trace\<close>)
  done

lemma pre_post_BranchToCapability:
  "pre_post_ignore_fail
     (\<lambda>s. (\<forall>c'. (CapIsTagSet c' \<longrightarrow> CapIsTagSet c \<and> \<not>CapIsSealed c \<and> c' \<in> branch_caps c) \<longrightarrow>
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
  apply (simp add: all_R_names_def register_defs invocation_regs_def)
  done

lemma pre_post_BranchXToCapability:
  "pre_post_ignore_fail
     (\<lambda>s. (\<forall>c' pstate.
              (CapIsTagSet c' \<longrightarrow> CapIsTagSet c \<and> \<not>CapIsSealed c \<and> c' \<in> branch_caps (clear_lsb c)) \<and>
              ProcState_C64 pstate = of_bl [lsb c] \<longrightarrow>
              Q () (add_branch_taken_write True (add_pcc_write c' (add_pstate_write pstate s)))))
     (BranchXToCapability c branch_type) Q E"
  unfolding BranchXToCapability_def Let_def bind_assoc
  apply (rule pre_post_strengthen_pre)
   apply (rule pre_post_bind)+
     apply (rule pre_post_BranchToCapability)
    apply (rule pre_post_write_reg_PSTATE)
   apply (rule pre_post_read_reg)
  apply (auto simp: register_defs word_lsb_alt test_bit_set_gen split: option.split)
  done

(* TODO: Move *)
lemma and_boolM_True[simp]:
  "and_boolM (return True) m = m"
  by (auto simp: and_boolM_def)

lemma pre_post_BranchTo:
  "pre_post_ignore_fail
     (\<lambda>s. (\<forall>c'. Q () (add_branch_taken_write True (add_pcc_write c' s))))
     (BranchTo (target :: 64 word) branch_type) Q E"
  apply (simp add: BranchTo_def Let_def)
  apply (rule pre_post_strengthen_pre)
  apply (rule pre_post_bind)+
          apply (rule pre_post_write_reg_BranchTaken)
         apply (rule pre_post_write_reg_PCC)
        apply (rule pre_post_ignore_fail_no_state_update_no_exception, rule no_state_updateI, no_reads_from_any_gpr, no_reg_writes_toI, rule monad_no_exception)
       apply (rule pre_post_ignore_fail_no_state_update_no_exception, rule no_state_updateI, no_reads_from_any_gpr, no_reg_writes_toI, rule monad_no_exception)
      apply (rule pre_post_read_other_reg, simp add: register_defs all_R_names_def)
     apply (rule pre_post_write_reg)
     apply (rule pre_post_ignore_fail_no_state_update_no_exception, rule no_state_updateI, no_reads_from_any_gpr, no_reg_writes_toI, rule monad_no_exception)
    apply (rule pre_post_ignore_fail_assert_exp)
   apply (rule pre_post_ignore_fail_no_state_update_no_exception, rule no_state_updateI, no_reads_from_any_gpr, no_reg_writes_toI, rule monad_no_exception)
  apply (simp add: PC_ref_def all_R_names_def invocation_regs_def)
  done

definition
  "is_branch_target c s \<equiv>
     (\<exists>c' \<in> code_reg_caps s. lsb c' = lsb c \<and> (CapIsTagSet c \<and> \<not>CapIsSealed c \<longrightarrow> c \<in> {c', CapUnseal c'}))
     \<or> (\<exists>c' \<in> original_mem_code_caps s.
          lsb c' = lsb c \<and>
          (if is_sentry c' then CapIsTagSet c \<longrightarrow> c = CapUnseal c'
           else CapIsTagSet c \<longrightarrow> (c = c' \<or> (\<not>CapIsSealed c' \<and> c = clear_perm mutable_perms c'))))"

lemma CapUnseal_unsealed_eq:
  assumes "\<not>CapIsSealed c"
  shows "CapUnseal c = c"
proof (intro word_eqI impI)
  fix n
  have "\<not>test_bit c n" if "n \<in> {95..109}"
    using assms that
    unfolding CapIsSealed_def CapGetObjectType_def
    by (auto dest!: word_eqD[where x = "n - 95"] simp: word_ao_nth nth_slice)
  then show "CapUnseal c !! n = c !! n"
    unfolding CapUnseal_def CapSetObjectType_def
    by (auto simp: update_subrange_vec_dec_test_bit word_eq_iff word_ao_nth nth_slice)
qed

lemma is_branch_target_invoked_code_caps:
  assumes "is_branch_target c s"
    and "CapIsTagSet c" and "\<not>CapIsSealed c"
  shows "branch_caps (clear_lsb c) \<subseteq> invoked_code_caps s"
proof -
  from assms consider (Reg) c' where "c \<in> {c', CapUnseal c'}" and "c' \<in> code_reg_caps s"
    | (Mem) c' where "is_sentry c' \<and> c = CapUnseal c' \<or> \<not>CapIsSealed c' \<and> c \<in> {c', clear_perm mutable_perms c'}"
        and "c' \<in> original_mem_code_caps s"
    by (auto simp: is_branch_target_def split: if_splits)
  then show ?thesis
  proof cases
    case Reg
    then show ?thesis
      using CapUnseal_unsealed_eq[OF assms(3)]
      by (auto simp: invoked_code_caps_def)
  next
    case Mem
    then have "branch_caps (clear_lsb c) \<subseteq> mem_branch_caps (clear_lsb c')"
      unfolding mem_branch_caps_def is_sentry_def
      by (auto simp: CapIsSealed_def CapUnseal_clear_lsb_commute CapClearPerms_clear_lsb_commute)
    also have "\<dots> \<subseteq> invoked_code_caps s"
      using Mem
      by (auto simp: invoked_code_caps_def)
    finally show ?thesis .
  qed
qed

abbreviation
  "has_no_expected_data_cap_invocation s \<equiv>
     mem_caps s = {} \<and> data_reg_caps s = {} \<and>
     (instr_indirect_sentry_type instr = Some Points_to_PCC \<longrightarrow> instr_invokes_indirect_cap_from_reg instr = None)"

definition performs_expected_idc_write where
  "performs_expected_idc_write pcc_tagged s \<equiv>
     (invoked_data_caps s \<noteq> {} \<longrightarrow>
        (\<exists>cd. idc_writes s = [Regval_bitvector_129_dec cd] \<and> (pcc_tagged \<longrightarrow> cd \<in> invoked_data_caps s)))"

abbreviation "invocation_post_load s \<equiv> has_expected_loads s \<and> has_expected_gpr_reads s"
abbreviation "invocation_post_idc pcc_tagged s \<equiv> performs_expected_idc_write pcc_tagged s \<and> has_load_cap_perm_if_needed pcc_tagged s \<and> invocation_post_load s"
abbreviation "invocation_post_final s \<equiv> has_expected_data_invocation s \<and> has_expected_pstate_writes s \<and> invocation_post_load s" (* \<and> invocation_post_idc s"*)
abbreviation "invocation_pre_final c s \<equiv> is_branch_target c s \<and> pcc_writes s = [] \<and> pstate_writes s = [] \<and> branch_taken_writes s = []"

lemma has_no_expected_data_cap_invocation_no_invoked_data_caps:
  "has_no_expected_data_cap_invocation s \<Longrightarrow> invoked_data_caps s = {}"
  unfolding invoked_data_caps_def original_reg_data_caps_def original_mem_data_caps_def
  by (auto split: option.splits indirect_sentry_type.splits)

lemma pre_post_has_no_expected_data_cap_invocation:
  assumes "pre_post P m (\<lambda>a s. Q a s \<and> has_no_expected_data_cap_invocation s) E F"
  shows "pre_post P m (\<lambda>a s. performs_expected_idc_write pcc_tagged s \<and> Q a s) E F"
  using assms
  by (elim pre_post_consequence)
     (auto simp: performs_expected_idc_write_def has_no_expected_data_cap_invocation_no_invoked_data_caps)

lemma performs_expected_idc_write_pcc_tagged_antimono:
  "performs_expected_idc_write pcc_tagged s \<Longrightarrow> pcc_tagged' \<longrightarrow> pcc_tagged \<Longrightarrow> performs_expected_idc_write pcc_tagged' s"
  by (auto simp: performs_expected_idc_write_def)

abbreviation
  "has_no_expected_loads s \<equiv> instr_indirect_sentry_type instr = None \<and> (load_auth_caps s = {} \<longrightarrow> mem_caps s = {})"

lemma pre_post_has_no_expected_loads:
  assumes "pre_post P m (\<lambda>a s. Q a s \<and> has_no_expected_loads s) E F"
  shows "pre_post P m (\<lambda>a s. has_expected_loads s \<and> Q a s) E F"
  using assms
  by (elim pre_post_consequence) (auto simp: has_expected_loads_def)

lemma original_mem_code_caps_cong:
  assumes "mem_caps s' = mem_caps s" and "load_auth_caps s' = load_auth_caps s"
  shows "original_mem_code_caps s' = original_mem_code_caps s"
  using assms
  by (auto simp: original_mem_code_caps_def)

lemma original_code_caps_cong:
  assumes "mem_caps s' = mem_caps s" and "load_auth_caps s' = load_auth_caps s"
    and "code_reg_caps s' = code_reg_caps s"
  shows "original_code_caps s' = original_code_caps s"
  using assms
  by (auto simp: original_code_caps_def cong: original_mem_code_caps_cong)

lemma invoked_code_caps_cong:
  assumes "mem_caps s' = mem_caps s" and "load_auth_caps s' = load_auth_caps s"
    and "code_reg_caps s' = code_reg_caps s"
  shows "invoked_code_caps s' = invoked_code_caps s"
  using assms
  by (auto simp: invoked_code_caps_def cong: original_mem_code_caps_cong)

lemma original_reg_data_caps_cong:
  assumes "data_reg_caps s' = data_reg_caps s" and "load_auth_caps s' = load_auth_caps s"
    and "code_reg_caps s' = code_reg_caps s"
  shows "original_reg_data_caps s' = original_reg_data_caps s"
  using assms
  by (auto simp: original_reg_data_caps_def split: option.splits indirect_sentry_type.splits)

lemma original_mem_data_caps_cong:
  assumes "mem_caps s' = mem_caps s" and "load_auth_caps s' = load_auth_caps s"
  shows "original_mem_data_caps s' = original_mem_data_caps s"
  using assms
  by (auto simp: original_mem_data_caps_def)

lemma invoked_data_caps_cong:
  assumes "data_reg_caps s' = data_reg_caps s" and "code_reg_caps s' = code_reg_caps s"
    and "mem_caps s' = mem_caps s" and "load_auth_caps s' = load_auth_caps s"
  shows "invoked_data_caps s' = invoked_data_caps s"
  using assms
  by (auto simp: invoked_data_caps_def cong: original_reg_data_caps_cong original_mem_data_caps_cong)

(*lemma has_expected_data_cap_invocation_cong:
  assumes "data_reg_caps s' = data_reg_caps s" and "code_reg_caps s' = code_reg_caps s"
    and "idc_writes s = idc_writes s'" and "mem_caps s' = mem_caps s"
    and "load_auth_caps s' = load_auth_caps s"
  shows "has_expected_data_cap_invocation s = has_expected_data_cap_invocation s'"
  using assms
  by (auto simp: has_expected_data_cap_invocation_def cong: invoked_data_caps_cong)

lemma has_expected_data_cap_invocation_add_simps[simp]:
  "has_expected_data_cap_invocation (add_branch_taken_write b s) = has_expected_data_cap_invocation s"
  "has_expected_data_cap_invocation (add_pcc_write c s) = has_expected_data_cap_invocation s"
  "has_expected_data_cap_invocation (add_pstate_write pstate s) = has_expected_data_cap_invocation s"
  by (auto simp: add_branch_taken_write_def add_pcc_write_def add_pstate_write_def
           cong: invoked_data_caps_cong has_expected_data_cap_invocation_cong)*)

lemma has_expected_loads_cong:
  assumes "mem_caps s = mem_caps s'" and "load_auth_caps s = load_auth_caps s'"
  shows "has_expected_loads s = has_expected_loads s'"
  using assms
  by (auto simp: has_expected_loads_def split: option.split indirect_sentry_type.split)

lemma has_expected_load_add_simps[simp]:
  "has_expected_loads (add_branch_taken_write b s) = has_expected_loads s"
  "has_expected_loads (add_pcc_write c s) = has_expected_loads s"
  "has_expected_loads (add_idc_write c s) = has_expected_loads s"
  "has_expected_loads (add_pstate_write pstate s) = has_expected_loads s"
  "has_expected_loads (s\<lparr>invocation_regs_written := b\<rparr>) \<longleftrightarrow> has_expected_loads s"
  by (auto simp: add_branch_taken_write_def add_pcc_write_def add_idc_write_def add_pstate_write_def
           cong: has_expected_loads_cong)

lemma has_expected_gpr_reads_add_simps[simp]:
  "has_expected_gpr_reads (add_branch_taken_write b s) = has_expected_gpr_reads s"
  "has_expected_gpr_reads (add_pcc_write c s) = has_expected_gpr_reads s"
  "has_expected_gpr_reads (add_idc_write c s) = has_expected_gpr_reads s"
  "has_expected_gpr_reads (add_pstate_write pstate s) = has_expected_gpr_reads s"
  "has_expected_gpr_reads (s\<lparr>invocation_regs_written := b\<rparr>) \<longleftrightarrow> has_expected_gpr_reads s"
  "has_expected_gpr_reads (s\<lparr>mem_caps := cs\<rparr>) \<longleftrightarrow> has_expected_gpr_reads s"
  by (auto simp: has_expected_gpr_reads_def add_branch_taken_write_def add_idc_write_def add_pcc_write_def add_pstate_write_def)

lemma has_expected_data_invocationI:
  assumes "pcc_writes s = []" and "branch_taken_writes s = []"
    (* and "CapIsTagSet c' \<longrightarrow> c' \<in> invoked_code_caps s" *)
    and "performs_expected_idc_write (CapIsTagSet c') s"
    and "has_load_cap_perm_if_needed (CapIsTagSet c') s"
    and "CapIsTagSet c' \<longrightarrow> (\<exists>c. is_branch_target c s \<and> CapIsTagSet c \<and> \<not>CapIsSealed c \<and> c' \<in> branch_caps (clear_lsb c))"
  shows "has_expected_data_invocation (add_branch_taken_write True (add_pcc_write c' (add_pstate_write pstate s)))"
  using assms
  unfolding has_expected_data_invocation_def performs_expected_idc_write_def
    add_branch_taken_write_def add_pcc_write_def add_pstate_write_def has_load_cap_perm_if_needed_def
  by (auto dest!: is_branch_target_invoked_code_caps cong: invoked_code_caps_cong invoked_data_caps_cong)

lemma has_expected_pstate_writesI:
  assumes "pstate_writes s = []"
    and "\<exists>c. is_branch_target c s \<and> ProcState_C64 pstate = of_bl [lsb c]"
  shows "has_expected_pstate_writes (add_pstate_write pstate s)"
  using assms
  by (auto simp: has_expected_pstate_writes_def add_pstate_write_def is_branch_target_def original_code_caps_def cong: original_code_caps_cong)

lemma has_expected_pstate_writes_add_simps[simp]:
  "has_expected_pstate_writes (add_branch_taken_write b s) = has_expected_pstate_writes s"
  "has_expected_pstate_writes (add_pcc_write c s) = has_expected_pstate_writes s"
  by (auto simp: has_expected_pstate_writes_def add_branch_taken_write_def add_pcc_write_def
           cong: original_code_caps_cong)

lemma BranchXToCapability_invocation_post_final:
  "pre_post_ignore_fail
     (\<lambda>s. invocation_post_idc (CapIsTagSet c) s \<and> invocation_pre_final c s)
     (BranchXToCapability c branch_type) (\<lambda>_ s. invocation_post_final s) E"
  by (rule pre_post_BranchXToCapability[THEN pre_post_strengthen_pre])
     (auto intro!: has_expected_data_invocationI has_expected_pstate_writesI
           simp: has_load_cap_perm_if_needed_def elim: performs_expected_idc_write_pcc_tagged_antimono)

lemma pre_post_R_read:
  "pre_post_ignore_fail
     (\<lambda>s. \<forall>r c e.
            n \<in> {0..30} \<and> R_name n = {r} \<and> e = E_read_reg r (Regval_bitvector_129_dec c) \<and>
            (\<not>invocation_regs_written s \<longrightarrow> reg_state s r = Some (Regval_bitvector_129_dec c) \<or> reg_state s r = None)
            \<longrightarrow> Q c (step_state s e))
     (R_read n) Q E"
  unfolding R_read_def Let_def
  apply (intro pre_post_if_common_pre)
  apply (rule pre_post_strengthen_pre, rule pre_post_read_reg, simp add: register_defs R_name_def ev_reads_invocation_regs_from_initial_reg_state_def invocation_regs_def all_R_names_def del: step_state.simps split: option.split)+
  apply (rule pre_post_bind, simp, rule pre_post_strengthen_pre, rule pre_post_ignore_fail_assert_exp, simp)
  done

lemma pre_post_C_read:
  "pre_post_ignore_fail
     (\<lambda>s. if n = 31 then Q 0 s else
            (\<forall>r c e.
               n \<in> {0..30} \<and> R_name n = {r} \<and> e = E_read_reg r (Regval_bitvector_129_dec c) \<and>
               (\<not>invocation_regs_written s \<longrightarrow> reg_state s r = Some (Regval_bitvector_129_dec c) \<or> reg_state s r = None)
               \<longrightarrow> Q c (step_state s e)))
     (C_read n) Q E"
  unfolding C_read_def Let_def
  apply (rule pre_post_strengthen_pre)
  apply (rule pre_post_bind, rule pre_post_if, rule pre_post_bind, rule pre_post_return)
    apply (rule pre_post_R_read)
   apply (rule pre_post_return)
   apply (rule pre_post_ignore_fail_assert_exp)
  apply (simp add: CapNull_def del: step_state.simps split: if_splits)
  done

lemma pre_post_R_set:
  "pre_post_ignore_fail
     (\<lambda>s. Q () ((if n = 29 then add_idc_write c s else s\<lparr>invocation_regs_written := True\<rparr>)))
     (R_set n c) Q E"
  unfolding R_set_def Let_def
  apply (intro pre_post_if_common_pre)
  apply (rule pre_post_strengthen_pre, rule pre_post_write_reg, simp add: register_defs all_R_names_def add_idc_write_def invocation_regs_def)+
  apply (rule pre_post_bind, simp, rule pre_post_strengthen_pre, rule pre_post_ignore_fail_assert_exp, simp)
  done

lemma pre_post_C_set:
  "pre_post_ignore_fail
     (\<lambda>s. Q () (if n = 31 then s else ((if n = 29 then add_idc_write c s else s\<lparr>invocation_regs_written := True\<rparr>))))
     (C_set n c) Q E"
  unfolding C_set_def
  apply (rule pre_post_strengthen_pre)
  apply (rule pre_post_bind pre_post_if pre_post_R_set pre_post_return pre_post_ignore_fail_assert_exp)+
  apply auto
  done

lemma pre_post_C_set_30:
  "pre_post_ignore_fail (\<lambda>s. Q () (s\<lparr>invocation_regs_written := True\<rparr>)) (C_set 30 c) Q E"
  by (rule pre_post_strengthen_pre, rule pre_post_C_set, simp)

lemma pre_post_C_set_other:
  "pre_post_ignore_fail (\<lambda>s. Q () (if n = 31 then s else (s\<lparr>invocation_regs_written := True\<rparr>)) \<and> n \<noteq> 29) (C_set n c) Q E"
  by (rule pre_post_strengthen_pre, rule pre_post_C_set, simp split: if_splits)

lemma pre_post_EndOfInstruction:
  "pre_post (E (Error_ExceptionTaken ())) (EndOfInstruction u) Q E F"
  unfolding EndOfInstruction_def
  by (rule pre_post_throw)

lemmas pre_post_prod_split = prod.split[where P = "\<lambda>m. pre_post P m Q E F" for P Q E F, THEN iffD2]

lemma pre_post_bind_UsingAArch32:
  assumes "pre_post_ignore_fail P (f False) Q E"
  shows "pre_post_ignore_fail P (bind (UsingAArch32 u) f) Q E"
proof -
  have *: "\<not>a" if "Run (UsingAArch32 ()) t a" for t a
    using that
    by (cases a) auto
  have "pre_post_ignore_fail P (UsingAArch32 ()) (\<lambda>_. P) E"
    by pre_post_ignore_fail_no_state_update_no_exception
  then show ?thesis
    using assms
    by (intro pre_post_bind[where R = "\<lambda>_. P"]) (auto dest: * )
qed

lemma pre_post_AArch64_TakeException:
  "pre_post_ignore_fail
     (\<lambda>s. pcc_writes s = [] \<and> idc_writes s = [])
     (AArch64_TakeException target_el exception preferred_exception_return vect_offset)
     Q is_expected_exception"
  (is "pre_post_ignore_fail ?P _ _ _")
proof -
  let ?R = "\<lambda>s. (\<exists>c. pcc_writes s = [Regval_bitvector_129_dec c]) \<and> idc_writes s = []"
  have 1: "pre_post ?R (EndOfInstruction ()) Q is_expected_exception F" for F
    by (rule pre_post_strengthen_pre, rule pre_post_EndOfInstruction)
       (auto simp: is_expected_exception_def)
  have 2: "pre_post_ignore_fail ?P (BranchToCapability c bt) (\<lambda>_. ?R) is_expected_exception" for c bt
    by (rule pre_post_strengthen_pre, rule pre_post_BranchToCapability)
       (auto simp: add_branch_taken_write_def add_pcc_write_def)
  have 3: "pre_post_ignore_fail ?P (BranchTo target bt) (\<lambda>_. ?R) is_expected_exception"
    for target :: "64 word" and bt
    by (rule pre_post_strengthen_pre, rule pre_post_BranchTo)
       (auto simp: add_branch_taken_write_def add_pcc_write_def)
  have 4: "pre_post_ignore_fail ?P (write_reg PSTATE_ref pstate) (\<lambda>_. ?P) is_expected_exception" for pstate
    by (rule pre_post_strengthen_pre, rule pre_post_write_reg) (auto simp: PSTATE_ref_def)
  have 5: "pre_post_ignore_fail ?P (read_reg PSTATE_ref) (\<lambda>_. ?P) is_expected_exception"
    by (rule pre_post_strengthen_pre, rule pre_post_read_reg_PSTATE) auto
  have 6: "pre_post_ignore_fail ?P (and_boolM m1 m2) (\<lambda>_. ?P) is_expected_exception"
    if "pre_post_ignore_fail ?P m1 (\<lambda>_. ?P) is_expected_exception"
    and "pre_post_ignore_fail ?P m2 (\<lambda>_. ?P) is_expected_exception"
    for m1 m2
    using that
    by (intro pre_post_and_boolM[where R = ?P]) auto
  have 7: "pre_post_ignore_fail ?P (or_boolM m1 m2) (\<lambda>_. ?P) is_expected_exception"
    if "pre_post_ignore_fail ?P m1 (\<lambda>_. ?P) is_expected_exception"
    and "pre_post_ignore_fail ?P m2 (\<lambda>_. ?P) is_expected_exception"
    for m1 m2
    using that
    by (intro pre_post_or_boolM[where R = ?P]) auto
  have 8: "pre_post_ignore_fail ?P (read_reg PCC_ref) (\<lambda>_. ?P) is_expected_exception"
    by (rule pre_post_strengthen_pre, rule pre_post_read_other_reg) (auto simp: PCC_ref_def all_R_names_def)
  have 9: "pre_post_ignore_fail ?P (assert_exp e msg) (\<lambda>_. ?P) is_expected_exception" for e msg
    by (rule pre_post_strengthen_pre, rule pre_post_ignore_fail_assert_exp) auto
  show ?thesis
    unfolding AArch64_TakeException_def Let_def
    by (rule pre_post_bind_UsingAArch32 pre_post_bind_ignore_trace pre_post_return pre_post_prod_split
             allI impI pre_post_if_False pre_post_if_common_pre 1 2 3 4 5 6 7 8 9
        | pre_post_ignore_fail_no_state_update_no_exception)+
qed

lemma pre_post_and_boolM_ignore:
  assumes "pre_post Q m2 (\<lambda>_. Q) E F"
    and "pre_post Q m1 (\<lambda>_. Q) E F"
  shows "pre_post Q (and_boolM m1 m2) (\<lambda>_. Q) E F"
  using assms
  by (auto intro: pre_post_and_boolM)

lemma pre_post_or_boolM_ignore:
  assumes "pre_post Q m2 (\<lambda>_. Q) E F"
    and "pre_post Q m1 (\<lambda>_. Q) E F"
  shows "pre_post Q (or_boolM m1 m2) (\<lambda>_. Q) E F"
  using assms
  by (auto intro: pre_post_or_boolM)

lemma pre_post_CapabilityAccessTrap:
  "pre_post_ignore_fail
     (\<lambda>s. pcc_writes s = [] \<and> idc_writes s = [])
     (CapabilityAccessTrap el) Q is_expected_exception"
  unfolding CapabilityAccessTrap_def Let_def
  by (rule pre_post_bind_ignore_trace pre_post_AArch64_TakeException
      | pre_post_ignore_fail_no_state_update_no_exception)+

lemma pre_post_UndefinedFault:
  "pre_post_ignore_fail
     (\<lambda>s. pcc_writes s = [] \<and> idc_writes s = [])
     (UndefinedFault u) Q is_expected_exception"
  unfolding UndefinedFault_def AArch64_UndefinedFault_def Let_def
  by (rule pre_post_bind_ignore_trace pre_post_if_common_pre pre_post_AArch64_TakeException pre_post_read_other_reg_ignore_result pre_post_and_boolM_ignore pre_post_return
      | pre_post_ignore_fail_no_state_update_no_exception
      | simp add: register_defs all_R_names_def)+

lemma pre_post_CheckCapabilitiesEnabled:
  "pre_post_ignore_fail
     (\<lambda>s. Q () s \<and> pcc_writes s = [] \<and> idc_writes s = [])
     (CheckCapabilitiesEnabled u) Q is_expected_exception"
  (is "pre_post_ignore_fail ?P _ _ _")
  unfolding CheckCapabilitiesEnabled_def Let_def bind_assoc
  by ((rule pre_post_bind_ignore_trace[where R = "\<lambda>_ s. ?P s"] pre_post_if_common_pre pre_post_or_boolM_ignore pre_post_and_boolM_ignore pre_post_return)
      | (rule pre_post_strengthen_pre, rule pre_post_CapabilityAccessTrap pre_post_exit pre_post_ignore_fail_assert_exp pre_post_return, solves \<open>simp\<close>)
      | (rule pre_post_strengthen_pre, rule pre_post_read_other_reg_ignore_result, solves \<open>simp add: register_defs all_R_names_def\<close>, solves \<open>simp\<close>)
      | pre_post_ignore_fail_no_state_update_no_exception)+

lemma and_boolM_trace_subset_Un:
  "monad_trace_subset S m \<Longrightarrow> monad_trace_subset S' m' \<Longrightarrow> monad_trace_subset (S \<union> S') (and_boolM m m')"
  by (rule and_boolM_trace_subset) (auto elim: monad_trace_subset_weaken)

lemma CapWithTagClear_lsb_iff[simp]:
  "lsb (CapWithTagClear c) \<longleftrightarrow> lsb c"
  by (auto simp: CapWithTagClear_def update_subrange_vec_dec_test_bit word_lsb_alt test_bit_set_gen)

abbreviation "invocation_pre_final_reg c s \<equiv> code_reg_caps s = {c} \<and> pcc_writes s = [] \<and> pstate_writes s = [] \<and> branch_taken_writes s = []"

lemma BranchXToCapability_if_unseal_untag_invocation_post_final_reg:
  fixes c clear
  defines "c' \<equiv> (if clear then CapWithTagClear c else c)"
  defines "unseal \<equiv> CapIsTagSet c' \<and> CapIsSealed c' \<and> CapGetObjectType c' = CAP_SEAL_TYPE_RB"
  defines "c'' \<equiv> (if unseal then CapUnseal c' else c')"
  shows "pre_post_ignore_fail
     (\<lambda>s. invocation_post_idc (CapIsTagSet c \<and> \<not>clear) s \<and> invocation_pre_final_reg c s)
     (BranchXToCapability c'' branch_type) (\<lambda>_ s. invocation_post_final s) E"
  by (rule pre_post_strengthen_pre, rule BranchXToCapability_invocation_post_final)
     (auto simp: c''_def unseal_def c'_def is_branch_target_def)

lemma BranchXToCapability_if_untag_invocation_post_final_reg:
  fixes c clear
  defines "c' \<equiv> (if clear then CapWithTagClear c else c)"
  shows "pre_post_ignore_fail
     (\<lambda>s. invocation_post_idc (CapIsTagSet c \<and> \<not>clear) s \<and> invocation_pre_final_reg c s)
     (BranchXToCapability c' branch_type) (\<lambda>_ s. invocation_post_final s) E"
  by (rule pre_post_strengthen_pre, rule BranchXToCapability_invocation_post_final)
     (auto simp: c'_def is_branch_target_def)

lemma BranchXToCapability_unseal_if_untag_invocation_post_final_reg:
  fixes c clear
  defines "c' \<equiv> (if clear then CapWithTagClear c else c)"
  shows "pre_post_ignore_fail
     (\<lambda>s. invocation_post_idc (CapIsTagSet c \<and> \<not>clear) s \<and> invocation_pre_final_reg c s)
     (BranchXToCapability (CapUnseal c') branch_type) (\<lambda>_ s. invocation_post_final s) E"
  by (rule pre_post_strengthen_pre, rule BranchXToCapability_invocation_post_final)
     (auto simp: c'_def is_branch_target_def)

lemma BranchXToCapability_untag_invocation_post_final_reg:
  shows "pre_post_ignore_fail
     (\<lambda>s. invocation_post_idc False s \<and> invocation_pre_final_reg c s)
     (BranchXToCapability (CapWithTagClear c) branch_type) (\<lambda>_ s. invocation_post_final s) E"
  by (rule pre_post_strengthen_pre, rule BranchXToCapability_invocation_post_final)
     (auto simp: is_branch_target_def)

lemma BranchXToCapability_unseal_invocation_post_final_reg:
  "pre_post_ignore_fail
     (\<lambda>s. invocation_post_idc (CapIsTagSet c) s \<and> invocation_pre_final_reg c s)
     (BranchXToCapability (CapUnseal c) branch_type) (\<lambda>_ s. invocation_post_final s) E"
  by (rule pre_post_strengthen_pre, rule BranchXToCapability_invocation_post_final)
     (auto simp: is_branch_target_def)

lemma pre_post_return_CapUnseal_is_branch_target_from_reg:
  "pre_post
     (\<lambda>s. has_expected_gpr_reads (f s) \<and> code_reg_caps (f s) = {c} \<and> Q s)
     (return (CapUnseal c))
     (\<lambda>c s. has_expected_gpr_reads (f s) \<and> is_branch_target c (f s) \<and> Q s) E F"
  by (rule pre_post_strengthen_pre, rule pre_post_return)
     (auto simp add: is_branch_target_def)

lemma pre_post_return_CapUnseal_if_clear_is_branch_target_from_reg:
  "pre_post
     (\<lambda>s. has_expected_gpr_reads (f s) \<and> code_reg_caps (f s) = {c} \<and> Q s)
     (return (CapUnseal (if clear then CapWithTagClear c else c)))
     (\<lambda>c s. has_expected_gpr_reads (f s) \<and> is_branch_target c (f s) \<and> Q s) E F"
  by (rule pre_post_strengthen_pre, rule pre_post_return)
     (auto simp add: is_branch_target_def)

lemma pre_post_return_if_untag_is_branch_target_from_reg:
  "pre_post
     (\<lambda>s. has_expected_gpr_reads (f s) \<and> code_reg_caps (f s) = {c} \<and> Q s)
     (return (if untag then CapWithTagClear c else c))
     (\<lambda>c s. has_expected_gpr_reads (f s) \<and> is_branch_target c (f s) \<and> Q s) E F"
  by (rule pre_post_strengthen_pre, rule pre_post_return)
     (auto simp add: is_branch_target_def)

lemma pre_post_return_CapUnseal_if_clear_invocation_post_idc_reg[unfolded conj_assoc]:
  "pre_post
     (\<lambda>s. invocation_post_idc (pcc_tagged (CapUnseal (if clear then CapWithTagClear c else c))) s \<and> invocation_pre_final_reg c s)
     (return (CapUnseal (if clear then CapWithTagClear c else c)))
     (\<lambda>c s. invocation_post_idc (pcc_tagged c) s \<and> invocation_pre_final c s) E F"
  by (rule pre_post_strengthen_pre, rule pre_post_return)
     (auto simp add: is_branch_target_def)

lemma pre_post_return_untag_invocation_post_idc_reg[unfolded conj_assoc]:
  "pre_post
     (\<lambda>s. invocation_post_idc (pcc_tagged (CapWithTagClear c)) s \<and> invocation_pre_final_reg c s)
     (return (CapWithTagClear c))
     (\<lambda>c s. invocation_post_idc (pcc_tagged c) s \<and> invocation_pre_final c s) E F"
  by (rule pre_post_strengthen_pre, rule pre_post_return)
     (auto simp add: is_branch_target_def)

lemma is_branch_target_cong:
  assumes "code_reg_caps s = code_reg_caps s'"
    and "mem_caps s = mem_caps s'"
    and "load_auth_caps s = load_auth_caps s'"
  shows "is_branch_target c s \<longleftrightarrow> is_branch_target c s'"
  using assms
  by (simp add: is_branch_target_def cong: original_mem_code_caps_cong)

definition
  "get_initial_reg_cap n s \<equiv>
     (if n \<in> {0..30} then
        (case reg_state s (the_elem (R_name n)) of
           Some (Regval_bitvector_129_dec c) \<Rightarrow> c
         | _ \<Rightarrow> undefined)
      else 0)"

definition add_initial_gpr_read where
  "add_initial_gpr_read n s \<equiv>
     (if n = 31 then s else
       (let c = get_initial_reg_cap n s in
       (s\<lparr>code_reg_caps := (if instr_invokes_code_cap_from_reg instr = Some n then {c} else {}) \<union> code_reg_caps s,
          data_reg_caps := (if instr_invokes_data_cap_from_reg instr = Some n then {c} else {}) \<union> data_reg_caps s,
          load_auth_caps := (if instr_load_auth instr = Some (RegAuth n) then {c} else {}) \<union> load_auth_caps s\<rparr>)))"

definition
  "add_initial_code_reg_cap s \<equiv>
     (case instr_invokes_code_cap_from_reg instr of
        Some n \<Rightarrow> s\<lparr>code_reg_caps := {get_initial_reg_cap n s}\<rparr>
      | None \<Rightarrow> s)"

lemma init_null_caps_accessor_simps[simp]:
  "load_auth_caps (init_null_caps s) = load_auth_caps s"
  "pcc_writes (init_null_caps s) = pcc_writes s"
  "idc_writes (init_null_caps s) = idc_writes s"
  "pstate_writes (init_null_caps s) = pstate_writes s"
  "branch_taken_writes (init_null_caps s) = branch_taken_writes s"
  "invocation_regs_written (init_null_caps s) = invocation_regs_written s"
  "gpr_reads_after_write (init_null_caps s) = gpr_reads_after_write s"
  "mem_caps (init_null_caps s) = mem_caps s"
  "reg_state (init_null_caps s) = reg_state s"
  by (auto simp: init_null_caps_def split: option.splits)

lemma add_initial_code_reg_cap_accessor_simps[simp]:
  "data_reg_caps (add_initial_code_reg_cap s) = data_reg_caps s"
  "load_auth_caps (add_initial_code_reg_cap s) = load_auth_caps s"
  "pcc_writes (add_initial_code_reg_cap s) = pcc_writes s"
  "pstate_writes (add_initial_code_reg_cap s) = pstate_writes s"
  "branch_taken_writes (add_initial_code_reg_cap s) = branch_taken_writes s"
  "mem_caps (add_initial_code_reg_cap s) = mem_caps s"
  by (auto simp: add_initial_code_reg_cap_def split: option.splits)

lemma add_idc_write_accessor_simps[simp]:
  "code_reg_caps (add_idc_write c s) = code_reg_caps s"
  "data_reg_caps (add_idc_write c s) = data_reg_caps s"
  "load_auth_caps (add_idc_write c s) = load_auth_caps s"
  "pcc_writes (add_idc_write c s) = pcc_writes s"
  "idc_writes (add_idc_write c s) = Regval_bitvector_129_dec c # idc_writes s"
  "pstate_writes (add_idc_write c s) = pstate_writes s"
  "branch_taken_writes (add_idc_write c s) = branch_taken_writes s"
  "mem_caps (add_idc_write c s) = mem_caps s"
  by (auto simp: add_idc_write_def)

lemma R_name_in_dom_has_value:
  "invocation_regs \<subseteq> dom s \<Longrightarrow> r \<in> R_name n \<Longrightarrow> s r \<noteq> None"
  by (auto dest: R_name_in_all_R_names simp: invocation_regs_def)

lemma pre_post_C_read_code_cap:
  "pre_post_ignore_fail
     (\<lambda>s. Q (add_initial_code_reg_cap s) \<and>
          has_null_caps s \<and> load_auth_caps s = {} \<and>
          \<not>gpr_reads_after_write s \<and> \<not>invocation_regs_written s \<and>
          invocation_regs \<subseteq> dom (reg_state s) \<and>
          instr_invokes_code_cap_from_reg instr = Some n \<and>
          instr_invokes_data_cap_from_reg instr = None \<and>
          instr_load_auth instr = None)
     (C_read n) (\<lambda>c s. has_expected_gpr_reads s \<and> code_reg_caps s = {c} \<and> Q s) E"
  apply (rule pre_post_strengthen_pre)
   apply (rule pre_post_C_read)
  subgoal for s
    apply (cases s)
    apply (auto simp: is_code_reg_def is_data_reg_def is_load_auth_reg_def has_null_caps_def
                      has_expected_gpr_reads_def add_initial_code_reg_cap_def get_initial_reg_cap_def
                dest: R_name_in_dom_has_value)
    done
  done

lemma R_name_inj:
  "r \<in> R_name n \<Longrightarrow> r \<in> R_name n' \<Longrightarrow> n' = n"
  by (auto simp add: R_name_def split: if_splits)

lemma all_R_names_dom_reg_not_None:
  "\<forall>r s. invocation_regs \<subseteq> dom (reg_state s) \<and> r \<in> R_name n \<longrightarrow> reg_state s r \<noteq> None"
  by (auto dest: R_name_in_all_R_names simp: invocation_regs_def)

lemma pre_post_C_read_initial:
  "pre_post_ignore_fail
     (\<lambda>s. Q (get_initial_reg_cap n s) (add_initial_gpr_read n s) \<and> \<not>invocation_regs_written s \<and> invocation_regs \<subseteq> dom (reg_state s))
     (C_read n) Q E"
proof -
  have *: "\<forall>r \<in> R_name n. reg_state s r \<noteq> None" if "invocation_regs \<subseteq> dom (reg_state s)" for s :: invocation_state
    by (use that in \<open>auto dest: R_name_in_all_R_names simp: invocation_regs_def\<close>)
  show ?thesis
    by (rule pre_post_strengthen_pre, rule pre_post_C_read)
       (cases "n = 31"; cases "instr_invokes_code_cap_from_reg instr = Some n";
        cases "instr_invokes_data_cap_from_reg instr = Some n"; cases "instr_load_auth instr = Some (RegAuth n)";
        use R_name_inj[of _ n] in
          \<open>auto simp:  get_initial_reg_cap_def add_initial_gpr_read_def Let_def is_code_reg_def is_data_reg_def is_load_auth_reg_def dest!: *\<close>)
qed

lemma no_sentry_no_indirect_cap_reg[simp]:
  "instr_indirect_sentry_type instr = None \<Longrightarrow> instr_invokes_indirect_cap_from_reg instr = None"
  by (cases instr) auto

lemma pre_post_C_set_29_unseal_data_reg_cap_invocation_post_idc[unfolded conj_assoc]:
  "pcc_tagged \<longrightarrow> invokable CC c' c \<Longrightarrow>
   pre_post_ignore_fail
     (\<lambda>s. has_expected_gpr_reads s \<and> invocation_pre_final_reg c' s \<and> data_reg_caps s = {c} \<and>
          idc_writes s = [] \<and> instr_indirect_sentry_type instr = None \<and> mem_caps s = {})
     (C_set 29 (CapUnseal c)) (\<lambda>_ s. invocation_post_idc pcc_tagged s \<and> invocation_pre_final_reg c' s) E"
  by (rule pre_post_strengthen_pre, rule pre_post_C_set)
     (auto simp: performs_expected_idc_write_def invoked_data_caps_def original_reg_data_caps_def
                 add_idc_write_def has_expected_loads_def has_expected_gpr_reads_def has_load_cap_perm_if_needed_def)

lemma pre_post_C_set_29_data_reg_cap_invocation_post_idc[unfolded conj_assoc]:
  "pcc_tagged \<longrightarrow> \<not>invokable CC c' c \<Longrightarrow>
   pre_post_ignore_fail
     (\<lambda>s. has_expected_gpr_reads s \<and> invocation_pre_final_reg c' s \<and> data_reg_caps s = {c} \<and>
          idc_writes s = [] \<and> instr_indirect_sentry_type instr = None \<and> mem_caps s = {})
     (C_set 29 c) (\<lambda>_ s. invocation_post_idc pcc_tagged s \<and> invocation_pre_final_reg c' s) E"
  by (rule pre_post_strengthen_pre, rule pre_post_C_set)
     (auto simp: performs_expected_idc_write_def invoked_data_caps_def original_reg_data_caps_def
                 add_idc_write_def has_expected_loads_def has_expected_gpr_reads_def original_mem_data_caps_def
                 has_load_cap_perm_if_needed_def)

lemma pre_post_C_set_30_is_branch_target:
  "pre_post_ignore_fail
     (\<lambda>s. has_expected_gpr_reads s \<and> is_branch_target c' s \<and> Q (s\<lparr>invocation_regs_written := True\<rparr>))
     (C_set 30 c) (\<lambda>_ s. has_expected_gpr_reads s \<and> is_branch_target c' s \<and> Q s) E"
  by (rule pre_post_strengthen_pre, rule pre_post_C_set_30)
     (auto simp: has_expected_gpr_reads_def cong: is_branch_target_cong)

lemma has_load_cap_perm_if_needed_cong:
  "load_auth_caps s = load_auth_caps s' \<Longrightarrow> has_load_cap_perm_if_needed pcc_tagged s = has_load_cap_perm_if_needed pcc_tagged s'"
  by (auto simp: has_load_cap_perm_if_needed_def)

lemma pre_post_C_set_30_invocation_post_final[unfolded conj_assoc]:
  "pre_post_ignore_fail
     (\<lambda>s. invocation_post_idc pcc_tagged s \<and> invocation_pre_final c' s)
     (C_set 30 c) (\<lambda>_ s. invocation_post_idc pcc_tagged s \<and> invocation_pre_final c' s) E"
  by (rule pre_post_strengthen_pre, rule pre_post_C_set_30)
     (auto simp: has_expected_gpr_reads_def performs_expected_idc_write_def
           cong: is_branch_target_cong invoked_data_caps_cong has_expected_loads_cong
                 has_load_cap_perm_if_needed_cong)

lemmas if_distrib_bind_BranchXToCapability =
  if_distrib[where f = "\<lambda>m. bind m (\<lambda>target. BranchXToCapability target _)"]

lemma if_else_if_merge:
  "(if P then t else if Q then t else e) = (if P \<or> Q then t else e)"
  by auto

lemma CapWithTagClear_idem:
  "CapWithTagClear (CapWithTagClear c) = CapWithTagClear c"
  by (auto simp: CapWithTagClear_def)

lemma CapWithTagClear_if_clear_eq:
  "CapWithTagClear (if b then CapWithTagClear c else c) = CapWithTagClear c"
  by (auto simp: CapWithTagClear_idem)

lemma get_initial_reg_cap_cong:
  "reg_state s = reg_state s' \<Longrightarrow> get_initial_reg_cap n s = get_initial_reg_cap n s'"
  by (auto simp: get_initial_reg_cap_def)

lemma get_initial_reg_cap_31[simp]:
  "get_initial_reg_cap 31 s = 0"
  by (auto simp: get_initial_reg_cap_def)

lemma has_expected_gpr_reads_invoked_reg_pair:
  assumes "instr_invokes_code_cap_from_reg instr = Some n"
    and "instr_invokes_data_cap_from_reg instr = Some m"
    and "instr_load_auth instr = None"
  shows "has_expected_gpr_reads (add_initial_gpr_read m (add_initial_gpr_read n (init_null_caps (initial_invocation_state regs))))"
  using assms
  by (auto simp: has_expected_gpr_reads_def add_initial_gpr_read_def init_null_caps_def Let_def is_singleton_def
           intro: get_initial_reg_cap_cong)

lemma code_reg_caps_add_initial_gpr_read:
  assumes "instr_invokes_code_cap_from_reg instr = Some n"
    and "has_null_caps s"
  shows "code_reg_caps (add_initial_gpr_read m (add_initial_gpr_read n s)) = {get_initial_reg_cap n s}"
  using assms
  by (auto simp: add_initial_gpr_read_def has_null_caps_def Let_def cong: get_initial_reg_cap_cong)

lemma data_reg_caps_add_initial_gpr_read:
  assumes "instr_invokes_data_cap_from_reg instr = Some m"
    and "has_null_caps s"
  shows "data_reg_caps (add_initial_gpr_read m (add_initial_gpr_read n s)) = {get_initial_reg_cap m s}"
  using assms
  by (auto simp: add_initial_gpr_read_def has_null_caps_def Let_def cong: get_initial_reg_cap_cong)

lemma get_initial_reg_cap_in_code_reg_caps:
  assumes "instr_invokes_code_cap_from_reg instr = Some n"
    and "has_null_caps s"
  shows "get_initial_reg_cap n s \<in> code_reg_caps (add_initial_gpr_read m (add_initial_gpr_read n s))"
  using assms
  by (auto simp: add_initial_gpr_read_def has_null_caps_def Let_def)

lemma get_initial_reg_cap_in_data_reg_caps:
  assumes "instr_invokes_data_cap_from_reg instr = Some m"
    and "has_null_caps s"
  shows "get_initial_reg_cap m (add_initial_gpr_read n s) \<in> data_reg_caps (add_initial_gpr_read m (add_initial_gpr_read n s))"
  using assms
  by (auto simp: add_initial_gpr_read_def has_null_caps_def Let_def cong: get_initial_reg_cap_cong)

lemma add_initial_gpr_read_accessor_simps[simp]:
  "pcc_writes (add_initial_gpr_read n s) = pcc_writes s"
  "idc_writes (add_initial_gpr_read n s) = idc_writes s"
  "pstate_writes (add_initial_gpr_read n s) = pstate_writes s"
  "branch_taken_writes (add_initial_gpr_read n s) = branch_taken_writes s"
  "invocation_regs_written (add_initial_gpr_read n s) = invocation_regs_written s"
  "mem_caps (add_initial_gpr_read n s) = mem_caps s"
  "reg_state (add_initial_gpr_read n s) = reg_state s"
  by (auto simp: add_initial_gpr_read_def Let_def)

lemma init_null_caps_has_null_caps[simp]:
  "has_null_caps (init_null_caps s)"
  by (auto simp: has_null_caps_def init_null_caps_def)

(* TODO: Move *)
lemma is_indirect_sentry_simps[simp]:
  "is_indirect_sentry CC c \<longleftrightarrow> CapGetObjectType c \<in> {CAP_SEAL_TYPE_LB, CAP_SEAL_TYPE_LPB}"
  "is_indirect_pcc_sentry CC c \<longleftrightarrow> CapGetObjectType c = CAP_SEAL_TYPE_LB"
  "is_indirect_pair_sentry CC c \<longleftrightarrow> CapGetObjectType c = CAP_SEAL_TYPE_LPB"
  unfolding is_indirect_sentry_def
  unfolding is_indirect_pcc_sentry_def is_indirect_pair_sentry_def
  by (auto simp: get_indirect_sentry_type_def CapIsSealed_def)

lemma [simp]:
  "CapIsSealed (CapWithTagClear c) = CapIsSealed c"
  "CapGetObjectType (CapWithTagClear c) = CapGetObjectType c"
  by (auto simp: CapIsSealed_def CapWithTagClear_def)

lemma pre_post_execute_BRS_C_C_C:
  "pre_post_ignore_fail
     (\<lambda>s. \<exists>regs Cm opc Cn. s = init_null_caps (initial_invocation_state regs) \<and> instr_invokes_code_cap_from_reg instr = Some n \<and> instr_invokes_data_cap_from_reg instr = Some m \<and> instr_load_auth instr = None \<and> instr_indirect_sentry_type instr = None \<and> invocation_regs \<subseteq> dom regs)
     (execute_BRS_C_C_C branch_type m n) (\<lambda>_ s. invocation_post_final s) is_expected_exception"
  unfolding execute_BRS_C_C_C_def Let_def bind_assoc bind_return if_distrib_bind_BranchXToCapability CapWithTagClear_if_clear_eq
  by (pre_postI_with \<open>unfold conj_assoc\<close> \<open>pre_post_ignore_fail_no_state_update_no_exception | solves \<open>auto intro: has_expected_gpr_reads_invoked_reg_pair simp: invokable_def is_sentry_def code_reg_caps_add_initial_gpr_read data_reg_caps_add_initial_gpr_read cong: get_initial_reg_cap_cong\<close>\<close> intro: BranchXToCapability_unseal_if_untag_invocation_post_final_reg BranchXToCapability_untag_invocation_post_final_reg pre_post_C_set_29_unseal_data_reg_cap_invocation_post_idc pre_post_C_set_29_data_reg_cap_invocation_post_idc pre_post_if_post_collapse pre_post_C_read_initial pre_post_CheckCapabilitiesEnabled)

lemma pre_post_has_no_expected_data_cap_invocation_pre:
  assumes "pre_post (\<lambda>s. performs_expected_idc_write pcc_tagged s \<and> P s) m Q E F"
  shows "pre_post (\<lambda>s. P s \<and> has_no_expected_data_cap_invocation s) m Q E F"
  using assms
  by (elim pre_post_strengthen_pre)
     (auto simp: performs_expected_idc_write_def has_no_expected_data_cap_invocation_no_invoked_data_caps)

lemma pre_post_load_cap_perm_not_needed:
  assumes "pre_post P m (\<lambda>a s. Q a s \<and> has_no_expected_loads s) E F"
  shows "pre_post P m (\<lambda>a s. has_load_cap_perm_if_needed pcc_tagged s \<and> Q a s) E F"
  using assms
  by (elim pre_post_consequence) (auto simp: has_load_cap_perm_if_needed_def)

lemma pre_post_load_cap_perm_not_needed_pre:
  assumes "pre_post (\<lambda>s. has_load_cap_perm_if_needed pcc_tagged s \<and> P s) m Q E F"
  shows "pre_post (\<lambda>s. P s \<and> has_no_expected_loads s) m Q E F"
  using assms
  by (elim pre_post_strengthen_pre) (auto simp: has_load_cap_perm_if_needed_def)

lemmas BranchXToCapability_unseal_if_untag_invocation_post_final_reg_no_data_cap =
  BranchXToCapability_unseal_if_untag_invocation_post_final_reg[unfolded conj_assoc,
    THEN pre_post_has_no_expected_data_cap_invocation_pre, unfolded conj_assoc,
    THEN pre_post_load_cap_perm_not_needed_pre]

lemmas BranchXToCapability_if_untag_invocation_post_final_reg_no_data_cap =
  BranchXToCapability_if_untag_invocation_post_final_reg[unfolded conj_assoc,
    THEN pre_post_has_no_expected_data_cap_invocation_pre, unfolded conj_assoc,
    THEN pre_post_load_cap_perm_not_needed_pre]

lemmas BranchXToCapability_unseal_invocation_post_final_reg_no_data_cap =
  BranchXToCapability_unseal_invocation_post_final_reg[unfolded conj_assoc,
    THEN pre_post_has_no_expected_data_cap_invocation_pre, unfolded conj_assoc,
    THEN pre_post_load_cap_perm_not_needed_pre]

lemmas BranchXToCapability_if_unseal_untag_invocation_post_final_reg_no_data_cap =
  BranchXToCapability_if_unseal_untag_invocation_post_final_reg[unfolded conj_assoc,
    THEN pre_post_has_no_expected_data_cap_invocation_pre, unfolded conj_assoc,
    THEN pre_post_load_cap_perm_not_needed_pre]

lemma pre_post_execute_BRS_C_C:
  "pre_post_ignore_fail
     (\<lambda>s. \<exists>regs opc Cn. s = init_null_caps (initial_invocation_state regs) \<and> instr = Instr_BRS_C_C (opc, Cn) \<and> uint Cn = n \<and> invocation_regs \<subseteq> dom regs)
     (execute_BRS_C_C branch_type n) (\<lambda>_ s. invocation_post_final s) is_expected_exception"
  unfolding execute_BRS_C_C_def Let_def bind_assoc bind_return conj_assoc if_distrib_bind_BranchXToCapability if_distrib[where f = CapWithTagClear] if_cancel if_else_if_merge CapWithTagClear_idem
  by (pre_postI_with \<open>unfold conj_assoc\<close> \<open>pre_post_ignore_fail_no_state_update_no_exception | solves \<open>auto simp: init_null_caps_def has_null_caps_def\<close>\<close> intro: pre_post_if_post_collapse BranchXToCapability_unseal_if_untag_invocation_post_final_reg_no_data_cap BranchXToCapability_if_untag_invocation_post_final_reg_no_data_cap pre_post_and_boolM_ignore pre_post_has_no_expected_loads[where m = "C_read n"] pre_post_C_read_code_cap pre_post_CheckCapabilitiesEnabled)

lemma pre_post_execute_BLRR_C_C:
  "pre_post_ignore_fail
     (\<lambda>s. \<exists>regs opc Cn. s = init_null_caps (initial_invocation_state regs) \<and> instr = Instr_BLRR_C_C (opc, Cn) \<and> uint Cn = n \<and> invocation_regs \<subseteq> dom regs)
     (execute_BLRR_C_C branch_type n) (\<lambda>_ s. invocation_post_final s) is_expected_exception"
  unfolding execute_BLRR_C_C_def Let_def
  by (pre_postI_with \<open>unfold conj_assoc\<close> \<open>pre_post_ignore_fail_no_state_update_no_exception | auto simp add: init_null_caps_def has_null_caps_def\<close> intro: BranchXToCapability_invocation_post_final pre_post_has_no_expected_data_cap_invocation pre_post_load_cap_perm_not_needed pre_post_has_no_expected_loads pre_post_if_post_collapse pre_post_C_set_30_is_branch_target pre_post_return_CapUnseal_is_branch_target_from_reg pre_post_return_if_untag_is_branch_target_from_reg pre_post_C_read_code_cap pre_post_CheckCapabilitiesEnabled pre_post_UndefinedFault)

lemma pre_post_execute_BLRS_C_C:
  "pre_post_ignore_fail
     (\<lambda>s. \<exists>regs opc Cn. s = init_null_caps (initial_invocation_state regs) \<and> instr = Instr_BLRS_C_C (opc, Cn) \<and> uint Cn = n \<and> invocation_regs \<subseteq> dom regs)
     (execute_BLRS_C_C branch_type n) (\<lambda>_ s. invocation_post_final s) is_expected_exception"
  unfolding execute_BLRS_C_C_def Let_def CapWithTagClear_if_clear_eq if_else_if_merge
  by (pre_postI_with \<open>unfold conj_assoc\<close> \<open>pre_post_ignore_fail_no_state_update_no_exception | auto simp: init_null_caps_def has_null_caps_def\<close> intro: BranchXToCapability_invocation_post_final pre_post_has_no_expected_data_cap_invocation pre_post_load_cap_perm_not_needed pre_post_has_no_expected_loads pre_post_C_set_30_is_branch_target pre_post_return_CapUnseal_if_clear_is_branch_target_from_reg pre_post_return_if_untag_is_branch_target_from_reg pre_post_C_read_code_cap pre_post_CheckCapabilitiesEnabled pre_post_if_post_collapse)

lemma pre_post_execute_BLRS_C_C_C:
  "pre_post_ignore_fail
     (\<lambda>s. \<exists>regs Cm opc Cn. s = init_null_caps (initial_invocation_state regs) \<and> instr_invokes_code_cap_from_reg instr = Some n \<and> instr_invokes_data_cap_from_reg instr = Some m \<and> instr_load_auth instr = None \<and> instr_indirect_sentry_type instr = None \<and> invocation_regs \<subseteq> dom regs)
     (execute_BLRS_C_C_C branch_type m n) (\<lambda>_ s. invocation_post_final s) is_expected_exception"
  unfolding execute_BLRS_C_C_C_def Let_def bind_assoc CapWithTagClear_if_clear_eq
  by (pre_postI_with \<open>unfold conj_assoc\<close> \<open>pre_post_ignore_fail_no_state_update_no_exception | solves \<open>auto intro: has_expected_gpr_reads_invoked_reg_pair simp: invokable_def is_sentry_def code_reg_caps_add_initial_gpr_read data_reg_caps_add_initial_gpr_read cong: get_initial_reg_cap_cong split: if_splits\<close>\<close> intro: BranchXToCapability_invocation_post_final pre_post_has_no_expected_loads pre_post_C_set_30_invocation_post_final pre_post_C_set_29_unseal_data_reg_cap_invocation_post_idc pre_post_C_set_29_data_reg_cap_invocation_post_idc pre_post_return_CapUnseal_if_clear_invocation_post_idc_reg pre_post_return_untag_invocation_post_idc_reg pre_post_C_read_initial pre_post_CheckCapabilitiesEnabled pre_post_if_post_collapse)

lemma pre_post_execute_BLR_C_C:
  "pre_post_ignore_fail
     (\<lambda>s. \<exists>regs opc Cn. s = init_null_caps (initial_invocation_state regs) \<and> instr = Instr_BLR_C_C (opc, Cn) \<and> uint Cn = n \<and> invocation_regs \<subseteq> dom regs)
     (execute_BLR_C_C branch_type n) (\<lambda>_ s. invocation_post_final s) is_expected_exception"
  unfolding execute_BLR_C_C_def Let_def bind_assoc conj_assoc
  by (pre_postI_with \<open>unfold conj_assoc\<close> \<open>pre_post_ignore_fail_no_state_update_no_exception | solves \<open>auto simp: has_expected_gpr_reads_def add_initial_gpr_read_def init_null_caps_def\<close>\<close> intro: BranchXToCapability_if_unseal_untag_invocation_post_final_reg pre_post_has_no_expected_data_cap_invocation pre_post_load_cap_perm_not_needed pre_post_has_no_expected_loads pre_post_C_set_30 pre_post_C_read_initial pre_post_CheckCapabilitiesEnabled pre_post_if_post_collapse)

lemma pre_post_execute_BRR_C_C:
  "pre_post_ignore_fail
     (\<lambda>s. \<exists>regs opc Cn. s = init_null_caps (initial_invocation_state regs) \<and> instr = Instr_BRR_C_C (opc, Cn) \<and> uint Cn = n \<and> invocation_regs \<subseteq> dom regs)
     (execute_BRR_C_C branch_type n) (\<lambda>_ s. invocation_post_final s) is_expected_exception"
  unfolding execute_BRR_C_C_def Let_def bind_assoc bind_return conj_assoc if_distrib_bind_BranchXToCapability
  by (pre_postI_with \<open>unfold conj_assoc\<close> \<open>pre_post_ignore_fail_no_state_update_no_exception | rule pre_post_has_no_expected_data_cap_invocation pre_post_has_no_expected_loads | solves \<open>auto simp: init_null_caps_def has_null_caps_def\<close>\<close> intro: BranchXToCapability_unseal_invocation_post_final_reg_no_data_cap BranchXToCapability_if_untag_invocation_post_final_reg_no_data_cap pre_post_if_post_collapse pre_post_C_read_code_cap pre_post_CheckCapabilitiesEnabled pre_post_UndefinedFault)

lemma pre_post_execute_BR_C_C:
  "pre_post_ignore_fail
     (\<lambda>s. \<exists>regs opc Cn. s = init_null_caps (initial_invocation_state regs) \<and> instr = Instr_BR_C_C (opc, Cn) \<and> uint Cn = n \<and> invocation_regs \<subseteq> dom regs)
     (execute_BR_C_C branch_type n) (\<lambda>_ s. invocation_post_final s) is_expected_exception"
  unfolding execute_BR_C_C_def Let_def bind_assoc conj_assoc
  by (pre_postI_with \<open>unfold conj_assoc\<close> \<open>pre_post_ignore_fail_no_state_update_no_exception | solves \<open>auto simp: init_null_caps_def has_null_caps_def\<close>\<close> intro: BranchXToCapability_if_unseal_untag_invocation_post_final_reg_no_data_cap pre_post_C_read_code_cap pre_post_CheckCapabilitiesEnabled pre_post_has_no_expected_data_cap_invocation pre_post_has_no_expected_loads pre_post_if_post_collapse)

lemma pre_post_execute_RETR_C_C:
  "pre_post_ignore_fail
     (\<lambda>s. \<exists>regs opc Cn. s = init_null_caps (initial_invocation_state regs) \<and> instr = Instr_RETR_C_C (opc, Cn) \<and> uint Cn = n \<and> invocation_regs \<subseteq> dom regs)
     (execute_RETR_C_C branch_type n) (\<lambda>_ s. invocation_post_final s) is_expected_exception"
  unfolding execute_RETR_C_C_def Let_def bind_assoc bind_return conj_assoc if_distrib_bind_BranchXToCapability
  by (pre_postI_with \<open>unfold conj_assoc\<close> \<open>pre_post_ignore_fail_no_state_update_no_exception | rule pre_post_has_no_expected_data_cap_invocation pre_post_has_no_expected_loads | solves \<open>auto simp: init_null_caps_def has_null_caps_def\<close>\<close> intro: BranchXToCapability_unseal_invocation_post_final_reg_no_data_cap BranchXToCapability_if_untag_invocation_post_final_reg_no_data_cap pre_post_if_post_collapse pre_post_C_read_code_cap pre_post_CheckCapabilitiesEnabled pre_post_UndefinedFault)

lemma pre_post_execute_RETS_C_C:
  "pre_post_ignore_fail
     (\<lambda>s. \<exists>regs opc Cn. s = init_null_caps (initial_invocation_state regs) \<and> instr = Instr_RETS_C_C (opc, Cn) \<and> uint Cn = n \<and> invocation_regs \<subseteq> dom regs)
     (execute_RETS_C_C branch_type n) (\<lambda>_ s. invocation_post_final s) is_expected_exception"
  unfolding execute_RETS_C_C_def Let_def bind_assoc bind_return conj_assoc if_distrib_bind_BranchXToCapability CapWithTagClear_if_clear_eq if_else_if_merge
  by (pre_postI_with \<open>unfold conj_assoc\<close> \<open>pre_post_ignore_fail_no_state_update_no_exception | rule pre_post_has_no_expected_data_cap_invocation pre_post_has_no_expected_loads | solves \<open>auto simp: init_null_caps_def has_null_caps_def\<close>\<close> intro: BranchXToCapability_unseal_if_untag_invocation_post_final_reg_no_data_cap BranchXToCapability_if_untag_invocation_post_final_reg_no_data_cap pre_post_if_post_collapse pre_post_C_read_code_cap pre_post_CheckCapabilitiesEnabled)

lemma pre_post_execute_RETS_C_C_C:
  "pre_post_ignore_fail
     (\<lambda>s. \<exists>regs. s = init_null_caps (initial_invocation_state regs) \<and> instr_invokes_code_cap_from_reg instr = Some n \<and> instr_invokes_data_cap_from_reg instr = Some m \<and> instr_load_auth instr = None \<and> instr_indirect_sentry_type instr = None \<and> invocation_regs \<subseteq> dom regs)
     (execute_RETS_C_C_C branch_type m n) (\<lambda>_ s. invocation_post_final s) is_expected_exception"
  unfolding execute_RETS_C_C_C_def Let_def bind_assoc bind_return conj_assoc if_distrib_bind_BranchXToCapability CapWithTagClear_if_clear_eq if_else_if_merge
  by (pre_postI_with \<open>unfold conj_assoc\<close> \<open>pre_post_ignore_fail_no_state_update_no_exception | solves \<open>auto intro: has_expected_gpr_reads_invoked_reg_pair simp: invokable_def is_sentry_def code_reg_caps_add_initial_gpr_read data_reg_caps_add_initial_gpr_read cong: get_initial_reg_cap_cong\<close>\<close> intro: BranchXToCapability_unseal_if_untag_invocation_post_final_reg BranchXToCapability_untag_invocation_post_final_reg pre_post_C_set_29_unseal_data_reg_cap_invocation_post_idc pre_post_C_set_29_data_reg_cap_invocation_post_idc pre_post_if_post_collapse pre_post_C_read_initial pre_post_CheckCapabilitiesEnabled)

lemma pre_post_execute_RET_C_C:
  "pre_post_ignore_fail
     (\<lambda>s. \<exists>regs opc Cn. s = init_null_caps (initial_invocation_state regs) \<and> instr = Instr_RET_C_C (opc, Cn) \<and> uint Cn = n \<and> invocation_regs \<subseteq> dom regs)
     (execute_RET_C_C branch_type n) (\<lambda>_ s. invocation_post_final s) is_expected_exception"
  unfolding execute_RET_C_C_def Let_def bind_assoc conj_assoc
  by (pre_postI_with \<open>unfold conj_assoc\<close> \<open>pre_post_ignore_fail_no_state_update_no_exception | rule pre_post_has_no_expected_data_cap_invocation pre_post_has_no_expected_loads | solves \<open>auto simp: init_null_caps_def has_null_caps_def\<close>\<close> intro: BranchXToCapability_if_unseal_untag_invocation_post_final_reg_no_data_cap pre_post_if_post_collapse pre_post_C_read_code_cap pre_post_CheckCapabilitiesEnabled)

definition "is_unsealed_mem_branch_target c s \<equiv>
  (\<exists>c' \<in> original_mem_code_caps s.
     lsb c' = lsb c \<and>
     (if is_sentry c' then CapIsTagSet c \<longrightarrow> c = c'
      else CapIsTagSet c \<longrightarrow> (c = c' \<or> (\<not>CapIsSealed c' \<and> c = clear_perm mutable_perms c'))))"

abbreviation "no_branch_writes s \<equiv> pcc_writes s = [] \<and> pstate_writes s = [] \<and> branch_taken_writes s = []"
abbreviation "invocation_pre_final_mem c s \<equiv> is_unsealed_mem_branch_target c s \<and> no_branch_writes s"

lemma is_mem_branch_target_CapWithTagClear:
  "is_unsealed_mem_branch_target c s \<Longrightarrow> is_branch_target (CapWithTagClear c) s"
  by (auto simp: is_branch_target_def is_unsealed_mem_branch_target_def)

lemma is_mem_branch_target_CapUnseal:
  "is_unsealed_mem_branch_target c s \<Longrightarrow> CapGetObjectType c = 1 \<Longrightarrow> is_branch_target (CapUnseal c) s"
  by (auto simp add: is_branch_target_def is_unsealed_mem_branch_target_def CapIsSealed_def is_sentry_def split: if_splits)

lemma mem_branch_target_is_branch_target:
  "is_unsealed_mem_branch_target c s \<Longrightarrow> CapIsTagSet c \<and> CapIsSealed c \<longrightarrow> CapGetObjectType c \<noteq> 1 \<Longrightarrow> is_branch_target c s"
  by (auto simp add: is_branch_target_def is_unsealed_mem_branch_target_def CapIsSealed_def is_sentry_def split: if_splits)

lemmas mem_is_branch_target_intros = is_mem_branch_target_CapWithTagClear
  is_mem_branch_target_CapUnseal mem_branch_target_is_branch_target

lemma is_unsealed_mem_branch_target_cong_aux:
  "original_mem_code_caps s = original_mem_code_caps s' \<Longrightarrow> is_unsealed_mem_branch_target c s = is_unsealed_mem_branch_target c s'"
  by (auto simp: is_unsealed_mem_branch_target_def)

lemmas is_unsealed_mem_branch_target_cong = is_unsealed_mem_branch_target_cong_aux[OF original_mem_code_caps_cong]

lemma is_unsealed_mem_branch_target_simp[simp]:
  "is_unsealed_mem_branch_target c (add_idc_write c' s) = is_unsealed_mem_branch_target c s"
  by (auto simp: add_idc_write_def cong: is_unsealed_mem_branch_target_cong)

lemma BranchXToCapability_if_unseal_untag_invocation_post_final_mem:
  fixes c clear
  defines "c' \<equiv> (if clear then CapWithTagClear c else c)"
  defines "unseal \<equiv> CapIsTagSet c' \<and> CapIsSealed c' \<and> CapGetObjectType c' = CAP_SEAL_TYPE_RB"
  defines "c'' \<equiv> (if unseal then CapUnseal c' else c')"
  shows "pre_post_ignore_fail
     (\<lambda>s. invocation_post_idc (CapIsTagSet c) s \<and> invocation_pre_final_mem c s)
     (BranchXToCapability c'' branch_type) (\<lambda>_ s. invocation_post_final s) E"
  by (rule pre_post_strengthen_pre, rule BranchXToCapability_invocation_post_final)
     (auto simp: c''_def c'_def unseal_def has_load_cap_perm_if_needed_def
           intro: mem_is_branch_target_intros elim: performs_expected_idc_write_pcc_tagged_antimono)

abbreviation "invocation_sentry_pre_idc_write type c s \<equiv> load_auth_caps s = {c} \<and> idc_writes s = [] \<and> instr_indirect_sentry_type instr = Some type"

definition is_VA_of_cap :: "VirtualAddress \<Rightarrow> Capability \<Rightarrow> bool" where
  "is_VA_of_cap va c \<equiv>
     VirtualAddress_vatype va = VA_Capability \<and>
     ((VirtualAddress_base va = c \<comment> \<open>\<and> \<not>CapIsSealed c\<close>) \<or>
      (VirtualAddress_base va = CapUnseal c \<and>
       get_indirect_sentry_type c = instr_indirect_sentry_type instr \<and>
       instr_invokes_indirect_cap_from_reg instr \<noteq> None))"

lemma pre_post_C_set_29_indirect_pcc_sentry_invocation_post_idc[unfolded conj_assoc]:
  "pre_post_ignore_fail
     (\<lambda>s. has_load_cap_perm_if_needed (CapIsTagSet c') s \<and> invocation_post_load s \<and> invocation_pre_final_mem c' s \<and> invocation_sentry_pre_idc_write Points_to_PCC c s)
     (C_set 29 (if (CapIsTagSet c \<and> CapIsSealed c \<and> CapGetObjectType c = CAP_SEAL_TYPE_LB) then CapUnseal c else c)) (\<lambda>_ s. invocation_post_idc (CapIsTagSet c') s \<and> invocation_pre_final_mem c' s) E"
  apply (rule pre_post_strengthen_pre, rule pre_post_C_set)
  apply (auto simp: performs_expected_idc_write_def invoked_data_caps_def original_reg_data_caps_def mem_data_caps_def original_mem_data_caps_def cong: is_unsealed_mem_branch_target_cong has_load_cap_perm_if_needed_cong)
  done

(* TODO: Move *)
lemma cap_permits_CapUnseal_iff:
  "cap_permits perms (CapUnseal c) \<longleftrightarrow> cap_permits perms c"
  by (auto simp: CapCheckPermissions_def CapGetPermissions_CapUnseal_eq)

lemma pre_post_CapSquashPostLoadCap:
  "pre_post_ignore_fail
      (\<lambda>s. \<forall>c'. c' = CapWithTagClear c \<or> (is_VA_of_cap addr auth \<longrightarrow> cap_permits CAP_PERM_LOAD_CAP auth) \<and> (c' = c \<or> CapIsTagSet c \<and> \<not>CapIsSealed c \<and> c' = clear_perm mutable_perms c) \<longrightarrow> Q c' s)
      (CapSquashPostLoadCap c addr) Q E"
  unfolding CapSquashPostLoadCap_def Let_def
  by (pre_postI_with \<open>-\<close> \<open>pre_post_ignore_fail_no_state_update_no_exception\<close>)
     (auto simp add: is_VA_of_cap_def VAIsBits64_def VAToCapability_def cap_permits_CapUnseal_iff)

lemma CapSquashPostLoadCap_sentry_mem_branch_target[unfolded conj_assoc]:
  "pre_post_ignore_fail (\<lambda>s. c \<in> original_mem_code_caps s \<and> is_VA_of_cap addr c'' \<and> invocation_post_load s \<and> no_branch_writes s \<and> invocation_sentry_pre_idc_write sentry_type c'' s)
     (CapSquashPostLoadCap c addr) (\<lambda>c' s. has_load_cap_perm_if_needed (CapIsTagSet c') s \<and> invocation_post_load s \<and> invocation_pre_final_mem c' s \<and> invocation_sentry_pre_idc_write sentry_type c'' s) E"
  by (rule pre_post_CapSquashPostLoadCap[THEN pre_post_strengthen_pre])
     (auto simp add: is_unsealed_mem_branch_target_def CapIsSealed_def is_sentry_def has_load_cap_perm_if_needed_def)

lemma points_to_pcc_no_invoked_data_caps:
  assumes "instr_indirect_sentry_type instr = Some Points_to_PCC"
    and "instr_invokes_indirect_cap_from_reg instr = None"
  shows "invoked_data_caps s = {}"
  using assms
  by (auto simp: invoked_data_caps_def mem_data_caps_def original_mem_data_caps_def original_reg_data_caps_def)

lemma CapSquashPostLoadCap_points_to_pcc_no_invocation[unfolded conj_assoc]:
  "pre_post_ignore_fail
     (\<lambda>s. c \<in> original_mem_code_caps s \<and> invocation_post_load s \<and> no_branch_writes s \<and> idc_writes s = [] \<and>
          instr_indirect_sentry_type instr = Some Points_to_PCC \<and> instr_invokes_indirect_cap_from_reg instr = None)
     (CapSquashPostLoadCap c addr)
     (\<lambda>c' s. invocation_post_idc (pcc_tagged c') s \<and> invocation_pre_final_mem c' s) E"
  by (rule pre_post_CapSquashPostLoadCap[THEN pre_post_strengthen_pre])
     (auto simp: is_unsealed_mem_branch_target_def CapIsSealed_def is_sentry_def performs_expected_idc_write_def
                 points_to_pcc_no_invoked_data_caps has_load_cap_perm_if_needed_def)

lemma pre_post_AArch64_Abort:
  "pre_post_ignore_fail
     (\<lambda>s. pcc_writes s = [] \<and> idc_writes s = [])
     (AArch64_Abort vaddress fault) (\<lambda>_. Q) is_expected_exception"
  unfolding AArch64_Abort_def AArch64_BreakpointException_def AArch64_WatchpointException_def
    AArch64_InstructionAbort_def AArch64_DataAbort_def Let_def
  by (pre_postI_with \<open>-\<close> \<open>pre_post_ignore_fail_no_state_update_no_exception | auto\<close>
          intro: pre_post_if_post_collapse pre_post_AArch64_TakeException pre_post_return)

lemma pre_post_CheckCapabilityAlignment:
  "pre_post_ignore_fail (\<lambda>s. Q s \<and> pcc_writes s = [] \<and> idc_writes s = [])
     (CheckCapabilityAlignment address acctype iswrite) (\<lambda>_. Q) is_expected_exception"
  unfolding CheckCapabilityAlignment_def Let_def
  by (pre_postI_with \<open>-\<close> \<open>pre_post_ignore_fail_no_state_update_no_exception | auto\<close> intro: pre_post_AArch64_Abort)

lemma pre_post_CheckLoadTagsPermission:
  "pre_post_ignore_fail (\<lambda>s. Q s \<and> pcc_writes s = [] \<and> idc_writes s = [])
     (CheckLoadTagsPermission desc acctype) (\<lambda>a. Q) is_expected_exception"
  unfolding CheckLoadTagsPermission_def Let_def
  by (pre_postI_with \<open>-\<close> \<open>pre_post_ignore_fail_no_state_update_no_exception | auto\<close> intro: pre_post_AArch64_Abort)

lemma of_bl_0th_eq: "of_bl [test_bit b 0] = (b :: 1 word)"
  by (intro word_eqI) auto

lemma pre_post_ReadTaggedMem:
  "pre_post_ignore_fail
     (\<lambda>s. \<forall>bytes tag. Q (tag :: 1 word, bytes :: 128 word) (s\<lparr>mem_caps := insert (unat (FullAddress_address (AddressDescriptor_paddress desc)), word_cat tag bytes) (mem_caps s)\<rparr>))
     (ReadTaggedMem desc CAPABILITY_DBYTES accdesc) Q is_expected_exception"
  unfolding ReadTaggedMem_def Let_def
  by clarsimp (pre_postI_with \<open>-\<close> \<open>auto simp: Bits_def split: option.splits\<close> intro: pre_post_read_memt)

lemma pre_post_ReadMem:
  "pre_post_ignore_fail
     (\<lambda>s. \<forall>bytes. Q (bytes :: 128 word) (s\<lparr>mem_caps := insert (unat (FullAddress_address (AddressDescriptor_paddress desc)), ucast bytes) (mem_caps s)\<rparr>))
     (ReadMem desc CAPABILITY_DBYTES accdesc) Q is_expected_exception"
  unfolding ReadMem_def Mem_read_def
  by (rule pre_post_read_mem[THEN pre_post_strengthen_pre]) (auto split: option.splits)

lemma debug_disabled_read_reg_iff:
  "\<And>v. debug_disabled (E_read_reg ''DBGEN'' (Regval_signal v)) \<longleftrightarrow> (v = LOW)"
  "\<And>v. debug_disabled (E_read_reg ''EDSCR'' (Regval_bitvector_32_dec v)) \<longleftrightarrow> (ucast v :: 6 word) = 2"
  "\<And>v. debug_disabled (E_read_reg ''MDSCR_EL1'' (Regval_bitvector_32_dec v)) \<longleftrightarrow> (\<not>v !! 15) \<and> (\<not>v !! 0)"
  by (auto simp: debug_disabled_def)

lemma HaltOnBreakpointOrWatchpoint_False:
  assumes "Run (HaltOnBreakpointOrWatchpoint u) t a" and "trace_assms s t"
  shows "\<not>a"
  using assms
  unfolding HaltOnBreakpointOrWatchpoint_def HaltingAllowed_def
    ExternalSecureInvasiveDebugEnabled_def ExternalInvasiveDebugEnabled_def
  by (auto simp:  debug_disabled_read_reg_iff register_defs word_eq_iff nth_slice
           elim!: Run_bindE Run_ifE Run_and_boolM_E Run_read_regE)

lemma read_reg_MDSCR_EL1_MDE_False:
  assumes "Run (read_reg MDSCR_EL1_ref) t a" and "trace_assms s t"
  shows "Word.slice 15 a = (0 :: 1 word)"
  using assms
  by (auto simp: debug_disabled_read_reg_iff register_defs word_eq_iff nth_slice elim!: Run_read_regE)

lemma no_state_update_AArch64_CheckDebug_deps[no_state_update]:
  "no_state_update (AArch64_NoFault u)"
  "no_state_update (AArch64_GenerateDebugExceptions u)"
  "no_state_update (HaltOnBreakpointOrWatchpoint u)"
  by (rule no_state_updateI, no_reads_from_any_gpr, no_reg_writes_toI)+

lemma no_state_update_read_reg:
  assumes "name r \<notin> all_R_names"
  shows "no_state_update (read_reg r :: 'a M)"
proof (unfold no_state_update_def, clarsimp)
  fix s t and m' :: "'a M"
  assume "(read_reg r, t, m') \<in> Traces" "trace_assms s t"
  then consider (Nil) "t = []" | (Cons) v where "t = [E_read_reg (name r) v]"
    by (auto simp: read_reg_def elim!: Read_reg_TracesE split: option.splits)
  then show "run_state s t = s"
  proof cases
    case (Cons v)
    have "\<not>is_code_reg (name r) \<and> \<not>is_data_reg (name r) \<and> \<not>is_indirect_reg (name r) \<and> \<not>is_load_auth_reg (name r)"
      using assms
      by (auto simp: is_code_reg_def is_data_reg_def is_indirect_reg_def is_load_auth_reg_def
                     all_R_names_iff_R_name)
    then show ?thesis
      using Cons assms
      by (cases v) auto
  qed auto
qed

lemma no_state_update_AArch64_CheckDebug[no_state_update]:
  "no_state_update (AArch64_CheckDebug vaddress acctype iswrite sz)"
  unfolding AArch64_CheckDebug_def Let_def
  by (auto simp: Run_and_boolM_True_iff read_reg_MDSCR_EL1_MDE_False register_defs all_R_names_def
           intro!: no_state_update no_state_update_read_reg dest!: HaltOnBreakpointOrWatchpoint_False)

lemma no_state_update_AArch64_FullTranslateWithTag[no_state_update]:
  "no_state_update (AArch64_FullTranslateWithTag vaddress acctype iswrite wasaligned sz iswritevalidcap)"
  by (rule no_state_updateI, no_reads_from_any_gpr, no_reg_writes_toI)

lemma pre_post_AArch64_TranslateAddress:
  "pre_post_ignore_fail
     (\<lambda>s. \<forall>addrdesc. IsFault addrdesc \<or> translate_address (unat vaddress) = Some (unat (FullAddress_address (AddressDescriptor_paddress addrdesc))) \<longrightarrow> Q addrdesc s)
     (AArch64_TranslateAddress vaddress acctype iswrite wasaligned sz) Q E"
  apply (rule pre_post_ignore_fail_no_state_update_no_exception[THEN pre_post_strengthen_pre])
  apply (auto simp: AArch64_TranslateAddress_def AArch64_TranslateAddressWithTag_def intro!: no_state_update)[]
  apply (rule monad_no_exception)
  apply (auto dest!: trace_assms_translation_assms_trace dest: AArch64_TranslateAddress_translate_address)
  done

lemma pre_post_AArch64_TaggedMemSingle:
  "pre_post_ignore_fail
     (\<lambda>s. (\<forall>bytes tag paddr. translate_address (unat vaddr) = Some paddr \<longrightarrow> Q (tag :: 1 word, bytes :: 128 word) (s\<lparr>mem_caps := insert (paddr, word_cat tag bytes) (mem_caps s)\<rparr>)) \<and> pcc_writes s = [] \<and> idc_writes s = [])
     (AArch64_TaggedMemSingle vaddr CAPABILITY_DBYTES acctype wasaligned) Q is_expected_exception"
  unfolding AArch64_TaggedMemSingle_def Let_def
  by (pre_postI_with \<open>-\<close> \<open>pre_post_ignore_fail_no_state_update_no_exception\<close> intro: pre_post_ReadMem pre_post_ReadTaggedMem pre_post_CheckLoadTagsPermission pre_post_AArch64_Abort pre_post_AArch64_TranslateAddress)
     (auto; fastforce elim: allE[where x = "0 :: 1 word"])

lemma pre_post_CapabilityFromData:
  "pre_post_ignore_fail
     (\<lambda>s. Q (word_cat (tag :: 1 word) (data :: 128 word) :: 129 word) s)
     (CapabilityFromData CAPABILITY_DBITS tag data) Q E"
  unfolding CapabilityFromData_def Let_def
  by (pre_postI_with \<open>-\<close> \<open>pre_post_ignore_fail_no_state_update_no_exception\<close>)
     (auto simp: Capability_of_tag_word_def of_bl_0th_eq)

lemma pre_post_MemC_read:
  "pre_post_ignore_fail
     (\<lambda>s. (\<forall>paddr c. translate_address (unat vaddr) = Some paddr \<longrightarrow>
            Q c (s\<lparr>mem_caps := insert (paddr, c) (mem_caps s)\<rparr>)) \<and> pcc_writes s = [] \<and> idc_writes s = [])
     (MemC_read vaddr acctype) Q is_expected_exception"
  unfolding MemC_read_def Let_def bind_assoc
  by (pre_postI_with \<open>-\<close> \<open>pre_post_ignore_fail_no_state_update_no_exception\<close>
         intro: pre_post_CapabilityFromData pre_post_AArch64_TaggedMemSingle pre_post_CheckCapabilityAlignment)
     (auto simp: of_bl_0th_eq)

lemma MemC_read_points_to_pcc_code[unfolded conj_assoc]:
  "pre_post_ignore_fail
     (\<lambda>s. cap_authorises_load auth (unat addr) 16 \<and> is_VA_of_cap va auth \<and> has_expected_gpr_reads s \<and> mem_caps s = {} \<and> no_branch_writes s \<and> invocation_sentry_pre_idc_write Points_to_PCC auth s)
     (MemC_read addr AccType_NORMAL) (\<lambda>c s. c \<in> original_mem_code_caps s \<and> is_VA_of_cap va auth \<and> invocation_post_load s \<and> no_branch_writes s \<and> invocation_sentry_pre_idc_write Points_to_PCC auth s) is_expected_exception"
  apply (rule pre_post_strengthen_pre)
   apply (rule pre_post_MemC_read)
  apply (auto simp: original_mem_code_caps_def has_expected_loads_def)
  done

lemma MemC_read_points_to_pcc_no_invocation[unfolded conj_assoc]:
  "pre_post_ignore_fail
     (\<lambda>s. (\<exists>auth \<in> load_auth_caps s. cap_authorises_load auth (unat addr) 16) \<and> has_expected_gpr_reads s \<and> mem_caps s = {} \<and> no_branch_writes s \<and> idc_writes s = [] \<and> instr_indirect_sentry_type instr = Some Points_to_PCC \<and> P)
     (MemC_read addr AccType_NORMAL) (\<lambda>c s. c \<in> original_mem_code_caps s \<and> invocation_post_load s \<and> no_branch_writes s \<and> idc_writes s = [] \<and> instr_indirect_sentry_type instr = Some Points_to_PCC \<and> P) is_expected_exception"
  apply (rule pre_post_strengthen_pre)
   apply (rule pre_post_MemC_read)
  apply (auto simp: original_mem_code_caps_def has_expected_loads_def)
  done

lemma pre_post_CheckCapability:
  "pre_post_ignore_fail
     (\<lambda>s. (CapIsTagSet c \<and> \<not>CapIsSealed c \<and> cap_permits requested_perms c \<longrightarrow> Q address s) \<and> pcc_writes s = [] \<and> idc_writes s = [])
     (CheckCapability c address sz requested_perms acctype) Q is_expected_exception"
  unfolding CheckCapability_def Let_def
  by (pre_postI_with \<open>-\<close> \<open>pre_post_ignore_fail_no_state_update_no_exception | auto\<close> intro: pre_post_AArch64_Abort)

lemma pre_post_VACheckAddress:
  fixes va perms Q
  defines "c \<equiv> VirtualAddress_base va"
  defines "c_checks \<equiv> CapIsTagSet c \<and> \<not>CapIsSealed c \<and> cap_permits perms c"
  defines "P \<equiv> \<lambda>s. VirtualAddress_vatype va = VA_Capability \<and> (c_checks \<longrightarrow> Q () s) \<and> pcc_writes s = [] \<and> idc_writes s = []"
  shows "pre_post_ignore_fail P (VACheckAddress va address sz perms acctype) Q is_expected_exception"
  unfolding VACheckAddress_def P_def c_checks_def c_def
  by (pre_postI_with \<open>-\<close> \<open>pre_post_ignore_fail_no_state_update_no_exception\<close>
        intro: pre_post_CheckCapability pre_post_if[OF pre_post_False, where b = "VAIsBits64 va"])
     (auto simp: VAIsBits64_def VAToCapability_def)

lemma VACheckAddress_cap_authorises_load:
  "pre_post_ignore_fail
     (\<lambda>s. is_VA_of_cap base c \<and> P s \<and> pcc_writes s = [] \<and> idc_writes s = [] \<and> nat sz = sz')
     (VACheckAddress base addr sz perms acctype) (\<lambda>_ s. cap_authorises_load c (unat addr) sz' \<and> is_VA_of_cap base c \<and> P s) is_expected_exception"
  apply (rule pre_post_VACheckAddress[THEN pre_post_strengthen_pre])
  apply (auto simp: is_VA_of_cap_def cap_authorises_load_def)
  done

lemma VACheckAddress_cap_authorises_load':
  "pre_post_ignore_fail
     (\<lambda>s. (\<exists>c \<in> load_auth_caps s. is_VA_of_cap base c) \<and> P s \<and> pcc_writes s = [] \<and> idc_writes s = [] \<and> nat sz = sz')
     (VACheckAddress base addr sz perms acctype) (\<lambda>_ s. (\<exists>c \<in> load_auth_caps s. cap_authorises_load c (unat addr) sz') \<and> P s) is_expected_exception"
  apply (rule pre_post_VACheckAddress[THEN pre_post_strengthen_pre])
  apply (auto simp: is_VA_of_cap_def cap_authorises_load_def)
  done

lemma VAFromCapability_sentry_is_VA_of_cap:
  "pre_post_ignore_fail
     (\<lambda>s. Q s \<and> (sentry \<longrightarrow> (\<exists>n. instr_invokes_indirect_cap_from_reg instr = Some n \<and> get_indirect_sentry_type c = instr_indirect_sentry_type instr))) (VAFromCapability (if sentry then CapUnseal c else c)) (\<lambda>va s. is_VA_of_cap va c \<and> Q s) E"
  unfolding VAFromCapability_def Let_def
  apply (pre_postI_with \<open>-\<close> \<open>fail\<close>)
   apply (pre_post_ignore_fail_no_state_update_no_exception)
  apply (auto simp: is_VA_of_cap_def)
  done

lemma VAFromCapability_is_VA_of_cap:
  "pre_post_ignore_fail
     (\<lambda>s. P s \<and> c \<in> load_auth_caps s) (VAFromCapability c) (\<lambda>va s. (\<exists>c \<in> load_auth_caps s. is_VA_of_cap va c) \<and> P s) E"
  unfolding VAFromCapability_def Let_def
  apply (pre_postI_with \<open>-\<close> \<open>fail\<close>)
   apply (pre_post_ignore_fail_no_state_update_no_exception)
  apply (auto simp: is_VA_of_cap_def)
  done

lemma step_state_ProcState_eq:
  "step_state s (E_read_reg r (Regval_ProcState v)) = s"
  by simp

lemma ev_reads_invocation_regs_from_initial_reg_stateD:
  assumes "ev_reads_invocation_regs_from_initial_reg_state s (E_read_reg r v)"
    and "\<not>invocation_regs_written s"
    and "invocation_regs \<subseteq> dom (reg_state s)"
    and "r \<in> invocation_regs"
  shows "reg_state s r = Some v"
  using assms
  by (auto simp: ev_reads_invocation_regs_from_initial_reg_state_def)

definition
  "reg_state_has_PSTATE_SP s \<equiv>
     (case reg_state s ''PSTATE'' of Some (Regval_ProcState ps) \<Rightarrow> ProcState_SP ps = 1 | _ \<Rightarrow> False)"

definition
  "reg_state_is_in_restricted s \<equiv>
     (case reg_state s ''PCC'' of Some (Regval_bitvector_129_dec c) \<Rightarrow> \<not>CapIsExecutive c | _ \<Rightarrow> True)"

definition
  "EL_of_reg_state s \<equiv>
     (case reg_state s ''PSTATE'' of Some (Regval_ProcState ps) \<Rightarrow> ProcState_EL ps | _ \<Rightarrow> EL0)"

definition
  "SP_of_reg_state s \<equiv>
     (if reg_state_is_in_restricted s then ''RSP_EL0''
      else if \<not>reg_state_has_PSTATE_SP s then ''SP_EL0''
      else if EL_of_reg_state s = EL0 then ''SP_EL0''
      else if EL_of_reg_state s = EL1 then ''SP_EL1''
      else if EL_of_reg_state s = EL2 then ''SP_EL2''
      else ''SP_EL3'')"

definition
  "get_initial_SP_cap s \<equiv>
     (case reg_state s (SP_of_reg_state s) of Some (Regval_bitvector_129_dec c) \<Rightarrow> c | _ \<Rightarrow> undefined)"

lemmas get_initial_SP_cap_defs = get_initial_SP_cap_def SP_of_reg_state_def reg_state_is_in_restricted_def
  reg_state_has_PSTATE_SP_def EL_of_reg_state_def

lemma get_initial_SP_cap_cong:
  "reg_state s = reg_state s' \<Longrightarrow> get_initial_SP_cap s = get_initial_SP_cap s'"
  by (auto simp: get_initial_SP_cap_defs)

lemma pre_post_read_reg_PSTATE':
  "pre_post_ignore_fail
     (\<lambda>s. (\<forall>ps. translation_el AccType_NORMAL = ProcState_EL ps
                \<and> (\<not>invocation_regs_written s \<and> invocation_regs \<subseteq> dom (reg_state s)
                     \<longrightarrow> reg_state s ''PSTATE'' = Some (Regval_ProcState ps) \<and>
                         ProcState_SP ps = (if reg_state_has_PSTATE_SP s then 1 else 0) \<and>
                         ProcState_EL ps = EL_of_reg_state s)
                \<longrightarrow> Q ps s))
     (read_reg PSTATE_ref :: ProcState M) Q E"
   (is "pre_post_ignore_fail ?P _ _ _")
proof (rule pre_postI)
  fix s t ps
  assume ps: "Run (read_reg PSTATE_ref :: ProcState M) t ps" and P: "?P s" and t: "trace_assms s t"
  have PSTATE: "''PSTATE'' \<in> invocation_regs"
    by (auto simp: invocation_regs_def)
  from ps P t show "Q ps (run_state s t)"
    using read_reg_PSTATE_translation_el[OF ps t[THEN trace_assms_translation_assms_trace], where acctype = AccType_NORMAL]
    by (cases "ProcState_SP ps" rule: exhaustive_1_word)
       (auto simp: register_defs reg_state_has_PSTATE_SP_def EL_of_reg_state_def
                   ev_reads_invocation_regs_from_initial_reg_stateD[OF _ _ _ PSTATE]
             elim!: Run_read_regE)
next
  fix s t e
  assume "(read_reg PSTATE_ref :: ProcState M, t, Exception e) \<in> Traces"
  then show "E e (run_state s t)"
    by (auto simp: read_reg_def elim: Traces_cases split: option.splits)
qed auto

lemmas EL_defs = EL0_def EL1_def EL2_def EL3_def

lemmas is_reg_defs = is_code_reg_def is_data_reg_def is_load_auth_reg_def

lemma neq_1_word_iff:
  "(w :: 1 word) \<noteq> 1 \<longleftrightarrow> w = 0"
  "(w :: 1 word) \<noteq> 0 \<longleftrightarrow> w = 1"
  by (cases w rule: exhaustive_1_word; auto)+

lemma PCC_no_gpr[simp]:
  "is_code_reg ''PCC'' \<longleftrightarrow> False"
  "is_data_reg ''PCC'' \<longleftrightarrow> False"
  "is_load_auth_reg ''PCC'' \<longleftrightarrow> False"
  "''PCC'' \<in> all_R_names \<longleftrightarrow> False"
  by (auto simp: is_reg_defs all_R_names_def dest!: R_name_in_all_R_names)

lemma invocation_regsI[simp]:
  "r \<in> all_R_names \<Longrightarrow> r \<in> invocation_regs"
  "''PCC'' \<in> invocation_regs"
  "''PSTATE'' \<in> invocation_regs"
  "''__BranchTaken'' \<in> invocation_regs"
  "''RSP_EL0'' \<in> invocation_regs"
  "''SP_EL0'' \<in> invocation_regs"
  "''SP_EL1'' \<in> invocation_regs"
  "''SP_EL2'' \<in> invocation_regs"
  "''SP_EL3'' \<in> invocation_regs"
  by (auto simp: invocation_regs_def all_R_names_def)

lemmas ev_reads_invocation_regs_from_initial_reg_state_instancesD =
  invocation_regsI(2-)[THEN ev_reads_invocation_regs_from_initial_reg_stateD[rotated 3]]

lemma Halted_False:
  assumes "Run (Halted u) t a" and "trace_assms s t"
  shows "\<not>a"
  using assms
  by (auto simp: Halted_def debug_disabled_read_reg_iff register_defs
           elim!: Run_bindE Run_or_boolM_E Run_read_regE)

lemma pre_post_IsInRestricted:
  "pre_post_ignore_fail
     (\<lambda>s. Q (reg_state_is_in_restricted s) s \<and> \<not>invocation_regs_written s \<and> invocation_regs \<subseteq> dom (reg_state s))
     (IsInRestricted u) Q E"
  unfolding IsInRestricted_def PCC_read_def
  by (pre_postI_with \<open>-\<close> \<open>pre_post_ignore_fail_no_state_update_no_exception\<close> intro: pre_post_read_reg)
     (auto simp: reg_state_is_in_restricted_def register_defs ev_reads_invocation_regs_from_initial_reg_state_instancesD
              dest: Halted_False split: option.splits)

abbreviation "add_load_auth_cap c s \<equiv> s\<lparr>load_auth_caps := insert c (load_auth_caps s)\<rparr>"

lemma instr_load_auth_no_reg_caps:
  assumes "instr_load_auth instr = Some auth"
  shows "instr_invokes_code_cap_from_reg instr = None"
    and "instr_invokes_data_cap_from_reg instr = None"
  using assms
  by (auto elim: instr_load_auth.elims)

lemma pre_post_read_reg_RSP_EL0:
  "pre_post_ignore_fail
     (\<lambda>s. Q (get_initial_SP_cap s) (add_load_auth_cap (get_initial_SP_cap s) s) \<and>
          \<not>invocation_regs_written s \<and> invocation_regs \<subseteq> dom (reg_state s) \<and>
          reg_state_is_in_restricted s \<and>
          instr_load_auth instr = Some (RegAuth 31))
     (read_reg RSP_EL0_ref :: Capability M) Q E"
  by (rule pre_post_read_reg[THEN pre_post_strengthen_pre])
     (auto simp: is_reg_defs get_initial_SP_cap_def SP_of_reg_state_def instr_load_auth_no_reg_caps
                    R_name_def register_defs ev_reads_invocation_regs_from_initial_reg_state_instancesD
           split: option.splits)

lemma pre_post_read_reg_SP_EL0:
  "pre_post_ignore_fail
     (\<lambda>s. Q (get_initial_SP_cap s) (add_load_auth_cap (get_initial_SP_cap s) s) \<and>
          \<not>invocation_regs_written s \<and> invocation_regs \<subseteq> dom (reg_state s) \<and>
          \<not>reg_state_is_in_restricted s \<and> (reg_state_has_PSTATE_SP s \<longrightarrow> EL_of_reg_state s = EL0) \<and>
          instr_load_auth instr = Some (RegAuth 31))
     (read_reg SP_EL0_ref :: Capability M) Q E"
  by (rule pre_post_read_reg[THEN pre_post_strengthen_pre])
     (auto simp: is_reg_defs get_initial_SP_cap_def SP_of_reg_state_def instr_load_auth_no_reg_caps
                    R_name_def register_defs ev_reads_invocation_regs_from_initial_reg_state_instancesD
           split: option.splits if_splits)

lemma pre_post_read_reg_SP_EL1:
  "pre_post_ignore_fail
     (\<lambda>s. Q (get_initial_SP_cap s) (add_load_auth_cap (get_initial_SP_cap s) s) \<and>
          \<not>invocation_regs_written s \<and> invocation_regs \<subseteq> dom (reg_state s) \<and>
          \<not>reg_state_is_in_restricted s \<and> reg_state_has_PSTATE_SP s \<and> EL_of_reg_state s = EL1 \<and>
          instr_load_auth instr = Some (RegAuth 31))
     (read_reg SP_EL1_ref :: Capability M) Q E"
  by (rule pre_post_read_reg[THEN pre_post_strengthen_pre])
     (auto simp: is_reg_defs get_initial_SP_cap_def SP_of_reg_state_def instr_load_auth_no_reg_caps EL_defs
                    R_name_def register_defs ev_reads_invocation_regs_from_initial_reg_state_instancesD
           split: option.splits if_splits)

lemma pre_post_read_reg_SP_EL2:
  "pre_post_ignore_fail
     (\<lambda>s. Q (get_initial_SP_cap s) (add_load_auth_cap (get_initial_SP_cap s) s) \<and>
          \<not>invocation_regs_written s \<and> invocation_regs \<subseteq> dom (reg_state s) \<and>
          \<not>reg_state_is_in_restricted s \<and> reg_state_has_PSTATE_SP s \<and> EL_of_reg_state s = EL2 \<and>
          instr_load_auth instr = Some (RegAuth 31))
     (read_reg SP_EL2_ref :: Capability M) Q E"
  by (rule pre_post_read_reg[THEN pre_post_strengthen_pre])
     (auto simp: is_reg_defs get_initial_SP_cap_def SP_of_reg_state_def instr_load_auth_no_reg_caps EL_defs
                    R_name_def register_defs ev_reads_invocation_regs_from_initial_reg_state_instancesD
           split: option.splits if_splits)

lemma pre_post_read_reg_SP_EL3:
  "pre_post_ignore_fail
     (\<lambda>s. Q (get_initial_SP_cap s) (add_load_auth_cap (get_initial_SP_cap s) s) \<and>
          \<not>invocation_regs_written s \<and> invocation_regs \<subseteq> dom (reg_state s) \<and>
          \<not>reg_state_is_in_restricted s \<and> reg_state_has_PSTATE_SP s \<and> EL_of_reg_state s = EL3 \<and>
          instr_load_auth instr = Some (RegAuth 31))
     (read_reg SP_EL3_ref :: Capability M) Q E"
  by (rule pre_post_read_reg[THEN pre_post_strengthen_pre])
     (auto simp: is_reg_defs get_initial_SP_cap_def SP_of_reg_state_def instr_load_auth_no_reg_caps EL_defs
                    R_name_def register_defs ev_reads_invocation_regs_from_initial_reg_state_instancesD
           split: option.splits if_splits)

lemmas pre_post_read_reg_SPs = pre_post_read_reg_RSP_EL0 pre_post_read_reg_SP_EL0
  pre_post_read_reg_SP_EL1 pre_post_read_reg_SP_EL2 pre_post_read_reg_SP_EL3

lemma pre_post_CSP_read:
  "pre_post_ignore_fail
     (\<lambda>s. Q (get_initial_SP_cap s) (add_load_auth_cap (get_initial_SP_cap s) s) \<and>
          \<not>invocation_regs_written s \<and> invocation_regs \<subseteq> dom (reg_state s) \<and>
          instr_load_auth instr = Some (RegAuth 31))
     (CSP_read u) Q E"
  unfolding CSP_read_def Let_def
  by (pre_postI_with \<open>-\<close> \<open>pre_post_ignore_fail_no_state_update_no_exception\<close>
          intro: pre_post_IsInRestricted pre_post_read_reg_PSTATE' pre_post_read_reg_SPs)
     (use EL_exhaust_disj[of "translation_el AccType_NORMAL"] in \<open>auto simp: EL_defs\<close>)

lemma pre_post_SP_read:
  "pre_post_ignore_fail
     (\<lambda>s. Q (CapGetValue (get_initial_SP_cap s)) (add_load_auth_cap (get_initial_SP_cap s) s) \<and>
          \<not>invocation_regs_written s \<and> invocation_regs \<subseteq> dom (reg_state s) \<and>
          instr_load_auth instr = Some (RegAuth 31))
     (SP_read 64) Q E"
  unfolding SP_read_def Let_def
  by (pre_postI_with \<open>-\<close> \<open>pre_post_ignore_fail_no_state_update_no_exception\<close>
          intro: pre_post_IsInRestricted pre_post_read_reg_PSTATE' pre_post_read_reg_SPs)
     (use EL_exhaust_disj[of "translation_el AccType_NORMAL"] in \<open>auto simp add: CapGetValue_def EL_defs\<close>)

lemma pre_post_CheckSPAlignment:
  "pre_post_ignore_fail
     (\<lambda>s. Q () (add_load_auth_cap (get_initial_SP_cap s) s) \<and> pcc_writes s = [] \<and> idc_writes s = [] \<and>
          \<not> invocation_regs_written s \<and> invocation_regs \<subseteq> dom (reg_state s) \<and> instr_load_auth instr = Some (RegAuth 31))
     (CheckSPAlignment u) Q is_expected_exception"
  unfolding CheckSPAlignment_def AArch64_SPAlignmentFault_def Let_def
  by (pre_postI_with \<open>-\<close> \<open>pre_post_ignore_fail_no_state_update_no_exception\<close>
         intro: pre_post_SP_read pre_post_read_reg_PSTATE pre_post_read_reg pre_post_AArch64_TakeException)
     (auto simp: register_defs split: option.splits)

lemma pre_post_CSP_or_C_read_load_auth_cap:
  "pre_post_ignore_fail
     (\<lambda>s. (\<forall>c. Q c (s\<lparr>load_auth_caps := insert c (load_auth_caps s)\<rparr>)) \<and>
          pcc_writes s = [] \<and> idc_writes s = [] \<and> \<not>invocation_regs_written s \<and>
          invocation_regs \<subseteq> dom (reg_state s) \<and> instr_load_auth instr = Some (RegAuth n))
     (if n = 31 then bind (CheckSPAlignment ()) (\<lambda>_. CSP_read ()) else C_read n)
     Q is_expected_exception"
  apply (rule pre_post_strengthen_pre)
  apply (pre_post_step)
    apply (pre_post_step)
     apply (rule pre_post_CSP_read)
    apply (rule pre_post_CheckSPAlignment)
   apply (rule pre_post_C_read)
  apply (auto simp: is_reg_defs instr_load_auth_no_reg_caps cong: get_initial_SP_cap_cong)
  done

lemma pre_post_C_set_30_invocation_post_final_mem[unfolded conj_assoc]:
  "pre_post_ignore_fail
     (\<lambda>s. invocation_post_idc pcc_tagged s \<and> invocation_pre_final_mem c' s)
     (C_set 30 c) (\<lambda>_ s. invocation_post_idc pcc_tagged s \<and> invocation_pre_final_mem c' s) E"
  by (rule pre_post_strengthen_pre, rule pre_post_C_set_30)
     (auto simp: has_expected_gpr_reads_def performs_expected_idc_write_def
           cong: is_branch_target_cong invoked_data_caps_cong has_expected_loads_cong
                 has_load_cap_perm_if_needed_cong is_unsealed_mem_branch_target_cong)

lemma pre_post_execute_BR_CI_C:
  "pre_post_ignore_fail
     (\<lambda>s. \<exists>regs imm7 Cn. s = init_null_caps (initial_invocation_state regs) \<and> instr = Instr_BR_CI_C (imm7, Cn) \<and> uint Cn = n \<and> invocation_regs \<subseteq> dom regs)
     (execute_BR_CI_C branch_type n offset) (\<lambda>_ s. invocation_post_final s) is_expected_exception"
  unfolding execute_BR_CI_C_def Let_def bind_assoc conj_assoc
  by (pre_postI_with \<open>unfold conj_assoc\<close>
        \<open>pre_post_ignore_fail_no_state_update_no_exception
         | solves \<open>auto simp: init_null_caps_def has_expected_gpr_reads_def\<close>\<close>
        intro: BranchXToCapability_if_unseal_untag_invocation_post_final_mem pre_post_if_post_collapse
               pre_post_C_set_29_indirect_pcc_sentry_invocation_post_idc
               CapSquashPostLoadCap_sentry_mem_branch_target MemC_read_points_to_pcc_code
               VACheckAddress_cap_authorises_load VAFromCapability_sentry_is_VA_of_cap
               CapSquashPostLoadCap_points_to_pcc_no_invocation MemC_read_points_to_pcc_no_invocation
               VACheckAddress_cap_authorises_load' VAFromCapability_is_VA_of_cap
               pre_post_CSP_or_C_read_load_auth_cap pre_post_CheckCapabilitiesEnabled)

lemma pre_post_execute_BLR_CI_C:
  "pre_post_ignore_fail
     (\<lambda>s. \<exists>regs imm7 Cn. s = init_null_caps (initial_invocation_state regs) \<and> instr = Instr_BLR_CI_C (imm7, Cn) \<and> uint Cn = n \<and> invocation_regs \<subseteq> dom regs)
     (execute_BLR_CI_C branch_type n offset) (\<lambda>_ s. invocation_post_final s) is_expected_exception"
  unfolding execute_BLR_CI_C_def Let_def bind_assoc conj_assoc ConstrainUnpredictable.simps bind_return Constraint.simps
  (* TODO: Support \<open>Error_Undefined\<close>, or use hard-coded definition of \<open>ConstrainUnpredictable\<close> *)
  by (pre_postI_with \<open>unfold conj_assoc\<close>
        \<open>pre_post_ignore_fail_no_state_update_no_exception
         | solves \<open>auto simp: init_null_caps_def has_expected_gpr_reads_def\<close>\<close>
        intro: BranchXToCapability_if_unseal_untag_invocation_post_final_mem pre_post_if_post_collapse
               pre_post_C_set_30_invocation_post_final_mem
               pre_post_C_set_29_indirect_pcc_sentry_invocation_post_idc
               CapSquashPostLoadCap_sentry_mem_branch_target MemC_read_points_to_pcc_code
               VACheckAddress_cap_authorises_load VAFromCapability_sentry_is_VA_of_cap
               CapSquashPostLoadCap_points_to_pcc_no_invocation MemC_read_points_to_pcc_no_invocation
               VACheckAddress_cap_authorises_load' VAFromCapability_is_VA_of_cap
               pre_post_CSP_or_C_read_load_auth_cap pre_post_CheckCapabilitiesEnabled)

definition is_squashed_cap :: "bool \<Rightarrow> Capability \<Rightarrow> Capability \<Rightarrow> bool" where
  "is_squashed_cap cap_perm c c' \<equiv>
     (let c = if cap_perm then c else CapWithTagClear c in
      c' = c \<or> (\<not>CapIsSealed c \<and> c' = clear_perm mutable_perms c))"

lemma is_squashed_capI:
  "cap_perm \<Longrightarrow> is_squashed_cap cap_perm c c"
  "cap_perm \<Longrightarrow> \<not>CapIsSealed c \<Longrightarrow> is_squashed_cap cap_perm c (clear_perm mutable_perms c)"
  "\<not>cap_perm \<Longrightarrow> is_squashed_cap cap_perm c (CapWithTagClear c)"
  "\<not>cap_perm \<Longrightarrow> \<not>CapIsSealed c \<Longrightarrow> is_squashed_cap cap_perm c (clear_perm mutable_perms (CapWithTagClear c))"
  by (auto simp: is_squashed_cap_def)

abbreviation VA_has_load_cap_perm :: "VirtualAddress \<Rightarrow> bool" where
  "VA_has_load_cap_perm va \<equiv>
   VirtualAddress_vatype va = VA_Capability \<longrightarrow> cap_permits CAP_PERM_LOAD_CAP (VirtualAddress_base va)"

lemma pre_post_CapSquashPostLoadCap_is_squashed_cap:
  "pre_post_ignore_fail (\<lambda>s. \<forall>c'. VirtualAddress_vatype addr = VA_Capability \<and> (is_squashed_cap (VA_has_load_cap_perm addr) c c' \<longrightarrow> Q c' s)) (CapSquashPostLoadCap c addr) Q E"
  by (rule pre_post_strengthen_pre, pre_post_ignore_fail_no_state_update_no_exception)
     (auto simp: CapSquashPostLoadCap_def VAIsBits64_def VAIsCapability_def VAToCapability_def elim!: Run_bindE;
      auto intro: is_squashed_capI simp: Let_def)

lemma pre_post_VAddress:
  "pre_post_ignore_fail
     (\<lambda>s. \<forall>addr. (VirtualAddress_vatype va = VA_Capability \<longrightarrow> addr = CapGetValue (VirtualAddress_base va)) \<longrightarrow> Q addr s)
     (VAddress va) Q E"
  by (rule pre_post_strengthen_pre, pre_post_ignore_fail_no_state_update_no_exception)
     (cases "VirtualAddress_vatype va = VA_Capability";
      auto simp: VAddress_def VAIsBits64_def VAToCapability_def elim!: Run_bindE split: if_splits)

lemma pre_post_VAFromCapability:
  "pre_post_ignore_fail (\<lambda>s. \<forall>va. VirtualAddress_vatype va = VA_Capability \<and> VirtualAddress_base va = c \<longrightarrow> Q va s) (VAFromCapability c) Q E"
  by (rule pre_post_strengthen_pre, pre_post_ignore_fail_no_state_update_no_exception)
     (auto simp: VAFromCapability_def)

lemma has_load_cap_perm_if_needed_False[intro, simp]:
  "has_load_cap_perm_if_needed False s"
  by (auto simp: has_load_cap_perm_if_needed_def)

lemma performs_expected_idc_write_simps[simp]:
  "performs_expected_idc_write pcc_tagged (s\<lparr>invocation_regs_written := True\<rparr>) \<longleftrightarrow> performs_expected_idc_write pcc_tagged s"
  by (auto simp: performs_expected_idc_write_def cong: invoked_data_caps_cong)

lemma is_squashed_cap_mem_data_caps:
  "is_squashed_cap cap_perm c c' \<Longrightarrow> cap_perm \<Longrightarrow> c' \<in> mem_data_caps c"
  by (auto simp: is_squashed_cap_def mem_data_caps_def)

lemma performs_expected_idc_write_pair_sentry:
  assumes "instr_indirect_sentry_type instr = Some Points_to_Pair"
    and "\<exists>auth \<in> load_auth_caps s. \<exists>(paddr, cd) \<in> mem_caps s. is_squashed_cap cap_perm cd cd' \<and> translate_address (unat (CapGetValue auth)) = Some paddr"
    and cc: "\<exists>cc. is_squashed_cap cap_perm cc cc'"
    and "idc_writes s = []"
  shows "performs_expected_idc_write (cc' !! 128) (add_idc_write cd' s)"
proof -
  have cap_perm if "cc' !! 128"
    using cc that
    by (auto simp: is_squashed_cap_def word_eq_iff Let_def split: if_splits)
  then show ?thesis
    using assms is_squashed_cap_mem_data_caps[of cap_perm _ cd']
    by (fastforce simp: performs_expected_idc_write_def invoked_data_caps_def original_mem_data_caps_def original_reg_data_caps_def)
qed

lemma performs_expected_idc_write_pair_sentry_no_invocation:
  assumes "instr_indirect_sentry_type instr = Some Points_to_Pair"
    and "instr_invokes_indirect_cap_from_reg instr = None"
  shows "performs_expected_idc_write pcc_tagged s"
proof -
  from assms have "invoked_data_caps s = {}"
    by (auto simp: invoked_data_caps_def original_reg_data_caps_def original_mem_data_caps_def)
  then show ?thesis
    by (auto simp: performs_expected_idc_write_def)
qed

lemma has_load_cap_perm_if_needed_mem:
  assumes "\<exists>auth \<in> load_auth_caps s. \<exists>cc. is_squashed_cap (cap_permits CAP_PERM_LOAD_CAP auth) cc cc'"
  shows "has_load_cap_perm_if_needed (cc' !! 128) s"
  using assms
  by (auto simp: has_load_cap_perm_if_needed_def is_squashed_cap_def word_eq_iff Let_def split: if_splits)

lemma (in Morello_ISA) instr_indirect_sentry_type_Points_to_Pair_simps:
  assumes "instr_indirect_sentry_type instr = Some Points_to_Pair"
  shows "instr_invokes_code_cap_from_reg instr = None"
    and "instr_invokes_data_cap_from_reg instr = None"
  using assms
  by (auto elim: instr_indirect_sentry_type.elims)

lemma has_expected_gpr_reads_indirect_pair:
  assumes "instr_indirect_sentry_type instr = Some Points_to_Pair"
    and "\<exists>c. load_auth_caps s = {c}"
    and "\<not>gpr_reads_after_write s"
  shows "has_expected_gpr_reads s"
  using assms
  by (auto simp: has_expected_gpr_reads_def instr_indirect_sentry_type_Points_to_Pair_simps)

lemma is_unsealed_mem_branch_target_indirect_pair:
  assumes "\<exists>auth \<in> load_auth_caps s. \<exists>(paddr, cc) \<in> mem_caps s. \<exists>cap_perm.
             is_squashed_cap cap_perm cc cc' \<and> translate_address (unat (CapGetValue auth + 16)) = Some paddr"
  shows "is_unsealed_mem_branch_target cc' s"
  using assms
  by (fastforce simp: is_unsealed_mem_branch_target_def original_mem_code_caps_def is_squashed_cap_def is_sentry_def CapIsSealed_def Let_def)

lemma pre_post_execute_LDPBR_C_C_C:
  "pre_post_ignore_fail
     (\<lambda>s. \<exists>regs opc Cn Ct. s = init_null_caps (initial_invocation_state regs) \<and> instr_indirect_sentry_type instr = Some Points_to_Pair \<and> instr_invokes_indirect_cap_from_reg instr = (if t = 29 then Some n else None) \<and> instr_load_auth instr = Some (RegAuth n) \<and> invocation_regs \<subseteq> dom regs)
     (execute_LDPBR_C_C_C branch_type n t) (\<lambda>_ s. invocation_post_final s) is_expected_exception"
  unfolding execute_LDPBR_C_C_C_def Let_def bind_assoc conj_assoc
  by (pre_postI_with \<open>-\<close>
        \<open>pre_post_ignore_fail_no_state_update_no_exception
         | auto simp: CapUnseal_get_bounds_helpers_eq cap_permits_CapUnseal_iff has_expected_loads_def cap_authorises_load_def\<close>
        intro: BranchXToCapability_if_unseal_untag_invocation_post_final_mem pre_post_if_post_collapse
               pre_post_C_set pre_post_CapSquashPostLoadCap_is_squashed_cap pre_post_MemC_read
               pre_post_VACheckAddress pre_post_VAddress pre_post_VAFromCapability
               pre_post_CSP_or_C_read_load_auth_cap pre_post_CheckCapabilitiesEnabled
               performs_expected_idc_write_pair_sentry performs_expected_idc_write_pair_sentry_no_invocation
               has_load_cap_perm_if_needed_mem has_expected_gpr_reads_indirect_pair
               is_unsealed_mem_branch_target_indirect_pair)

lemma pre_post_execute_LDPBLR_C_C_C:
  "pre_post_ignore_fail
     (\<lambda>s. \<exists>regs opc Cn Ct. s = init_null_caps (initial_invocation_state regs) \<and> instr_indirect_sentry_type instr = Some Points_to_Pair \<and> instr_invokes_indirect_cap_from_reg instr = (if t = 29 then Some n else None) \<and> instr_load_auth instr = Some (RegAuth n) \<and> uint Cn = n \<and> uint Ct = t \<and> invocation_regs \<subseteq> dom regs)
     (execute_LDPBLR_C_C_C branch_type n t) (\<lambda>_ s. invocation_post_final s) is_expected_exception"
  unfolding execute_LDPBLR_C_C_C_def Let_def bind_assoc conj_assoc ConstrainUnpredictable.simps bind_return Constraint.simps
  (* TODO: Support \<open>Error_Undefined\<close>, or use hard-coded definition of \<open>ConstrainUnpredictable\<close> *)
  by (pre_postI_with \<open>-\<close>
        \<open>pre_post_ignore_fail_no_state_update_no_exception | clarsimp
         | auto simp: CapUnseal_get_bounds_helpers_eq cap_permits_CapUnseal_iff has_expected_loads_def cap_authorises_load_def\<close>
        intro: BranchXToCapability_if_unseal_untag_invocation_post_final_mem pre_post_if_post_collapse
               pre_post_C_set pre_post_CapSquashPostLoadCap_is_squashed_cap pre_post_MemC_read
               pre_post_VACheckAddress pre_post_VAddress pre_post_VAFromCapability
               pre_post_CSP_or_C_read_load_auth_cap pre_post_CheckCapabilitiesEnabled
               performs_expected_idc_write_pair_sentry performs_expected_idc_write_pair_sentry_no_invocation
               has_load_cap_perm_if_needed_mem has_expected_gpr_reads_indirect_pair
               is_unsealed_mem_branch_target_indirect_pair conjI impI allI)

lemmas prepost_invocation_executes =
  pre_post_execute_BRS_C_C_C pre_post_execute_BRS_C_C pre_post_execute_BLRR_C_C pre_post_execute_BLRS_C_C
  pre_post_execute_BLRS_C_C_C pre_post_execute_BLR_C_C pre_post_execute_BRR_C_C pre_post_execute_BR_C_C
  pre_post_execute_RETR_C_C pre_post_execute_RETS_C_C pre_post_execute_RETS_C_C_C pre_post_execute_RET_C_C
  pre_post_execute_BLR_CI_C pre_post_execute_BR_CI_C pre_post_execute_LDPBLR_C_C_C pre_post_execute_LDPBR_C_C_C

lemma get_reg_val_has_R_names: "invocation_regs \<subseteq> dom (\<lambda>r. get_regval r s)"
  by (auto simp: invocation_regs_def all_R_names_def register_defs)

lemma get_regval_invocation_regs: "r \<in> invocation_regs \<Longrightarrow> \<exists>v. get_regval r (regstate s) = Some v"
  by (auto simp: invocation_regs_def all_R_names_def register_defs)

abbreviation "initial_invocation_from_seq_state s \<equiv> init_null_caps (initial_invocation_state (restrict_map (\<lambda>r. get_regval r (regstate s)) invocation_regs))"

lemma pre_post_DecodeA64:
  assumes "instr_of_exp (DecodeA64 pc opcode) = Some instr" (is "?assm (DecodeA64 pc opcode)")
    and "instr_may_invoke"
  shows "pre_post_ignore_fail
           (\<lambda>s. s = initial_invocation_from_seq_state seq_s)
           (DecodeA64 pc opcode)
           (\<lambda>_ s. invocation_post_final s) is_expected_exception" (is "pre_post_ignore_fail ?P _ ?Q ?E")
proof -
  let ?goal = "\<lambda>m. pre_post_ignore_fail ?P m ?Q ?E"
  have ifE: "?goal (if b then m1 else m2)"
    if "?assm (if b then m1 else m2)"
    and "?assm m1 \<Longrightarrow> ?goal m1" and "?assm m2 \<Longrightarrow> ?goal m2" for b m1 m2
    by (use that in auto)
  have no_instr: "?goal m" if "?assm m" and "no_reg_writes_to {''__ThisInstrAbstract''} m" for m
    using that(1) that(2)[THEN no_reg_writes_to_instr_of_exp]
    by auto
  have write_instr_simp: "instr = instr'" if "?assm (seq (write_reg ThisInstrAbstract_ref instr') m)" for m instr'
    by (use that in simp)
  have write_instr: "?goal (seq (write_reg ThisInstrAbstract_ref instr') m)"
    if "?assm (seq (write_reg ThisInstrAbstract_ref instr') m)"
    and "instr = instr' \<Longrightarrow> ?goal m"
    for instr' m
    by (pre_postI_with \<open>-\<close> \<open>solves \<open>use that in \<open>simp add: register_defs all_R_names_def invocation_regs_def\<close>\<close>\<close>
          intro: that write_instr_simp[OF that(1)] pre_post_write_reg)
  from assms show ?thesis
    by -
       (unfold DecodeA64_def Let_def invocation_decode_defs, elim ifE,
        ((erule write_instr, rule prepost_invocation_executes[THEN pre_post_strengthen_pre],
          solves \<open>unfold init_null_caps_def initial_invocation_state_def, auto intro: get_regval_invocation_regs\<close>)
          | (erule write_instr, solves \<open>simp\<close>)
          | (erule no_instr, solves \<open>no_reg_writes_toI\<close>))+)
qed

lemma pre_post_instr_sem:
  assumes "instr_of_exp (instr_sem opcode) = Some instr"
    and "instr_may_invoke"
  shows "pre_post_ignore_fail
           (\<lambda>s. s = initial_invocation_from_seq_state seq_s)
           (instr_sem opcode)
           (\<lambda>_ s. invocation_post_final s) is_expected_exception"
  (* TODO: Thread through value of ''__BranchTaken'' into Step_PC to make sure that
     the latter doesn't write to PCC again *)
  sorry

lemma ev_reads_invocation_regs_from_initial_reg_stateI:
  assumes "\<not>invocation_regs_written s \<longrightarrow> (\<forall>r \<in> invocation_regs. \<forall>v. e = E_read_reg r v \<longrightarrow> reg_state s r = Some v)"
  shows "ev_reads_invocation_regs_from_initial_reg_state s e"
  using assms
  by (cases e) (auto simp: ev_reads_invocation_regs_from_initial_reg_state_def restrict_map_def split: option.splits)

lemma reg_state_step_state[simp]: "reg_state (step_state s e) = reg_state s"
  by (cases "(s, e)" rule: step_state.cases) (auto split: option.split)

lemma s_run_trace_trace_assms:
  assumes "s_run_trace t seq_s = Some seq_s'"
    and "\<not>invocation_regs_written s \<longrightarrow> reg_state s = restrict_map (\<lambda>r. get_regval r (regstate seq_s)) invocation_regs"
    and "\<forall>e \<in> set t. translation_assms e"
    and "\<forall>e \<in> set t. debug_disabled e"
  shows "trace_assms s t"
proof (use assms in \<open>induction t arbitrary: s seq_s\<close>)
  case (Cons e t)
  then show ?case
  proof (cases e)
    case (E_read_reg r v)
    have "invocation_regs_written (step_state s (E_read_reg r v)) \<longleftrightarrow> invocation_regs_written s"
      by (cases v) auto
    with Cons E_read_reg show ?thesis
      by (auto simp add: bind_eq_Some_conv simp del: step_state.simps intro: ev_reads_invocation_regs_from_initial_reg_stateI split: if_splits)
  next
    case (E_write_reg r v)
    with Cons.prems obtain regs' where regs': "set_regval r v (regstate seq_s) = Some regs'"
      and t: "s_run_trace t (seq_s\<lparr>regstate := regs'\<rparr>) = Some seq_s'"
      by (auto simp: bind_eq_Some_conv)
    then have invocation_regs_written: "invocation_regs_written (step_state s e) \<longleftrightarrow> invocation_regs_written s \<or> r \<in> invocation_regs"
      by (auto simp: E_write_reg)
    then have "(\<lambda>r. get_regval r (regstate seq_s)) |` invocation_regs = (\<lambda>r. get_regval r regs') |` invocation_regs"
      if "\<not>invocation_regs_written (step_state s e)"
      using regs' that
      by (intro ext) (auto simp: restrict_map_def invocation_regs_def intro: read_ignore_write[OF regs', symmetric])
    then have "trace_assms (step_state s e) t"
      using Cons.prems t invocation_regs_written
      by (intro Cons.IH[of "seq_s\<lparr>regstate := regs'\<rparr>"]) auto
    then show ?thesis
      using Cons.prems E_write_reg
      by (auto simp del: step_state.simps intro: ev_reads_invocation_regs_from_initial_reg_stateI)
  qed (auto simp: bind_eq_Some_conv intro: ev_reads_invocation_regs_from_initial_reg_stateI split: if_splits option.split)
qed auto

(* TODO: Move existing versions of these lemmas into more general context *)
(*lemma (in Morello_ISA) determ_instrs_of_exp_DecodeA64:
  "determ_instr_exp (DecodeA64 pc opcode)"
  by (unfold DecodeA64_def Let_def)
     (intro determ_instr_exp_if_split_no_asm determ_instrs_of_exp_bind_write_reg_ThisInstrAbstract no_reg_writes_to_determ_instrs_of_exp;
            no_reg_writes_toI)

lemma (in Morello_ISA) determ_instrs_instr_sem:
  "determ_instr_exp (instr_sem opcode)"
  unfolding instr_sem_def Step_PC_def
  by (intro determ_instrs_of_exp_DecodeA64[THEN determ_instrs_of_exp_bind_no_reg_writes]; no_reg_writes_toI)*)

lemma (in Morello_ISA) instr_of_exp_instr_of_trace:
  "determ_instr_exp m \<Longrightarrow> instr_of_exp m = Some instr' \<Longrightarrow> hasTrace t m \<Longrightarrow> instr_of_trace t = Some instr'"
  using no_reg_writes_to_instr_of_exp[of m]
  by (auto simp: determ_instr_exp_def hasTrace_iff_Traces_final write_reg_def register_defs
                 instr_of_exp_def instrs_of_exp_def is_singleton_def final_def split: if_splits
           elim!: bind_Traces_cases Write_reg_TracesE)

lemma branch_instr_trace_has_expected_invocationsI:
  assumes "hasTrace t (instr_sem opcode)"
    and s: "s_run_trace t s = Some s'"
    and "\<not>hasFailure t (instr_sem opcode)"
    and "translation_assms_trace t"
    and "\<forall>e \<in> set t. debug_disabled e"
    (* and "cap_inv_trace t" *)
    and instr: "instr_of_exp (instr_sem opcode) = Some instr"
    and "instr_may_invoke"
  shows "branch_instr_trace_has_expected_invocations opcode t"
proof (use assms(1) in \<open>cases rule: hasTrace_cases\<close>)
  case (Run a)
  note instr_t = instr_of_exp_instr_of_trace[OF determ_instrs_instr_sem instr assms(1)]
  have "trace_assms (initial_invocation_from_seq_state s) t"
    using assms(4,5)
    by (intro s_run_trace_trace_assms[OF s]) auto
  then have post: "invocation_post_final (run_state (initial_invocation_from_seq_state s) t)"
    using instr \<open>instr_may_invoke\<close>
    by (intro impI pre_post_RunE[OF pre_post_instr_sem Run]) auto
  have "branch_instr_run_has_expected_gpr_reads t"
    using instr_t \<open>instr_may_invoke\<close> post
    by (intro branch_instr_run_has_expected_gpr_readsI) auto
  moreover have "branch_instr_run_has_expected_invocation_loads t"
    using no_mem_writes_in_exp_instr_sem[OF instr, THEN no_mem_writes_in_trace_of_exp, OF _ assms(1)] post instr_t
    by (intro branch_instr_run_has_expected_invocation_loadsI) auto
  moreover have "branch_instr_run_has_expected_pstate_writes opcode t"
    using post instr_t
    by (intro branch_instr_run_has_expected_pstate_writesI[where s = "initial_invocation_from_seq_state s"]) auto
  ultimately show ?thesis
    using Run
    unfolding branch_instr_trace_has_expected_invocations_def
    unfolding branch_instr_trace_has_expected_exceptions_def
    unfolding runTrace_iff_Traces[symmetric]
    by auto
next
  case (Fail f)
  then show ?thesis
    using assms(3)
    unfolding hasFailure_def runTrace_iff_Traces[symmetric]
    by auto
next
  case (Ex e)
  have trace_assms: "trace_assms (initial_invocation_from_seq_state s) t"
    using assms(4,5)
    by (intro s_run_trace_trace_assms[OF s]) auto
  then have "is_expected_exception e (run_state (initial_invocation_from_seq_state s) t)"
    using Ex pre_post_instr_sem[OF instr \<open>instr_may_invoke\<close>, where seq_s = s]
    by (elim pre_post_ExceptionE) auto
  then have "branch_instr_trace_has_expected_exceptions opcode t"
    using Ex
    by (intro branch_instr_trace_has_expected_exceptionsI[where s = "initial_invocation_from_seq_state s"])
       (auto simp: runTrace_iff_Traces[symmetric])
  then show ?thesis
    using Ex
    unfolding branch_instr_trace_has_expected_invocations_def runTrace_iff_Traces[symmetric]
    by auto
qed

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
    and instr: "instr_of_exp (instr_sem opcode) = Some instr" \<comment> \<open>instruction AST, e.g. @{verbatim Instr_BRS_C_C}, not opcode\<close>
    and "\<not>hasException t (instr_sem opcode)"
    and "\<not>hasFailure t (instr_sem opcode)" \<comment> \<open>ignoring assertion failures\<close>
    and "translation_assms_trace t"
    and "\<forall>e \<in> set t. debug_disabled e"
    and "s_run_trace t s = Some s'"
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
    and "instr_invokes_code_cap_from_reg instr = None"
    and "instr_invokes_data_cap_from_reg instr = None"
    and "trace_reads_initial_caps_from_gpr n t = {c}"
    and "instr_trace_load_auth_caps t = {c}"
    and "instr_indirect_sentry_type instr = Some sentry_type"
    and "\<not>CapIsSealed c"
    (* and "set (address_range (bounds_address AccType_NORMAL vaddr) 16) \<subseteq> get_mem_region CC c" *)
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
    and "instr_invokes_code_cap_from_reg instr = None"
    and "instr_invokes_data_cap_from_reg instr = None"
    and "trace_reads_initial_caps_from_gpr 29 t = {c}"
    and "instr_trace_load_auth_caps t = {c}"
    and "CapIsTagSet c"
    and "CapGetObjectType c = CAP_SEAL_TYPE_LB"
    and "instr_invokes_indirect_caps opcode t = {CapUnseal c}"
    and "translate_address vaddr = Some paddr"
    and "initial_mem_cap_loads_of_trace t = {(paddr, c')}"
    (* and "set (address_range (bounds_address AccType_NORMAL vaddr) 16) \<subseteq> get_mem_region CC c" *)
    and "original_code_caps_invoked_in_trace t = (if CapIsTagSet c' \<and> cap_permits CAP_PERM_LOAD_CAP c then {c'} else {})"
    and "instr_invokes_code_caps opcode t = (if CapIsTagSet c' \<and> cap_permits CAP_PERM_LOAD_CAP c then mem_branch_caps (clear_lsb c') else {})"
    and "instr_invokes_data_caps opcode t = {CapUnseal c}"
  | (IndirectPointsToPair) n c cc cd paddr_cc paddr_cd
    where "instr_invokes_indirect_cap_from_reg instr = Some n"
    and "instr_indirect_sentry_type instr = Some Points_to_Pair"
    and "instr_invokes_code_cap_from_reg instr = None"
    and "instr_invokes_data_cap_from_reg instr = None"
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
    (* and "set (address_range (bounds_address AccType_NORMAL (unat (CapGetValue c))) 32) \<subseteq> get_mem_region CC c" *)
  | (NoInvocation) "instr_invokes_code_caps opcode t = {}"
    and "instr_invokes_data_caps opcode t = {}"
    and "instr_invokes_indirect_caps opcode t = {}"
proof (use instr_of_exp_instr_of_trace[OF determ_instrs_instr_sem instr assms(1)] in
       \<open>cases rule: instr_of_trace_invocation_cases[where opcode = opcode,
          case_names SealedPair' DirectRegSentry' DirectMemSentry' IndirectPointsToPCC' IndirectPointsToPair' NoInvocation']\<close>)
  case (SealedPair' nc nd)
  note instr_t = instr_of_exp_instr_of_trace[OF determ_instrs_instr_sem instr assms(1)]
  interpret Morello_Instr_Invocation_Property where instr = instr ..
  have *: "branch_instr_trace_has_expected_invocations opcode t"
    using SealedPair'
    by (intro branch_instr_trace_has_expected_invocationsI[OF assms(1,7,4,5,6) instr]) auto
  obtain cc where cc: "trace_reads_caps_from_gpr_or_null nc t = {cc}" "trace_reads_initial_caps_from_gpr_or_null nc t = {cc}"
    using * SealedPair' hasTrace_Run[OF assms(1,3,4)] \<open>instr_of_trace t = Some instr\<close>
    by (auto simp: branch_instr_trace_has_expected_invocations_def branch_instr_run_has_expected_gpr_reads_def trace_invokes_code_cap_from_reg_def)
  obtain cd where cd: "trace_reads_caps_from_gpr_or_null nd t = {cd}" "trace_reads_initial_caps_from_gpr_or_null nd t = {cd}"
    using * SealedPair' hasTrace_Run[OF assms(1,3,4)] \<open>instr_of_trace t = Some instr\<close>
    by (auto simp: branch_instr_trace_has_expected_invocations_def branch_instr_run_has_expected_gpr_reads_def trace_invokes_data_cap_from_reg_def)
  show thesis
  proof (cases "invokable CC cc cd")
    case True
    then have "CapIsTagSet cc" and "CapIsTagSet cd"
      by (auto simp: invokable_def)
    then show ?thesis
      using SealedPair' cc cd True
      by (intro SealedPair[of nc nd cc cd])
         (auto simp: image_UN clear_lsb_image_branch_caps_eq trace_reads_caps_from_gpr_or_null_def
                     trace_reads_initial_caps_from_gpr_or_null_def split: if_splits)
  next
    case False
    then show ?thesis
      using SealedPair' cc cd
      by (intro NoInvocation) (auto simp: trace_reads_caps_from_gpr_or_null_def)
  qed
next
  case (DirectRegSentry' n)
  note instr_t = instr_of_exp_instr_of_trace[OF determ_instrs_instr_sem instr assms(1)]
  interpret Morello_Instr_Invocation_Property where instr = instr ..
  have *: "branch_instr_trace_has_expected_invocations opcode t"
    using DirectRegSentry'
    by (intro branch_instr_trace_has_expected_invocationsI[OF assms(1,7,4,5,6) instr]) auto
  obtain c where c: "trace_reads_caps_from_gpr_or_null n t = {c}" "trace_reads_initial_caps_from_gpr_or_null n t = {c}"
    using * DirectRegSentry' hasTrace_Run[OF assms(1,3,4)] \<open>instr_of_trace t = Some instr\<close>
    by (auto simp: branch_instr_trace_has_expected_invocations_def branch_instr_run_has_expected_gpr_reads_def
                   trace_invokes_code_cap_from_reg_def)
  show ?thesis
  proof (cases "CapIsTagSet c \<and> is_sentry c")
    case True
    then show ?thesis
      using DirectRegSentry' c
      by (intro DirectRegSentry[of n c])
         (auto simp: is_sentry_def image_UN clear_lsb_image_branch_caps_eq
                     trace_reads_caps_from_gpr_or_null_def trace_reads_initial_caps_from_gpr_or_null_def
               split: if_splits)
  next
    case False
    then show ?thesis
      using DirectRegSentry' c
      by (intro NoInvocation) (auto simp: trace_reads_caps_from_gpr_or_null_def)
  qed
next
  case (DirectMemSentry' sentry_type)
  note instr_t = instr_of_exp_instr_of_trace[OF determ_instrs_instr_sem instr assms(1)]
  interpret Morello_Instr_Invocation_Property where instr = instr ..
  have *: "branch_instr_trace_has_expected_invocations opcode t"
    using DirectMemSentry'
    by (intro branch_instr_trace_has_expected_invocationsI[OF assms(1,7,4,5,6) instr]) auto
  then have **: "branch_instr_run_has_expected_invocation_loads t"
    using hasTrace_Run[OF assms(1,3,4)]
    by (auto simp: branch_instr_trace_has_expected_invocations_def)
  obtain n where n: "instr_load_auth instr = Some (RegAuth n)"
    and [simp]: "instr_invokes_code_cap_from_reg instr = None"
    and [simp]: "instr_invokes_data_cap_from_reg instr = None"
    by (use \<open>instr_indirect_sentry_type instr = Some sentry_type\<close> in \<open>auto elim!: instr_indirect_sentry_type.elims\<close>)
  then have [simp]: "trace_indirect_sentry_type t = Some sentry_type"
    and [simp]: "trace_load_auths t = Some (RegAuth n)"
    using DirectMemSentry' instr_t
    by (auto simp: trace_indirect_sentry_type_def trace_load_auths_def)
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
        (* and bounds: "set (address_range (bounds_address AccType_NORMAL vaddr) 16) \<subseteq> get_mem_region CC c" *)
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
        using DirectMemSentry'(1,7-9) n c cc False original_code_caps cap_loads Points_to_PCC paddr_cc vaddr (*bounds*) ** instr
        by (intro DirectMemSentry[of n c sentry_type vaddr paddr cc])
           (auto simp add: image_UN clear_lsb_image_branch_caps_eq)
    next
      case Points_to_Pair
      then obtain cc cd paddr_cc paddr_cd
        where initial_loads: "initial_mem_cap_loads_of_trace t = {(paddr_cd, cd), (paddr_cc, cc)}"
        and paddr_cd: "translate_address (unat (CapGetValue c)) = Some paddr_cd"
        and paddr_cc: "translate_address (unat (CapGetValue c + 16)) = Some paddr_cc"
        (* and bounds: "set (address_range (bounds_address AccType_NORMAL (unat (CapGetValue c) + 16)) 16) \<subseteq> get_mem_region CC c" *)
        using ** c
        by (auto simp: branch_instr_run_has_expected_invocation_loads_def trace_has_reg_load_auth_for_addr_def subset_eq)
      have paddr_distinct: "paddr_cd \<noteq> paddr_cc"
        using translate_address_unat_vaddr_offset_paddr_different[OF paddr_cd, where offset = 16] paddr_cc
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
        using DirectMemSentry'(1,8,9) n c initial_loads paddr_cc (*bounds*)
        by (intro DirectMemSentry[of n c sentry_type "unat (CapGetValue c + 16)" paddr_cc cc])
           (auto simp: is_sentry_def)
    qed
  qed
next
  case IndirectPointsToPCC'
  note instr_t = instr_of_exp_instr_of_trace[OF determ_instrs_instr_sem instr assms(1)]
  interpret Morello_Instr_Invocation_Property where instr = instr ..
  have *: "branch_instr_trace_has_expected_invocations opcode t"
    using IndirectPointsToPCC'
    by (intro branch_instr_trace_has_expected_invocationsI[OF assms(1,7,4,5,6) instr]) auto
  then have **: "branch_instr_run_has_expected_invocation_loads t"
    using hasTrace_Run[OF assms(1,3,4)]
    by (auto simp: branch_instr_trace_has_expected_invocations_def)
  from IndirectPointsToPCC' have load_auth: "instr_load_auth instr = Some (RegAuth 29)"
    and [simp]: "instr_invokes_code_cap_from_reg instr = None"
    and [simp]: "instr_invokes_data_cap_from_reg instr = None"
    by (auto elim!: instr_indirect_sentry_type.elims split: if_splits)
  then have [simp]: "trace_indirect_sentry_type t = Some Points_to_PCC"
    and [simp]: "trace_load_auths t = Some (RegAuth 29)"
    using IndirectPointsToPCC' instr_t
    by (auto simp: trace_indirect_sentry_type_def trace_load_auths_def)
  obtain c where c: "trace_reads_caps_from_gpr 29 t = {c}" "trace_reads_initial_caps_from_gpr 29 t = {c}"
                    "CapIsTagSet c" "CapGetObjectType c = CAP_SEAL_TYPE_LB"
    and indirect_sentries: "instr_invokes_indirect_caps opcode t = {CapUnseal c}"
    using IndirectPointsToPCC' * hasTrace_Run[OF assms(1,3,4)] instr_t
    by (auto simp: branch_instr_trace_has_expected_invocations_def branch_instr_run_has_expected_gpr_reads_def)
  then have [simp]: "instr_trace_load_auth_caps t = {c}"
    by (fastforce simp add: instr_trace_load_auth_caps_def trace_reads_caps_from_gpr_def set_eq_iff)
  then have load_cap: "trace_has_cap_load_auth t \<longleftrightarrow> cap_permits CAP_PERM_LOAD_CAP c"
    by (auto simp: trace_has_cap_load_auth_def)
  obtain cc vaddr paddr where paddr_cc: "initial_mem_cap_loads_of_trace t = {(paddr, cc)}"
    and vaddr: "translate_address vaddr = Some paddr"
    and authorised: "trace_has_reg_load_auth_for_addr t c" (* vaddr 16"*)
    using ** load_auth c
    by (auto simp: branch_instr_run_has_expected_invocation_loads_def trace_has_reg_load_auth_for_addr_def)
  then have cap_loads: "mem_cap_loads_of_trace t = (if CapIsTagSet cc then {(paddr, cc)} else {})"
    using **
    by (intro set_eqI; simp add: branch_instr_run_has_expected_invocation_loads_def; fastforce)
  have "original_code_caps_invoked_in_trace t =
          {cc. \<exists>vaddr paddr. (paddr, cc) \<in> mem_cap_loads_of_trace t \<and> translate_address vaddr = Some paddr \<and>
                             cap_permits CAP_PERM_LOAD_CAP c \<and> trace_has_reg_load_auth_for_addr t c}" (* vaddr 16}"*)
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
  note instr_t = instr_of_exp_instr_of_trace[OF determ_instrs_instr_sem instr assms(1)]
  interpret Morello_Instr_Invocation_Property where instr = instr ..
  have *: "branch_instr_trace_has_expected_invocations opcode t"
    using IndirectPointsToPair'
    by (intro branch_instr_trace_has_expected_invocationsI[OF assms(1,7,4,5,6) instr]) auto
  then have **: "branch_instr_run_has_expected_invocation_loads t"
    using hasTrace_Run[OF assms(1,3,4)]
    by (auto simp: branch_instr_trace_has_expected_invocations_def)
  have [simp]: "trace_indirect_sentry_type t = Some Points_to_Pair"
    and [simp]: "trace_load_auths t = Some (RegAuth n)"
    and [simp]: "instr_invokes_code_cap_from_reg instr = None"
    and [simp]: "instr_invokes_data_cap_from_reg instr = None"
    using \<open>instr_invokes_indirect_cap_from_reg instr = Some n\<close> \<open>instr_indirect_sentry_type instr = Some Points_to_Pair\<close> instr_t
    by (auto simp: trace_indirect_sentry_type_def trace_load_auths_def
             elim!: instr_indirect_sentry_type.elims split: if_splits)
  obtain c where c: "trace_reads_caps_from_gpr n t = {c}" "trace_reads_initial_caps_from_gpr n t = {c}"
                    "CapIsTagSet c" "CapGetObjectType c = CAP_SEAL_TYPE_LPB"
    and indirect_sentries: "instr_invokes_indirect_caps opcode t = {CapUnseal c}"
    using IndirectPointsToPair'(1,3,7) * hasTrace_Run[OF assms(1,3,4)] instr
    by (auto simp: branch_instr_trace_has_expected_invocations_def branch_instr_run_has_expected_gpr_reads_def)
  then have [simp]: "instr_trace_load_auth_caps t = {c}"
    by (fastforce simp add: instr_trace_load_auth_caps_def trace_reads_caps_from_gpr_def set_eq_iff)
  then have load_cap: "trace_has_cap_load_auth t \<longleftrightarrow> cap_permits CAP_PERM_LOAD_CAP c"
    by (auto simp: trace_has_cap_load_auth_def)
  obtain cc cd paddr_cc paddr_cd
    where initial_loads: "initial_mem_cap_loads_of_trace t = {(paddr_cd, cd), (paddr_cc, cc)}"
    and paddr_cd: "translate_address (unat (CapGetValue c)) = Some paddr_cd"
    and paddr_cc: "translate_address (unat (CapGetValue c + 16)) = Some paddr_cc"
    and authorised: "trace_has_reg_load_auth_for_addr t c" (* (unat (CapGetValue c)) 32"*)
    (*and no_overflow[simp]:
      "unat (CapGetValue c + 16) = unat (CapGetValue c) + 16"
      "bounds_address AccType_NORMAL (unat (CapGetValue c) + 16) = bounds_address AccType_NORMAL (unat (CapGetValue c)) + 16"*)
    using ** c
    by (auto simp: branch_instr_run_has_expected_invocation_loads_def trace_has_reg_load_auth_for_addr_def subset_eq)
  then have cap_loads:
    "mem_cap_loads_of_trace t =
       (if CapIsTagSet cd then {(paddr_cd, cd)} else {}) \<union>
       (if CapIsTagSet cc then {(paddr_cc, cc)} else {})"
    using **
    by (intro set_eqI; simp add: branch_instr_run_has_expected_invocation_loads_def; fastforce)
  have paddr_distinct: "paddr_cd \<noteq> paddr_cc"
    using translate_address_unat_vaddr_offset_paddr_different[OF paddr_cd, where offset = 16] paddr_cc
    by auto
  have "original_code_caps_invoked_in_trace t = {cc. \<exists>paddr.
          (paddr, cc) \<in> mem_cap_loads_of_trace t \<and> translate_address (unat (CapGetValue c + 16)) = Some paddr \<and>
          cap_permits CAP_PERM_LOAD_CAP c \<and> trace_has_reg_load_auth_for_addr t c}" (* (unat (CapGetValue c + 16)) 16}"*)
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
              cap_permits CAP_PERM_LOAD_CAP c \<and> trace_has_reg_load_auth_for_addr t c}" (* (unat (CapGetValue c)) 16}"*)
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

lemma mem_data_caps_nonempty[simp]:
  "mem_data_caps c \<noteq> {}"
  by (auto simp: mem_data_caps_def)

(* TODO: Move *)
lemma determ_instr_exp_instr_of_exp_None:
  assumes "determ_instr_exp m"
    and "instr_of_exp m = None"
    and "(m, t, m') \<in> Traces"
  shows "instr_of_trace t = None"
  by (use assms in \<open>auto simp: determ_instr_exp_def no_reg_writes_to_instr_of_trace
                         elim: write_reg_ThisInstrAbstract_Traces_instr_of_trace_cases\<close>)

end

context Morello_Instr_Invocation_Property
begin

lemma trace_writes_pcc_caps_eq_pcc_cap_writes:
  "pcc_writes s = [] \<Longrightarrow> trace_writes_pcc_caps ISA (instr_trace opcode t) = pcc_cap_writes (run_state s t)"
  by (auto simp: pcc_cap_writes_run_state trace_writes_pcc_caps_def fold_un_map_eq_Un)

lemma trace_writes_idc_caps_eq_idc_cap_writes:
  "idc_writes s = [] \<Longrightarrow> trace_writes_idc_caps ISA (instr_trace opcode t) = idc_cap_writes (run_state s t)"
  by (auto simp: idc_cap_writes_run_state trace_writes_idc_caps_def fold_un_map_eq_Un)

lemma branch_instr_run_performs_expected_data_invocationI:
  assumes "hasTrace t (instr_sem opcode)"
    and "instr_of_exp (instr_sem opcode) = Some instr"
    and "\<not>hasException t (instr_sem opcode)"
    and "\<not>hasFailure t (instr_sem opcode)"
    and "translation_assms_trace t"
    and "\<forall>e \<in> set t. debug_disabled e"
    and "s_run_trace t s = Some s'"
  shows "branch_instr_run_performs_expected_data_invocation opcode t"
proof -
  have Run: "Run (instr_sem opcode) t ()"
    using assms(1,3,4)
    by (cases rule: hasTrace_cases)
       (auto simp: hasException_def hasFailure_def runTrace_iff_Traces[symmetric])
  note instr_t = instr_of_exp_instr_of_trace[OF determ_instrs_instr_sem assms(2,1)]
  let ?s' = "run_state (initial_invocation_from_seq_state s) t"
  have "trace_assms (initial_invocation_from_seq_state s) t"
    using assms(5,6)
    by (intro s_run_trace_trace_assms[OF assms(7)]) auto
  then have post_if: "invocation_post_final ?s'" if "instr_may_invoke"
    using assms(2) that
    by (intro impI pre_post_RunE[OF pre_post_instr_sem Run]) auto
  show ?thesis
  proof (use assms(1-7) in \<open>cases rule: hasTrace_instr_sem_invocation_cases\<close>)
    case (SealedPair cc cd nc nd)
    note this[simp]
    from post_if have post: "invocation_post_final ?s'"
      by auto
    from post have "\<not>gpr_reads_after_write ?s'"
      by (auto simp: has_expected_gpr_reads_def)
    note trace_reads_initial_caps_from_gpr_eq[OF this, symmetric, simp]
    have [simp]: "instr_indirect_sentry_type instr = None \<and> instr_load_auth instr = None"
      using \<open>instr_invokes_data_cap_from_reg instr = Some nd\<close>
      by (cases instr) auto
    then have [simp]: "mem_caps ?s' = {}"
      using post
      by (auto simp: has_expected_loads_def no_load_auth_caps_run_state)
    from post have [simp]: "code_reg_caps ?s' = {cc}"
      by (auto simp: code_reg_caps_run_state_trace_reads_caps_from_gpr has_expected_gpr_reads_def is_singleton_def)
    from post have [simp]: "data_reg_caps ?s' = {cd}"
      by (auto simp: data_reg_caps_run_state_trace_reads_caps_from_gpr has_expected_gpr_reads_def is_singleton_def)
    have invoked_code_caps: "invoked_code_caps ?s' = branch_caps (clear_lsb (CapUnseal cc))"
      by (auto simp: invoked_code_caps_def original_mem_code_caps_def)
    have invoked_data_caps: "invoked_data_caps ?s' = {CapUnseal cd}"
      by (auto simp: invoked_data_caps_def original_reg_data_caps_def original_mem_data_caps_def)
    then obtain cc' cd' where "trace_writes_pcc_caps ISA (instr_trace opcode t) = {cc'}"
      and "trace_writes_idc_caps ISA (instr_trace opcode t) = {cd'}"
      and "CapIsTagSet cc' \<longrightarrow> cc' \<in> invoked_code_caps ?s' \<and> cd' = CapUnseal cd"
      using post
      by (auto simp: has_expected_data_invocation_def
                     trace_writes_pcc_caps_eq_pcc_cap_writes[of "initial_invocation_from_seq_state s"]
                     trace_writes_idc_caps_eq_idc_cap_writes[of "initial_invocation_from_seq_state s"])
    then show ?thesis
      by (auto simp: branch_instr_run_performs_expected_data_invocation_def invoked_code_caps)
  next
    case (IndirectPointsToPCC c c' paddr vaddr)
    note IndirectPointsToPCC(1-5,7-8,13,14)[simp]
    from post_if have post: "invocation_post_final ?s'"
      by auto
    from post have "\<not>gpr_reads_after_write ?s'"
      by (auto simp: has_expected_gpr_reads_def)
    note trace_reads_initial_caps_from_gpr_eq[OF this, symmetric, simp]
    have "no_mem_writes_in_trace t"
      using no_mem_writes_in_exp_instr_sem[THEN no_mem_writes_in_trace_of_exp, OF assms(2) _ assms(1)]
      by auto
    then have [simp]: "mem_caps ?s' = {(paddr, c')}"
      using IndirectPointsToPCC(11) mem_caps_initial_mem_cap_loads_of_trace
      by auto
    have "instr_load_auth instr = Some (RegAuth 29)"
      using IndirectPointsToPCC(1)
      by (cases instr) (auto split: if_splits)
    from load_auth_caps_run_state_trace_reads_caps_from_gpr[OF this]
    have [simp]: "load_auth_caps ?s' = {c}"
      by auto
    (*then have [simp]: "cap_permits CAP_PERM_LOAD_CAP c"
      using post
      by (auto simp: has_expected_loads_def cap_authorises_load_def)*)
    have [simp]: "invoked_data_caps ?s' = {CapUnseal c}"
      using \<open>CapIsTagSet c\<close>
      by (auto simp: invoked_data_caps_def original_reg_data_caps_def original_mem_data_caps_def CapIsSealed_def)
    have [simp]: "code_reg_caps ?s' = {}"
      by (auto simp: no_code_reg_caps_run_state init_null_caps_def)
    have [simp]: "invoked_code_caps ?s' = mem_branch_caps (clear_lsb c')"
      using post
      by (auto simp: invoked_code_caps_def no_code_reg_caps_run_state original_mem_code_caps_def)
    obtain cc cd where "trace_writes_pcc_caps ISA (instr_trace opcode t) = {cc}"
      and "trace_writes_idc_caps ISA (instr_trace opcode t) = {cd}"
      and "CapIsTagSet cc \<longrightarrow> cc \<in> mem_branch_caps (clear_lsb c') \<and> cd = CapUnseal c \<and> cap_permits CAP_PERM_LOAD_CAP c"
      using post
      by (auto simp: has_expected_data_invocation_def has_load_cap_perm_if_needed_def
                     trace_writes_pcc_caps_eq_pcc_cap_writes[of "initial_invocation_from_seq_state s"]
                     trace_writes_idc_caps_eq_idc_cap_writes[of "initial_invocation_from_seq_state s"])
    then show ?thesis
      by (auto simp: branch_instr_run_performs_expected_data_invocation_def mem_branch_caps_128th_iff test_bit_set_gen)
  next
    case (IndirectPointsToPair n c cc cd paddr_cc paddr_cd)
    note IndirectPointsToPair(1-5,7,8,10,11,14,15)[simp]
    from post_if have post: "invocation_post_final ?s'"
      by auto
    from post have "\<not>gpr_reads_after_write ?s'"
      by (auto simp: has_expected_gpr_reads_def)
    note trace_reads_initial_caps_from_gpr_eq[OF this, symmetric, simp]
    have "no_mem_writes_in_trace t"
      using no_mem_writes_in_exp_instr_sem[THEN no_mem_writes_in_trace_of_exp, OF assms(2) _ assms(1)]
      by auto
    then have [simp]: "mem_caps ?s' = {(paddr_cd, cd), (paddr_cc, cc)}"
      using IndirectPointsToPair(12) mem_caps_initial_mem_cap_loads_of_trace
      by auto
    have "instr_load_auth instr = Some (RegAuth n)"
      using IndirectPointsToPair(1)
      by (cases instr) (auto split: if_splits)
    from load_auth_caps_run_state_trace_reads_caps_from_gpr[OF this]
    have [simp]: "load_auth_caps ?s' = {c}"
      by auto
    have [simp]: "code_reg_caps ?s' = {}"
      by (auto simp: no_code_reg_caps_run_state init_null_caps_def)
    (*then have perm[simp]: "cap_permits CAP_PERM_LOAD_CAP c"
      (* and addr: "unat (CapGetValue c + 16) = unat (CapGetValue c) + 16" *)
      using post
      by (auto simp: has_expected_loads_def cap_authorises_load_def valid_address_no_overflow)*)
    have [simp]: "invoked_data_caps ?s' = mem_data_caps cd"
      using translate_address_unat_vaddr_offset_paddr_different[OF IndirectPointsToPair(10), where offset = 16]
      unfolding (*addr*) IndirectPointsToPair(11)(*[unfolded addr]*)
      by (auto simp: invoked_data_caps_def original_mem_data_caps_def original_reg_data_caps_def)
    have [simp]: "invoked_code_caps ?s' = mem_branch_caps (clear_lsb cc)"
      using translate_address_unat_vaddr_offset_paddr_different[OF IndirectPointsToPair(10), where offset = 16]
      unfolding (*addr*) IndirectPointsToPair(11)(*[unfolded addr]*)
      by (auto simp: invoked_code_caps_def original_mem_code_caps_def no_code_reg_caps_run_state)
    obtain cc' cd' where "trace_writes_pcc_caps ISA (instr_trace opcode t) = {cc'}"
      and "trace_writes_idc_caps ISA (instr_trace opcode t) = {cd'}"
      and "CapIsTagSet cc' \<longrightarrow> cc' \<in> mem_branch_caps (clear_lsb cc) \<and> cd' \<in> mem_data_caps cd"
      using post
      by (auto simp: has_expected_data_invocation_def
                     trace_writes_pcc_caps_eq_pcc_cap_writes[of "initial_invocation_from_seq_state s"]
                     trace_writes_idc_caps_eq_idc_cap_writes[of "initial_invocation_from_seq_state s"])
    then show ?thesis
      by (auto simp: branch_instr_run_performs_expected_data_invocation_def mem_branch_caps_128th_iff test_bit_set_gen)
  qed (auto simp: branch_instr_run_performs_expected_data_invocation_def)
qed

end

context Morello_ISA
begin

lemma idc_write_axiomI:
  assumes "hasTrace t (instr_sem opcode)"
    and "translation_assms_trace t"
    and "\<forall>e \<in> set t. debug_disabled e"
    and "s_run_trace t s = Some s'"
  shows "idc_write_axiom CC ISA (instr_trace opcode t)"
proof (cases "instr_of_exp (instr_sem opcode)")
  case None
  then have instr_t: "instr_of_trace t = None"
    using determ_instr_exp_instr_of_exp_None[OF determ_instrs_instr_sem None] assms(1)
    by (auto simp: hasTrace_iff_Traces_final)
  then show ?thesis
    using instr_of_trace_None_instr_invokes_no_caps[OF instr_t, where instr = opcode]
    by (auto simp: idc_write_axiom_def)
next
  case (Some instr)
  interpret Morello_Instr_Invocation_Property where instr = instr ..
  note instr_t = instr_of_exp_instr_of_trace[OF determ_instrs_instr_sem Some assms(1)]
  then show ?thesis
  proof (use assms(1) in \<open>cases rule: hasTrace_cases\<close>)
    case (Run a)
    have [simp]:
      "trace_invokes_code_cap_from_reg t = instr_invokes_code_cap_from_reg instr"
      "trace_invokes_data_cap_from_reg t = instr_invokes_data_cap_from_reg instr"
      "trace_invokes_indirect_cap_from_reg t = instr_invokes_indirect_cap_from_reg instr"
      "trace_indirect_sentry_type t = instr_indirect_sentry_type instr"
      using instr_t
      by (auto simp: trace_invokes_code_cap_from_reg_def trace_invokes_data_cap_from_reg_def
                     trace_invokes_indirect_cap_from_reg_def trace_indirect_sentry_type_def)
    have if_mem_data_caps_eq_empty[simp]: "(if b then mem_data_caps cd else {}) = {} \<longleftrightarrow> \<not>b" for b cd
      by auto
    from Run have no_ex: "\<not>hasException t (instr_sem opcode)"
      and no_fail: "\<not>hasFailure t (instr_sem opcode)"
      by (auto simp add: hasException_def hasFailure_def simp flip: runTrace_iff_Traces)
    have "instr_may_invoke \<longrightarrow> branch_instr_trace_has_expected_invocations opcode t"
      using branch_instr_trace_has_expected_invocationsI[OF assms(1,4) no_fail assms(2,3) Some]
      by auto
    moreover have "branch_instr_run_performs_expected_data_invocation opcode t"
      using assms Some no_ex no_fail
      by (intro branch_instr_run_performs_expected_data_invocationI)
    ultimately show ?thesis
      using Run Some
      by (cases rule: hasTrace_instr_sem_invocation_cases[OF assms(1) Some no_ex no_fail assms(2,3,4)])
         (auto simp add: idc_write_axiom_def branch_instr_trace_has_expected_invocations_def
                         branch_instr_run_performs_expected_data_invocation_def)
  next
    case (Fail f)
    then show ?thesis
      by (auto simp: idc_write_axiom_def trace_has_assertion_failure_def runTrace_iff_Traces)
  next
    case (Ex e)
    show ?thesis
    proof (cases "instr_may_invoke")
      case True
      then have "branch_instr_trace_has_expected_invocations opcode t"
        using assms Some Ex
        by (intro branch_instr_trace_has_expected_invocationsI)
           (auto simp: hasFailure_def runTrace_iff_Traces[symmetric])
      then show ?thesis
        using Ex
        by (auto simp: idc_write_axiom_def branch_instr_trace_has_expected_invocations_def
                       branch_instr_trace_has_expected_exceptions_def is_singleton_def
                       trace_raises_ex_def runTrace_iff_Traces[symmetric])
    next
      case False
      then have "instr_invokes_data_caps opcode t = {}"
        by (auto simp: trace_invoked_cap_defs instr_t)
      then show ?thesis
        by (auto simp: idc_write_axiom_def)
    qed
  qed
qed

lemma invocation_writes_pstate_c64_instr_trace:
  assumes "hasTrace t (instr_sem opcode)"
    and "\<not>hasException t (instr_sem opcode)" \<comment> \<open>TODO?\<close>
    and "\<not>hasFailure t (instr_sem opcode)"
    and "translation_assms_trace t"
    and "\<forall>e \<in> set t. debug_disabled e"
    and "s_run_trace t s = Some s'"
  shows "invocation_writes_pstate_c64 (instr_trace opcode t)"
proof (cases "instr_of_exp (instr_sem opcode)")
  case None
  then have instr_t: "instr_of_trace t = None"
    using determ_instr_exp_instr_of_exp_None[OF determ_instrs_instr_sem None] assms(1)
    by (auto simp: hasTrace_iff_Traces_final)
  then show ?thesis
    using instr_of_trace_None_instr_invokes_no_caps[OF instr_t, where instr = opcode]
    by (auto simp: invocation_writes_pstate_c64_def)
next
  case (Some instr)
  interpret Morello_Instr_Invocation_Property where instr = instr ..
  note instr_t = instr_of_exp_instr_of_trace[OF determ_instrs_instr_sem Some assms(1)]
  show ?thesis
  proof cases
    assume "instr_may_invoke"
    then have "branch_instr_trace_has_expected_invocations opcode t"
      using branch_instr_trace_has_expected_invocationsI[OF assms(1,6,3,4,5) Some]
      by blast
    then have "branch_instr_run_has_expected_pstate_writes opcode t"
      using hasTrace_Run[OF assms(1-3)]
      by (auto simp: branch_instr_trace_has_expected_invocations_def)
    then show ?thesis
      using Some
      by (cases rule: hasTrace_instr_sem_invocation_cases[OF assms(1) Some assms(2-6)])
         (auto simp add: invocation_writes_pstate_c64_def branch_instr_run_has_expected_pstate_writes_def
                         image_Un clear_lsb_image_branch_caps_eq clear_lsb_image_mem_branch_caps_eq
                         branch_caps_128th_iff mem_branch_caps_128th_iff test_bit_set_gen invokable_def)
  next
    assume "\<not>instr_may_invoke"
    then have "trace_invokes_code_caps ISA (instr_trace opcode t) = {}"
      by (auto simp: trace_invoked_cap_defs instr_t)
    then show ?thesis
      unfolding invocation_writes_pstate_c64_def
      by blast
  qed
qed

end

end
