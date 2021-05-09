theory CHERI_Monotonicity
  imports CHERI_Cap_Properties CHERI_Mem_Properties CHERI_Fetch_Properties "Sail-T-CHERI.Properties"
begin

print_locale Morello_Fixed_Address_Translation
print_locale CHERI_ISA_State

interpretation Register_Accessors get_regval set_regval
  apply standard
  sorry

definition "determ_instrs_of_exp m \<equiv>
  (\<forall>t. hasTrace t m \<longrightarrow> instrs_of_exp m = set_option (instr_of_trace t))"

lemma hasTrace_determ_instrs_eqs:
  assumes "hasTrace t m" and "determ_instrs_of_exp m"
  shows "exp_invokes_regs m = trace_invokes_regs t"
    and "exp_invokes_indirect_regs m = trace_invokes_indirect_regs t"
    and "exp_load_auths m = trace_load_auths t"
    and "exp_is_indirect_branch m = trace_is_indirect_branch t"
  using assms
  unfolding exp_invokes_regs_def trace_invokes_regs_def
  unfolding exp_invokes_indirect_regs_def trace_invokes_indirect_regs_def
  unfolding exp_load_auths_def trace_load_auths_def
  unfolding trace_is_indirect_branch_def
  by (auto simp: determ_instrs_of_exp_def split: option.splits)

lemma determ_instrs_instr_sem: "determ_instrs_of_exp (instr_sem instr)"
  sorry

lemma trace_invokes_indirect_regs_None[simp]:
  assumes "instr_of_trace t = None"
  shows "trace_invokes_indirect_regs t = {}"
  using assms
  by (auto simp: trace_invokes_indirect_regs_def)

lemma instr_trace_invokes_indirect_regs[simp]:
  assumes "instr_of_trace t = Some instr"
  shows "trace_invokes_indirect_regs t = instr_invokes_indirect_regs instr"
  using assms
  by (auto simp: trace_invokes_indirect_regs_def)

lemma trace_invokes_indirect_caps_no_regs[simp]:
  assumes "trace_invokes_indirect_regs t = {}"
  shows "trace_invokes_indirect_caps t = {}"
  using assms
  by (auto simp: trace_invokes_indirect_caps_def)

context Morello_Axiom_Automaton
begin

lemma instrs_eq_instr_exp_assms_iff:
  assumes "instrs_of_exp m1 = instrs_of_exp m2"
  shows "instr_exp_assms m1 \<longleftrightarrow> instr_exp_assms m2"
  using assms
  unfolding instr_exp_assms_def invocation_instr_exp_assms_def load_instr_exp_assms_def
  unfolding exp_invokes_regs_def exp_invokes_indirect_regs_def exp_load_auths_def
  by auto

lemma T_bind_leftI:
  assumes "(m, e, m') \<in> T"
  shows "(bind m f, e, bind m' f) \<in> T"
  using assms
  by induction auto

lemma Traces_bind_leftI:
  assumes "(m, t, m') \<in> Traces"
  shows "(bind m f, t, bind m' f) \<in> Traces"
  using assms
  by induction (auto intro: T_bind_leftI)

lemma instr_of_trace_no_writes_None:
  assumes "\<nexists>v. E_write_reg ''__ThisInstrAbstract'' v \<in> set t"
  shows "instr_of_trace t = None"
  using assms
  by (cases t rule: instr_of_trace.cases) auto

lemma instr_of_trace_append_no_writes:
  assumes "\<nexists>v. E_write_reg ''__ThisInstrAbstract'' v \<in> set t2"
  shows "instr_of_trace (t1 @ t2) = instr_of_trace t1"
  using assms
  by (cases t1 rule: instr_of_trace.cases) (auto simp: instr_of_trace_no_writes_None)

lemma instrs_of_exp_bind_no_writes:
  assumes "\<forall>a. no_reg_writes_to {''__ThisInstrAbstract''} (f a)"
  shows "instrs_of_exp (bind m f) = instrs_of_exp m"
  using assms
  by (fastforce simp: instrs_of_exp_def instr_of_trace_append_no_writes no_reg_writes_to_def
                intro: Traces_bind_leftI elim!: bind_Traces_cases)

lemma instr_exp_assms_TryInstructionExecute_iff:
  "instr_exp_assms (TryInstructionExecute enc instr) \<longleftrightarrow> instr_exp_assms (DecodeExecute enc instr)"
  unfolding TryInstructionExecute_def SSAdvance_def bind_assoc
  by (intro instrs_eq_instr_exp_assms_iff instrs_of_exp_bind_no_writes allI)
     (no_reg_writes_toI simp: register_defs)

end

locale Morello_Trace_Automaton = Morello_Fixed_Address_Translation + fixes t :: "register_value trace"

locale Morello_Instr_Trace_Automaton = Morello_Trace_Automaton + fixes instr :: instr

(*sublocale Morello_Instr_Trace_Automaton \<subseteq> Morello_Axiom_Automaton
  where ex_traces = "instr_raises_ex instr t"
    and invoked_caps = "invokes_caps instr t"
    and invoked_regs = "trace_invokes_regs t"
    and invoked_indirect_caps = "invokes_indirect_caps instr t"
    and invoked_indirect_regs = "trace_invokes_indirect_regs t"
    and load_auths = "trace_load_auths t"
    and use_mem_caps = "uses_mem_caps instr t"
    and is_fetch = False
    and is_indirect_branch = "trace_is_indirect_branch t"
    and no_system_reg_access = "\<not>trace_has_system_reg_access t"
    and is_in_c64 = "trace_is_in_c64 t"
    and translate_address = "\<lambda>addr _ _. translate_address addr"
  apply standard
  oops*)

locale Morello_Instr_Trace_Write_Cap_Automaton =
  Morello_Instr_Trace_Automaton + Morello_Instr_Write_Cap_Automaton
  where ex_traces = "instr_raises_ex instr t"
    and invoked_caps = "trace_invokes_caps t"
    and invoked_regs = "trace_invokes_regs t"
    and invoked_indirect_caps = "invokes_indirect_caps instr t"
    and invoked_indirect_regs = "trace_invokes_indirect_regs t"
    and load_auths = "trace_load_auths t"
    and use_mem_caps = "uses_mem_caps instr t"
    and is_indirect_branch = "trace_is_indirect_branch t"
    and no_system_reg_access = "\<not>trace_has_system_reg_access t"
    and is_in_c64 = "trace_is_in_c64 t"
    and translate_address = "\<lambda>addr _ _. translate_address addr"
begin

abbreviation "instr_trace_assms \<equiv> trace_assms initial t \<and> \<not>trace_has_system_reg_access t"

lemma instr_exp_assms_instr_semI:
  assumes "hasTrace t (instr_sem instr)"
  shows "instr_exp_assms (instr_sem instr)"
  using hasTrace_determ_instrs_eqs[OF assms determ_instrs_instr_sem]
  unfolding instr_exp_assms_def invocation_instr_exp_assms_def load_instr_exp_assms_def
  by auto

end

locale Morello_Instr_Trace_Mem_Automaton =
  Morello_Instr_Trace_Automaton + Morello_Instr_Mem_Automaton
  where ex_traces = "instr_raises_ex instr t"
    and invoked_caps = "trace_invokes_caps t"
    and invoked_regs = "trace_invokes_regs t"
    and invoked_indirect_caps = "invokes_indirect_caps instr t"
    and invoked_indirect_regs = "trace_invokes_indirect_regs t"
    and load_auths = "trace_load_auths t"
    and use_mem_caps = "uses_mem_caps instr t"
    and is_indirect_branch = "trace_is_indirect_branch t"
    and no_system_reg_access = "\<not>trace_has_system_reg_access t"
    and is_in_c64 = "trace_is_in_c64 t"


locale Morello_Fetch_Trace_Write_Cap_Automaton =
  Morello_Trace_Automaton + Morello_Fetch_Write_Cap_Automaton
  where ex_traces = "fetch_raises_ex t"
    and invoked_caps = "{}"
    and invoked_regs = "{}"
    and invoked_indirect_caps = "{}"
    and invoked_indirect_regs = "{}"
    and load_auths = "{}"
    and use_mem_caps = "True"
    and is_indirect_branch = "False"
    and no_system_reg_access = "\<not>trace_has_system_reg_access t"
    and is_in_c64 = "trace_is_in_c64 t"
    and translate_address = "\<lambda>addr _ _. translate_address addr"
begin

abbreviation "fetch_trace_assms \<equiv> trace_assms initial t \<and> \<not>trace_has_system_reg_access t"

end

locale Morello_Fetch_Trace_Mem_Automaton =
  Morello_Trace_Automaton + Morello_Fetch_Mem_Automaton
  where ex_traces = "fetch_raises_ex t"
    and invoked_caps = "{}"
    and invoked_regs = "{}"
    and invoked_indirect_caps = "{}"
    and invoked_indirect_regs = "{}"
    and load_auths = "{}"
    and use_mem_caps = "True"
    and is_indirect_branch = "False"
    and no_system_reg_access = "\<not>trace_has_system_reg_access t"
    and is_in_c64 = "trace_is_in_c64 t"

term Morello_Instr_Trace_Write_Cap_Automaton.instr_trace_assms

context Morello_Fixed_Address_Translation
begin

thm Morello_Axiom_Assms.ev_assms.simps
term "Morello_Instr_Trace_Write_Cap_Automaton.instr_trace_assms translate_address is_translation_event translation_assms UNKNOWN_caps"

abbreviation "instr_ev_assms_in_trace instr t \<equiv> Morello_Axiom_Assms.ev_assms UNKNOWN_caps (invokes_caps instr t) (trace_invokes_regs t) (trace_invokes_indirect_caps t) (trace_invokes_indirect_regs t) (trace_load_auths t) (trace_uses_mem_caps t) False (trace_is_indirect_branch t) (\<not>trace_has_system_reg_access t) (trace_is_in_c64 t) translation_assms"

abbreviation "instr_assms instr t \<equiv> Morello_Instr_Trace_Write_Cap_Automaton.instr_trace_assms translate_address is_translation_event translation_assms UNKNOWN_caps t"
abbreviation "fetch_assms t \<equiv> Morello_Fetch_Trace_Write_Cap_Automaton.fetch_trace_assms translate_address is_translation_event translation_assms UNKNOWN_caps t"

lemma more_ISA_simps[simp]:
  "isa.fetch_raises_ex ISA t = fetch_raises_ex t"
  by (auto simp: ISA_def)

(* TODO:
   - Add write_reg_axiom to traces_enabled_reg_axioms
   - Add hasFailure to fetch_raises_ex
   - Later: Restrict ex_traces case to only exceptions, not failures; clean up instr/fetch_raises_ex again
   - Add __FetchNextInstr and __CheckPendingInterrupts to fetch exps in lemma generation
 *)

sublocale CHERI_ISA CC ISA cap_invariant UNKNOWN_caps fetch_assms instr_assms
proof
  fix t :: "register_value trace" and instr :: instr and n :: nat
  interpret Write_Cap?: Morello_Instr_Trace_Write_Cap_Automaton where instr = instr and t = t
    by standard (auto simp: trace_uses_mem_caps_def)
  assume t: "hasTrace t (instr_sem_ISA instr)"
    and inv: "instr_available_caps_invariant instr t n"
    and ia: "instr_assms instr t"
    and n: "n \<le> length t"
  from t have iea: "instr_exp_assms (instr_sem instr)"
    by (intro instr_exp_assms_instr_semI) simp
  from ia have no_asr: "\<not>trace_has_system_reg_access t"
    by simp
  have *: "Write_Cap.traces_enabled (instr_sem instr) initial"
    unfolding instr_sem_def TryInstructionExecute_def bind_assoc
    by (traces_enabledI assms: iea simp: instr_sem_def instr_exp_assms_TryInstructionExecute_iff
          intro: no_asr elim: BranchTaken_or_PCC_accessible)
  interpret Mem: Morello_Instr_Trace_Mem_Automaton where instr = instr and t = t
    by standard (auto simp: trace_uses_mem_caps_def)
  have **: "Mem.traces_enabled (instr_sem instr) initial"
    unfolding instr_sem_def TryInstructionExecute_def bind_assoc
    by (traces_enabledI assms: iea simp: instr_sem_def instr_exp_assms_TryInstructionExecute_iff intro: no_asr)
  show "instr_cheri_axioms instr t n"
    using * **
    unfolding cheri_axioms_def ISA_simps
    apply (intro conjI)
    subgoal
      apply (elim traces_enabled_reg_axioms)
      using t inv ia n
      by (auto simp: instr_raises_ex_def intro: holds_along_trace_take)
    subgoal
      apply (elim traces_enabled_reg_axioms)
      using t inv ia n
      by (auto simp: instr_raises_ex_def intro: holds_along_trace_take)
    subgoal
      apply (elim traces_enabled_reg_axioms)
      using t inv ia n
      by (auto simp: instr_raises_ex_def intro: holds_along_trace_take)
    subgoal
      sorry
    subgoal
      apply (elim Mem.traces_enabled_mem_axioms)
      using t inv ia n
      by (auto simp: instr_raises_ex_def intro: holds_along_trace_take)
    subgoal
      apply (elim Mem.traces_enabled_mem_axioms)
      using t inv ia n
      by (auto simp: instr_raises_ex_def intro: holds_along_trace_take)
    subgoal
      apply (elim Mem.traces_enabled_mem_axioms)
      using t inv ia n
      by (auto simp: instr_raises_ex_def intro: holds_along_trace_take)
    done
next
  fix t :: "register_value trace" and n :: nat
  interpret Write_Cap?: Morello_Fetch_Trace_Write_Cap_Automaton where t = t
    by standard auto
  assume t: "hasTrace t (isa.instr_fetch ISA)"
    and inv: "fetch_available_caps_invariant t n"
    and ia: "fetch_assms t"
    and n: "n \<le> length t"
  from ia have no_asr: "\<not>trace_has_system_reg_access t"
    by simp
  have *: "Write_Cap.traces_enabled (instr_fetch) initial"
    unfolding instr_fetch_def FetchNextInstr_def bind_assoc
    apply (traces_enabledI)
    sorry
  interpret Mem: Morello_Fetch_Trace_Mem_Automaton where t = t
    by standard auto
  have **: "Mem.traces_enabled (instr_fetch) initial"
    unfolding instr_fetch_def FetchNextInstr_def bind_assoc
    apply (traces_enabledI)
    sorry
  show "fetch_cheri_axioms t n"
    using * **
    unfolding cheri_axioms_def ISA_simps more_ISA_simps
    apply (intro conjI)
    subgoal
      apply (elim traces_enabled_reg_axioms)
      using t inv ia n
      apply (auto simp: fetch_raises_ex_def intro: holds_along_trace_take)
      sorry
    subgoal
      apply (elim traces_enabled_reg_axioms)
      using t inv ia n
      apply (auto simp: fetch_raises_ex_def intro: holds_along_trace_take)
      sorry
    subgoal
      apply (elim traces_enabled_reg_axioms)
      using t inv ia n
      apply (auto simp: fetch_raises_ex_def intro: holds_along_trace_take)
      sorry
    subgoal
      sorry
    subgoal
      apply (elim Mem.traces_enabled_mem_axioms)
      using t inv ia n
      apply (auto simp: fetch_raises_ex_def intro: holds_along_trace_take)
      sorry
    subgoal
      apply (elim Mem.traces_enabled_mem_axioms)
      using t inv ia n
      apply (auto simp: fetch_raises_ex_def intro: holds_along_trace_take)
      sorry
    subgoal
      apply (elim Mem.traces_enabled_mem_axioms)
      using t inv ia n
      apply (auto simp: fetch_raises_ex_def intro: holds_along_trace_take)
      sorry
    done
qed

(*abbreviation "s_translate_address addr acctype s \<equiv> translate_address addr"

sublocale CHERI_ISA_State CC ISA cap_invariant UNKNOWN_caps fetch_assms instr_assms get_regval set_regval s_translate_address
  apply standard
  subgoal
    apply (auto simp: set_regval_unfold get_regval_unfold split: bind_splits)
    sorry
  subgoal
    apply (auto simp: set_regval_unfold get_regval_unfold split: bind_splits)
    sorry
  sorry*)

end

end
