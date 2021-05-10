theory CHERI_Monotonicity
  imports CHERI_Cap_Properties CHERI_Mem_Properties CHERI_Fetch_Properties "Sail-T-CHERI.Properties"
begin

interpretation Register_Accessors get_regval set_regval
  apply standard
  sorry

locale Morello_Trace_Automaton = Morello_Fixed_Address_Translation + fixes t :: "register_value trace"

locale Morello_Instr_Trace_Automaton = Morello_Trace_Automaton + fixes instr :: instr

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

context Morello_Fixed_Address_Translation
begin

abbreviation "instr_assms instr t \<equiv> Morello_Instr_Trace_Write_Cap_Automaton.instr_trace_assms translate_address is_translation_event translation_assms UNKNOWN_caps t"
abbreviation "fetch_assms t \<equiv> Morello_Fetch_Trace_Write_Cap_Automaton.fetch_trace_assms translate_address is_translation_event translation_assms UNKNOWN_caps t"

(* TODO:
   - Restrict ex_traces case to only exceptions, not failures; clean up instr/fetch_raises_ex again
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
    unfolding instr_sem_def
    by (traces_enabledI assms: iea simp: instr_sem_def intro: no_asr)
  interpret Mem: Morello_Instr_Trace_Mem_Automaton where instr = instr and t = t
    by standard (auto simp: trace_uses_mem_caps_def)
  have **: "Mem.traces_enabled (instr_sem instr) initial"
    unfolding instr_sem_def TryInstructionExecute_def bind_assoc
    by (traces_enabledI assms: iea simp: instr_sem_def instr_exp_assms_TryInstructionExecute_iff intro: no_asr)
  show "instr_cheri_axioms instr t n"
    using * ** t inv ia n
    unfolding cheri_axioms_def ISA_simps
    by (intro conjI; elim traces_enabled_reg_axioms Mem.traces_enabled_mem_axioms)
       (auto simp: instr_raises_ex_def intro: holds_along_trace_take)
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
    unfolding instr_fetch_def bind_assoc
    by traces_enabledI
  interpret Mem: Morello_Fetch_Trace_Mem_Automaton where t = t
    by standard auto
  have **: "Mem.traces_enabled (instr_fetch) initial"
    unfolding instr_fetch_def bind_assoc
    by traces_enabledI
  show "fetch_cheri_axioms t n"
    using * ** t inv ia n
    unfolding cheri_axioms_def ISA_simps more_ISA_simps
    by (intro conjI; elim traces_enabled_reg_axioms Mem.traces_enabled_mem_axioms)
       (auto simp: fetch_raises_ex_def intro: holds_along_trace_take)
qed

abbreviation "s_translate_address addr acctype s \<equiv> translate_address addr"

sublocale CHERI_ISA_State CC ISA cap_invariant UNKNOWN_caps fetch_assms instr_assms get_regval set_regval s_translate_address
  by standard auto

thm reachable_caps_instrs_trace_intradomain_monotonicity

end

end
