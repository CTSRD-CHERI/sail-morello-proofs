section \<open>Monotonicity theorem\<close>

theory CHERI_Monotonicity
  imports
    "Sail-Morello.Morello_lemmas"
    CHERI_Instantiation
    CHERI_Cap_Properties
    CHERI_Mem_Properties
    CHERI_Fetch_Properties
    CHERI_Invariant
    "Sail-T-CHERI.Trace_Assumptions"
    "Sail-T-CHERI.Properties"
begin

locale Morello_Trace_Automaton = Morello_Fixed_Address_Translation + fixes t :: "register_value trace"

locale Morello_Instr_Trace_Automaton = Morello_Trace_Automaton + fixes instr :: instr

(* TODO: Move *)
lemma (in Morello_Axiom_Assms) ev_assms_translation_assms:
  "ev_assms s e \<Longrightarrow> translation_assms e"
  by (cases e; simp only: ev_assms.simps)

locale Morello_Instr_Trace_Write_Cap_Automaton =
  Morello_Instr_Trace_Automaton + Morello_Instr_Write_Cap_Automaton
  where ex_traces = "isa.trace_raises_ex ISA \<lparr>trace = t, trace_kind = Instr_Trace instr\<rparr>"
    and instr_opt = "instr_of_trace t"
    and invoked_code_caps = "Cheri_axioms.trace_invokes_code_caps ISA \<lparr>trace = t, trace_kind = Instr_Trace instr\<rparr>"
    and invoked_data_caps = "Cheri_axioms.trace_invokes_data_caps ISA \<lparr>trace = t, trace_kind = Instr_Trace instr\<rparr>"
    (* and invoked_regs = "trace_invokes_regs t" *)
    and invoked_indirect_caps = "Cheri_axioms.trace_invokes_indirect_caps ISA \<lparr>trace = t, trace_kind = Instr_Trace instr\<rparr>"
    (* and invoked_indirect_regs = "trace_invokes_indirect_regs t" *)
    and load_auth = "trace_load_auths t"
    and load_caps_permitted = "isa.trace_uses_mem_caps ISA \<lparr>trace = t, trace_kind = Instr_Trace instr\<rparr>"
    (* and is_indirect_branch = "trace_is_indirect_branch t" *)
    and no_system_reg_access = "\<not>trace_has_system_reg_access t"
    and is_in_c64 = "trace_is_in_c64 t"
    (* and translate_address = "\<lambda>addr _ _. translate_address addr" *)
begin

abbreviation "instr_trace_assms \<equiv> trace_assms initial t \<and> \<not>trace_has_system_reg_access t"

lemma instr_exp_assms_instr_semI:
  assumes "hasTrace t (instr_sem instr)"
  shows "instr_exp_assms (instr_sem instr)"
  (* using hasTrace_determ_instrs_eqs[OF assms determ_instrs_instr_sem] *)
  (* unfolding instr_exp_assms_def invocation_instr_exp_assms_def load_instr_exp_assms_def *)
  (* by auto *)
  unfolding instr_exp_assms_def invocation_instr_exp_assms_def load_instr_exp_assms_def
  sorry

sublocale Write_Cap_Assm_Automaton_For_Trace
  where CC = CC and ISA = ISA and initial_caps = UNKNOWN_caps and ev_assms = ev_assms
    and is_isa_exception = is_isa_exception and wellformed_ev = wellformed_ev
    and cap_invariant = cap_invariant
    and t = "\<lparr>trace = t, trace_kind = Instr_Trace instr\<rparr>"
  by (unfold_locales, elim ev_assms_translation_assms)

end

locale Morello_Instr_Trace_Mem_Automaton =
  Morello_Instr_Trace_Automaton + Morello_Mem_Axiom_Automaton
  where ex_traces = "isa.trace_raises_ex ISA \<lparr>trace = t, trace_kind = Instr_Trace instr\<rparr>"
    and instr_opt = "instr_of_trace t"
    and invoked_code_caps = "Cheri_axioms.trace_invokes_code_caps ISA \<lparr>trace = t, trace_kind = Instr_Trace instr\<rparr>"
    and invoked_data_caps = "Cheri_axioms.trace_invokes_data_caps ISA \<lparr>trace = t, trace_kind = Instr_Trace instr\<rparr>"
    (* and invoked_regs = "trace_invokes_regs t" *)
    and invoked_indirect_caps = "Cheri_axioms.trace_invokes_indirect_caps ISA \<lparr>trace = t, trace_kind = Instr_Trace instr\<rparr>"
    (* and invoked_indirect_regs = "trace_invokes_indirect_regs t" *)
    and load_auth = "trace_load_auths t"
    and load_caps_permitted = "isa.trace_uses_mem_caps ISA \<lparr>trace = t, trace_kind = Instr_Trace instr\<rparr>"
    (* and is_indirect_branch = "trace_is_indirect_branch t" *)
    and no_system_reg_access = "\<not>trace_has_system_reg_access t"
    and is_in_c64 = "trace_is_in_c64 t"
    and is_fetch = "is_fetch_trace \<lparr>trace = t, trace_kind = Instr_Trace instr\<rparr>"
begin

sublocale Mem_Assm_Automaton_For_Trace
  where CC = CC and ISA = ISA and initial_caps = UNKNOWN_caps and ev_assms = ev_assms
    and is_isa_exception = is_isa_exception and wellformed_ev = wellformed_ev
    and cap_invariant = cap_invariant
    and t = "\<lparr>trace = t, trace_kind = Instr_Trace instr\<rparr>"
  by (unfold_locales, elim ev_assms_translation_assms)

end

locale Morello_Fetch_Trace_Write_Cap_Automaton =
  Morello_Trace_Automaton + Morello_Fetch_Write_Cap_Automaton
  where ex_traces = "isa.trace_raises_ex ISA \<lparr>trace = t, trace_kind = Fetch_Trace\<rparr>"
    and instr_opt = "None"
    and invoked_code_caps = "Cheri_axioms.trace_invokes_code_caps ISA \<lparr>trace = t, trace_kind = Fetch_Trace\<rparr>"
    and invoked_data_caps = "Cheri_axioms.trace_invokes_data_caps ISA \<lparr>trace = t, trace_kind = Fetch_Trace\<rparr>"
    (* and invoked_regs = "{}" *)
    and invoked_indirect_caps = "Cheri_axioms.trace_invokes_indirect_caps ISA \<lparr>trace = t, trace_kind = Fetch_Trace\<rparr>"
    (* and invoked_indirect_regs = "{}" *)
    and load_auth = "None"
    and load_caps_permitted = "isa.trace_uses_mem_caps ISA \<lparr>trace = t, trace_kind = Fetch_Trace\<rparr>"
    (* and is_indirect_branch = "False" *)
    and no_system_reg_access = "\<not>trace_has_system_reg_access t"
    and is_in_c64 = "trace_is_in_c64 t"
    (* and translate_address = "\<lambda>addr _ _. translate_address addr" *)
begin

sublocale Write_Cap_Assm_Automaton_For_Trace
  where CC = CC and ISA = ISA and initial_caps = UNKNOWN_caps and ev_assms = ev_assms
    and is_isa_exception = is_isa_exception and wellformed_ev = wellformed_ev
    and cap_invariant = cap_invariant
    and t = "\<lparr>trace = t, trace_kind = Fetch_Trace\<rparr>"
  by (unfold_locales, elim ev_assms_translation_assms)

abbreviation "fetch_trace_assms \<equiv> trace_assms initial t \<and> \<not>trace_has_system_reg_access t"

end

locale Morello_Fetch_Trace_Mem_Automaton =
  Morello_Trace_Automaton + Morello_Mem_Axiom_Automaton
  where ex_traces = "isa.trace_raises_ex ISA (fetch_trace t)"
    and instr_opt = "None"
    and invoked_code_caps = "Cheri_axioms.trace_invokes_code_caps ISA (fetch_trace t)"
    and invoked_data_caps = "Cheri_axioms.trace_invokes_data_caps ISA (fetch_trace t)"
    (* and invoked_regs = "{}" *)
    and invoked_indirect_caps = "trace_invokes_indirect_caps ISA (fetch_trace t)"
    (* and invoked_indirect_regs = "{}" *)
    and load_auth = "None"
    and load_caps_permitted = "isa.trace_uses_mem_caps ISA (fetch_trace t)"
    (* and is_indirect_branch = "False" *)
    and no_system_reg_access = "\<not>trace_has_system_reg_access t"
    and is_in_c64 = "trace_is_in_c64 t"
    (* and is_fetch = "is_fetch_trace (fetch_trace t)" *)
    and is_fetch = "is_fetch_trace (fetch_trace t :: (register_value, instr) isa_trace)"
begin

sublocale Mem_Assm_Automaton_For_Trace
  where CC = CC and ISA = ISA and initial_caps = UNKNOWN_caps and ev_assms = ev_assms
    and is_isa_exception = is_isa_exception and wellformed_ev = wellformed_ev
    and cap_invariant = cap_invariant
    and t = "fetch_trace t"
  by (unfold_locales, elim ev_assms_translation_assms)

end

context Morello_Fixed_Address_Translation
begin

abbreviation "s_read_from reg s \<equiv> read_from reg (regstate s)"

abbreviation "pcc_not_sealed s \<equiv> (let pcc = s_read_from PCC_ref s in CapIsTagSet pcc \<longrightarrow> \<not>CapIsSealed pcc)"
abbreviation "pcc_tagged s \<equiv> CapIsTagSet (s_read_from PCC_ref s)"
abbreviation "non_debug_state s \<equiv> ((ucast (s_read_from EDSCR_ref s) :: 6 word) = 2) \<and> (s_read_from DBGEN_ref s = LOW)"
abbreviation "cache_line_size_64 s \<equiv> ((ucast (s_read_from DCZID_EL0_ref s) :: 4 word) = 4)"

definition "fetch_state_assms s \<equiv> pcc_not_sealed s \<and> non_debug_state s \<and> cache_line_size_64 s"
definition "instr_state_assms _ s \<equiv> fetch_state_assms s \<and> pcc_tagged s"

text \<open>TODO: Show that the trace assumptions (apart from the translation and UNKNOWN cap ones) are
  implied by the state assumptions and reduce the following to the remaining trace assumptions.\<close>
abbreviation "instr_trace_assms instr t \<equiv> Morello_Instr_Trace_Write_Cap_Automaton.instr_trace_assms translate_address is_translation_event translation_assms UNKNOWN_caps t instr \<and> wellformed_trace t"
abbreviation "fetch_trace_assms t \<equiv> Morello_Fetch_Trace_Write_Cap_Automaton.fetch_trace_assms translate_address is_translation_event translation_assms UNKNOWN_caps t \<and> wellformed_trace t"

abbreviation "s_translate_address addr acctype s \<equiv> translate_address addr"

sublocale CHERI_ISA_State CC ISA cap_invariant UNKNOWN_caps fetch_trace_assms fetch_state_assms instr_trace_assms instr_state_assms get_regval set_regval s_translate_address
proof
  fix t :: "register_value trace" and instr :: instr and n :: nat
  interpret Write_Cap: Morello_Instr_Trace_Write_Cap_Automaton where instr = instr and t = t
    ..
  assume t: "hasTrace t (instr_sem_ISA instr)"
    and inv: "instr_available_caps_invariant instr t n"
    and ia: "instr_trace_assms instr t"
    and n: "n \<le> length t"
  from t have iea: "Write_Cap.instr_exp_assms (instr_sem instr)"
    by (intro Write_Cap.instr_exp_assms_instr_semI) simp
  from ia have no_asr: "\<not>trace_has_system_reg_access t"
    by simp
  have *: "Write_Cap.traces_enabled (instr_sem instr) Write_Cap.initial"
    using iea[unfolded Write_Cap.instr_exp_assms_instr_sem_iff] no_asr
    unfolding instr_sem_def
    by (intro Write_Cap.traces_enabledI) auto
  interpret Mem: Morello_Instr_Trace_Mem_Automaton where instr = instr and t = t
    ..
  have **: "Mem.traces_enabled (instr_sem instr) Mem.initial"
    using iea[unfolded Write_Cap.instr_exp_assms_instr_sem_iff] no_asr
    unfolding instr_sem_def
    (* by (intro Mem.traces_enabledI) auto *)
    apply (intro Mem.traces_enabled_bind)
    sorry
  show "instr_cheri_axioms instr t n"
    using * ** t inv ia n
    unfolding cheri_axioms_def ISA_simps
    by (intro conjI; elim Write_Cap.traces_enabled_reg_axioms Mem.traces_enabled_mem_axioms)
       (auto simp: instr_raises_ex_def Write_Cap.trace_raises_isa_exception_def
             elim: is_isa_exception.elims intro: Write_Cap.holds_along_trace_take)
next
  fix t :: "register_value trace" and n :: nat
  interpret Write_Cap: Morello_Fetch_Trace_Write_Cap_Automaton where t = t
    ..
  assume t: "hasTrace t (isa.instr_fetch ISA)"
    and inv: "fetch_available_caps_invariant t n"
    and ia: "fetch_trace_assms t"
    and n: "n \<le> length t"
  from ia have no_asr: "\<not>trace_has_system_reg_access t"
    by simp
  have *: "Write_Cap.traces_enabled (instr_fetch) Write_Cap.initial"
    using no_asr
    unfolding instr_fetch_def bind_assoc
    by (intro Write_Cap.traces_enabledI Write_Cap.accessible_regs_no_writes_run_subset) auto
  interpret Mem: Morello_Fetch_Trace_Mem_Automaton where t = t
    ..
  have **: "Mem.traces_enabled (instr_fetch) Mem.initial"
    unfolding instr_fetch_def bind_assoc
    by (intro Mem.traces_enabledI Mem.accessible_regs_no_writes_run_subset) auto
  show "fetch_cheri_axioms t n"
    using * ** t inv ia n
    unfolding cheri_axioms_def ISA_simps
    by (intro conjI; elim Write_Cap.traces_enabled_reg_axioms Mem.traces_enabled_mem_axioms)
       (auto simp: fetch_raises_ex_def Write_Cap.trace_raises_isa_exception_def
             elim: is_isa_exception.elims intro: Write_Cap.holds_along_trace_take)
qed auto

abbreviation "unknown_caps_of_trace t \<equiv> {c. E_choose ''UNKNOWN_Capability'' (Regval_bitvector_129_dec c) \<in> set t}"
abbreviation "unknown_caps_reachable t s \<equiv> unknown_caps_of_trace t \<subseteq> UNKNOWN_caps \<and> UNKNOWN_caps \<subseteq> reachable_caps s"

lemma fetch_state_assms_iff_invs:
  "fetch_state_assms s \<longleftrightarrow> cheri_invariant s"
  unfolding fetch_state_assms_def
  by (auto simp: register_defs cheri_invariant_defs reg_inv_def)

theorem morello_monotonicity:
  assumes "hasTrace t (fetch_execute_loop ISA n)"
    and "s_run_trace t s = Some s'"
    and "\<forall>c\<in>reachable_caps s. is_tagged_method CC c \<longrightarrow> cap_invariant c"
    and "\<not>instrs_raise_ex ISA n t"
    and "instrs_invoke_caps ISA n t \<union> instrs_invoke_indirect_caps ISA n t \<subseteq> reachable_caps s"
    and "\<not>system_access_reachable s"
    and "translation_assms_trace t"
    and "unknown_caps_reachable t s"
    and "pcc_not_sealed s"
    and "non_debug_state s"
    and "cache_line_size_64 s" \<comment> \<open>Fixed in Morello, but configurable in ASL\<close>
    and "instrs_trace_assms n t" \<comment> \<open>TODO: Show that the above assumptions imply this\<close>
  shows "reachable_caps s' \<subseteq> reachable_caps s"
proof (rule reachable_caps_instrs_trace_intradomain_monotonicity[OF assms(1)])
  show "instrs_preserve_state_assms s"
  proof (unfold instrs_preserve_state_assms_plus_def, intro allI impI, elim conjE)
    fix ti instr si si'
    assume ti: "Run (instr_sem_ISA instr) ti ()" "s_run_trace ti si = Some si'"
      and si: "instr_state_assms instr si"
    have "runs_preserve_invariant (liftS (instr_sem instr)) fetch_state_assms"
      unfolding fetch_state_assms_iff_invs instr_sem_def liftState_simp comp_def
      by (preserves_invariantI)
    then show "fetch_state_assms si'"
      using Run_runTraceS_Value_liftState[OF ti] si
      by (auto simp: instr_state_assms_def elim: PrePostE_elim)
  qed
  show "fetch_preserves_state_assms s"
  proof (unfold fetch_preserves_state_assms_plus_def, intro allI impI, elim conjE)
    fix tf instr sf sf'
    assume tf: "Run (isa.instr_fetch ISA) tf instr" "s_run_trace tf sf = Some sf'"
      and sf: "fetch_state_assms sf"
    have "runs_preserve_invariant (liftS instr_fetch) fetch_state_assms"
      unfolding fetch_state_assms_iff_invs instr_fetch_def liftState_simp comp_def
      by (preserves_invariantI)
    moreover have "runs_establish_invariant (liftS instr_fetch) pcc_tagged"
      by (rule instr_fetch_establishes_PCC_tagged[THEN PrePostE_weaken_post])
         (auto simp: register_defs PCC_tagged_def reg_inv_def)
    ultimately show "instr_state_assms instr sf'"
      using Run_runTraceS_Value_liftState[OF tf] sf
      by (auto simp: instr_state_assms_def elim: PrePostE_elim)
  qed
  show "s_invariant_holds (addr_trans_invariant False s) t s"
    \<comment> \<open>Holds trivially because of the @{locale Morello_Fixed_Address_Translation} setup;  the real proof
        obligations about the actual address translation will show up when instantiating that locale.\<close>
    by (rule take_s_invariant_holdsI[OF \<open>s_run_trace t s = Some s'\<close>])
       (auto simp: addr_trans_invariant_plus_def)
qed (use assms in \<open>auto simp: fetch_state_assms_def\<close>)

end

end
