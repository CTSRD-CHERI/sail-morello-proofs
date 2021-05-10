theory CHERI_Lemmas
  imports CHERI_Gen_Lemmas
begin

context Morello_Axiom_Automaton
begin

definition VAIsTaggedCap :: "VirtualAddress \<Rightarrow> bool" where
  "VAIsTaggedCap va \<longleftrightarrow> (VAIsCapability va \<and> CapIsTagSet (VirtualAddress_base va))"

definition VAIsSealedCap :: "VirtualAddress \<Rightarrow> bool" where
  "VAIsSealedCap va \<longleftrightarrow> (VAIsCapability va \<and> CapIsSealed (VirtualAddress_base va))"

lemma CheckCapability_CapIsSealed_False:
  assumes "Run (CheckCapability c addr sz perms acctype) t a"
  shows "CapIsSealed c \<longleftrightarrow> False"
  using assms
  by (auto simp: CheckCapability_def elim!: Run_bindE)

lemma Run_VAToBits64_vatype_Bits64[simp]:
  assumes "Run (VAToBits64 va) t addr"
  shows "VirtualAddress_vatype va = VA_Bits64"
  using assms
  by (auto simp: VAToBits64_def VAIsBits64_def)

lemma VADeref_VAIsSealedCap_False[simp]:
  assumes "Run (VACheckAddress va addr sz perms acctype) t u"
  shows "VAIsSealedCap va \<longleftrightarrow> False"
  using assms
  unfolding VACheckAddress_def
  by (auto simp: VAIsSealedCap_def VAIsCapability_def VAIsBits64_def CheckCapability_CapIsSealed_False elim!: Run_bindE Run_ifE)

lemma VADeref_not_sealed[derivable_capsE]:
  assumes "Run (VACheckAddress va addr sz perms acctype) t u"
  shows "\<not>VAIsSealedCap va"
  using assms
  by auto

lemma if_VADerefs_VAIsSealedCap_False[derivable_capsE]:
  assumes "Run (if b then VACheckAddress va vaddr sz perms acctype else VACheckAddress va vaddr sz' perms' acctype') t u"
  shows "\<not>VAIsSealedCap va"
  using assms
  by (auto split: if_splits)

(*lemma Run_case_MemOp_LOAD_STORE_not_VAIsSealedCap[derivable_capsE]:
  assumes "Run (case memop of MemOp_LOAD \<Rightarrow> VACheckAddress va addr sz perms acctype \<bind> m | MemOp_STORE \<Rightarrow> VACheckAddress va addr' sz' perms' acctype' \<bind> m' | MemOp_PREFETCH \<Rightarrow> return ()) t a"
    and "memop \<noteq> MemOp_PREFETCH"
    and "\<not>VAIsPCCRelative va"
  shows "\<not>VAIsSealedCap va"
  using assms
  by (cases memop) (auto elim!: Run_bindE)

lemma Run_case_MemOp_LOAD_STORE_not_VAIsSealedCap_pre_idx[derivable_capsE]:
  assumes "Run (case memop of MemOp_LOAD \<Rightarrow> VACheckAddress va addr sz perms acctype \<bind> m | MemOp_STORE \<Rightarrow> VACheckAddress va addr' sz' perms' acctype' \<bind> m' | MemOp_PREFETCH \<Rightarrow> return ()) t a"
    and "memop \<noteq> MemOp_PREFETCH"
    and "\<not>VAIsPCCRelative va"
    and "VAIsSealedCap va = VAIsSealedCap va'"
  shows "\<not>VAIsSealedCap va'"
  using assms
  by (cases memop) (auto elim!: Run_bindE)*)

lemma Run_case_MemOp_LOAD_STORE_not_VAIsSealedCap_generic[derivable_capsE]:
  assumes "Run (case memop of MemOp_LOAD \<Rightarrow> VACheckAddress va addr sz perms acctype \<bind> m | MemOp_STORE \<Rightarrow> VACheckAddress va addr' sz' perms' acctype' \<bind> m' | MemOp_PREFETCH \<Rightarrow> m'') t a"
    and "memop = MemOp_PREFETCH \<longrightarrow> Run m'' t a \<longrightarrow> \<not>VAIsSealedCap va"
  shows "\<not>VAIsSealedCap va"
  using assms
  by (cases memop) (auto elim!: Run_bindE)

declare Run_bindE'[where P = "\<lambda>t. VA_derivable va (run s t)" for va s, simplified, derivable_caps_combinators]

lemma VAAdd_derivable[derivable_capsE]:
  assumes t: "Run (VAAdd va offset) t va'"
    and "VAIsTaggedCap va \<and> VAIsTaggedCap va' \<and> (VAIsSealedCap va' \<longleftrightarrow> VAIsSealedCap va) \<longrightarrow> \<not>VAIsSealedCap va"
    and "VAIsTaggedCap va \<and> \<not>VAIsSealedCap va \<longrightarrow> VA_derivable va s"
  shows "VA_derivable va' s"
proof -
  have *: "VAIsSealedCap va' \<longleftrightarrow> VAIsSealedCap va"
    using t
    by (auto simp: VAAdd_def VAIsSealedCap_def VAIsCapability_def elim!: Run_bindE Run_ifE)
  have **: "VAIsTaggedCap va' \<longrightarrow> VAIsTaggedCap va"
    using t
    by (auto simp: VAAdd_def VAIsTaggedCap_def VAIsCapability_def elim!: Run_bindE Run_ifE Run_CapAdd_tag_imp)
  have "\<not>VAIsTaggedCap va' \<longrightarrow> VA_derivable va' s"
    by (cases "VirtualAddress_vatype va'")
       (auto simp add: VA_derivable_def derivable_caps_def VAIsTaggedCap_def VAIsCapability_def)
  moreover have "VAIsTaggedCap va' \<longrightarrow> VA_derivable va' (run s t)"
    using assms **
    unfolding VAAdd_def *
    by - (derivable_capsI simp: VAIsSealedCap_def)
  ultimately show ?thesis
    using non_cap_exp_Run_run_invI[OF non_cap_exp_VAAdd t]
    by auto
qed

lemma VAFromCapability_base_derivable_run:
  assumes "Run (VAFromCapability c) t va"
    and "c \<in> derivable_caps s"
  shows "VirtualAddress_base va \<in> derivable_caps (run s t)"
  using assms
  by (auto simp: VAFromCapability_base_derivable non_cap_exp_VAFromCapability[THEN non_cap_exp_Run_run_invI])

lemma BaseReg_read_VA_derivable[derivable_capsE]:
  assumes "Run (BaseReg_read n is_prefetch) t va"
    and "{''_R29'', ''PCC''} \<subseteq> accessible_regs s"
  shows "VA_derivable va (run s t)"
proof (cases "VirtualAddress_vatype va")
  case VA_Bits64
  then show ?thesis
    by (auto simp: VA_derivable_def)
next
  case VA_Capability
  then have "VirtualAddress_base va \<in> derivable_caps (run s t)"
    using assms
    unfolding BaseReg_read_def
    by - (derivable_capsI elim: VAFromCapability_base_derivable_run)
  then show ?thesis
    using VA_Capability
    by (auto simp: VA_derivable_def)
qed

lemmas BaseReg_read__1_VA_derivable[derivable_capsE] =
  BaseReg_read_VA_derivable[where is_prefetch = False, folded BaseReg_read__1_def]

lemma AltBaseReg_read_VA_derivable[derivable_capsE]:
  assumes "Run (AltBaseReg_read n is_prefetch) t va"
    and "{''_R29''} \<subseteq> accessible_regs s"
  shows "VA_derivable va (run s t)"
proof (cases "VirtualAddress_vatype va")
  case VA_Bits64
  then show ?thesis
    by (auto simp: VA_derivable_def)
next
  case VA_Capability
  then have "VirtualAddress_base va \<in> derivable_caps (run s t)"
    using assms
    unfolding AltBaseReg_read_def
    by - (derivable_capsI elim: VAFromCapability_base_derivable_run)
  then show ?thesis
    using VA_Capability
    by (auto simp: VA_derivable_def)
qed

declare AltBaseReg_read_VA_derivable[where is_prefetch = False, folded AltBaseReg_read__1_def, derivable_capsE]

lemmas VA_derivable_combinators[derivable_caps_combinators] =
  Run_bindE'[where P = "\<lambda>t. VA_derivable va (run s t)" for va s, simplified]
  Run_ifE[where thesis = "VA_derivable va (run s t)" and t = t for va s t]
  Run_letE[where thesis = "VA_derivable va (run s t)" and t = t for va s t]
  Run_case_prodE[where thesis = "VA_derivable va (run s t)" and t = t for va s t]

end

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

lemma determ_instrs_of_exp_bind_write_reg_ThisInstrAbstract:
  "determ_instrs_of_exp (write_reg ThisInstrAbstract_ref instr \<bind> f)"
  by (auto simp: determ_instrs_of_exp_def instr_of_trace_bind_write_reg_ThisInstrAbstract)

lemma no_reg_writes_to_instr_of_trace_None:
  assumes "hasTrace t m" and "no_reg_writes_to {''__ThisInstrAbstract''} m"
  shows "instr_of_trace t = None"
  using assms
  by (intro instr_of_trace_no_writes_None) (auto simp: no_reg_writes_to_def hasTrace_iff_Traces_final)

lemma no_reg_writes_to_determ_instrs_of_exp:
  assumes "no_reg_writes_to {''__ThisInstrAbstract''} m"
  shows "determ_instrs_of_exp m"
  using assms
  by (auto simp: determ_instrs_of_exp_def no_reg_writes_to_instrs_of_exp no_reg_writes_to_instr_of_trace_None)

lemma if_split_no_asm: "P x \<Longrightarrow> P y \<Longrightarrow> P (if b then x else y)"
  by auto

lemmas determ_instrs_of_exp_if_split_no_asm = if_split_no_asm[where P = determ_instrs_of_exp]

lemma hasTrace_intros:
  "Run m t a \<Longrightarrow> hasTrace t m"
  "hasException t m \<Longrightarrow> hasTrace t m"
  "hasFailure t m \<Longrightarrow> hasTrace t m"
  by (auto simp: hasTrace_iff_Traces_final hasException_iff_Traces_Exception hasFailure_iff_Traces_Fail)

lemma determ_instrs_of_exp_bind_no_reg_writes:
  assumes "determ_instrs_of_exp m" and"\<forall>a. no_reg_writes_to {''__ThisInstrAbstract''} (f a)"
  shows "determ_instrs_of_exp (bind m f)"
proof (unfold determ_instrs_of_exp_def, intro allI impI)
  fix t
  assume "hasTrace t (m \<bind> f)"
  then show "instrs_of_exp (m \<bind> f) = set_option (instr_of_trace t)"
  proof (cases rule: hasTrace_bind_cases)
    case (Bind tm am tf)
    then have "instr_of_trace (tm @ tf) = instr_of_trace tm"
      using assms(2)
      by (intro instr_of_trace_append_no_writes)
         (auto simp: no_reg_writes_to_def hasTrace_iff_Traces_final)
    with assms Bind show ?thesis
      by (auto simp: determ_instrs_of_exp_def instrs_of_exp_bind_no_writes hasTrace_intros)
  next
    case Fail
    with assms show ?thesis
      by (auto simp: determ_instrs_of_exp_def instrs_of_exp_bind_no_writes hasTrace_intros)
  next
    case Ex
    with assms show ?thesis
      by (auto simp: determ_instrs_of_exp_def instrs_of_exp_bind_no_writes hasTrace_intros)
  qed
qed

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

lemma determ_instrs_of_exp_DecodeA64:
  "determ_instrs_of_exp (DecodeA64 pc opcode)"
  by (unfold DecodeA64_def Let_def)
     (intro determ_instrs_of_exp_if_split_no_asm determ_instrs_of_exp_bind_write_reg_ThisInstrAbstract no_reg_writes_to_determ_instrs_of_exp;
            no_reg_writes_toI)

lemma determ_instrs_of_exp_DecodeExecute:
  "determ_instrs_of_exp (DecodeExecute enc opcode)"
  by (cases enc; auto simp: ExecuteA64_def ExecuteA32_def ExecuteT16_def ExecuteT32_def determ_instrs_of_exp_DecodeA64 no_reg_writes_to_determ_instrs_of_exp)

lemma determ_instrs_instr_sem:
  "determ_instrs_of_exp (instr_sem instr)"
  unfolding instr_sem_def TryInstructionExecute_def
  by (auto intro!: determ_instrs_of_exp_DecodeExecute[THEN determ_instrs_of_exp_bind_no_reg_writes]; no_reg_writes_toI)

lemma instrs_eq_instr_exp_assms_iff:
  assumes "instrs_of_exp m1 = instrs_of_exp m2"
  shows "instr_exp_assms m1 \<longleftrightarrow> instr_exp_assms m2"
  using assms
  unfolding instr_exp_assms_def invocation_instr_exp_assms_def load_instr_exp_assms_def
  unfolding exp_invokes_regs_def exp_invokes_indirect_regs_def exp_load_auths_def
  by auto

lemma instr_exp_assms_TryInstructionExecute_iff:
  "instr_exp_assms (TryInstructionExecute enc instr) \<longleftrightarrow> instr_exp_assms (DecodeExecute enc instr)"
  unfolding TryInstructionExecute_def SSAdvance_def bind_assoc
  by (intro instrs_eq_instr_exp_assms_iff instrs_of_exp_bind_no_writes allI)
     (no_reg_writes_toI simp: register_defs)

end

context Morello_Write_Cap_Automaton
begin

lemmas traces_enabled_return = non_cap_exp_return[THEN non_cap_exp_traces_enabledI]

lemma traces_enabled_Mem_read[traces_enabledI]:
  shows "traces_enabled (Mem_read addrdesc sz accdesc) s"
  by (unfold Mem_read_def, traces_enabledI)

lemma traces_enabled_ReadMem[traces_enabledI]:
  shows "traces_enabled (ReadMem addrdesc sz accdesc) s"
  by (unfold ReadMem_def, traces_enabledI)

lemma traces_enabled_ReadTaggedMem[traces_enabledI]:
  shows "traces_enabled (ReadTaggedMem addrdesc sz accdesc) s"
  by (unfold ReadTaggedMem_def, traces_enabledI intro: traces_enabled_return)

lemma traces_enabled_ReadTags[traces_enabledI]:
  shows "traces_enabled (ReadTags addrdesc sz accdesc) s"
  by (unfold ReadTags_def, traces_enabledI intro: traces_enabled_return)

lemma traces_enabled_Mem_set[traces_enabledI]:
  shows "traces_enabled (Mem_set addrdesc sz accdesc data) s"
  by (unfold Mem_set_def, traces_enabledI intro: traces_enabled_return)

lemma traces_enabled_WriteTaggedMem[traces_enabledI]:
  fixes tags :: "'a::len word" and data :: "'b::len word"
  assumes "Capability_of_tag_word (tags !! 0) (ucast data) \<in> derivable_caps s"
    and "sz \<noteq> 16 \<longrightarrow> Capability_of_tag_word (tags !! 1) (Word.slice 128 data) \<in> derivable_caps s"
  shows "traces_enabled (WriteTaggedMem addrdesc sz accdesc tags data) s"
  unfolding WriteTaggedMem_def
  by (traces_enabledI assms: assms intro: traces_enabled_return
                      simp: cap_of_mem_bytes_of_word_Capability_of_tag_word nth_ucast)

lemma cap_of_mem_bytes_B0_untagged[simp]:
  "cap_of_mem_bytes bytes B0 = Some c \<Longrightarrow> c !! 128 = False"
  by (auto simp: cap_of_mem_bytes_def bind_eq_Some_conv nth_ucast test_bit_above_size)

lemma traces_enabled_WriteTags[traces_enabledI]:
  assumes "tags = 0" and "LENGTH('a) = nat sz"
  shows "traces_enabled (WriteTags addrdesc sz (tags :: 'a::len word) accdesc) s"
  unfolding WriteTags_def write_tag_bool_def
  by (traces_enabledI assms: assms intro: traces_enabled_return not_tagged_derivable
                      intro: non_cap_exp_mword_nondet[THEN non_cap_exp_traces_enabledI]
                      simp: cap_of_mem_bytes_of_word_Capability_of_tag_word[where tag = False, simplified])

text \<open>Capability invocation\<close>

definition enabled_pcc :: "Capability \<Rightarrow> (Capability, register_value) axiom_state \<Rightarrow> bool" where
  "enabled_pcc c s \<equiv>
     c \<in> derivable_caps s \<or>
     (c \<in> exception_targets (read_from_KCC s) \<and> ex_traces) \<or>
     (c \<in> invoked_caps \<and>
      ((\<exists>c' \<in> derivable_caps s.
          CapIsTagSet c' \<and> CapGetObjectType c' = CAP_SEAL_TYPE_RB \<and>
          leq_cap CC c (CapUnseal c')) \<or>
       (\<exists>cc cd.
          cc \<in> derivable_caps s \<and> cd \<in> derivable_caps s \<and>
          invokable CC cc cd \<and>
          leq_cap CC c (CapUnseal cc)) \<or>
       (\<exists>c' \<in> derivable_mem_caps s.
          invokes_indirect_caps \<and>
          (leq_cap CC c c' \<or> leq_cap CC c (CapUnseal c') \<and> CapIsTagSet c' \<and> CapGetObjectType c' = CAP_SEAL_TYPE_RB))))"

lemma derivable_mem_caps_run_imp:
  assumes "c \<in> derivable_mem_caps s"
  shows "c \<in> derivable_mem_caps (run s t)"
  using assms derivable_mono[OF Un_mono[OF subset_refl[where A = UNKNOWN_caps] accessed_mem_caps_run_mono]]
  by (auto simp: derivable_mem_caps_def)

lemma run_append_derivable_mem_capsE[derivable_caps_combinators]:
  assumes "t = t1 @ t2" and "t = t1 @ t2 \<longrightarrow> c \<in> derivable_mem_caps (run (run s t1) t2)"
  shows "c \<in> derivable_mem_caps(run s t)"
  using assms
  by auto

lemma traces_enabled_PCC_set:
  assumes "enabled_pcc c s"
  shows "traces_enabled (write_reg PCC_ref c) s"
  using assms
  unfolding PCC_set_def enabled_pcc_def derivable_caps_def derivable_mem_caps_def
  by (intro traces_enabled_write_reg)
     (auto simp: register_defs is_sentry_def invokable_def CapIsSealed_def leq_cap_tag_imp[of CC, simplified])

definition enabled_branch_target :: "Capability \<Rightarrow> (Capability, register_value) axiom_state \<Rightarrow> bool" where
  "enabled_branch_target c s \<equiv>
     (CapIsTagSet c \<and> \<not>CapIsSealed c) \<longrightarrow> (\<forall>c' \<in> branch_caps c. enabled_pcc c' s)"

declare Run_ifE[where thesis = "enabled_branch_target c s" and a = c for c s, derivable_caps_combinators]
declare Run_letE[where thesis = "enabled_branch_target c s" and a = c for c s, derivable_caps_combinators]
declare Run_return_resultE[where P = "\<lambda>c. enabled_branch_target c s" for s, derivable_caps_combinators]

declare Run_bindE'[where P = "\<lambda>t. enabled_branch_target c (run s t)" for c s, simplified, derivable_caps_combinators]
declare Run_bindE[where thesis = "enabled_branch_target c s" and a = c for c s, derivable_caps_combinators]
declare if_split[where P = "\<lambda>c. enabled_branch_target c s" for s, THEN iffD2, derivable_capsI]

declare Run_ifE[where thesis = "enabled_branch_target (CapUnseal c) s" and a = c for c s, derivable_caps_combinators]
declare Run_letE[where thesis = "enabled_branch_target (CapUnseal c) s" and a = c for c s, derivable_caps_combinators]
declare Run_return_resultE[where P = "\<lambda>c. enabled_branch_target (CapUnseal c) s" for s, derivable_caps_combinators]

declare Run_bindE'[where P = "\<lambda>t. enabled_branch_target (CapUnseal c) (run s t)" for c s, simplified, derivable_caps_combinators]
declare Run_bindE[where thesis = "enabled_branch_target (CapUnseal c) s" and a = c for c s, simplified, derivable_caps_combinators]
declare if_split[where P = "\<lambda>c. enabled_branch_target (CapUnseal c) s" for s, THEN iffD2, derivable_capsI]

lemma run_append_enabled_branch_targetE[derivable_caps_combinators]:
  assumes "t = t1 @ t2" and "t = t1 @ t2 \<longrightarrow> enabled_branch_target c (run (run s t1) t2)"
  shows "enabled_branch_target c (run s t)"
  using assms
  by auto

lemma enabled_branch_targetI:
  assumes "CapIsTagSet c \<and> \<not>CapIsSealed c \<longrightarrow> (\<forall>c' \<in> branch_caps c. enabled_pcc c' s)"
  shows "enabled_branch_target c s"
  using assms
  by (auto simp: enabled_branch_target_def)

lemma exception_targets_mono:
  assumes "C \<subseteq> C'"
  shows "exception_targets C \<subseteq> exception_targets C'"
  using assms derivable_mono[of "\<Union>(caps_of_regval ` C)" "\<Union>(caps_of_regval ` C')"]
  by (auto simp: exception_targets_def)

lemma read_from_KCC_mono:
  "read_from_KCC s \<subseteq> read_from_KCC (run s t)"
  by (induction t rule: rev_induct) auto

lemma exception_targets_read_from_KCC_run_imp[derivable_caps_runI]:
  assumes "c \<in> exception_targets (read_from_KCC s)"
  shows "c \<in> exception_targets (read_from_KCC (run s t))"
  using assms exception_targets_mono[OF read_from_KCC_mono]
  by auto

lemma enabled_pcc_run_imp:
  assumes "enabled_pcc c s"
  shows "enabled_pcc c (run s t)"
  using assms derivable_caps_run_imp[of _ s t] derivable_mem_caps_run_imp[of _ s t]
  using exception_targets_read_from_KCC_run_imp
  unfolding enabled_pcc_def
  by fastforce

lemma enabled_branch_target_run_imp[derivable_caps_runI]:
  assumes "enabled_branch_target c s"
  shows "enabled_branch_target c (run s t)"
  using assms
  by (auto simp: enabled_branch_target_def intro: derivable_caps_run_imp enabled_pcc_run_imp)

lemma enabled_branch_target_CapUnseal:
  assumes "c \<in> derivable_caps s"
    and "CapIsTagSet c \<longrightarrow> CapGetObjectType c = CAP_SEAL_TYPE_RB \<and> branch_caps (CapUnseal c) \<subseteq> invoked_caps"
  shows "enabled_branch_target (CapUnseal c) s"
  using assms
  unfolding enabled_branch_target_def enabled_pcc_def
  by (fastforce intro: branch_caps_leq)

lemma untagged_enabled_branch_target[simp]:
  "\<not>CapIsTagSet c \<longrightarrow> enabled_branch_target c s"
  by (auto simp: enabled_branch_target_def)

lemma C_read_enabled_branch_target_CapUnseal[derivable_capsE]:
  assumes "Run (C_read n) t c" and "invocation_trace_assms t" and "{''_R29''} \<subseteq> accessible_regs s"
    and "CapIsTagSet c \<longrightarrow> CapGetObjectType c = CAP_SEAL_TYPE_RB \<and> n \<in> invoked_regs"
  shows  "enabled_branch_target (CapUnseal c) (run s t)"
  using assms
  by - (derivable_capsI intro: enabled_branch_target_CapUnseal simp: CapIsSealed_def)

lemma enabled_branch_target_CapWithTagClear[derivable_capsI]:
  "enabled_branch_target (CapWithTagClear c) s"
  "enabled_branch_target (CapUnseal (CapWithTagClear c)) s"
  by (auto simp: enabled_branch_target_def enabled_pcc_def derivable_caps_def branch_caps_128th_iff)

lemma if_CapWithTagClear_128th_iff[simp]:
  "(if clear then CapWithTagClear c else c) !! 128 \<longleftrightarrow> \<not>clear \<and> c !! 128"
  by auto

lemma enabled_branch_target_CapUnseal_if_clear:
  assumes "CapIsTagSet c \<longrightarrow> (\<forall>c' \<in> branch_caps (CapUnseal c). enabled_pcc c' s)"
  shows "enabled_branch_target (CapUnseal (if clear then CapWithTagClear c else c)) s"
  using assms
  by (auto simp: enabled_branch_target_def)

lemma derivable_enabled_branch_target:
  assumes "CapIsTagSet c \<longrightarrow> \<not>CapIsSealed c \<longrightarrow> c \<in> derivable_caps s"
  shows "enabled_branch_target c s"
  using assms branch_caps_derivable_caps[where c = c]
  by (auto simp: enabled_branch_target_def enabled_pcc_def)

lemma C_read_enabled_branch_target[derivable_capsE]:
  assumes "Run (C_read n) t c" and "{''_R29''} \<subseteq> accessible_regs s"
  shows "enabled_branch_target c (run s t)"
  using assms
  by (auto intro: derivable_enabled_branch_target C_read_derivable)

lemma CapSetOffset_enabled_branch_target[derivable_capsE]:
  assumes "Run (CapSetOffset c offset) t c'"
    and "c \<in> derivable_caps s"
  shows "enabled_branch_target c' s"
proof -
  have "CapIsSealed c' \<longleftrightarrow> CapIsSealed c"
    using assms
    by (auto simp: CapSetOffset_def elim!: Run_bindE)
  then show ?thesis
    using assms
    by (auto intro!: derivable_enabled_branch_target elim!: CapSetOffset_derivable)
qed

lemma CapSetValue_enabled_branch_target[derivable_capsE]:
  assumes "Run (CapSetValue c addr) t c'"
    and "c \<in> derivable_caps s"
  shows "enabled_branch_target c' s"
proof -
  have "CapIsSealed c' \<longleftrightarrow> CapIsSealed c"
    using assms
    unfolding CapSetValue_def CapIsSealed_def CapWithTagClear_def
    by (auto elim!: Run_bindE Run_letE split: if_splits)
  then show ?thesis
    using assms
    by (auto intro!: derivable_enabled_branch_target elim!: CapSetValue_derivable)
qed

lemma BranchAddr_enabled_pcc[derivable_capsE]:
  assumes "Run (BranchAddr c el) t c'" and "enabled_branch_target c s"
  shows "enabled_pcc c' s"
proof cases
  assume "CapIsTagSet c'"
  then have "c' \<in> branch_caps c" and "\<not>CapIsSealed c" and "CapIsTagSet c"
    using BranchAddr_in_branch_caps[OF assms(1)]
    using BranchAddr_not_sealed[OF assms(1)]
    by auto
  then show ?thesis
    using assms(2)
    by (auto simp: enabled_branch_target_def)
next
  assume "\<not>CapIsTagSet c'"
  then show ?thesis
    by (auto simp: enabled_pcc_def derivable_caps_def)
qed

lemma CVBAR_read_in_read_from_KCC:
  assumes "Run (CVBAR_read el) t c"
  shows "Regval_bitvector_129_dec c \<in> read_from_KCC (run s t)"
  using assms
  by (auto simp: CVBAR_read_def register_defs elim!: Run_bindE Run_ifE Run_read_regE)

lemma CVBAR_read__1_in_read_from_KCC:
  assumes "Run (CVBAR_read__1 u) t c"
  shows "Regval_bitvector_129_dec c \<in> read_from_KCC (run s t)"
  using assms
  by (auto simp: CVBAR_read__1_def elim!: Run_bindE CVBAR_read_in_read_from_KCC)

lemma CVBAR_read__1_exception_target[derivable_capsE]:
  assumes "Run (CVBAR_read__1 u) t c"
  shows "c \<in> exception_targets (read_from_KCC (run s t))"
  using CVBAR_read__1_in_read_from_KCC[OF assms, where s = s]
  by (auto simp: exception_targets_def intro!: derivable.Copy)

lemma exception_target_enabled_branch_target:
  assumes c: "CapIsTagSet c \<and> \<not>CapIsSealed c \<longrightarrow> c \<in> exception_targets (read_from_KCC s)" and ex: "ex_traces"
  shows "enabled_branch_target c s"
proof (unfold enabled_branch_target_def, intro impI ballI)
  fix c'
  assume valid: "CapIsTagSet c \<and> \<not>CapIsSealed c" and c': "c' \<in> branch_caps c"
  have "c' \<in> exception_targets (read_from_KCC s)"
    using branch_caps_derivable[OF c'] valid c
    by (auto simp: exception_targets_def)
  with ex show "enabled_pcc c' s"
    unfolding enabled_pcc_def
    by blast
qed

lemma CapSetValue_exception_target_enabled_branch_target:
  assumes t: "Run (CapSetValue c addr) t c'"
    and c: "c \<in> exception_targets (read_from_KCC s)" and ex: "ex_traces"
  shows "enabled_branch_target c' s"
proof -
  from t c have "CapIsTagSet c' \<and> \<not>CapIsSealed c' \<longrightarrow> c' \<in> exception_targets (read_from_KCC s)"
    unfolding CapSetValue_def exception_targets_def
    by (auto simp: update_subrange_vec_dec_test_bit CapIsSealed_def
             elim!: Run_bindE Run_letE
             dest!: update_subrange_addr_CapIsRepresentable_derivable[where a = True and C = "\<Union>(caps_of_regval ` read_from_KCC s)"])
  then show ?thesis
    using ex
    by (elim exception_target_enabled_branch_target)
qed

lemma invokable_enabled_pccI:
  assumes "invokable CC cc cd"
    and "cc \<in> derivable_caps s" and "cd \<in> derivable_caps s"
    and "leq_cap CC c (CapUnseal cc)"
    and "c \<in> invoked_caps"
  shows "enabled_pcc c s"
  using assms
  unfolding enabled_pcc_def
  by auto

lemma CapGetObjectType_CapWithTagClear_eq[simp]:
  "CapGetObjectType (CapWithTagClear c) = CapGetObjectType c"
  by (auto simp: CapGetObjectType_def CapWithTagClear_def slice_set_bit_above)

lemma CapGetObjectType_if_CapWithTagClear_eq:
  "CapGetObjectType (if clear then CapWithTagClear c else c) = CapGetObjectType c"
  by auto

lemma branch_sealed_pair_enabled_pcc:
  assumes "CapGetObjectType (if clear then CapWithTagClear cc else cc) = CapGetObjectType cd"
    and "CapIsTagSet cc" and "CapIsTagSet cd"
    and "cap_permits CAP_PERM_EXECUTE cc" and "\<not>cap_permits CAP_PERM_EXECUTE cd"
    and "cap_permits CAP_PERM_BRANCH_SEALED_PAIR cc" and "cap_permits CAP_PERM_BRANCH_SEALED_PAIR cd"
    and "CAP_MAX_FIXED_SEAL_TYPE < uint (CapGetObjectType cc)"
    and "cc \<in> derivable_caps s" and "cd \<in> derivable_caps s"
    and "branch_caps (CapUnseal cc) \<subseteq> invoked_caps"
  shows "\<forall>c' \<in> branch_caps (CapUnseal cc). enabled_pcc c' s"
  using assms
  unfolding CapGetObjectType_if_CapWithTagClear_eq
  by (auto simp: invokable_def CapIsSealed_def is_sentry_def split: if_splits
           intro!: branch_caps_leq invokable_enabled_pccI[of cc cd])

lemma (in Write_Cap_Assm_Automaton) traces_enabled_write_IDC_CCall:
  assumes "c \<in> invoked_caps" and "invokable CC cc cd"
    and "isa.caps_of_regval ISA (regval_of r v) = {c}"
    and "cc \<in> derivable (initial_caps \<union> accessed_caps (\<not>invokes_indirect_caps \<and> use_mem_caps) s)"
    and "cd \<in> derivable (initial_caps \<union> accessed_caps (\<not>invokes_indirect_caps \<and> use_mem_caps) s)"
    and "name r \<in> IDC ISA - write_privileged_regs ISA"
    and "leq_cap CC c (unseal_method CC cd)"
  shows "traces_enabled (write_reg r v) s"
  using assms
  by (intro traces_enabled_write_reg) auto

lemma traces_enabled_C_set_29_branch_sealed_pair:
  assumes "CapGetObjectType (if clear then CapWithTagClear cc else cc) = CapGetObjectType cd"
    and "CapIsTagSet cc" and "CapIsTagSet cd"
    and "cap_permits CAP_PERM_EXECUTE cc" and "\<not>cap_permits CAP_PERM_EXECUTE cd"
    and "cap_permits CAP_PERM_BRANCH_SEALED_PAIR cc" and "cap_permits CAP_PERM_BRANCH_SEALED_PAIR cd"
    and "CAP_MAX_FIXED_SEAL_TYPE < uint (CapGetObjectType cc)"
    and "cc \<in> derivable_caps s" and "cd \<in> derivable_caps s"
    and "CapUnseal cd \<in> invoked_caps"
  shows "traces_enabled (C_set 29 (CapUnseal cd)) s"
  using assms
  unfolding CapGetObjectType_if_CapWithTagClear_eq
  by (fastforce simp: C_set_def R_set_def derivable_caps_def invokable_def CapIsSealed_def is_sentry_def register_defs
                intro: traces_enabled_write_IDC_CCall[of "CapUnseal cd" cc cd])

lemma (in Write_Cap_Assm_Automaton) traces_enabled_write_IDC_sentry:
  assumes "c \<in> invoked_indirect_caps"
    and "isa.caps_of_regval ISA (regval_of r v) = {c}"
    and "cs \<in> derivable (initial_caps \<union> accessed_reg_caps s)"
    and "is_indirect_sentry_method CC cs" and "is_sealed_method CC cs"
    and "leq_cap CC c (unseal_method CC cs)"
    and "name r \<in> IDC ISA - write_privileged_regs ISA"
  shows "traces_enabled (write_reg r v) s"
  using assms
  by (intro traces_enabled_write_reg) auto

lemma traces_enabled_C_set_29:
  assumes "c \<in> derivable_caps s"
  shows "traces_enabled (C_set 29 c) s"
  using assms
  by (auto simp: C_set_def R_set_def register_defs derivable_caps_def
           intro!: traces_enabled_write_reg)

lemma leq_cap_derivable_mem_caps:
  assumes "c \<in> derivable_mem_caps s"
    and "leq_cap CC c' c"
  shows "c' \<in> derivable_mem_caps s"
  using assms
  by (auto simp: derivable_mem_caps_def leq_cap_def intro: derivable.Restrict)

lemma CapSquashPostLoadCap_invoked_cap[derivable_capsE]:
  assumes "Run (CapSquashPostLoadCap c base) t c'"
    and "CapIsTagSet c \<longrightarrow> mem_branch_caps c \<subseteq> invoked_caps"
    and "CapIsTagSet c'"
  shows "c' \<in> invoked_caps"
  using assms
  by (cases rule: CapSquashPostLoadCap_cases)
     (auto simp: mem_branch_caps_def branch_caps_def CapIsSealed_def split: if_splits)

lemma traces_enabled_C_set_mem_cap:
  assumes "Run (CapSquashPostLoadCap c base) t c'" "load_cap_trace_assms t"
    and "VA_from_load_auth base"
    and "c \<in> derivable_mem_caps s"
    and "invokes_indirect_caps \<and> CapIsTagSet c' \<and> CapIsTagSet c \<longrightarrow> n = 29 \<and> mem_branch_caps c \<subseteq> invoked_caps"
  shows "traces_enabled (C_set n c') s"
proof cases
  assume indirect: "invokes_indirect_caps \<and> CapIsTagSet c'"
  then have c: "CapIsTagSet c" and c': "c' \<in> derivable_mem_caps s"
    using assms(1,4)
    by (auto elim!: CapSquashPostLoadCap_cases leq_cap_derivable_mem_caps[of c s c'] intro: clear_perm_leq_cap)
  then have "c' \<in> invoked_caps"
    using assms(1,5) indirect
    by (elim CapSquashPostLoadCap_invoked_cap) auto
  then have "traces_enabled (write_reg R29_ref c') s"
    using c c' assms indirect
    by (intro traces_enabled_write_reg) (auto simp: register_defs derivable_mem_caps_def)
  moreover have "n = 29"
    using assms indirect c
    by auto
  ultimately show ?thesis
    by (auto simp: C_set_def R_set_def)
next
  assume "\<not>(invokes_indirect_caps \<and> CapIsTagSet c')"
  then have "c' \<in> derivable_caps s"
    using assms(1-4)
    by (elim CapSquashPostLoadCap_from_load_auth_reg_derivable_caps) auto
  then show ?thesis
    by (auto simp: C_set_def R_set_def register_defs derivable_caps_def
             intro!: traces_enabled_write_reg traces_enabled_bind non_cap_expI[THEN non_cap_exp_traces_enabledI])
qed

lemma enabled_branch_target_CapUnseal_mem_cap:
  assumes "Run (CapSquashPostLoadCap c base) t c'" "load_cap_trace_assms t"
    and "VA_from_load_auth base"
    and "c \<in> derivable_mem_caps s"
    and "CapIsTagSet c' \<and> CapIsTagSet c \<and> CapGetObjectType c' = CapGetObjectType c \<longrightarrow> CapGetObjectType c = CAP_SEAL_TYPE_RB \<and> mem_branch_caps c \<subseteq> invoked_caps"
  shows "enabled_branch_target (CapUnseal c') s"
proof cases
  assume tagged: "CapIsTagSet c'"
  moreover have "c' \<in> derivable_mem_caps s"
    using assms(1,4)
    by (elim CapSquashPostLoadCap_cases leq_cap_derivable_mem_caps[of c s c']) (auto intro: clear_perm_leq_cap)
  moreover have *: use_mem_caps if "invoked_indirect_caps = {}"
    using tagged assms(1-3)
    by (elim Run_CapSquashPostLoadCap_use_mem_caps[OF _ _ _ _ that]) auto
  ultimately have "c' \<in> derivable_mem_caps s \<and> invokes_indirect_caps \<or> c' \<in> derivable_caps s"
    using assms(5) derivable_mem_caps_derivable_caps[of c' s]
    unfolding derivable_caps_def
    by (cases "invokes_indirect_caps") auto
  moreover have "CapGetObjectType c' = CAP_SEAL_TYPE_RB \<and> branch_caps (CapUnseal c') \<subseteq> invoked_caps"
    using assms(1,5) tagged
    unfolding mem_branch_caps_def
    by (elim CapSquashPostLoadCap_cases) (auto simp: CapIsSealed_def)
  ultimately show ?thesis
    using branch_caps_leq
    unfolding enabled_branch_target_def enabled_pcc_def mem_branch_caps_def
    by auto
qed (auto intro: derivable_enabled_branch_target)

lemma CapSquashPostLoadCap_sealed_branch_caps_invoked_caps[derivable_capsE]:
  assumes "Run (CapSquashPostLoadCap c base) t c'"
    and "CapIsTagSet c'"
    and "(c' = c \<or> c' = CapClearPerms c mutable_perms) \<longrightarrow> CapIsSealed c \<and> branch_caps (CapUnseal c) \<subseteq> invoked_caps"
  shows "branch_caps (CapUnseal c') \<subseteq> invoked_caps"
  using assms
  by (cases rule: CapSquashPostLoadCap_cases) auto

lemma invokes_mem_cap_leq_enabled_pccI:
  assumes "c' \<in> derivable_mem_caps s" and "leq_cap CC c c'"
    and "c \<in> invoked_caps"
    and "invokes_indirect_caps"
  shows "enabled_pcc c s"
  using assms
  unfolding enabled_pcc_def
  by blast

lemma VAIsBits64_iff_not_VAIsCapability:
  "VAIsBits64 va \<longleftrightarrow> \<not>VAIsCapability va"
  by (cases "VirtualAddress_vatype va") (auto simp: VAIsBits64_def VAIsCapability_def)

lemma enabled_branch_target_CapSquashPostLoadCap:
  assumes "Run (CapSquashPostLoadCap c base) t c'" "load_cap_trace_assms t"
    and "c \<in> derivable_mem_caps s"
    and "\<not>invokes_indirect_caps \<longrightarrow> VA_from_load_auth base"
    and "(CapIsTagSet c \<and> \<not>CapIsSealed c \<and> invokes_indirect_caps) \<longrightarrow> mem_branch_caps c \<subseteq> invoked_caps"
  shows "enabled_branch_target c' s"
proof (cases "invokes_indirect_caps")
  case True
  note leqI = branch_caps_leq leq_cap_trans[OF branch_caps_leq clear_perm_leq_cap]
  show ?thesis
    using assms True
    by (cases rule: CapSquashPostLoadCap_cases)
       (auto simp: enabled_branch_target_def mem_branch_caps_def CapIsSealed_def
             elim!: invokes_mem_cap_leq_enabled_pccI[OF _ _ _ True] leqI)
next
  case False
  then have "c' \<in> derivable_caps s"
    using assms
    by (elim CapSquashPostLoadCap_from_load_auth_reg_derivable_caps) auto
  then show ?thesis
    by (auto intro: derivable_enabled_branch_target)
qed

lemma clear_perm_derivable_mem_caps[derivable_capsI]:
  assumes "c \<in> derivable_mem_caps s" and "CapIsTagSet c \<longrightarrow> \<not>CapIsSealed c"
  shows "clear_perm perms c \<in> derivable_mem_caps s"
  using assms
  unfolding derivable_mem_caps_def
  by (auto elim: clear_perm_derivable)

declare Run_ifE[where thesis = "c \<in> derivable_mem_caps s" and a = c for c s, derivable_caps_combinators]
declare Run_letE[where thesis = "c \<in> derivable_mem_caps s" and a = c for c s, derivable_caps_combinators]
declare Run_return_resultE[where P = "\<lambda>c. c \<in> derivable_mem_caps s" for s, derivable_caps_combinators]
declare Run_bindE'[where P = "\<lambda>t. c \<in> derivable_mem_caps (run s t)" for c s, simplified, derivable_caps_combinators]
declare Run_bindE[where thesis = "c \<in> derivable_mem_caps s" and a = c for c s, derivable_caps_combinators]
declare if_split[where P = "\<lambda>c. c \<in> derivable_mem_caps s" for s, THEN iffD2, derivable_capsI]
declare Run_case_prodE[where thesis = "c \<in> derivable_mem_caps s" and a = c for c s, derivable_caps_combinators]

lemma bind_derivable_caps[derivable_caps_combinators]:
  assumes "Run (m \<bind> f) t a"
    and "\<And>tm am tf. Run m tm am \<Longrightarrow> Run (f am) tf a \<Longrightarrow> t = tm @ tf \<Longrightarrow> c \<in> derivable_mem_caps (run (run s tm) tf)"
  shows "c \<in> derivable_mem_caps (run s t)"
  using assms
  by (auto elim: Run_bindE)

lemma CapWithTagClear_derivable_mem_caps[intro, simp, derivable_capsI]:
  "CapWithTagClear c \<in> derivable_mem_caps s"
  by (auto simp: derivable_mem_caps_def)

lemma CapSquashPostLoadCap_derivable_mem_caps[derivable_capsE]:
  assumes "Run (CapSquashPostLoadCap c base) t c'"
    and "c \<in> derivable_mem_caps s"
  shows "c' \<in> derivable_mem_caps s"
  using assms
  by (cases rule: CapSquashPostLoadCap_cases) (auto intro: clear_perm_derivable_mem_caps)

lemma CapabilityFromData_derivable_mem_caps[derivable_capsE]:
  fixes s :: "(Capability, register_value) axiom_state"
  shows "Run (CapabilityFromData n arg1 arg2) t c \<Longrightarrow> n = 128 \<Longrightarrow> Capability_of_tag_word (arg1 !! 0) arg2 \<in> derivable_mem_caps s \<Longrightarrow> c \<in> derivable_mem_caps s"
  by (auto simp: CapabilityFromData_def)

(* Common patterns of capability/data conversions in memory access helpers *)
lemma Capability_of_tag_word_derivable_mem_caps_pairE[derivable_capsE]:
  assumes "x = (tag, data)"
    and "Capability_of_tag_word ((vec_of_bits [access_vec_dec (fst x) i] :: 1 word) !! 0) (slice (snd x) j 128) \<in> derivable_mem_caps s"
  shows "Capability_of_tag_word ((vec_of_bits [access_vec_dec tag i] :: 1 word) !! 0) (slice data j 128) \<in> derivable_mem_caps s"
  using assms
  by auto

lemma Capability_of_tag_word_derivable_mem_caps_rev_pairE[derivable_capsE]:
  assumes "x = (data, tag)"
    and "Capability_of_tag_word ((vec_of_bits [access_vec_dec (snd x) i] :: 1 word) !! 0) (slice (fst x) j 128) \<in> derivable_mem_caps s"
  shows "Capability_of_tag_word ((vec_of_bits [access_vec_dec tag i] :: 1 word) !! 0) (slice data j 128) \<in> derivable_mem_caps s"
  using assms
  by auto

declare Run_case_prodE[where thesis = "Capability_of_tag_word tag word \<in> derivable_mem_caps s" for tag word s, derivable_capsE]
declare Run_letE[where thesis = "Capability_of_tag_word tag word \<in> derivable_mem_caps s" for tag word s, derivable_capsE]

lemma Capability_of_tag_word_return_rev_derivable_mem_caps_pairE[derivable_capsE]:
  assumes "Run (return (data, tag)) t x"
    and "t = [] \<longrightarrow> Capability_of_tag_word ((vec_of_bits [access_vec_dec tag i] :: 1 word) !! 0) (slice data j 128) \<in> derivable_mem_caps s"
  shows "Capability_of_tag_word ((vec_of_bits [access_vec_dec (snd x) i] :: 1 word) !! 0) (slice (fst x) j 128) \<in> derivable_mem_caps s"
  using assms
  by auto

lemma Capability_of_tag_word_False_derivable[intro, simp, derivable_capsI]:
  "Capability_of_tag_word False data \<in> derivable_mem_caps s"
  by (auto simp: derivable_mem_caps_def)

declare derivable_mem_caps_run_imp[derivable_caps_runI]

(* declare MemAtomicCompareAndSwapC_derivable[derivable_capsE del] *)

lemma MemAtomicCompareAndSwapC_from_load_auth_derivable_caps[derivable_capsE]:
  assumes "Run (MemAtomicCompareAndSwapC vaddr address expectedcap newcap ldacctype stacctype) t c" and "inv_trace_assms s t"
    and "VA_from_load_auth vaddr" and "\<not>invokes_indirect_caps"
  shows "c \<in> derivable_caps (run s t)"
  using assms
  unfolding MemAtomicCompareAndSwapC_def
  by - (derivable_capsI_with \<open>split_inv_trace_assms_append | solves \<open>accessible_regsI\<close>\<close>
          elim: Run_ifE[where thesis = "Capability_of_tag_word ((vec_of_bits [access_vec_dec (snd x) i] :: 1 word) !! 0) (slice (fst x) j 128) \<in> derivable_mem_caps s" and a = x for x i j s])

lemma MemAtomicC_derivable_mem_caps[derivable_capsE]:
  assumes "Run (MemAtomicC address op v ldacctype stacctype) t c"
  shows "c \<in> derivable_mem_caps (run s t)"
  using assms
  unfolding MemAtomicC_def
  by - (derivable_capsI elim: Run_ifE[where thesis = "Capability_of_tag_word ((vec_of_bits [access_vec_dec (snd x) i] :: 1 word) !! 0) (slice (fst x) j 128) \<in> derivable_mem_caps s" and a = x for x i j s])

lemma traces_enabled_C_set_if_sentry:
  fixes c :: Capability and n :: int
  assumes "indirect_sentry \<and> CapIsTagSet c \<longrightarrow> n = 29 \<and> CapGetObjectType c = CAP_SEAL_TYPE_LB \<and> c \<in> derivable_caps s \<and> CapUnseal c \<in> invoked_indirect_caps"
    and "indirect_sentry \<and> \<not>CapIsTagSet c \<longrightarrow> traces_enabled (C_set n (CapUnseal c)) s"
    and "\<not>indirect_sentry \<longrightarrow> traces_enabled (C_set n c) s"
  shows "traces_enabled (C_set n (if indirect_sentry then CapUnseal c else c)) s"
proof cases
  assume *: "indirect_sentry \<and> CapIsTagSet c"
  then have "c \<in> derivable (UNKNOWN_caps \<union> accessed_reg_caps s)"
    using no_invoked_indirect_caps_if_use_mem_caps assms
    unfolding derivable_caps_def accessed_caps_def
    by auto
  then show ?thesis
    using assms *
    unfolding C_set_def R_set_def
    by (auto simp: register_defs is_indirect_sentry_def derivable_caps_def CapIsSealed_def
             intro!: traces_enabled_write_IDC_sentry split: if_splits)
next
  assume "\<not>(indirect_sentry \<and> CapIsTagSet c)"
  then show ?thesis
    using assms(2,3)
    by auto
qed

(* declare Run_ifE[where thesis = "CapUnseal c \<in> invoked_caps" and a = c for c, derivable_caps_combinators] *)

lemma Run_CSP_or_C_read_invoked_indirect_caps:
  assumes "Run (if n = 31 then csp_read else C_read n) t c"
    and "n \<noteq> 31"
    and "Run (C_read n) t c \<longrightarrow> CapUnseal c \<in> invoked_indirect_caps"
  shows "CapUnseal c \<in> invoked_indirect_caps"
  using assms
  by auto

lemma traces_enabled_BranchToCapability[traces_enabledI]:
  assumes "enabled_branch_target c s"
  shows "traces_enabled (BranchToCapability c branch_type) s"
  unfolding BranchToCapability_def
  by (traces_enabledI assms: assms intro: traces_enabled_PCC_set non_cap_expI[THEN non_cap_exp_traces_enabledI] simp: BranchTaken_ref_def PSTATE_ref_def PC_ref_def)

lemma enabled_branch_target_set_0th[derivable_capsI]:
  assumes "enabled_branch_target c s"
  shows "enabled_branch_target (update_vec_dec c 0 (Morello.Bit 0)) s"
  using assms
  by (auto simp: enabled_branch_target_def branch_caps_def CapGetValue_def nth_ucast test_bit_set_gen)

lemma traces_enabled_BranchXToCapability[traces_enabledI]:
  assumes "enabled_branch_target c s"
  shows "traces_enabled (BranchXToCapability c branch_type) s"
  unfolding BranchXToCapability_def
  by (traces_enabledI assms: assms intro: non_cap_expI[THEN non_cap_exp_traces_enabledI] simp: PSTATE_ref_def)

text \<open>Sealing and unsealing\<close>

lemma CapSetObjectType_derivable[derivable_capsI]:
  assumes "c \<in> derivable_caps s" and "c' \<in> derivable_caps s"
    and "CapIsTagSet c" and "CapIsTagSet c'"
    and "\<not>CapIsSealed c" and "\<not>CapIsSealed c'"
    and "cap_permits CAP_PERM_SEAL c'"
    and "unat (CapGetValue c') \<in> get_mem_region CC c'"
  shows "CapSetObjectType c (CapGetValue c') \<in> derivable_caps s"
proof -
  from assms have "permits_seal_method CC c'"
    by (auto simp: CC_def)
  then have "seal_method CC c (get_cursor_method CC c') \<in> derivable (UNKNOWN_caps \<union> accessed_caps (invoked_indirect_caps = {} \<and> use_mem_caps) s)"
    using assms
    by (intro derivable.Seal) (auto simp: derivable_caps_def)
  then show ?thesis
    by (auto simp: seal_def derivable_caps_def)
qed

lemma CapSetObjectType_sentry_derivable:
  assumes "c \<in> derivable_caps s"
    and "\<not>CapIsSealed c"
    and "otype \<in> {CAP_SEAL_TYPE_RB, CAP_SEAL_TYPE_LPB, CAP_SEAL_TYPE_LB}"
  shows "CapSetObjectType c otype \<in> derivable_caps s"
proof -
  note simps = CapGetObjectType_CapSetObjectType_and_mask
  have "seal_method CC c (unat otype) \<in> derivable (UNKNOWN_caps \<union> accessed_caps (invoked_indirect_caps = {} \<and> use_mem_caps) s)"
    if "CapIsTagSet c"
    using that assms
    by (intro derivable.SealEntry)
       (auto simp: is_sentry_def is_indirect_sentry_def seal_def derivable_caps_def simps and_mask_bintr)
  then show ?thesis
    by (auto simp: seal_def derivable_caps_def)
qed

lemma CapSetObjectType_sentries_derivable[derivable_capsI]:
  assumes "c \<in> derivable_caps s"
    and "\<not>CapIsSealed c"
  shows "CapSetObjectType c CAP_SEAL_TYPE_RB \<in> derivable_caps s"
    and "CapSetObjectType c CAP_SEAL_TYPE_LPB \<in> derivable_caps s"
    and "CapSetObjectType c CAP_SEAL_TYPE_LB \<in> derivable_caps s"
  using assms
  by (auto intro: CapSetObjectType_sentry_derivable)

lemma CapIsInBounds_cursor_in_mem_region:
  assumes "Run (CapIsInBounds c) t a" and "a"
  shows "unat (CapGetValue c) \<in> get_mem_region CC c"
  using assms
  unfolding CapIsInBounds_def get_mem_region_def
  by (auto simp: CapGetBounds_get_base CapGetBounds_get_limit elim!: Run_bindE)

abbreviation check_global_perm :: "Capability \<Rightarrow> Capability \<Rightarrow> Capability" where
  "check_global_perm c auth \<equiv>
     (if \<not>cap_permits CAP_PERM_GLOBAL auth then clear_perm CAP_PERM_GLOBAL c else c)"

lemma CapUnseal_check_global_derivable:
  assumes "cap_permits CAP_PERM_UNSEAL auth"
    and "c \<in> derivable_caps s" and "auth \<in> derivable_caps s"
    and "CapIsTagSet auth"
    and "CapIsSealed c" and "\<not>CapIsSealed auth"
    and "CapGetObjectType c = CapGetValue auth"
    and in_bounds: "\<exists>t. Run (CapIsInBounds auth) t True"
  shows "check_global_perm (CapUnseal c) auth \<in> derivable_caps s"
proof -
  have "unat (CapGetValue auth) \<in> get_mem_region CC auth"
    using in_bounds
    by (auto simp: elim!: Run_bindE CapIsInBounds_cursor_in_mem_region)
  then have "clear_global_unless CC (is_global_method CC auth) (unseal_method CC c) \<in> derivable (UNKNOWN_caps \<union> accessed_caps (invoked_indirect_caps = {} \<and> use_mem_caps) s)"
    if "CapIsTagSet c"
    using that assms
    by (intro derivable.Unseal) (auto simp: derivable_caps_def)
  then show ?thesis
    by (auto simp: derivable_caps_def clear_global_unless_def)
qed

text \<open>Derivability of capabilities that are a subset of already derivable ones.\<close>

lemma CapIsSubSetOf_WithTagSet_derivable:
  assumes "Run (CapIsSubSetOf c c') t a" and "a"
    and "c' \<in> derivable_caps s"
    and "CapIsTagSet c'" and "\<not>CapIsSealed c'" and "\<not>CapIsSealed c"
    and "get_base c \<le> get_limit c"
  shows "CapWithTagSet c \<in> derivable_caps s"
proof -
  have "leq_perms (to_bl (CapGetPermissions c)) (to_bl (CapGetPermissions c'))"
    using assms
    unfolding leq_perms_to_bl_iff CapIsSubSetOf_def
    by (auto elim!: Run_bindE simp: AND_NOT_eq_0_iff)
  then have "leq_cap CC (CapWithTagSet c) c'"
    using assms
    unfolding leq_cap_def leq_bounds_def CapIsSubSetOf_def
    by (auto simp: CapGetBounds_get_base CapGetBounds_get_limit
             elim: leq_perms_cap_permits_imp elim!: Run_bindE)
  then show "CapWithTagSet c \<in> derivable_caps s"
    using \<open>c' \<in> derivable_caps s\<close> and \<open>CapIsTagSet c'\<close>
    by (auto simp: derivable_caps_def intro: derivable.Restrict)
qed

lemma (in Cap_Axiom_Assm_Automaton) derivable_caps_invariant:
  assumes "c \<in> derivable_caps s"
    and "accessed_caps_invariant s"
    and "is_tagged_method CC c"
  shows "cap_invariant c"
  using assms
  by (auto simp: accessed_caps_invariant_def derivable_caps_def intro: derivable_cap_invariant)

lemma CapIsSubSetOf_CapUnseal_derivable:
  assumes "Run (CapIsSubSetOf c c') t a" and "a" and "\<exists>t. inv_trace_assms s t"
    and "c \<in> derivable_caps s"
    and "c' \<in> derivable_caps s"
    and "CapIsTagSet c'" and "\<not>CapIsSealed c'"
  shows "CapUnseal c \<in> derivable_caps s"
proof cases
  assume tag: "CapIsTagSet c"
  then have "get_base (CapUnseal c) \<le> get_limit (CapUnseal c)"
    using derivable_caps_invariant[OF \<open>c \<in> derivable_caps s\<close>]
    using inv_trace_assms_accessed_caps_invariant[where s = s] assms(3)
    unfolding get_bounds_CapUnseal_eq
    by (auto simp: cap_invariant_def)
  then have "CapWithTagSet (CapUnseal c) \<in> derivable_caps s"
    using assms
    by (intro CapIsSubSetOf_WithTagSet_derivable) (auto simp: CapIsSubSetOf_CapUnseal_eq)
  then show ?thesis
    using tag
    by (auto simp: CapIsTagSet_CapWithTagSet_eq)
next
  assume "\<not>CapIsTagSet c"
  then show ?thesis
    by (auto simp: derivable_caps_def)
qed

lemmas inv_trace_assms_ex_trace[derivable_capsE] = exI[where P = "\<lambda>t. inv_trace_assms s t" for s]

(*lemma CapIsInternalExponent_CapSetObjectType_iff[simp]:
  "CapIsInternalExponent (CapSetObjectType c otype) = CapIsInternalExponent c"
  unfolding CapIsInternalExponent_def CapSetObjectType_def CAP_OTYPE_LO_BIT_def CAP_OTYPE_HI_BIT_def CAP_IE_BIT_def
  by (auto simp: update_subrange_vec_dec_test_bit)*)

text \<open>Resetting the system requires system access permission\<close>

lemma CapIsSystemAccessEnabled_True_no_system_reg_access_False:
  assumes "Run (CapIsSystemAccessEnabled u) t True" and "sysreg_trace_assms s t"
    and "{''PCC''} \<subseteq> accessible_regs s"
  obtains "\<not>no_system_reg_access"
  using assms
  by (elim CapIsSystemAccessEnabled_no_system_reg_access_cases) auto

lemma Run_RMR_EL1_SysRegWrite_system_reg_access:
  assumes "Run (RMR_EL1_SysRegWrite_0ae19f794f511c7a el op0 op1 crn op2 crm v) t u" and "sysreg_trace_assms s t"
    and "{''PCC''} \<subseteq> accessible_regs s"
  obtains "\<not>no_system_reg_access"
  using assms
  by (auto simp: RMR_EL1_SysRegWrite_0ae19f794f511c7a_def HaveCapabilitiesExt_def no_reg_writes_runs_no_reg_writes
           elim!: Run_bindE Run_ifE Run_and_boolM_E accessible_regs_no_writes_run
                  CapIsSystemAccessEnabled_True_no_system_reg_access_False)

lemma Run_RMR_EL2_SysRegWrite_system_reg_access:
  assumes "Run (RMR_EL2_SysRegWrite_df7b9a989e2495d2 el op0 op1 crn op2 crm v) t u" and "sysreg_trace_assms s t"
    and "{''PCC''} \<subseteq> accessible_regs s"
  obtains "\<not>no_system_reg_access"
  using assms
  by (auto simp: RMR_EL2_SysRegWrite_df7b9a989e2495d2_def HaveCapabilitiesExt_def no_reg_writes_runs_no_reg_writes
           elim!: Run_bindE Run_ifE Run_and_boolM_E accessible_regs_no_writes_run
                  CapIsSystemAccessEnabled_True_no_system_reg_access_False)

lemma Run_RMR_EL3_SysRegWrite_system_reg_access:
  assumes "Run (RMR_EL3_SysRegWrite_2849130fc457929e el op0 op1 crn op2 crm v) t u" and "sysreg_trace_assms s t"
    and "{''PCC''} \<subseteq> accessible_regs s"
  obtains "\<not>no_system_reg_access"
  using assms
  by (auto simp: RMR_EL3_SysRegWrite_2849130fc457929e_def HaveCapabilitiesExt_def no_reg_writes_runs_no_reg_writes
          elim!: Run_bindE Run_ifE Run_and_boolM_E accessible_regs_no_writes_run
                  CapIsSystemAccessEnabled_True_no_system_reg_access_False)

lemma Run_AArch64_AutoGen_SysRegWrite_RMR_EL_system_reg_access:
  assumes "Run (AArch64_AutoGen_SysRegWrite el op0 op1 crn op2 crm v) t u" and "sysreg_trace_assms s t"
    and "op0 = 3 \<and> op1 \<in> {0, 4, 6} \<and> op2 = 2 \<and> crn = 12 \<and> crm = 0"
    and "{''PCC''} \<subseteq> accessible_regs s"
  obtains "\<not>no_system_reg_access"
  using assms
  by (auto simp: AArch64_AutoGen_SysRegWrite_def
           elim!: Run_RMR_EL1_SysRegWrite_system_reg_access
                  Run_RMR_EL2_SysRegWrite_system_reg_access
                  Run_RMR_EL3_SysRegWrite_system_reg_access)

text \<open>Assume that PCC is not sealed\<close>

declare PCC_unsealed[intro, simp, derivable_capsE]

lemma PCC_read_unsealed[intro, simp, derivable_capsE]:
  assumes "Run (PCC_read u) t c"
    and "\<exists>s. sysreg_trace_assms s t \<and> {''PCC''} \<subseteq> accessible_regs s"
  shows "\<not>CapIsSealed c"
  using assms
  unfolding PCC_read_def
  by (elim PCC_unsealed)

end

context Morello_Mem_Axiom_Automaton
begin

lemma access_enabled_runI[derivable_caps_runI]:
  assumes "access_enabled s acctype vaddr paddr sz v tag"
  shows "access_enabled (run s t) acctype vaddr paddr sz v tag"
  using assms derivable_mono[OF Un_mono[OF subset_refl[where A = UNKNOWN_caps] accessed_caps_run_mono]]
  by (auto simp: access_enabled_def)

abbreviation paccess_enabled where
  "paccess_enabled s acctype paddr sz v tag
   \<equiv> \<exists>vaddr. access_enabled s acctype vaddr paddr sz v tag"

lemma (in Mem_Automaton) access_enabled_PTW[intro]:
  assumes "tag \<noteq> B0 \<longrightarrow> address_tag_aligned ISA paddr \<and> sz = tag_granule ISA"
  shows "access_enabled s PTW vaddr paddr sz v tag"
  using assms
  by (auto simp: access_enabled_def)

lemma (in Mem_Automaton) access_enabled_tagged_aligned[intro]:
  assumes "access_enabled s acctype vaddr paddr sz v tag" and "tag \<noteq> B0"
  shows "address_tag_aligned ISA paddr" and "sz = tag_granule ISA"
  using assms
  by (auto simp: access_enabled_def)

lemma paccess_enabled_PTW:
  assumes "tag \<noteq> B0 \<longrightarrow> address_tag_aligned ISA paddr \<and> sz = tag_granule ISA"
  shows "paccess_enabled s PTW paddr sz v tag"
  using assms
  by (auto simp: access_enabled_def)

lemma paccess_enabled_tagged_aligned:
  assumes "paccess_enabled s acctype paddr sz v tag" and "tag \<noteq> B0"
  shows "address_tag_aligned ISA paddr" and "sz = tag_granule ISA"
  using assms
  by (auto simp: access_enabled_def)

lemma paccess_enabled_runI[derivable_caps_runI]:
  assumes "paccess_enabled s acctype paddr sz v tag"
  shows "paccess_enabled (run s t) acctype paddr sz v tag"
  using assms
  by (auto intro: derivable_caps_runI)

lemma traces_enabled_ReadMemory:
  assumes "\<And>v. paccess_enabled s Load (unat paddr) sz v B0" and "\<not>is_fetch"
  shows "traces_enabled (ReadMemory sz paddr) s"
  using assms(1)
  unfolding ReadMemory_def
  by (intro traces_enabled_read_mem) (auto; simp add: assms(2))

lemma traces_enabled_Mem_read[traces_enabledI]:
  assumes "\<And>v. paccess_enabled s Load (unat (FullAddress_address (AddressDescriptor_paddress desc))) (nat sz) v B0"
    and "\<not>is_fetch"
  shows "traces_enabled (Mem_read desc sz accdesc) s"
  unfolding Mem_read_def bind_assoc
  by (traces_enabledI intro: traces_enabled_read_mem assms: assms(1); simp add: assms(2))

lemma traces_enabled_ReadMem[traces_enabledI]:
  assumes "\<And>v. paccess_enabled s Load (unat (FullAddress_address (AddressDescriptor_paddress desc))) (nat sz) v B0"
    and "\<not>is_fetch"
  shows "traces_enabled (ReadMem desc sz accdesc) s"
  unfolding ReadMem_def bind_assoc
  by (traces_enabledI intro: traces_enabled_read_mem assms: assms)

lemma traces_enabled_ReadTaggedMem[traces_enabledI]:
  assumes "\<And>v tag. paccess_enabled s Load (unat (FullAddress_address (AddressDescriptor_paddress desc))) 16 v tag"
    and "\<And>v tag. sz = 32 \<Longrightarrow> paccess_enabled s Load (unat (FullAddress_address (AddressDescriptor_paddress desc)) + 16) 16 v tag"
    and "sz = 16 \<or> sz = 32"
    and "\<not>is_fetch"
  shows "traces_enabled (ReadTaggedMem desc sz accdesc) s"
  unfolding ReadTaggedMem_def bind_assoc
  by (traces_enabledI intro: traces_enabled_read_memt non_cap_expI[THEN non_cap_exp_traces_enabledI] paccess_enabled_runI assms: assms(1-3); fastforce simp: assms(4))

lemma traces_enabled_ReadTags[traces_enabledI]:
  assumes "\<And>v tag. paccess_enabled s Load (unat (FullAddress_address (AddressDescriptor_paddress desc))) 16 v tag"
    and "\<not>is_fetch"
  shows "traces_enabled (ReadTags desc 1 accdesc) s"
  unfolding ReadTags_def bind_assoc
  by (traces_enabledI intro: traces_enabled_read_memt non_cap_expI[THEN non_cap_exp_traces_enabledI] paccess_enabled_runI
                      assms: assms(1); fastforce simp: assms(2))

(* TODO: Move? *)
lemma traces_enabled_Write_mem:
  assumes "\<And>r. traces_enabled (m r) (axiom_step s (E_write_mem wk paddr sz v r))"
    and "\<And>r. enabled s (E_write_mem wk paddr sz v r)"
  shows "traces_enabled (Write_mem wk paddr sz v m) s"
  using assms
  by (fastforce simp: traces_enabled_def take_Cons pre_inv_trace_assms_Cons split: nat.splits elim!: Traces_cases[where m = "Write_mem wk paddr sz v m"])

lemma length_take_chunks:
  assumes "n > 0" and "n dvd length xs"
  shows "length (take_chunks n xs) = length xs div n"
proof (use assms in \<open>induction n xs rule: take_chunks.induct[case_names Nil Zero Take]\<close>)
  case (Take n xs)
  then show ?case
    by (cases "length xs < n") (auto simp: div_geq)
qed auto

lemma length_mem_bytes_of_word:
  fixes w :: "'a::len word"
  assumes "8 dvd LENGTH('a)"
  shows "length (mem_bytes_of_word w) = LENGTH('a) div 8"
  using assms
  by (auto simp add: mem_bytes_of_word_def length_take_chunks simp del: take_chunks.simps)

lemma traces_enabled_write_mem:
  fixes data :: "'a::len word"
  assumes "paccess_enabled s Store (unat paddr) (nat sz) (mem_bytes_of_word data) B0"
    and "LENGTH('a) = nat sz * 8" and "sz > 0"
  shows "traces_enabled (write_mem BC_mword BC_mword wk addr_sz paddr sz data) s"
  using assms
  unfolding write_mem_def
  by (fastforce intro!: traces_enabled_Write_mem non_cap_expI[THEN non_cap_exp_traces_enabledI]
                split: option.splits simp: legal_store_def length_mem_bytes_of_word)

lemma traces_enabled_Mem_set[traces_enabledI]:
  fixes data :: "'a::len word"
  assumes "paccess_enabled s Store (unat (FullAddress_address (AddressDescriptor_paddress desc))) (nat sz) (mem_bytes_of_word data) B0"
    and "LENGTH('a) = nat sz * 8" and "sz > 0"
  shows "traces_enabled (Mem_set desc sz accdesc data) s"
  using assms
  unfolding Mem_set_def
  by (auto intro!: traces_enabled_bind traces_enabled_write_mem non_cap_expI[THEN non_cap_exp_traces_enabledI])

(* TODO: Move? *)
lemma traces_enabled_Write_memt:
  assumes "\<And>r. traces_enabled (m r) (axiom_step s (E_write_memt wk paddr sz v tag r))"
    and "\<And>r. enabled s (E_write_memt wk paddr sz v tag r)"
  shows "traces_enabled (Write_memt wk paddr sz v tag m) s"
  using assms
  by (fastforce simp: traces_enabled_def take_Cons pre_inv_trace_assms_Cons split: nat.splits elim!: Traces_cases[where m = "Write_memt wk paddr sz v tag m"])

fun bitU_nonzero :: "bitU \<Rightarrow> bool" where
  "bitU_nonzero B0 = False"
| "bitU_nonzero _ = True"

lemma traces_enabled_write_memt:
  fixes data :: "128 word"
  assumes "paccess_enabled s Store (unat paddr) 16 (mem_bytes_of_word data) tag"
    and "tag = B0 \<or> tag = B1"
  shows "traces_enabled (write_memt BC_mword BC_mword wk paddr 16 data tag) s"
  using assms
  unfolding write_memt_def
  by (fastforce intro!: traces_enabled_Write_memt non_cap_expI[THEN non_cap_exp_traces_enabledI]
                split: option.splits simp: legal_store_def length_mem_bytes_of_word)

lemma traces_enabled_write_tag_bool:
  assumes "\<And>data :: 128 word. paccess_enabled s Store (unat paddr) 16 (mem_bytes_of_word data) B0" and "\<not>tag"
  shows "traces_enabled (write_tag_bool wk paddr 16 tag) s"
  unfolding write_tag_bool_def
  by (traces_enabledI intro: traces_enabled_write_memt non_cap_expI[THEN non_cap_exp_traces_enabledI] assms: assms)

lemma traces_enabled_WriteTags[traces_enabledI]:
  assumes "\<And>data :: 128 word. paccess_enabled s Store (unat (FullAddress_address (AddressDescriptor_paddress addrdesc))) 16 (mem_bytes_of_word data) B0"
    and "tags = 0" and "sz = 1"
  shows "traces_enabled (WriteTags addrdesc sz (tags :: 1 word) accdesc) s"
  unfolding WriteTags_def
  using assms
  by (auto intro: traces_enabled_write_tag_bool)

lemma traces_enabled_WriteTaggedMem_single[traces_enabledI]:
  fixes tag :: "1 word" and data :: "128 word"
  assumes "paccess_enabled s Store (unat (FullAddress_address (AddressDescriptor_paddress desc))) 16 (mem_bytes_of_word data) (bitU_of_bool (tag !! 0))"
  shows "traces_enabled (WriteTaggedMem desc 16 accdesc tag data) s"
  using assms
  unfolding WriteTaggedMem_def
  by (cases "tag !! 0")
     (auto intro!: traces_enabled_write_memt traces_enabled_bind non_cap_expI[THEN non_cap_exp_traces_enabledI])

lemma run_write_memt:
  assumes "Run (write_memt BC_a BC_b wk paddr sz v tag) t a"
  shows "run s t = s"
  using assms
  by (auto simp add: write_memt_def split: option.splits elim!: Write_memt_TracesE)

lemma traces_enabled_WriteTaggedMem_pair[traces_enabledI]:
  fixes tags :: "2 word" and data :: "256 word"
  assumes "paccess_enabled s Store (unat (FullAddress_address (AddressDescriptor_paddress desc))) 16 (mem_bytes_of_word (ucast data :: 128 word)) (bitU_of_bool (tags !! 0))"
    and "paccess_enabled s Store (unat (FullAddress_address (AddressDescriptor_paddress desc)) + 16) 16 (mem_bytes_of_word (Word.slice 128 data :: 128 word)) (bitU_of_bool (tags !! 1))"
  shows "traces_enabled (WriteTaggedMem desc 32 accdesc tags data) s"
  using assms
  unfolding WriteTaggedMem_def
  by (auto intro!: traces_enabled_write_memt traces_enabled_bind traces_enabled_let non_cap_expI[THEN non_cap_exp_traces_enabledI]
           simp: run_write_memt bitU_of_bool_def)

lemma traces_enabled_WriteTaggedMem[traces_enabledI]:
  fixes tags :: "'t::len word" and data :: "'d::len word"
  assumes "paccess_enabled s Store (unat (FullAddress_address (AddressDescriptor_paddress desc))) 16 (mem_bytes_of_word (ucast data :: 128 word)) (bitU_of_bool (tags !! 0))"
    and "sz = 32 \<Longrightarrow> paccess_enabled s Store (unat (FullAddress_address (AddressDescriptor_paddress desc)) + 16) 16 (mem_bytes_of_word (Word.slice 128 data :: 128 word)) (bitU_of_bool (tags !! 1))"
    and "sz = 16 \<or> sz = 32"
    and "LENGTH('t) = nat sz div 16" and "LENGTH('d) = 8 * nat sz"
  shows "traces_enabled (WriteTaggedMem desc sz accdesc tags data) s"
  using assms
  unfolding WriteTaggedMem_def
  by (auto intro!: traces_enabled_write_memt traces_enabled_bind traces_enabled_let non_cap_expI[THEN non_cap_exp_traces_enabledI]
           simp: run_write_memt nth_ucast bitU_of_bool_def;
      fastforce)

definition store_enabled where
  "store_enabled s acctype vaddr sz data tag \<equiv>
     sz > 0 \<and>
     (\<forall>paddr.
        translate_address vaddr = Some paddr \<longrightarrow>
        bounds_address acctype vaddr + nat sz \<le> 2^64 \<and>
        (access_enabled s Store (bounds_address acctype vaddr) paddr (nat sz) (mem_bytes_of_word data) (bitU_of_bool tag)))"

definition load_enabled where
  "load_enabled s acctype vaddr sz tagged \<equiv>
     sz > 0 \<and> \<comment> \<open> vaddr + nat sz \<le> 2^64 \<and>\<close>
     (\<forall>paddr data tag.
        translate_address vaddr = Some paddr \<longrightarrow>
        bounds_address acctype vaddr + nat sz \<le> 2 ^ 64 \<and>
        access_enabled s (if is_fetch then Fetch else Load) (bounds_address acctype vaddr) paddr (nat sz) data (if tagged then tag else B0))"

lemma store_enabled_runI[derivable_caps_runI]:
  assumes "store_enabled s acctype vaddr sz data tag"
  shows "store_enabled (run s t) acctype vaddr sz data tag"
  using assms
  by (auto simp: store_enabled_def intro: access_enabled_runI)

lemma load_enabled_runI[derivable_caps_runI]:
  assumes "load_enabled s acctype vaddr sz tagged"
  shows "load_enabled (run s t) acctype vaddr sz tagged"
  using assms
  by (auto simp: load_enabled_def intro: access_enabled_runI)

lemma addrs_in_mem_region_subset:
  assumes "addrs_in_mem_region c acctype vaddr paddr sz"
    and "vaddr \<le> vaddr'" and "vaddr' + sz' \<le> vaddr + sz"
    and "translate_address vaddr' = Some paddr'"
  shows "addrs_in_mem_region c acctype vaddr' paddr' sz'"
  using assms
  unfolding addrs_in_mem_region_def
  by (auto simp: get_mem_region_def)

lemma access_enabled_data_subset:
  assumes "access_enabled s acctype vaddr paddr sz data tag"
    and "vaddr \<le> vaddr'" and "vaddr' + sz' \<le> vaddr + sz"
    and "translate_address vaddr' = Some paddr'"
  shows "access_enabled s acctype vaddr' paddr' sz' data' B0"
  using assms
  unfolding access_enabled_def authorises_access_def has_access_permission_def
  by (cases acctype; auto intro: addrs_in_mem_region_subset)

lemma access_enabled_data_offset:
  assumes "access_enabled s acctype vaddr paddr sz data tag"
    and "offset + sz' \<le> sz"
    and "translate_address (vaddr + offset) = Some paddr'"
  shows "access_enabled s acctype (vaddr + offset) paddr' sz' data' B0"
  using assms
  unfolding access_enabled_def authorises_access_def has_access_permission_def
  by (cases acctype; fastforce intro: addrs_in_mem_region_subset[where vaddr = vaddr and paddr = paddr and sz = sz])

lemma bounds_address_lteq_2p64:
  assumes "bounds_address acctype addr + sz \<le> 2^64"
    and "valid_address acctype addr" and "sz < 2^52" and "addr < 2^64"
  shows "addr + sz \<le> 2^64"
proof -
  let ?baddr = "bounds_address acctype addr"
  have "?baddr + sz = 2^56 * (?baddr div 2^56) + (addr mod 2^56 + sz)"
    by (auto simp add: bounds_address_def)
  from assms[unfolded this]
  have "tbi_enabled acctype addr \<longrightarrow> 2^56 * (addr div 2^56) + (addr mod 2^56 + sz) \<le> 2^56 * 255 + 2^56"
    by (intro add_le_mono impI)
       (auto simp: bounds_address_def valid_address_def div_plus_div_distrib_dvd_right split: if_splits)
  then show ?thesis
    using assms
    by (auto simp: bounds_address_def)
qed

lemma load_enabled_data_subset[intro]:
  assumes vaddr: "load_enabled s acctype vaddr sz False"
    and vaddr': "vaddr + nat sz \<le> 2^64 \<longrightarrow> vaddr \<le> vaddr' \<and> vaddr' + nat sz' \<le> vaddr + nat sz"
    and sz: "sz < 2 ^ 52"
    and sz': "sz' > 0"
    and paddr: "translate_address vaddr \<noteq> None"
    and "vaddr < 2^64"
  shows "load_enabled s acctype vaddr' sz' False"
proof -
  have lteq_2p64: "vaddr + nat sz \<le> 2^64"
    using vaddr paddr sz \<open>vaddr < 2^64\<close>
    by (intro bounds_address_lteq_2p64[of acctype vaddr "nat sz"])
       (auto simp: load_enabled_def intro: translate_address_valid)
  then obtain offset where offset: "vaddr' = vaddr + offset" "offset + nat sz' \<le> nat sz"
    using vaddr vaddr' sz'
    by (auto simp: load_enabled_def le_iff_add)
  then have "bounds_address acctype vaddr' = bounds_address acctype vaddr + offset"
    using offset paddr sz vaddr sz'
    by (auto simp: load_enabled_def intro!: bounds_address_offset translate_address_valid)
  then show ?thesis
    using offset sz' vaddr paddr lteq_2p64 translate_bounds_address[of acctype vaddr']
    by (auto simp: load_enabled_def translate_address_valid intro!: access_enabled_data_offset)
qed

lemma load_enabled_access_enabled[intro]:
  assumes "load_enabled s acctype vaddr sz tagged"
    and "sz' = nat sz"
    and "translate_address vaddr = Some paddr"
    and "tagged \<or> tag = B0"
    and "\<not>is_fetch"
  shows "\<exists>vaddr. access_enabled s Load vaddr paddr sz' data tag"
  using assms
  unfolding load_enabled_def
  by (cases tagged) auto

lemma store_enabled_data_subset[intro]:
  assumes vaddr: "store_enabled s acctype vaddr sz data tag"
    and vaddr': "vaddr + nat sz \<le> 2^64 \<longrightarrow> vaddr \<le> vaddr' \<and> vaddr' + nat sz' \<le> vaddr + nat sz"
    and sz: "sz < 2 ^ 52"
    and sz': "sz' > 0"
    and paddr: "translate_address vaddr \<noteq> None"
    and "vaddr < 2^64"
  shows "store_enabled s acctype vaddr' sz' data' False"
proof -
  have lteq_2p64: "vaddr + nat sz \<le> 2^64"
    using vaddr paddr sz \<open>vaddr < 2^64\<close>
    by (intro bounds_address_lteq_2p64[of acctype vaddr "nat sz"])
       (auto simp: store_enabled_def intro: translate_address_valid)
  then obtain offset where offset: "vaddr' = vaddr + offset" "offset + nat sz' \<le> nat sz"
    using vaddr vaddr' sz'
    by (auto simp: store_enabled_def le_iff_add)
  then have "bounds_address acctype vaddr' = bounds_address acctype vaddr + offset"
    using offset paddr sz vaddr sz'
    by (auto simp: store_enabled_def intro!: bounds_address_offset translate_address_valid)
  then show ?thesis
    using offset sz' vaddr paddr lteq_2p64 translate_bounds_address[of acctype vaddr']
    by (auto simp: store_enabled_def translate_address_valid intro!: access_enabled_data_offset)
qed

lemma store_enabled_access_enabled[intro]:
  assumes "store_enabled s acctype vaddr sz data tag"
    and "sz' = nat sz" and "data' = mem_bytes_of_word data" and "tag' = bitU_of_bool tag"
    and "translate_address vaddr = Some paddr"
  shows "\<exists>vaddr. access_enabled s Store vaddr paddr sz' data' tag'"
  using assms
  unfolding store_enabled_def
  by auto

lemma store_enabled_reverse_endianness[simp]:
  "store_enabled s acctype vaddr sz (reverse_endianness0 data) False = store_enabled s acctype vaddr sz data False"
  by (auto simp: store_enabled_def access_enabled_def)

lemma aligned_dvd_plus_lt:
  assumes "aligned x sz" and "y < sz" and "sz dvd sz'" and "x < sz'"
  shows "x + y < sz'"
proof -
  obtain k k' where k: "x = sz * k" and k': "sz' = sz * k'" "k < k'" "k' > 0"
    using assms
    by (auto simp: aligned_def dvd_def)
  have "sz * k + y < sz * (Suc k)"
    using assms
    by auto
  also have "\<dots> \<le> sz * k'"
    using k'
    unfolding less_eq_Suc_le
    by (intro mult_le_mono2)
  finally show ?thesis
    unfolding k k' .
qed

lemma aligned_mod_iff:
  assumes "sz dvd sz'"
  shows "aligned (addr mod sz') sz \<longleftrightarrow> aligned addr sz"
  unfolding aligned_def dvd_mod_iff[OF assms]
  ..

lemma translate_address_aligned_plus:
  assumes paddr: "translate_address vaddr = Some paddr"
    and vaddr: "aligned vaddr sz" and sz: "sz dvd 2^12" and offset: "offset < sz"
  shows "translate_address (vaddr + offset) = Some (paddr + offset)"
proof -
  obtain k where k: "2^12 = sz * k"
    using sz
    by (auto simp: dvd_def)
  have *: "(vaddr + offset) div 2^12 = vaddr div 2^12"
    using assms
    unfolding k
    by (auto simp: aligned_def div_mult2_eq)
  have "(vaddr + offset) mod 2^12 = (vaddr mod 2^12 + offset mod 2^12) mod 2^12"
    unfolding mod_add_eq
    ..
  also have "\<dots> = vaddr mod 2^12 + offset mod 2^12"
    using vaddr sz offset aligned_dvd_plus_lt[of "vaddr mod 2^12" sz offset "2^12"]
    by (intro mod_less) (auto simp: aligned_mod_iff)
  finally have "translate_address (vaddr + offset) = Some (2^12 * (paddr div 2^12) + vaddr mod 2^12 + offset)"
    using translate_address_paged[OF assms(1), where vaddr' = "vaddr + offset"] assms(2) *
    by (auto simp: aligned_def)
  also have "\<dots> = Some (paddr + offset)"
    using translate_address_paged[OF assms(1), where vaddr' = vaddr] assms(1)
    by auto
  finally show ?thesis
    .
qed

lemma translate_address_aligned32_plus16:
  assumes "translate_address vaddr = Some paddr"
    and "aligned vaddr 32"
  shows "translate_address (vaddr + 16) = Some (paddr + 16)"
  using assms
  by (auto intro: translate_address_aligned_plus)

lemma store_enabled_data_paccess_enabled_subset:
  assumes "store_enabled s acctype vaddr sz data tag"
    and "\<exists>paddr offset. translate_address vaddr = Some paddr \<and> paddr' = paddr + offset \<and> offset + sz' \<le> nat sz"
    and "aligned vaddr (nat sz)" and "nat sz dvd 2^12" and "vaddr < 2^64" and "sz' > 0"
  shows "paccess_enabled s Store paddr' sz' (mem_bytes_of_word data') B0"
proof -
  obtain paddr offset
    where paddr: "translate_address vaddr = Some paddr"
      and offset: "paddr' = paddr + offset \<and> offset + sz' \<le> nat sz"
    using assms(2)
    by auto
  moreover have paddr': "translate_address (vaddr + offset) = Some (paddr + offset)"
    using paddr offset assms(3,4,6)
    by (intro translate_address_aligned_plus[where sz = "nat sz"]) auto
  moreover have "store_enabled s acctype (vaddr + offset) (int sz') data' False"
    using paddr offset assms(1,3-6)
    by (elim store_enabled_data_subset) (auto simp flip: zless_nat_eq_int_zless dest: dvd_imp_le)
  ultimately show ?thesis
    by (elim store_enabled_access_enabled) auto
qed

lemma AArch64_MemSingle_read_translate_address_Some:
  assumes "Run (AArch64_MemSingle_read vaddr sz acctype wasaligned) t a"
    and "translation_assms_trace t"
  shows "\<exists>paddr. translate_address (unat vaddr) = Some paddr"
  using assms
  unfolding AArch64_MemSingle_read_def
  by (auto elim!: Run_bindE simp: exp_fails_if_then_else)

lemma AArch64_MemSingle_set_translate_address_Some:
  assumes "Run (AArch64_MemSingle_set vaddr sz acctype wasaligned data) t a"
    and "translation_assms_trace t"
  shows "\<exists>paddr. translate_address (unat vaddr) = Some paddr"
  using assms
  unfolding AArch64_MemSingle_set_def
  by (auto elim!: Run_bindE simp: exp_fails_if_then_else)

lemma AArch64_MemSingle_read_valid_address[derivable_capsE]:
  assumes "Run (AArch64_MemSingle_read vaddr sz acctype wasaligned) t a" and "translation_assms_trace t"
  shows "valid_address acctype (unat vaddr)"
  using AArch64_MemSingle_read_translate_address_Some[OF assms]
  by (auto intro: translate_address_valid)

lemma AArch64_TaggedMemSingle_valid_address[derivable_capsE]:
  assumes "Run (AArch64_TaggedMemSingle vaddr sz acctype wasaligned) t a" and "translation_assms_trace t"
  shows "valid_address acctype (unat vaddr)"
  using assms
  unfolding AArch64_TaggedMemSingle_def bind_assoc
  by (auto elim!: Run_bindE simp: exp_fails_if_then_else translate_address_valid)

lemma MemC_read_valid_address[derivable_capsE]:
  assumes "Run (MemC_read vaddr acctype) t a" and "translation_assms_trace t"
  shows "valid_address acctype (unat vaddr)"
  using assms
  unfolding MemC_read_def
  by (auto elim!: Run_bindE Run_ifE derivable_capsE)

lemma Mem_read0_valid_address[derivable_capsE]:
  assumes "Run (Mem_read0 vaddr sz acctype) t a" and "translation_assms_trace t"
  shows "valid_address acctype (unat vaddr)"
  using assms
  unfolding Mem_read0_def
  by (fastforce elim!: Run_bindE Run_ifE intro: AArch64_MemSingle_read_valid_address)

lemma Mem_read0_plus_0_valid_address[derivable_capsE]:
  assumes "Run (Mem_read0 (add_vec_int vaddr 0) sz acctype) t a" and "translation_assms_trace t"
  shows "valid_address acctype (unat vaddr)"
  using assms
  unfolding Mem_read0_def
  by (fastforce elim!: Run_bindE Run_ifE intro: AArch64_MemSingle_read_valid_address)

lemma Mem_set0_valid_address[derivable_capsE]:
  assumes "Run (Mem_set0 vaddr sz acctype data) t a" and "translation_assms_trace t"
  shows "valid_address acctype (unat vaddr)"
  using assms
  unfolding Mem_set0_def
  by (auto elim!: Run_bindE Run_letE Run_ifE dest: AArch64_MemSingle_set_translate_address_Some intro: translate_address_valid)

lemma Mem_set0_plus_0_valid_address[derivable_capsE]:
  assumes "Run (Mem_set0 (add_vec_int vaddr 0) sz acctype data) t a" and "translation_assms_trace t"
  shows "valid_address acctype (unat vaddr)"
  using assms
  by (auto intro: Mem_set0_valid_address)

lemma AArch64_CapabilityTag_valid_address[derivable_capsE]:
  assumes "Run (AArch64_CapabilityTag addr acctype) t a" and "translation_assms_trace t"
  shows "valid_address acctype (unat addr)"
  using assms
  unfolding AArch64_CapabilityTag_def
  by (auto elim!: Run_bindE simp: exp_fails_if_then_else intro: translate_address_valid)

(* TODO *)
(*lemma
  assumes "load_enabled s (vaddr + offset) acctype sz tagged"
    and "translate_address vaddr (acctype_of_AccType acctype False) = Some paddr"
    and "tagged \<or> tag = B0"
  shows "access_enabled s Load (paddr + offset) (nat sz) data tag"
  using assms
  unfolding access_enabled_def
  apply (cases tagged)
  apply (auto simp: load_enabled_def translate_address_def dvd_def)
  oops*)

text \<open>The VirtualAddress type in the ASL\<close>

definition perm_bits_included :: "64 word \<Rightarrow> 64 word \<Rightarrow> bool" where
  "perm_bits_included perms1 perms2 \<equiv> (\<forall>n < 64. perms1 !! n \<longrightarrow> perms2 !! n)"

lemma perm_bits_included_refl[simp, intro]:
  "perm_bits_included p p"
  by (auto simp: perm_bits_included_def)

lemma perm_bits_included_OR[simp, intro]:
  assumes "perm_bits_included p p1 \<or> perm_bits_included p p2"
  shows "perm_bits_included p (p1 OR p2)"
  using assms
  by (auto simp: perm_bits_included_def word_ao_nth)

lemmas perm_bits_included_if[simp] = if_split[where P = "\<lambda>p. perm_bits_included p' p" for p']

lemma Align__1_iff_aligned[simp]:
  assumes "addr \<ge> 0" and "sz > 0"
  shows "addr = Align__1 addr sz \<longleftrightarrow> aligned (nat addr) (nat sz)"
  using assms
  by (auto simp: Align__1_def aligned_def dvd_def nat_mult_distrib nat_eq_iff;
      metis int_nat_eq pos_imp_zdiv_nonneg_iff)

lemma Align__1_leq:
  assumes "addr \<ge> 0" and "sz > 0"
  shows "0 \<le> Align__1 addr sz" and "Align__1 addr sz \<le> addr"
  using assms
  by (auto simp: Align__1_def div_int_pos_iff)
     (metis Euclidean_Division.pos_mod_sign add_le_cancel_left cancel_div_mod_rules(2) group_cancel.rule0)

lemma Align_woi_Align__1:
  fixes addr :: "'a::len word"
  shows "Align addr sz = word_of_int (Align__1 (uint addr) sz)"
  by (auto simp: Align_def integer_subrange_def of_bl_bin_word_of_int)

lemma Align_eq_iff_aligned[simp]:
  fixes addr :: "'a::len word"
  assumes "sz > 0"
  shows "addr = Align addr sz \<longleftrightarrow> aligned (unat addr) (nat sz)"
proof -
  have "Align__1 (uint addr) sz \<le> uint addr" and "uint addr < 2^LENGTH('a)"
    using assms
    by (auto simp: Align__1_leq)
  from le_less_trans[OF this]
  have *: "Align__1 (uint addr) sz mod 2^LENGTH('a) = Align__1 (uint addr) sz"
    using assms
    by (intro mod_pos_pos_trivial) (auto simp: Align__1_leq)
  then show ?thesis
    using assms
    unfolding word_uint_eq_iff Align_woi_Align__1 uint_word_of_int * unat_def
    by auto
qed

lemma aligned_Align__1[simp, intro]:
  assumes "sz' = nat sz" and "sz > 0"
  shows "aligned (nat (Align__1 addr sz)) sz'"
  using assms
  by (auto simp: Align__1_def aligned_def dvd_def nat_mult_distrib)

lemma aligned_Align[simp, intro]:
  assumes "sz' = nat sz" and "sz > 0" and "nat sz dvd 2^LENGTH('a)"
  shows "aligned (unat (Align addr sz :: 'a::len word)) sz'"
  using assms
  by (auto simp: Align_woi_Align__1 Align__1_leq aligned_mod_iff nat_mod_distrib nat_power_eq)

lemma Align_AND_NOT_mask:
  "Align w (2 ^ n) = (w AND NOT (mask n))"
  unfolding Align_def Align__1_def
  by (intro word_eqI) (auto simp: bin_nth_prod bin_nth_div word_ops_nth_size simp flip: test_bit_def')

lemma AArch64_CheckAlignment_ATOMICRW_aligned[simp]:
  assumes "Run (AArch64_CheckAlignment addr (int sz) AccType_ATOMICRW iswrite) t a" and "sz > 0"
  shows "aligned (unat addr) sz"
  using assms
  by (auto simp: AArch64_CheckAlignment_def elim!: Run_bindE Run_letE Run_ifE)

lemma AArch64_ExclusiveMonitorsPass_aligned[simp]:
  assumes "Run (AArch64_ExclusiveMonitorsPass addr (int sz)) t a" and "sz > 0"
  shows "aligned (unat addr) sz"
  using assms
  unfolding AArch64_ExclusiveMonitorsPass_def Let_def
  by (auto elim!: Run_bindE split: if_splits)

lemma TranslateAddress_aligned_vaddr_aligned_paddr:
  assumes "Run (AArch64_TranslateAddressWithTag vaddr acctype iswrite wasaligned sz iscapwrite) t addrdesc"
    and "\<not>IsFault addrdesc"
    and "aligned (unat vaddr) sz" and "sz dvd 2^12"
    and "translation_assms_trace t"
  shows "aligned (unat (FullAddress_address (AddressDescriptor_paddress addrdesc))) sz"
    (is "aligned ?paddr sz")
proof -
  have *: "translate_address (unat vaddr) = Some ?paddr"
    using assms
    by auto
  show ?thesis
    using \<open>aligned (unat vaddr) sz\<close>
    unfolding translate_address_aligned_iff[OF * \<open>sz dvd 2^12\<close>] .
qed

lemmas TranslateAddress_aligned_unat_paddr_plus_distrib =
  TranslateAddress_aligned_vaddr_aligned_paddr[THEN aligned_unat_plus_distrib]

lemma CheckCapabilityAlignment_address_tag_aligned[intro, simp]:
  assumes "Run (CheckCapabilityAlignment vaddr acctype iswrite) t u"
  shows "aligned (unat vaddr) 16"
  using assms
  by (auto simp add: CheckCapabilityAlignment_def elim!: Run_bindE Run_ifE)

(*lemma CapGetBounds_base_leq_limit:
  assumes "Run (CapGetBounds c) t (base, limit, valid)"
    and "trace_assms t"
  shows "base \<le> limit"
  (* TODO: add global bounds validity assumption and prove as invariant *)
  sorry*)

lemma CapIsRangeInBounds_in_get_mem_region:
  assumes "Run (CapIsRangeInBounds c addr sz) t True" and "translation_assms_trace t"
    and "unat sz \<le> 2^64"
  shows "set (address_range (unat addr) (unat sz)) \<subseteq> get_mem_region CC c"
proof -
  have "unat (ucast addr + sz) = unat addr + unat sz"
    using add_less_le_mono[OF unat_lt2p[of addr] \<open>unat sz \<le> 2^64\<close>]
    by (auto simp: unat_plus_if_size)
  then show ?thesis
    using assms (*CapGetBounds_base_leq_limit*)
    unfolding CapIsRangeInBounds_def get_mem_region_def
    by (auto simp: CapGetBounds_get_base CapGetBounds_get_limit word_le_nat_alt
             elim!: Run_bindE Run_letE)
qed

lemma sail_ones_max_word[simp]: "sail_ones n = max_word"
  by (auto simp: sail_ones_def zeros_def)

lemma cap_perm_bits_included_trans:
  assumes "cap_permits perms c"
    and "perm_bits_included perms' perms"
  shows "cap_permits perms' c"
  using assms
  unfolding CapCheckPermissions_def Ones_def perm_bits_included_def
  by (auto simp: word_eq_iff word_ops_nth_size nth_ucast)

lemma slice_mask_shiftl_mask[simp]:
  assumes len: "LENGTH('a) = nat len" and slice_len: "slice_len > 0" and "len > 0"
  shows "slice_mask len lo slice_len = (mask (nat slice_len) << nat lo :: 'a::len word)"
proof -
  have "uint (2 ^ nat slice_len - 1 :: 'a::len word) = 2 ^ nat slice_len - 1"
    if "slice_len < len"
  proof -
    have "uint (2 ^ nat slice_len :: 'a word) = 2 ^ nat slice_len"
      using that \<open>len > 0\<close> slice_len
      using power_strict_increasing[of 1 "nat len" "2 :: int"]
      by (auto simp: word_arith_power_alt uint_word_of_int bintrunc_mod2p len)
    then show ?thesis
      by (auto simp: uint_sub_if_size len uint_2p)
  qed
  then have "uint (slice_mask len lo slice_len :: 'a::len word) = bintrunc (nat len) ((2 ^ min (nat len) (nat slice_len) - 1) << nat lo)"
    using slice_len
    by (auto simp: slice_mask_def uint_shiftl uint_max_word len min_def Let_def sail_mask_def not_le)
  also have "\<dots> = uint (mask (nat slice_len) << nat lo :: 'a::len word)"
    by (auto simp: uint_shiftl len uint_mask min_def)
  finally show ?thesis
    by auto
qed

lemma sext_subrange_64_55_scast_ucast:
  "sext_subrange 64 (w :: 64 word) 55 0 = (scast (ucast w :: 56 word) :: 64 word)"
proof (intro word_eqI impI)
  fix n
  assume "n < size (sext_subrange 64 w 55 0 :: 64 word)"
  then show "(sext_subrange 64 w 55 0 :: 64 word) !! n = (scast (ucast w :: 56 word) :: 64 word) !! n"
    unfolding sext_subrange_def sext_slice_def arith_shiftr_def arith_shiftr_mword_def
    by (cases "n = 55")
       (auto simp: nth_scast nth_sshiftr nth_shiftl word_ao_nth nth_ucast not_le)
qed

lemma sext_subrange_64_55_word_cat:
  "sext_subrange 64 (w :: 64 word) 55 0 = (word_cat (if w !! 55 then max_word else 0 :: 8 word) (ucast w :: 56 word) :: 64 word)"
  unfolding sext_subrange_64_55_scast_ucast
  using scast_alt_def[where ?'a = 56 and ?'b = 8 and ?'c = 64 and x = "ucast w :: 56 word" and m = 55]
  by (auto simp: nth_ucast)

lemma zext_subrange_64_55_ucast_ucast:
  "zext_subrange 64 (w :: 64 word) 55 0 = (ucast (ucast w :: 56 word) :: 64 word)"
  unfolding zext_subrange_def zext_slice_def
  by auto

lemma unat_sext_subrange_64_55:
  fixes vaddr :: "64 word"
  shows "unat (sext_subrange 64 vaddr 55 0 :: 64 word) =
         (if vaddr !! 55 then unat vaddr mod 2 ^ 56 + (255 * 2 ^ 56) else unat vaddr mod 2 ^ 56)"
  unfolding sext_subrange_64_55_word_cat
  by (auto simp: unat_def word_cat_def uint_word_of_int uint_and_mask bintrunc_mod2p
                 nat_mod_distrib nat_add_distrib bin_cat_num uint_max_word)

lemma unat_zext_subrange_64_55:
  fixes vaddr :: "64 word"
  shows "unat (zext_subrange 64 vaddr 55 0 :: 64 word) = unat vaddr mod 2 ^ 56"
  unfolding zext_subrange_64_55_ucast_ucast
  by (auto simp: unat_def uint_and_mask nat_mod_distrib)

lemma bin_nth_int_unat:
  "bin_nth (int (unat w)) n = w !! n"
  by (auto simp: unat_def word_test_bit_def)

lemma tbi_enabled':
  assumes "Run (AddrTop addr (translation_el acctype)) t atop" and "translation_assms_trace t"
  shows "(atop = 63 \<and> \<not>tbi_enabled acctype (unat addr)) \<or> (atop = 55 \<and> tbi_enabled acctype (unat addr))"
  using assms AddrTop_63_or_55[OF assms(1)] tbi_enabled[of addr acctype t atop]
  by auto

lemma in_host':
  assumes "Run (ELIsInHost el) t ih" and "translation_assms_trace t"
    and "translation_el acctype = el"
  shows "in_host acctype = ih"
  using assms in_host[of acctype t ih]
  by auto

(*lemma
  assumes "valid_address acctype (addr + offset)"
    and "offset < 2^52"
  shows "valid_address acctype addr"
  using assms
  apply (auto simp: valid_address_def split: if_splits)
  oops

lemma
  assumes "bounds_address acctype vaddr + sz \<le> 2 ^ 64"
    and "valid_address acctype vaddr"
    and "vaddr < 2 ^ 64" and "sz < 2 ^ 52"
  shows "vaddr mod 2 ^ 56 + vaddr div 2 ^ 56 * 2 ^ 56 + sz \<le> 2 ^ 64"
  using assms
  apply (auto simp add: bounds_address_def valid_address_def split: if_splits)
  find_theorems "_ mod _ + _ div _ * _"
  oops*)

lemma CheckCapability_load_enabled:
  assumes t: "Run (CheckCapability c vaddr sz req_perms acctype') t addr" "inv_trace_assms s t"
    and sz: "sz > 0" "sz < 2^52" (*"unat vaddr + nat sz \<le> 2^64"*)
    and sz': "sz' > 0" "unat vaddr + nat sz \<le> 2^64 \<and> addr = vaddr \<longrightarrow> unat vaddr \<le> vaddr' \<and> vaddr' + nat sz' \<le> unat vaddr + nat sz"
    and "perm_bits_included (if is_fetch then CAP_PERM_EXECUTE else CAP_PERM_LOAD) req_perms"
    and "tagged \<and> use_mem_caps \<longrightarrow> cap_permits CAP_PERM_LOAD_CAP c"
    and "tagged \<longrightarrow> nat sz' = 16 \<and> aligned vaddr' 16 \<and> \<not>is_fetch"
    and "\<not>CapIsSealed c \<longrightarrow> c \<in> derivable_caps s \<or> (\<exists>c' \<in> derivable_caps s. is_indirect_sentry c' \<and> CapUnseal c' = c \<and> c \<in> invoked_indirect_caps \<and> \<not>is_fetch)"
    and "valid_address acctype vaddr' \<and> addr = vaddr \<longrightarrow> valid_address acctype (unat vaddr)"
    and "acctype' = acctype"
  shows "load_enabled (run s t) acctype vaddr' sz' tagged"
proof (unfold load_enabled_def, intro conjI allI impI)
  from sz' show "sz' > 0"
    by auto
next
  fix paddr' data tag
  let ?tag = "if tagged then tag else B0"
  let ?is_cap = "?tag \<noteq> B0"
  let ?is_local_cap = "mem_val_is_local_cap CC ISA data ?tag \<and> tag = B1"
  let ?bvaddr = "bounds_address acctype (unat vaddr)"
  let ?bvaddr' = "bounds_address acctype vaddr'"
  let ?loadtype = "if is_fetch then Fetch else Load"
  assume paddr': "translate_address vaddr' = Some paddr'"
  from translate_address_valid[OF this, where acctype = acctype]
  have vaddr_valid: "valid_address acctype (unat vaddr)" if "addr = vaddr"
    using assms that
    by blast
  from t obtain t' bvaddr
    where t': "Run (CapIsRangeInBounds c bvaddr (word_of_int sz)) t' True" "translation_assms_trace t'"
      and bvaddr: "bounds_address acctype (unat vaddr) = unat bvaddr"
      and addr: "addr = vaddr"
      and "CapIsTagSet c" and"\<not>CapIsSealed c"
      and "cap_permits req_perms c"
    unfolding CheckCapability_def bounds_address_def has_ttbr1_def \<open>acctype' = acctype\<close>
    by (auto simp: bin_nth_int_unat unat_sext_subrange_64_55 unat_zext_subrange_64_55
             elim!: Run_bindE Run_and_boolM_E Run_or_boolM_E
             split: if_splits dest!: translation_el s1_enabled tbi_enabled' in_host)
  have aligned: "nat sz' = 16 \<and> aligned paddr' 16 \<and> \<not>is_fetch" if "tagged"
    using assms paddr' that
    by auto
  obtain c' where c': "c' \<in> derivable_caps s"
    and c: "c = c' \<or> (is_indirect_sentry c' \<and> c = CapUnseal c' \<and> c \<in> invoked_indirect_caps \<and> \<not>is_fetch)"
    using assms \<open>\<not>CapIsSealed c\<close>
    by blast
  then have tagged: "CapIsTagSet c'"
    and sentry_if_sealed: "CapIsSealed c' \<longrightarrow> is_indirect_sentry c' \<and> CapUnseal c' \<in> invoked_indirect_caps \<and> \<not>is_fetch"
    using \<open>CapIsTagSet c\<close> \<open>\<not>CapIsSealed c\<close>
    by auto
  from c' tagged have c_limit: "get_limit c' \<le> 2 ^ 64"
    using derivable_caps_invariant inv_trace_assms_accessed_caps_invariant[OF \<open>inv_trace_assms s t\<close>]
    by (auto simp: cap_invariant_def)
  from c have perms': "cap_permits p c' \<longleftrightarrow> cap_permits p c" for p
    by (auto simp: CapCheckPermissions_def CapGetPermissions_CapUnseal_eq)
  from c have "get_mem_region CC c' = get_mem_region CC c"
    by (auto simp: get_mem_region_def get_bounds_CapUnseal_eq)
  with CapIsRangeInBounds_in_get_mem_region[OF t']
  have mem_region: "set (address_range ?bvaddr (nat sz)) \<subseteq> get_mem_region CC c'"
    using sz bvaddr
    by auto
  with c_limit have mem_region_2p64: "?bvaddr + nat sz \<le> 2 ^ 64"
    using sz
    by (auto simp: get_mem_region_def split: if_splits)
  then have "unat vaddr + nat sz \<le> 2^64"
    using vaddr_valid addr \<open>sz < 2^52\<close> unat_lt2p[of vaddr]
    by (intro bounds_address_lteq_2p64[where addr = "unat vaddr"]) (auto)
  then obtain offset where offset: "vaddr' = unat vaddr + offset" "offset + nat sz' \<le> nat sz"
    using sz' addr
    by (auto simp: le_iff_add)
  then have bvaddr': "?bvaddr' = ?bvaddr + offset"
    using vaddr_valid addr mem_region_2p64 \<open>sz < 2^52\<close> \<open>sz' > 0\<close>
    unfolding \<open>vaddr' = unat vaddr + offset\<close>
    by (intro bounds_address_offset) auto
  then show "?bvaddr' + nat sz' \<le> 2 ^ 64"
    using mem_region_2p64 offset
    by auto
  have "addrs_in_mem_region c' ?loadtype ?bvaddr' paddr' (nat sz')"
    using mem_region offset paddr'
    using translate_address_valid[OF paddr', THEN translate_bounds_address, of acctype]
    unfolding bvaddr' addrs_in_mem_region_def
    by (auto intro!: translate_bounds_address translate_address_valid)
  moreover have "\<forall>is_local_cap. has_access_permission c' ?loadtype ?is_cap is_local_cap"
    using assms cap_perm_bits_included_trans[OF \<open>cap_permits req_perms c\<close>]
    unfolding has_access_permission_def
    by (cases is_fetch; auto simp: CC_def perms' CapIsExecutePermitted_def)
  ultimately have "\<forall>is_local_cap. authorises_access c' ?loadtype ?is_cap is_local_cap ?bvaddr' paddr' (nat sz')"
    using assms tagged sentry_if_sealed
    by (auto simp: authorises_access_def)
  then show "access_enabled (run s t) ?loadtype ?bvaddr' paddr' (nat sz') data ?tag"
    using derivable_caps_run_imp[OF c', where t = t] aligned tagged
    by (fastforce simp: access_enabled_def derivable_caps_def)
qed

(*proof (unfold load_enabled_def, intro allI impI conjI)
  show "sz' > 0" and "vaddr' + nat sz' \<le> 2 ^ 64"
    using sz sz'
    by auto
next
  fix paddr data tag
  assume paddr: "translate_address vaddr' Load = Some paddr"
  let ?tag = "if tagged then tag else B0"
  let ?is_cap = "?tag \<noteq> B0"
  let ?is_local_cap = "mem_val_is_local_cap CC ISA data ?tag \<and> tag = B1"
  have tagged: "CapIsTagSet c" and not_sealed: "\<not>CapIsSealed c"
    using assms
    (* by (auto elim!: Run_bindE split: if_splits simp: CheckCapability_def) *)
    sorry
  then have c: "c \<in> derivable (accessed_caps (invoked_indirect_caps = {}) (run s t))"
    using \<open>\<not>CapIsSealed c \<longrightarrow> c \<in> derivable_caps (run s t)\<close>
    by (auto simp: derivable_caps_def)
  have aligned: "nat sz' = 16 \<and> aligned paddr 16" if "tagged"
    using assms paddr that
    by auto
  obtain t' where "Run (CapIsRangeInBounds c vaddr (word_of_int sz)) t' True" and "trace_assms t'"
    using t
    by (auto elim!: Run_bindE simp: CheckCapability_def split: if_splits)
  from CapIsRangeInBounds_in_get_mem_region[OF this]
  have "addrs_in_mem_region c Load vaddr' paddr (nat sz')"
    using paddr sz sz'
    unfolding addrs_in_mem_region_def
    by (auto simp: unat_def uint_word_of_int subset_eq)
  moreover have "\<forall>is_local_cap. has_access_permission c Load ?is_cap is_local_cap"
  proof -
    have "cap_permits req_perms c"
      using assms
      by (auto simp: CheckCapability_def elim!: Run_bindE split: if_splits)
    from cap_perm_bits_included_trans[OF this]
    show ?thesis
      using assms
      unfolding has_access_permission_def
      by (auto simp: CC_def)
  qed
  ultimately have "\<forall>is_local_cap. authorises_access c Load ?is_cap is_local_cap vaddr' paddr (nat sz')"
    using assms tagged not_sealed
    by (auto simp: authorises_access_def)
  then show "access_enabled (run s t) Load (bounds_address acctype vaddr') paddr (nat sz') data ?tag"
    using c aligned
    by (fastforce simp: access_enabled_def)
qed*)

lemma CheckCapability_store_enabled:
  fixes data :: "'a::len word"
  assumes t: "Run (CheckCapability c vaddr sz req_perms acctype') t addr" "inv_trace_assms s t"
    and sz: "sz > 0" "sz < 2^52" (* "unat vaddr + nat sz \<le> 2^64" *)
    and sz': "sz' > 0" "unat vaddr + nat sz \<le> 2^64 \<longrightarrow> unat vaddr \<le> vaddr' \<and> vaddr' + nat sz' \<le> unat vaddr + nat sz"
    and store_perm: "perm_bits_included CAP_PERM_STORE req_perms"
    and store_cap_perm: "tag \<longrightarrow> perm_bits_included CAP_PERM_STORE_CAP req_perms"
    and local_perm: "tag \<and> CapIsLocal (Capability_of_tag_word tag (ucast data)) \<longrightarrow> perm_bits_included CAP_PERM_STORE_LOCAL req_perms"
    and aligned: "tag \<longrightarrow> nat sz' = 16 \<and> aligned vaddr' 16 \<and> LENGTH('a) = 128"
    and "\<not>CapIsSealed c \<longrightarrow> c \<in> derivable_caps s"
    and "valid_address acctype vaddr' \<longrightarrow> valid_address acctype (unat vaddr)"
    and "acctype' = acctype"
  shows "store_enabled (run s t) acctype vaddr' sz' data tag"
proof (unfold store_enabled_def, intro conjI allI impI)
  from sz' show "sz' > 0"
    by auto
next
  fix paddr'
  let ?tagbit = "bitU_of_bool tag"
  let ?bytes = "mem_bytes_of_word data"
  let ?is_local_cap = "mem_val_is_local_cap CC ISA ?bytes ?tagbit \<and> ?tagbit = B1"
  let ?bvaddr = "bounds_address acctype (unat vaddr)"
  let ?bvaddr' = "bounds_address acctype vaddr'"
  assume paddr': "translate_address vaddr' = Some paddr'"
  from translate_address_valid[OF this, where acctype = acctype]
  have "valid_address acctype (unat vaddr)"
    using assms
    by blast
  have is_local_cap: "?is_local_cap \<longleftrightarrow> tag \<and> CapIsLocal (Capability_of_tag_word tag (ucast data))"
    using aligned
    by (cases tag)
       (auto simp: mem_val_is_local_cap_def CC_def cap_of_mem_bytes_of_word_B1_Capability_of_tag_word)
  from t obtain t' bvaddr
    where t': "Run (CapIsRangeInBounds c bvaddr (word_of_int sz)) t' True" "translation_assms_trace t'"
      and bvaddr: "bounds_address acctype (unat vaddr) = unat bvaddr"
      and tagged: "CapIsTagSet c" and not_sealed: "\<not>CapIsSealed c"
      and "cap_permits req_perms c"
    unfolding CheckCapability_def bounds_address_def has_ttbr1_def \<open>acctype' = acctype\<close>
    by (auto simp: bin_nth_int_unat unat_sext_subrange_64_55 unat_zext_subrange_64_55
             elim!: Run_bindE Run_and_boolM_E Run_or_boolM_E
             split: if_splits dest!: translation_el s1_enabled tbi_enabled' in_host)
  have aligned: "nat sz' = 16 \<and> aligned paddr' 16" if "tag"
    using assms paddr' that
    by auto
  from not_sealed have c: "c \<in> derivable_caps s"
    using assms
    by blast
  from derivable_caps_invariant[OF this]
  have c_limit: "get_limit c \<le> 2 ^ 64"
    using tagged inv_trace_assms_accessed_caps_invariant[OF \<open>inv_trace_assms s t\<close>]
    by (auto simp: cap_invariant_def)
  from CapIsRangeInBounds_in_get_mem_region[OF t']
  have mem_region: "set (address_range ?bvaddr (nat sz)) \<subseteq> get_mem_region CC c"
    using sz bvaddr
    by auto
  with c_limit have mem_region_2p64: "?bvaddr + nat sz \<le> 2 ^ 64"
    using sz
    by (auto simp: get_mem_region_def split: if_splits)
  then have "unat vaddr + nat sz \<le> 2^64"
    using \<open>valid_address acctype (unat vaddr)\<close> \<open>sz < 2^52\<close> unat_lt2p[of vaddr]
    by (intro bounds_address_lteq_2p64[where addr = "unat vaddr"]) (auto)
  then obtain offset where offset: "vaddr' = unat vaddr + offset" "offset + nat sz' \<le> nat sz"
    using sz'
    by (auto simp: le_iff_add)
  then have bvaddr': "?bvaddr' = ?bvaddr + offset"
    using \<open>valid_address acctype (unat vaddr)\<close> mem_region_2p64 \<open>sz < 2^52\<close> \<open>sz' > 0\<close>
    unfolding \<open>vaddr' = unat vaddr + offset\<close>
    by (intro bounds_address_offset) auto
  then show "?bvaddr' + nat sz' \<le> 2 ^ 64"
    using mem_region_2p64 offset
    by auto
  have "addrs_in_mem_region c Store ?bvaddr' paddr' (nat sz')"
    using mem_region offset paddr'
    using translate_address_valid[OF paddr', THEN translate_bounds_address, of acctype]
    unfolding bvaddr' addrs_in_mem_region_def
    by (auto intro!: translate_bounds_address translate_address_valid)
  moreover have "has_access_permission c Store tag ?is_local_cap"
  proof -
    have "cap_permits req_perms c"
      using t
      by (auto simp: CheckCapability_def elim!: Run_bindE split: if_splits)
    from cap_perm_bits_included_trans[OF this]
    show ?thesis
      using store_perm store_cap_perm local_perm
      unfolding has_access_permission_def is_local_cap
      by (auto simp: CC_def)
  qed
  ultimately have "authorises_access c Store tag ?is_local_cap ?bvaddr' paddr' (nat sz')"
    using assms tagged not_sealed
    by (auto simp: authorises_access_def)
  then show "access_enabled (run s t) Store ?bvaddr' paddr' (nat sz') ?bytes ?tagbit"
    using derivable_caps_run_imp[OF c, where t = t] aligned tagged
    by (cases tag) (auto simp: access_enabled_def derivable_caps_def)
qed

(*proof (unfold store_enabled_def, intro allI impI conjI)
  show "sz' > 0" and "vaddr' + nat sz' \<le> 2 ^ 64"
    using sz sz'
    by auto
next
  fix paddr
  assume paddr: "translate_address vaddr' Store = Some paddr"
  let ?tagbit = "bitU_of_bool tag"
  let ?bytes = "mem_bytes_of_word data"
  let ?is_local_cap = "mem_val_is_local_cap CC ISA ?bytes ?tagbit \<and> ?tagbit = B1"
  have is_local_cap: "?is_local_cap \<longleftrightarrow> tag \<and> CapIsLocal (Capability_of_tag_word tag (ucast data))"
    using aligned
    by (cases tag)
       (auto simp: mem_val_is_local_cap_def CC_def cap_of_mem_bytes_of_word_B1_Capability_of_tag_word)
  have tagged: "CapIsTagSet c" and not_sealed: "\<not>CapIsSealed c"
    using assms
    by (auto elim!: Run_bindE split: if_splits simp: CheckCapability_def)
  then have c: "c \<in> derivable (accessed_caps (invoked_indirect_caps = {}) (run s t))"
    using \<open>\<not>CapIsSealed c \<longrightarrow> c \<in> derivable_caps (run s t)\<close>
    by (auto simp: derivable_caps_def)
  have aligned': "nat sz' = 16 \<and> aligned paddr 16" if "tag"
    using aligned paddr that
    by auto
  (*obtain t' bvaddr
    where t': "Run (CapIsRangeInBounds c bvaddr (word_of_int sz)) t' True"
      and bvaddr: "unat bvaddr \<in> bounds_addresses (unat vaddr)"
    using t
    unfolding CheckCapability_def bounds_addresses_def
    by (auto elim!: Run_bindE AddrTop_cases split: if_splits
             simp: Run_and_boolM_True_iff bin_nth_int_unat unat_sext_subrange_64_55 unat_zext_subrange_64_55)*)
  obtain t' bvaddr
    where t': "Run (CapIsRangeInBounds c bvaddr (word_of_int sz)) t' True"
      and bvaddr: "bounds_address acctype (unat vaddr) = unat bvaddr"
    using t
    unfolding CheckCapability_def bounds_address_def
    by (auto elim!: Run_bindE AddrTop_cases split: if_splits
             simp: Run_and_boolM_True_iff bin_nth_int_unat unat_sext_subrange_64_55 unat_zext_subrange_64_55)
  from CapIsRangeInBounds_in_get_mem_region[OF t']
  have "addrs_in_mem_region c Store (bounds_address acctype vaddr') paddr (nat sz')"
    using paddr sz sz' bvaddr
    unfolding addrs_in_mem_region_def
    by (auto simp: unat_def uint_word_of_int subset_eq)
  moreover have "has_access_permission c Store tag ?is_local_cap"
  proof -
    have "cap_permits req_perms c"
      using t
      by (auto simp: CheckCapability_def elim!: Run_bindE split: if_splits)
    from cap_perm_bits_included_trans[OF this]
    show ?thesis
      using store_perm store_cap_perm local_perm
      unfolding has_access_permission_def is_local_cap
      by (auto simp: CC_def)
  qed
  ultimately have "authorises_access c Store tag ?is_local_cap (bounds_address acctype vaddr') paddr (nat sz')"
    using tagged not_sealed
    by (auto simp: authorises_access_def)
  then show "access_enabled (run s t) Store (bounds_address acctype vaddr') paddr (nat sz') ?bytes ?tagbit"
    using aligned' c bvaddr'
    by (cases tag) (auto simp: access_enabled_def)
qed*)

(*lemma VADeref_addr_l2p64[intro, simp, derivable_capsE]:
  assumes "Run (VACheckAddress base addr sz perms acctype) t u" "trace_assms t"
  shows "uint addr + sz \<le> 2^64"
  (* TODO: Add capability validness assumption to trace_assms, and prove
     that it is an invariant of the derivable caps *)
  sorry

lemma VADeref_addr_l2p64_nat[intro, simp, derivable_capsE]:
  assumes "Run (VACheckAddress base addr sz perms acctype) t u" "trace_assms t"
    and "0 \<le> sz"
  shows "unat addr + nat sz \<le> 2^64"
  using VADeref_addr_l2p64[OF assms(1,2)] assms(3)
  by (auto simp add: unat_def simp flip: nat_add_distrib)*)

lemma MorelloCheckForCMO_store_enabled_data[derivable_capsE]:
  assumes "Run (MorelloCheckForCMO c CAP_PERM_STORE acctype) t addr" and "inv_trace_assms s t"
    and "c \<in> derivable_caps s"
    and "{''PCC''} \<subseteq> accessible_regs s"
  shows "store_enabled (run s t) acctype (unat (Align addr 64)) 64 data False"
proof (unfold store_enabled_def, intro conjI allI impI)
  fix paddr
  let ?tagbit = "bitU_of_bool False"
  let ?bytes = "mem_bytes_of_word data"
  let ?vaddr = "unat (Align addr 64)"
  let ?bvaddr = "bounds_address acctype ?vaddr"
  assume "translate_address ?vaddr = Some paddr"
  then have paddr: "translate_address ?bvaddr = Some paddr"
    by (auto simp: translate_bounds_address translate_address_valid)
  (* We need to prove the existence of a derivable capability with certain properties in a way for
     which our proof tactics for derivability etc are not tailored, so we use standard proof
     methods but provide some helpful simplification rules. *)
  note Align64 = Align_AND_NOT_mask[where n = 6, simplified]
  note [simp] = arith_shiftr_def arith_shiftr_mword_def
  have [simp]: "Run (if x then CapabilityFault f a i \<bind> AArch64_Abort addr else return ()) t () \<longleftrightarrow> (\<not>x \<and> t = [])" for x f a i t
    by (cases x) (auto elim!: Run_bindE)
  have [simp]: "(if x then Fault_CapBounds else Fault_None) = Fault_None \<longleftrightarrow> \<not>x" for x
    by (cases x) auto
  have [simp]: "tbi_enabled acctype (unat addr) = tbi_enabled acctype (unat (Align addr 64))"
    by (rule tbi_enabled_cong) (auto simp: Align64 bin_nth_int_unat word_ops_nth_size)
  have [simp]: "Align (zext_subrange 64 addr 55 0 :: 64 word) 64 = zext_subrange 64 (Align addr 64) 55 0"
    by (intro word_eqI) (auto simp: Align64 zext_subrange_def zext_slice_def word_ops_nth_size)
  have [simp]: "Align (sext_subrange 64 addr 55 0 :: 64 word) 64 = sext_subrange 64 (Align addr 64) 55 0"
    by (intro word_eqI) (auto simp: Align64 sext_subrange_def sext_slice_def word_ops_nth_size nth_scast nth_sshiftr nth_shiftl)
  have [simp]: "Align addr 64 !! 55 = addr !! 55"
    by (auto simp: Align64 word_ops_nth_size)
  (* The standard proof methods seem to struggle with existential quantifiers in this case,
     in particular when associativity of list append is involved, so we define a helper predicate
     and prove some rules. *)
  define c_or_DDC_in where "c_or_DDC_in \<equiv> \<lambda>t c'. c' = c \<or> (\<exists>t1 t2 t3. Run (DDC_read ()) t2 c' \<and> t = t1 @ t2 @ t3)"
  have [simp]: "c_or_DDC_in t' c" for t'
    by (auto simp: c_or_DDC_in_def)
  have c_or_DDC_in_append1: "c_or_DDC_in (t1 @ t2) c'" if "Run (DDC_read ()) t1 c'" for t1 t2 c'
    using that
    by (fastforce simp: c_or_DDC_in_def)
  have c_or_DDC_in_append2: "c_or_DDC_in (t1 @ t2) c'" if "c_or_DDC_in t2 c'" for t1 t2 c'
  proof -
    from that
    consider (c) "c' = c"
      | (t2) t1' t2' t3' where "Run (DDC_read ()) t2' c'" and "t2 = t1' @ t2' @ t3'"
      by (auto simp: c_or_DDC_in_def)
    then show ?thesis
    proof cases
      case t2
      then have "Run (DDC_read ()) t2' c' \<and> t1 @ t2 = (t1 @ t1') @ t2' @ t3'"
        by auto
      then show ?thesis
        unfolding c_or_DDC_in_def
        by blast
    qed simp
  qed
  note Run_ifEs = Run_ifE[where f = "VAFromCapability c"]
  with assms obtain t' c' bvaddr
    where t': "Run (CapIsRangeInBounds c' bvaddr 64) t' True" "translation_assms_trace t'"
      and bvaddr: "?bvaddr = unat bvaddr"
      and tagged: "CapIsTagSet c'" and not_sealed: "\<not>CapIsSealed c'"
      and perms: "cap_permits CAP_PERM_STORE c'"
      and "c_or_DDC_in t c'"
    unfolding MorelloCheckForCMO_def VAToCapability_def bounds_address_def has_ttbr1_def
    (* TODO: This takes extremely long (around 20 minutes, on a somewhat slow machine).
       It also assumes that CheckCapability.patch has been applied to the ASL. *)
    by (cases "s1_enabled acctype", cases "has_ttbr1 acctype \<and> addr !! 55")
       (auto simp: bin_nth_int_unat unat_zext_subrange_64_55 unat_sext_subrange_64_55 VAIsCapability_def has_ttbr1_def
             elim!: Run_bindE Run_and_boolM_E Run_or_boolM_E Run_ifE[where f = "VAFromCapability c"]
             dest!: translation_el s1_enabled tbi_enabled' in_host
             simp: c_or_DDC_in_append1 c_or_DDC_in_append2)
  have "\<forall>rv. E_write_reg ''PCC'' rv \<notin> set t"
    using assms runs_no_reg_writes_to_MorelloCheckForCMO[of "{''PCC''}"]
    by (fastforce simp: runs_no_reg_writes_to_def)
  then have c': "c' \<in> derivable_caps (run s t)"
    using \<open>c_or_DDC_in t c'\<close> assms
    by (fastforce simp: c_or_DDC_in_def intro: derivable_caps_run_imp accessible_regs_no_writes_trace elim: derivable_capsE)
  from derivable_caps_invariant[OF this]
  have "get_limit c' \<le> 2^64"
    using \<open>CapIsTagSet c'\<close> inv_trace_assms_accessed_caps_invariant[OF \<open>inv_trace_assms s t\<close>]
    by (auto simp: cap_invariant_def)
  with t' show "?bvaddr + nat 64 \<le> 2^64"
    using CapIsRangeInBounds_in_get_mem_region[OF t']
    by (auto simp: bvaddr get_mem_region_def split: if_splits)
  show "access_enabled (run s t) Store ?bvaddr paddr (nat 64) ?bytes ?tagbit"
    using c' paddr tagged not_sealed perms CapIsRangeInBounds_in_get_mem_region[OF t']
    unfolding access_enabled_def authorises_access_def addrs_in_mem_region_def has_access_permission_def
    by (auto simp: bvaddr derivable_caps_def)
qed simp

text \<open>Loads enabled by VADeref\<close>

lemmas load_enabled_combinators[derivable_caps_combinators] =
  Run_bindE'[where P = "\<lambda>t. load_enabled (run s t) acctype addr sz tagged" for s acctype addr sz tagged, simplified]
  Run_ifE[where thesis = "load_enabled (run s t) acctype addr sz tagged" and t = t for s acctype addr sz tagged t]
  Run_letE[where thesis = "load_enabled (run s t) acctype addr sz tagged" and t = t for s acctype addr sz tagged t]
  Run_case_prodE[where thesis = "load_enabled (run s t) acctype addr sz tagged" and t = t for s acctype addr sz tagged t]

lemma Run_VAToCapability_iff:
  "Run (VAToCapability va) t c \<longleftrightarrow> VAIsCapability va \<and> c = VirtualAddress_base va \<and> t = []"
  unfolding VAToCapability_def
  by auto

abbreviation
  "derivable_or_invoked c s \<equiv>
     c \<in> derivable_caps s
     \<or> (\<exists>c' \<in> derivable_caps s. is_indirect_sentry c' \<and> CapUnseal c' = c \<and> c \<in> invoked_indirect_caps \<and> \<not>is_fetch)"

lemma derivable_or_invokedI1:
  "c \<in> derivable_caps s \<Longrightarrow> derivable_or_invoked c s"
  by auto

definition
  "VA_derivable_or_invoked va s \<equiv> VAIsCapability va \<longrightarrow> derivable_or_invoked (VirtualAddress_base va) s"

lemma VA_derivable_imp_VA_derivable_or_invoked[intro]:
  "VA_derivable va s \<Longrightarrow> VA_derivable_or_invoked va s"
  by (auto simp: VA_derivable_def VA_derivable_or_invoked_def VAIsCapability_def)

lemma VAFromCapability_if_sentry_derivable_or_invoked[derivable_capsE]:
  assumes "Run (VAFromCapability (if sentry then CapUnseal c else c)) t va"
    and "c \<in> derivable_caps s"
    and "sentry \<longrightarrow> CapGetObjectType c \<in> {CAP_SEAL_TYPE_LB, CAP_SEAL_TYPE_LPB} \<and> CapUnseal c \<in> invoked_indirect_caps \<and> \<not>is_fetch"
  shows "VA_derivable_or_invoked va s"
  using assms
  by (auto simp: VA_derivable_or_invoked_def is_indirect_sentry_def)

lemma VAFromCapability_derivable_or_invoked[derivable_capsE]:
  assumes "Run (VAFromCapability c) t va"
    and "c \<in> derivable_caps s"
  shows "VA_derivable_or_invoked va s"
  using assms
  by (auto simp: VA_derivable_or_invoked_def)

lemma VAToCapability_derivable_or_invoked[derivable_capsE]:
  assumes "Run (VAToCapability va) t c"
    and "VA_derivable_or_invoked va s"
  shows "derivable_or_invoked c s"
  using assms
  unfolding VA_derivable_or_invoked_def VAToCapability_def
  by auto

lemma VA_derivable_or_invoked_run_imp[derivable_caps_runI]:
  assumes "VA_derivable_or_invoked va s"
  shows "VA_derivable_or_invoked va (run s t)"
  using assms
  by (auto simp: VA_derivable_or_invoked_def intro: derivable_caps_run_imp)

lemmas BaseReg_read__1_VA_derivable_or_invoked[derivable_capsE] =
  BaseReg_read__1_VA_derivable[THEN VA_derivable_imp_VA_derivable_or_invoked]

lemma VADeref_load_enabled:
  assumes "Run (VACheckAddress va vaddr sz perms acctype') t u" "inv_trace_assms s t"
    and "sz > 0 \<and> sz < 2^52 \<and> sz' > 0"
    and "unat vaddr + nat sz \<le> 2^64 \<longrightarrow> unat vaddr \<le> vaddr' \<and> vaddr' + nat sz' \<le> unat vaddr + nat sz"
    and "perm_bits_included (if is_fetch then CAP_PERM_EXECUTE else CAP_PERM_LOAD) perms"
    and "tagged \<and> use_mem_caps \<longrightarrow> VA_from_load_auth va"
    and "tagged \<longrightarrow> nat sz' = 16 \<and> aligned vaddr' 16 \<and> \<not>is_fetch"
    and "\<not>VAIsSealedCap va \<longrightarrow> VA_derivable_or_invoked va s"
    and "{''PCC''} \<subseteq> accessible_regs s"
    and "valid_address acctype vaddr' \<longrightarrow> valid_address acctype (unat vaddr)"
    and "acctype' = acctype"
  shows "load_enabled (run s t) acctype vaddr' sz' tagged"
proof (cases "VirtualAddress_vatype va")
  case VA_Bits64
  then have *: "cap_permits CAP_PERM_LOAD_CAP c"
    if t: "Run (DDC_read ()) t c" "load_cap_trace_assms t" and tag: "tagged \<and> use_mem_caps" for t c
    using t \<open>tagged \<and> use_mem_caps \<longrightarrow> VA_from_load_auth va\<close>
    unfolding DDC_read_def Let_def VA_from_load_auth_def
    by (elim Run_bindE Run_if_ELs_cases Run_ifE Run_read_regE)
       (simp add: register_defs DDC_names_def load_cap_trace_assms_def;
        use tag no_invoked_indirect_caps_if_use_mem_caps in blast)+
  show ?thesis
    using assms
    unfolding VACheckAddress_def VAIsBits64_def Let_def
    by (elim Run_bindE)
       (simp add: VA_Bits64, derivable_capsI elim: CheckCapability_load_enabled * intro: derivable_or_invokedI1)
next
  case VA_Capability
  then have "cap_permits CAP_PERM_LOAD_CAP (VirtualAddress_base va)" if "tagged \<and> use_mem_caps"
    using that \<open>tagged \<and> use_mem_caps \<longrightarrow> VA_from_load_auth va\<close>
    using no_invoked_indirect_caps_if_use_mem_caps
    unfolding VA_from_load_auth_def load_cap_ev_assms.simps
    by auto
  then show ?thesis
    using assms VA_Capability
    unfolding VACheckAddress_def VAIsBits64_def VAIsCapability_def VAIsSealedCap_def Let_def
    by (elim Run_bindE)
       (simp, derivable_capsI elim: CheckCapability_load_enabled)
qed

text \<open>Common patterns\<close>

lemma VADeref_data_load_enabled[derivable_capsE]:
  assumes "Run (VACheckAddress va vaddr sz CAP_PERM_LOAD acctype') t u" "inv_trace_assms s t"
    and "sz > 0 \<and> sz < 2^52 \<and> sz' > 0"
    and "unat vaddr + nat sz \<le> 2^64 \<longrightarrow> unat vaddr \<le> vaddr' \<and> vaddr' + nat sz' \<le> unat vaddr + nat sz"
    and "\<not>VAIsSealedCap va \<longrightarrow> VA_derivable va s"
    and "{''PCC''} \<subseteq> accessible_regs s"
    and "valid_address acctype vaddr' \<longrightarrow> valid_address acctype (unat vaddr)"
    and "acctype' = acctype"
    and "\<not>is_fetch"
  shows "load_enabled (run s t) acctype vaddr' sz' False"
  using assms VA_derivable_imp_VA_derivable_or_invoked
  by (elim VADeref_load_enabled) auto

lemma VADeref_cap_load_enabled[derivable_capsE]:
  assumes "Run (VACheckAddress va vaddr sz CAP_PERM_LOAD acctype') t u" "inv_trace_assms s t"
    and "sz > 0 \<and> sz < 2^52 \<and> sz' > 0"
    and "unat vaddr + nat sz \<le> 2^64 \<longrightarrow> unat vaddr \<le> vaddr' \<and> vaddr' + nat sz' \<le> unat vaddr + nat sz"
    and "nat sz' = 16 \<and> aligned vaddr' 16"
    and "\<not>VAIsSealedCap va \<longrightarrow> VA_derivable va s"
    and "use_mem_caps \<longrightarrow> VA_from_load_auth va"
    and "{''PCC''} \<subseteq> accessible_regs s"
    and "valid_address acctype vaddr' \<longrightarrow> valid_address acctype (unat vaddr)"
    and "acctype' = acctype"
    and "\<not>is_fetch"
  shows "load_enabled (run s t) acctype vaddr' sz' True"
  using assms VA_derivable_imp_VA_derivable_or_invoked
  by (elim VADeref_load_enabled) auto

lemma VADeref_load_data_access_enabled[derivable_capsE]:
  assumes "Run (VACheckAddress va vaddr sz CAP_PERM_LOAD acctype) t u" "inv_trace_assms s t"
    and "sz > 0" "sz < 2^52"
    and "translate_address (unat vaddr) = Some paddr"
    and "\<not>VAIsSealedCap va \<longrightarrow> VA_derivable va s"
    and "{''PCC''} \<subseteq> accessible_regs s"
    and "\<not>is_fetch"
  shows "paccess_enabled (run s t) Load paddr (nat sz) data B0"
  using assms
  by (elim VADeref_data_load_enabled[THEN load_enabled_access_enabled]) auto

text \<open>Stores enabled by VADeref\<close>

lemmas store_enabled_combinators[derivable_caps_combinators] =
  Run_bindE'[where P = "\<lambda>t. store_enabled (run s t) acctype addr sz data tag" for s acctype addr sz data tag, simplified]
  Run_ifE[where thesis = "store_enabled (run s t) acctype addr sz data tag" and t = t for s acctype addr sz data tag t]
  Run_letE[where thesis = "store_enabled (run s t) acctype addr sz data tag" and t = t for s acctype addr sz data tag t]
  Run_case_prodE[where thesis = "store_enabled (run s t) acctype addr sz data tag" and t = t for s acctype addr sz data tag t]

lemma VADeref_store_enabled:
  assumes "Run (VACheckAddress va vaddr sz perms acctype') t u" "inv_trace_assms s t"
    and "sz > 0 \<and> sz < 2^52 \<and> sz' > 0"
    and "unat vaddr + nat sz \<le> 2^64 \<longrightarrow> unat vaddr \<le> vaddr' \<and> vaddr' + nat sz' \<le> unat vaddr + nat sz"
    and "perm_bits_included CAP_PERM_STORE perms"
    and "tag \<longrightarrow> perm_bits_included CAP_PERM_STORE_CAP perms"
    and "tag \<and> CapIsLocal (Capability_of_tag_word tag (ucast data)) \<longrightarrow> perm_bits_included CAP_PERM_STORE_LOCAL perms"
    and "tag \<longrightarrow> LENGTH('a) = 128 \<and> nat sz' = 16 \<and> aligned vaddr' 16"
    and "\<not>VAIsSealedCap va \<longrightarrow> VA_derivable va s"
    and "{''PCC''} \<subseteq> accessible_regs s"
    and "valid_address acctype vaddr' \<longrightarrow> valid_address acctype (unat vaddr)"
    and "acctype' = acctype"
  shows "store_enabled (run s t) acctype vaddr' sz' (data :: 'a::len word) tag"
proof (cases "VAIsBits64 va")
  case True
  then show ?thesis
    using assms(1,2)
    unfolding VACheckAddress_def
    by - (derivable_capsI_with \<open>split_inv_trace_assms_append | solves \<open>accessible_regsI assms: assms(3-)\<close>\<close>
            elim: CheckCapability_store_enabled)
next
  case False
  let ?c = "VirtualAddress_base va"
  obtain t1 t2 t3 addr
    where "Run (CheckCapability ?c vaddr sz perms acctype) t3 addr"
      and "inv_trace_assms (run (run s t1) t2) t3"
      and "VirtualAddress_vatype va = VA_Capability"
      and "t = t1 @ t2 @ t3"
    using False assms(1,2)
    unfolding VACheckAddress_def \<open>acctype' = acctype\<close>
    by (auto elim!: Run_bindE Run_ifE)
  then show ?thesis
    using assms(3-)
    unfolding \<open>t = t1 @ t2 @ t3\<close> foldl_append
    by (elim CheckCapability_store_enabled)
       (auto simp: VA_derivable_def VAIsSealedCap_def intro: derivable_caps_run_imp)
qed

text \<open>Common patterns\<close>

lemma VADeref_store_data_enabled[derivable_capsE]:
  assumes "Run (VACheckAddress va vaddr sz CAP_PERM_STORE acctype') t u" "inv_trace_assms s t"
    and "sz > 0 \<and> sz < 2^52 \<and> sz' > 0"
    and "unat vaddr + nat sz \<le> 2^64 \<longrightarrow> unat vaddr \<le> vaddr' \<and> vaddr' + nat sz' \<le> unat vaddr + nat sz"
    and "\<not>VAIsSealedCap va \<longrightarrow> VA_derivable va s"
    and "{''PCC''} \<subseteq> accessible_regs s"
    and "valid_address acctype vaddr' \<longrightarrow> valid_address acctype (unat vaddr)"
    and "acctype' = acctype"
  shows "store_enabled (run s t) acctype vaddr' sz' (data :: 'a::len word) False"
  using assms
  by (elim VADeref_store_enabled) auto

lemma VADeref_store_data_enabled'[derivable_capsE]:
  assumes "Run (VACheckAddress va vaddr sz (perms OR CAP_PERM_STORE) acctype') t u" "inv_trace_assms s t"
    and "sz > 0 \<and> sz < 2^52 \<and> sz' > 0"
    and "unat vaddr + nat sz \<le> 2^64 \<longrightarrow> unat vaddr \<le> vaddr' \<and> vaddr' + nat sz' \<le> unat vaddr + nat sz"
    and "\<not>VAIsSealedCap va \<longrightarrow> VA_derivable va s"
    and "{''PCC''} \<subseteq> accessible_regs s"
    and "valid_address acctype vaddr' \<longrightarrow> valid_address acctype (unat vaddr)"
    and "acctype' = acctype"
  shows "store_enabled (run s t) acctype vaddr' sz' (data :: 'a::len word) False"
  using assms
  by (elim VADeref_store_enabled) auto

abbreviation cap_store_perms where
  "cap_store_perms c \<equiv>
     (if CapIsTagSet c
      then let req_perms = or_vec CAP_PERM_STORE CAP_PERM_STORE_CAP
           in if CapIsLocal c then or_vec req_perms CAP_PERM_STORE_LOCAL else req_perms
      else CAP_PERM_STORE)"

lemma VADeref_store_cap_enabled[derivable_capsE]:
  assumes "Run (VACheckAddress va vaddr CAPABILITY_DBYTES (cap_store_perms c) acctype') t u" "inv_trace_assms s t"
    and "aligned (unat vaddr) 16"
    and "Capability_of_tag_word tag data = c"
    and "\<not>VAIsSealedCap va \<longrightarrow> VA_derivable va s"
    and "{''PCC''} \<subseteq> accessible_regs s"
    and "acctype' = acctype"
  shows "store_enabled (run s t) acctype (unat vaddr) 16 (data :: 128 word) tag"
  using assms
  by (elim VADeref_store_enabled) (auto split: if_splits)

lemma VADeref_store_cap_pair_snd_enabled[derivable_capsE]:
  assumes "Run (VACheckAddress va (add_vec vaddr (integer_subrange CAPABILITY_DBYTES 63 0)) CAPABILITY_DBYTES (cap_store_perms c) acctype') t u" "inv_trace_assms s t"
    and "aligned (unat vaddr) 32"
    and "Capability_of_tag_word tag data = c"
    and "\<not>VAIsSealedCap va \<longrightarrow> VA_derivable va s"
    and "{''PCC''} \<subseteq> accessible_regs s"
    and "acctype' = acctype"
  shows "store_enabled (run s t) acctype (unat vaddr + 16) 16 (data :: 128 word) tag"
  using assms
  by (elim VADeref_store_enabled) (auto split: if_splits simp: aligned_unat_plus_distrib)

lemma VADeref_store_cap_enabled'[derivable_capsE]:
  assumes "Run (VACheckAddress va vaddr CAPABILITY_DBYTES (perms OR cap_store_perms c) acctype') t u" "inv_trace_assms s t"
    and "aligned (unat vaddr) 16"
    and "Capability_of_tag_word tag data = c"
    and "\<not>VAIsSealedCap va \<longrightarrow> VA_derivable va s"
    and "{''PCC''} \<subseteq> accessible_regs s"
    and "acctype' = acctype"
  shows "store_enabled (run s t) acctype (unat vaddr) 16 (data :: 128 word) tag"
  using assms
  by (elim VADeref_store_enabled) (auto split: if_splits)

lemma VADeref_store_data_access_enabled[derivable_capsE]:
  assumes "Run (VACheckAddress va vaddr sz CAP_PERM_STORE acctype) t u" "inv_trace_assms s t"
    and "sz > 0" "sz < 2^52"
    and "translate_address (unat vaddr) = Some paddr"
    and "\<not>VAIsSealedCap va \<longrightarrow> VA_derivable va s"
    and "{''PCC''} \<subseteq> accessible_regs s"
    and "valid_address acctype vaddr' \<longrightarrow> valid_address acctype (unat vaddr)"
  shows "paccess_enabled (run s t) Store paddr (nat sz) (mem_bytes_of_word data) B0"
  using assms
  by (elim VADeref_store_data_enabled[THEN store_enabled_access_enabled]) auto

lemma VADeref_store_data_access_enabled'[derivable_capsE]:
  assumes "Run (VACheckAddress va vaddr sz (perms OR CAP_PERM_STORE) acctype) t u" "inv_trace_assms s t"
    and "sz > 0" "sz < 2^52"
    and "translate_address (unat vaddr) = Some paddr"
    and "\<not>VAIsSealedCap va \<longrightarrow> VA_derivable va s"
    and "{''PCC''} \<subseteq> accessible_regs s"
  shows "paccess_enabled (run s t) Store paddr (nat sz) (mem_bytes_of_word data) B0"
  using assms
  by (elim VADeref_store_data_enabled'[THEN store_enabled_access_enabled]) auto

lemma unat_le_add_vec_int_elim:
  "unat x + z \<le> 2 ^ N \<Longrightarrow> N = size x \<Longrightarrow> 0 \<le> n \<Longrightarrow> nat n < z \<Longrightarrow>
    unat x \<le> unat (add_vec_int x n)"
  apply (subgoal_tac "\<exists> i. n = int i")
   apply (clarsimp)
  apply (rule_tac x="nat n" in exI)
  apply simp
  done

lemma unat_add_vec_int_plus_le:
  "unat x + nat n + i \<le> j \<Longrightarrow> 0 \<le> n \<Longrightarrow>
    unat (add_vec_int x n) + i \<le> j"
  apply (erule order_trans[rotated])
  apply (simp add: unat_word_ariths)
  apply (rule order_trans, rule mod_less_eq_dividend)
  apply (simp add: int_mod_le nat_mono unat_def uint_word_of_int)
  done

(*lemma traces_enabled_bind_VADeref_Let[traces_enabled_combinatorI]:
  assumes "traces_enabled (VADeref va sz perms acctype \<bind> (\<lambda>addr. f addr y)) s"
  shows "traces_enabled (VADeref va sz perms acctype \<bind> (\<lambda>addr. let x = y in f addr x)) s"
  using assms
  by auto*)

text \<open>Work around a problem with a common pattern of VirtualAddress dereference
  in the ASL, where there are two calls to VADeref with the same address and size,
  but requesting different permissions.  This is used to get the priority of faults
  right for instructions that both load and store data.  The ASL assumes that the
  virtual address returned by the two calls is the same, and ignores the second.
  This does not hold for arbitrary traces, because the returned value depends on
  register reads, so we'll have to add an assumption on traces that consecutive
  reads from the same register (without writes in between) read the same values.\<close>

(*lemma traces_enabled_bind_VADeref_pair_ignore_second[traces_enabled_combinatorI]:
  assumes "traces_enabled (VADeref va sz perms1 acctype1) s"
    and "\<And>t1. traces_enabled (VADeref va sz perms2 acctype2) (run s t1)"
    and "\<And>t1 t2 addr. Run (VADeref va sz (perms1 OR perms2) acctype1) t1 addr \<Longrightarrow> trace_assms t1  \<Longrightarrow> trace_assms t2 \<Longrightarrow> traces_enabled (f addr) (run (run s t1) t2)"
  shows "traces_enabled (VADeref va sz perms1 acctype1 \<bind> (\<lambda>addr. VADeref va sz perms2 acctype2 \<bind> (\<lambda>_. f addr))) s"
  sorry

lemma traces_enabled_bind_VADeref_pair_ignore_first[traces_enabled_combinatorI]:
  assumes "traces_enabled (VADeref va sz perms1 acctype1) s"
    and "\<And>t1. traces_enabled (VADeref va sz perms2 acctype2) (run s t1)"
    and "\<And>t1 t2 addr addr'. Run (VADeref va sz perms1 acctype1) t1 addr' \<Longrightarrow> Run (VADeref va sz (perms1 OR perms2) acctype2) t2 addr \<Longrightarrow> trace_assms t1  \<Longrightarrow> trace_assms t2 \<Longrightarrow> traces_enabled (f addr) (run (run s t1) t2)"
  shows "traces_enabled (VADeref va sz perms1 acctype1 \<bind> (\<lambda>_. VADeref va sz perms2 acctype2 \<bind> (\<lambda>addr. f addr))) s"
  sorry

lemma traces_enabled_bind_VADeref_pair_add[traces_enabled_combinatorI]:
  assumes "traces_enabled (VADeref va sz perms1 acctype1) s"
    and "\<And>t1. traces_enabled (VAAdd va (integer_subrange sz 63 0)) (run s t1)"
    and "\<And>t1 t2 va'. traces_enabled (VADeref va' sz perms2 acctype2) (run (run s t1) t2)"
    and "\<And>t1 t2 t3 addr va'. Run (VADeref va (sz * 2) (perms1 OR perms2) acctype1) t1 addr \<Longrightarrow> trace_assms t1  \<Longrightarrow> trace_assms t2 \<Longrightarrow> trace_assms t3 \<Longrightarrow> traces_enabled (f addr) (run (run (run s t1) t2) t3)"
  shows "traces_enabled (VADeref va sz perms1 acctype1 \<bind> (\<lambda>addr. VAAdd va (integer_subrange sz 63 0) \<bind> (\<lambda>va'. VADeref va' sz perms2 acctype2 \<bind> (\<lambda>_. f addr)))) s"
  sorry*)

text \<open>Define loop invariant and a helper lemma for the vector_multiple_no_wb instruction with a nested loop\<close>

fun Inv_vector_multiple_no_wb :: "nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> 64 word \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> 64 word \<times> 'b \<Rightarrow> 'c \<Rightarrow> bool" where
  "Inv_vector_multiple_no_wb ebytes elements selem base idx_a idx_b idx_c vars s =
     ((unat (fst vars) = nat idx_a * nat elements * nat selem * ebytes +
                         nat idx_b * nat selem * ebytes +
                         nat idx_c * ebytes) \<and>
      ((idx_a = 0 \<and> idx_b = 0 \<and> idx_c = 0) \<or> valid_address AccType_VEC (unat base)))"

lemma Inv_vector_multiple_no_wb_step:
  assumes "Inv_vector_multiple_no_wb ebytes elements selem base idx_a idx_b idx_c vars s"
    and "idx_a \<le> 4" and "idx_b \<le> 16" and "0 \<le> idx_c" and "idx_c \<le> 4"
    and "elements \<le> 16" and "selem \<le> 4" and "ebytes \<le> 8"
    and "fst vars' = fst vars + (word_of_int (int ebytes))"
    and "fst vars = 0 \<longrightarrow> valid_address AccType_VEC (unat base)"
  shows "Inv_vector_multiple_no_wb ebytes elements selem base idx_a idx_b (idx_c + 1) vars' s'"
proof -
  have "nat idx_a * nat elements * nat selem * ebytes + nat idx_b * nat selem * ebytes + nat idx_c * ebytes \<le> 4 * 16 * 4 * 8 + 16 * 4 * 8 + 4 * 8"
    using assms
    by (intro add_le_mono mult_le_mono) auto
  then show ?thesis
    using assms
    by (auto simp: nat_add_distrib unat_0_iff)
qed

fun Inv_vector_single_no_wb where
  "Inv_vector_single_no_wb ebytes idx address offset =
     (unat offset = nat idx * nat ebytes \<and> (idx \<noteq> 0 \<longrightarrow> valid_address AccType_VEC (unat address)))"

end

context Morello_Fetch_Mem_Automaton
begin

lemma traces_enabled_Mem_read_Fetch[traces_enabledI]:
  assumes "\<And>v. paccess_enabled s Fetch (unat (FullAddress_address (AddressDescriptor_paddress desc))) (nat sz) v B0"
  shows "traces_enabled (Mem_read desc sz accdesc) s"
  unfolding Mem_read_def bind_assoc
  by (traces_enabledI intro: traces_enabled_read_mem assms: assms)

lemma load_enabled_paccess_enabled_Fetch[intro]:
  assumes "load_enabled s acctype vaddr sz tagged"
    and "sz' = nat sz"
    and "translate_address vaddr = Some paddr"
    and "tagged \<or> tag = B0"
  shows "paccess_enabled s Fetch paddr sz' data tag"
  using assms
  unfolding load_enabled_def
  by (cases tagged) auto

end

end
