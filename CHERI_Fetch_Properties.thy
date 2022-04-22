section \<open>Generated instruction fetch proofs\<close>

theory CHERI_Fetch_Properties
imports CHERI_Mem_Properties
begin

context Morello_Fetch_Write_Cap_Automaton
begin

lemma traces_enabled_write_regs[traces_enabledI]:
  "\<And>c. c \<in> derivable_caps s \<Longrightarrow> system_reg_access s \<Longrightarrow> traces_enabled (write_reg CDBGDTR_EL0_ref c) s"
  "\<And>c. c \<in> derivable_caps s \<Longrightarrow> system_reg_access s \<Longrightarrow> traces_enabled (write_reg CDLR_EL0_ref c) s"
  "\<And>c. c \<in> derivable_caps s \<Longrightarrow> traces_enabled (write_reg CID_EL0_ref c) s"
  "\<And>c. c \<in> derivable_caps s \<Longrightarrow> traces_enabled (write_reg DDC_EL0_ref c) s"
  "\<And>c. c \<in> derivable_caps s \<Longrightarrow> traces_enabled (write_reg DDC_EL1_ref c) s"
  "\<And>c. c \<in> derivable_caps s \<Longrightarrow> traces_enabled (write_reg DDC_EL2_ref c) s"
  "\<And>c. c \<in> derivable_caps s \<Longrightarrow> traces_enabled (write_reg DDC_EL3_ref c) s"
  "\<And>c. c \<in> derivable_caps s \<Longrightarrow> traces_enabled (write_reg ELR_EL1_ref c) s"
  "\<And>c. c \<in> derivable_caps s \<Longrightarrow> traces_enabled (write_reg ELR_EL2_ref c) s"
  "\<And>c. c \<in> derivable_caps s \<Longrightarrow> traces_enabled (write_reg ELR_EL3_ref c) s"
  "\<And>v. system_reg_access s \<Longrightarrow> traces_enabled (write_reg MAIR_EL1_ref v) s"
  "\<And>v. system_reg_access s \<Longrightarrow> traces_enabled (write_reg MAIR_EL2_ref v) s"
  "\<And>v. system_reg_access s \<Longrightarrow> traces_enabled (write_reg MAIR_EL3_ref v) s"
  "\<And>v. system_reg_access s \<Longrightarrow> traces_enabled (write_reg MPAM0_EL1_ref v) s"
  "\<And>v. system_reg_access s \<Longrightarrow> traces_enabled (write_reg MPAM3_EL3_ref v) s"
  "\<And>v. system_reg_access s \<Longrightarrow> traces_enabled (write_reg MPAMHCR_EL2_ref v) s"
  "\<And>v. system_reg_access s \<Longrightarrow> traces_enabled (write_reg MPAMIDR_EL1_ref v) s"
  "\<And>v. system_reg_access s \<Longrightarrow> traces_enabled (write_reg MPAMVPM0_EL2_ref v) s"
  "\<And>v. system_reg_access s \<Longrightarrow> traces_enabled (write_reg MPAMVPM1_EL2_ref v) s"
  "\<And>v. system_reg_access s \<Longrightarrow> traces_enabled (write_reg MPAMVPM2_EL2_ref v) s"
  "\<And>v. system_reg_access s \<Longrightarrow> traces_enabled (write_reg MPAMVPM3_EL2_ref v) s"
  "\<And>v. system_reg_access s \<Longrightarrow> traces_enabled (write_reg MPAMVPM4_EL2_ref v) s"
  "\<And>v. system_reg_access s \<Longrightarrow> traces_enabled (write_reg MPAMVPM5_EL2_ref v) s"
  "\<And>v. system_reg_access s \<Longrightarrow> traces_enabled (write_reg MPAMVPM6_EL2_ref v) s"
  "\<And>v. system_reg_access s \<Longrightarrow> traces_enabled (write_reg MPAMVPM7_EL2_ref v) s"
  "\<And>v. system_reg_access s \<Longrightarrow> traces_enabled (write_reg MPAMVPMV_EL2_ref v) s"
  "\<And>c. c \<in> derivable_caps s \<Longrightarrow> traces_enabled (write_reg PCC_ref c) s"
  "\<And>c. c \<in> derivable_caps s \<Longrightarrow> traces_enabled (write_reg RDDC_EL0_ref c) s"
  "\<And>c. c \<in> derivable_caps s \<Longrightarrow> traces_enabled (write_reg RSP_EL0_ref c) s"
  "\<And>c. c \<in> derivable_caps s \<Longrightarrow> traces_enabled (write_reg RTPIDR_EL0_ref c) s"
  "\<And>v. system_reg_access s \<Longrightarrow> traces_enabled (write_reg SCR_EL3_ref v) s"
  "\<And>v. system_reg_access s \<Longrightarrow> traces_enabled (write_reg SCTLR_EL1_ref v) s"
  "\<And>v. system_reg_access s \<Longrightarrow> traces_enabled (write_reg SCTLR_EL2_ref v) s"
  "\<And>v. system_reg_access s \<Longrightarrow> traces_enabled (write_reg SCTLR_EL3_ref v) s"
  "\<And>c. c \<in> derivable_caps s \<Longrightarrow> traces_enabled (write_reg SP_EL0_ref c) s"
  "\<And>c. c \<in> derivable_caps s \<Longrightarrow> traces_enabled (write_reg SP_EL1_ref c) s"
  "\<And>c. c \<in> derivable_caps s \<Longrightarrow> traces_enabled (write_reg SP_EL2_ref c) s"
  "\<And>c. c \<in> derivable_caps s \<Longrightarrow> traces_enabled (write_reg SP_EL3_ref c) s"
  "\<And>v. system_reg_access s \<Longrightarrow> traces_enabled (write_reg TCR_EL1_ref v) s"
  "\<And>v. system_reg_access s \<Longrightarrow> traces_enabled (write_reg TCR_EL2_ref v) s"
  "\<And>v. system_reg_access s \<Longrightarrow> traces_enabled (write_reg TCR_EL3_ref v) s"
  "\<And>c. c \<in> derivable_caps s \<Longrightarrow> traces_enabled (write_reg TPIDRRO_EL0_ref c) s"
  "\<And>c. c \<in> derivable_caps s \<Longrightarrow> traces_enabled (write_reg TPIDR_EL0_ref c) s"
  "\<And>c. c \<in> derivable_caps s \<Longrightarrow> traces_enabled (write_reg TPIDR_EL1_ref c) s"
  "\<And>c. c \<in> derivable_caps s \<Longrightarrow> traces_enabled (write_reg TPIDR_EL2_ref c) s"
  "\<And>c. c \<in> derivable_caps s \<Longrightarrow> traces_enabled (write_reg TPIDR_EL3_ref c) s"
  "\<And>v. system_reg_access s \<Longrightarrow> traces_enabled (write_reg TTBR0_EL1_ref v) s"
  "\<And>v. system_reg_access s \<Longrightarrow> traces_enabled (write_reg TTBR0_EL2_ref v) s"
  "\<And>v. system_reg_access s \<Longrightarrow> traces_enabled (write_reg TTBR0_EL3_ref v) s"
  "\<And>v. system_reg_access s \<Longrightarrow> traces_enabled (write_reg TTBR1_EL1_ref v) s"
  "\<And>v. system_reg_access s \<Longrightarrow> traces_enabled (write_reg TTBR1_EL2_ref v) s"
  "\<And>c. c \<in> derivable_caps s \<Longrightarrow> system_reg_access s \<Longrightarrow> traces_enabled (write_reg VBAR_EL1_ref c) s"
  "\<And>c. c \<in> derivable_caps s \<Longrightarrow> system_reg_access s \<Longrightarrow> traces_enabled (write_reg VBAR_EL2_ref c) s"
  "\<And>c. c \<in> derivable_caps s \<Longrightarrow> system_reg_access s \<Longrightarrow> traces_enabled (write_reg VBAR_EL3_ref c) s"
  "\<And>v. system_reg_access s \<Longrightarrow> traces_enabled (write_reg VTCR_EL2_ref v) s"
  "\<And>v. system_reg_access s \<Longrightarrow> traces_enabled (write_reg VTTBR_EL2_ref v) s"
  "\<And>v. system_reg_access s \<Longrightarrow> traces_enabled (write_reg MPAM1_EL1_0_62_ref v) s"
  "\<And>v. system_reg_access s \<Longrightarrow> traces_enabled (write_reg MPAM2_EL2_0_62_ref v) s"
  "\<And>c. c \<in> derivable_caps s \<Longrightarrow> traces_enabled (write_reg R00_ref c) s"
  "\<And>c. c \<in> derivable_caps s \<Longrightarrow> traces_enabled (write_reg R01_ref c) s"
  "\<And>c. c \<in> derivable_caps s \<Longrightarrow> traces_enabled (write_reg R02_ref c) s"
  "\<And>c. c \<in> derivable_caps s \<Longrightarrow> traces_enabled (write_reg R03_ref c) s"
  "\<And>c. c \<in> derivable_caps s \<Longrightarrow> traces_enabled (write_reg R04_ref c) s"
  "\<And>c. c \<in> derivable_caps s \<Longrightarrow> traces_enabled (write_reg R05_ref c) s"
  "\<And>c. c \<in> derivable_caps s \<Longrightarrow> traces_enabled (write_reg R06_ref c) s"
  "\<And>c. c \<in> derivable_caps s \<Longrightarrow> traces_enabled (write_reg R07_ref c) s"
  "\<And>c. c \<in> derivable_caps s \<Longrightarrow> traces_enabled (write_reg R08_ref c) s"
  "\<And>c. c \<in> derivable_caps s \<Longrightarrow> traces_enabled (write_reg R09_ref c) s"
  "\<And>c. c \<in> derivable_caps s \<Longrightarrow> traces_enabled (write_reg R10_ref c) s"
  "\<And>c. c \<in> derivable_caps s \<Longrightarrow> traces_enabled (write_reg R11_ref c) s"
  "\<And>c. c \<in> derivable_caps s \<Longrightarrow> traces_enabled (write_reg R12_ref c) s"
  "\<And>c. c \<in> derivable_caps s \<Longrightarrow> traces_enabled (write_reg R13_ref c) s"
  "\<And>c. c \<in> derivable_caps s \<Longrightarrow> traces_enabled (write_reg R14_ref c) s"
  "\<And>c. c \<in> derivable_caps s \<Longrightarrow> traces_enabled (write_reg R15_ref c) s"
  "\<And>c. c \<in> derivable_caps s \<Longrightarrow> traces_enabled (write_reg R16_ref c) s"
  "\<And>c. c \<in> derivable_caps s \<Longrightarrow> traces_enabled (write_reg R17_ref c) s"
  "\<And>c. c \<in> derivable_caps s \<Longrightarrow> traces_enabled (write_reg R18_ref c) s"
  "\<And>c. c \<in> derivable_caps s \<Longrightarrow> traces_enabled (write_reg R19_ref c) s"
  "\<And>c. c \<in> derivable_caps s \<Longrightarrow> traces_enabled (write_reg R20_ref c) s"
  "\<And>c. c \<in> derivable_caps s \<Longrightarrow> traces_enabled (write_reg R21_ref c) s"
  "\<And>c. c \<in> derivable_caps s \<Longrightarrow> traces_enabled (write_reg R22_ref c) s"
  "\<And>c. c \<in> derivable_caps s \<Longrightarrow> traces_enabled (write_reg R23_ref c) s"
  "\<And>c. c \<in> derivable_caps s \<Longrightarrow> traces_enabled (write_reg R24_ref c) s"
  "\<And>c. c \<in> derivable_caps s \<Longrightarrow> traces_enabled (write_reg R25_ref c) s"
  "\<And>c. c \<in> derivable_caps s \<Longrightarrow> traces_enabled (write_reg R26_ref c) s"
  "\<And>c. c \<in> derivable_caps s \<Longrightarrow> traces_enabled (write_reg R27_ref c) s"
  "\<And>c. c \<in> derivable_caps s \<Longrightarrow> traces_enabled (write_reg R28_ref c) s"
  "\<And>c. c \<in> derivable_caps s \<Longrightarrow> traces_enabled (write_reg R29_ref c) s"
  "\<And>c. c \<in> derivable_caps s \<Longrightarrow> traces_enabled (write_reg R30_ref c) s"
  by (intro traces_enabled_write_reg; auto simp: register_defs derivable_caps_def)+

lemma traces_enabled_read_regs[traces_enabledI]:
  "system_reg_access s \<Longrightarrow> traces_enabled (read_reg CDBGDTR_EL0_ref) s"
  "system_reg_access s \<Longrightarrow> traces_enabled (read_reg CDLR_EL0_ref) s"
  "traces_enabled (read_reg CID_EL0_ref) s"
  "traces_enabled (read_reg DDC_EL0_ref) s"
  "traces_enabled (read_reg DDC_EL1_ref) s"
  "traces_enabled (read_reg DDC_EL2_ref) s"
  "traces_enabled (read_reg DDC_EL3_ref) s"
  "traces_enabled (read_reg ELR_EL1_ref) s"
  "traces_enabled (read_reg ELR_EL2_ref) s"
  "traces_enabled (read_reg ELR_EL3_ref) s"
  "traces_enabled (read_reg PCC_ref) s"
  "traces_enabled (read_reg RDDC_EL0_ref) s"
  "traces_enabled (read_reg RSP_EL0_ref) s"
  "traces_enabled (read_reg RTPIDR_EL0_ref) s"
  "traces_enabled (read_reg SP_EL0_ref) s"
  "traces_enabled (read_reg SP_EL1_ref) s"
  "traces_enabled (read_reg SP_EL2_ref) s"
  "traces_enabled (read_reg SP_EL3_ref) s"
  "traces_enabled (read_reg TPIDRRO_EL0_ref) s"
  "traces_enabled (read_reg TPIDR_EL0_ref) s"
  "traces_enabled (read_reg TPIDR_EL1_ref) s"
  "traces_enabled (read_reg TPIDR_EL2_ref) s"
  "traces_enabled (read_reg TPIDR_EL3_ref) s"
  "system_reg_access s \<or> ex_traces \<Longrightarrow> traces_enabled (read_reg VBAR_EL1_ref) s"
  "system_reg_access s \<or> ex_traces \<Longrightarrow> traces_enabled (read_reg VBAR_EL2_ref) s"
  "system_reg_access s \<or> ex_traces \<Longrightarrow> traces_enabled (read_reg VBAR_EL3_ref) s"
  "traces_enabled (read_reg R00_ref) s"
  "traces_enabled (read_reg R01_ref) s"
  "traces_enabled (read_reg R02_ref) s"
  "traces_enabled (read_reg R03_ref) s"
  "traces_enabled (read_reg R04_ref) s"
  "traces_enabled (read_reg R05_ref) s"
  "traces_enabled (read_reg R06_ref) s"
  "traces_enabled (read_reg R07_ref) s"
  "traces_enabled (read_reg R08_ref) s"
  "traces_enabled (read_reg R09_ref) s"
  "traces_enabled (read_reg R10_ref) s"
  "traces_enabled (read_reg R11_ref) s"
  "traces_enabled (read_reg R12_ref) s"
  "traces_enabled (read_reg R13_ref) s"
  "traces_enabled (read_reg R14_ref) s"
  "traces_enabled (read_reg R15_ref) s"
  "traces_enabled (read_reg R16_ref) s"
  "traces_enabled (read_reg R17_ref) s"
  "traces_enabled (read_reg R18_ref) s"
  "traces_enabled (read_reg R19_ref) s"
  "traces_enabled (read_reg R20_ref) s"
  "traces_enabled (read_reg R21_ref) s"
  "traces_enabled (read_reg R22_ref) s"
  "traces_enabled (read_reg R23_ref) s"
  "traces_enabled (read_reg R24_ref) s"
  "traces_enabled (read_reg R25_ref) s"
  "traces_enabled (read_reg R26_ref) s"
  "traces_enabled (read_reg R27_ref) s"
  "traces_enabled (read_reg R28_ref) s"
  "traces_enabled (read_reg R29_ref) s"
  "traces_enabled (read_reg R30_ref) s"
  by (intro traces_enabled_read_reg; auto simp: register_defs)+


lemmas non_cap_exp_traces_enabled[traces_enabledI] = non_cap_expI[THEN non_cap_exp_traces_enabledI]


lemma traces_enabled_BranchTo[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (BranchTo target branch_type) s"
  unfolding BranchTo_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_BranchToCapability[traces_enabledI]:
  assumes "target \<in> derivable_caps s"
  shows "traces_enabled (BranchToCapability target branch_type) s"
  unfolding BranchToCapability_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CELR_set[traces_enabledI]:
  assumes "value_name \<in> derivable_caps s"
  shows "traces_enabled (CELR_set el value_name) s"
  unfolding CELR_set_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CELR_set__1[traces_enabledI]:
  assumes "value_name \<in> derivable_caps s"
  shows "traces_enabled (CELR_set__1 value_name) s"
  unfolding CELR_set__1_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CVBAR_read[traces_enabledI]:
  assumes "{''VBAR_EL1'', ''VBAR_EL2'', ''VBAR_EL3''} \<subseteq> accessible_regs s \<or> ex_traces"
  shows "traces_enabled (CVBAR_read regime) s"
  unfolding CVBAR_read_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CVBAR_read__1[traces_enabledI]:
  assumes "{''VBAR_EL1'', ''VBAR_EL2'', ''VBAR_EL3''} \<subseteq> accessible_regs s \<or> ex_traces"
  shows "traces_enabled (CVBAR_read__1 arg0) s"
  unfolding CVBAR_read__1_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ELR_set[traces_enabledI]:
  "traces_enabled (ELR_set el value_name) s"
  unfolding ELR_set_def bind_assoc
  by (traces_enabledI)

lemma traces_enabled_ELR_set__1[traces_enabledI]:
  "traces_enabled (ELR_set__1 value_name) s"
  unfolding ELR_set__1_def bind_assoc
  by (traces_enabledI)

lemma traces_enabled_PCC_read[traces_enabledI]:
  "traces_enabled (PCC_read arg0) s"
  unfolding PCC_read_def bind_assoc
  by (traces_enabledI)

lemma traces_enabled_IsInRestricted[traces_enabledI]:
  "traces_enabled (IsInRestricted arg0) s"
  unfolding IsInRestricted_def bind_assoc
  by (traces_enabledI)

lemma traces_enabled_VBAR_read[traces_enabledI]:
  assumes "{''VBAR_EL1'', ''VBAR_EL2'', ''VBAR_EL3''} \<subseteq> accessible_regs s \<or> ex_traces"
  shows "traces_enabled (VBAR_read regime) s"
  unfolding VBAR_read_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_VBAR_read__1[traces_enabledI]:
  assumes "{''VBAR_EL1'', ''VBAR_EL2'', ''VBAR_EL3''} \<subseteq> accessible_regs s \<or> ex_traces"
  shows "traces_enabled (VBAR_read__1 arg0) s"
  unfolding VBAR_read__1_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_AArch64_TakeException[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (AArch64_TakeException target_el exception preferred_exception_return vect_offset__arg) s"
  by (rule AArch64_TakeException_raises_isa_ex[THEN exp_raises_ex_traces_enabled], unfold AArch64_TakeException_def bind_assoc, traces_enabledI assms: assms elim: CapSetValue_exception_target_enabled_branch_target)

lemma traces_enabled_Halt[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "system_reg_access s"
  shows "traces_enabled (Halt reason) s"
  unfolding Halt_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_AArch64_BreakpointException[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (AArch64_BreakpointException fault) s"
  unfolding AArch64_BreakpointException_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_AArch64_DataAbort[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (AArch64_DataAbort vaddress fault) s"
  unfolding AArch64_DataAbort_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_AArch64_InstructionAbort[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (AArch64_InstructionAbort vaddress fault) s"
  unfolding AArch64_InstructionAbort_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_AArch64_WatchpointException[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (AArch64_WatchpointException vaddress fault) s"
  unfolding AArch64_WatchpointException_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_AArch64_Abort[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (AArch64_Abort vaddress fault) s"
  unfolding AArch64_Abort_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_AArch64_CheckBreakpoint[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (AArch64_CheckBreakpoint vaddress size__arg) s"
  unfolding AArch64_CheckBreakpoint_def bind_assoc
  by (traces_enabledI assms: assms elim: Run_and_HaltOnBreakpointOrWatchpoint_system_reg_access)

lemma traces_enabled_AArch64_CheckWatchpoint[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (AArch64_CheckWatchpoint vaddress acctype iswrite size__arg) s"
  unfolding AArch64_CheckWatchpoint_def bind_assoc
  by (traces_enabledI assms: assms elim: Run_and_HaltOnBreakpointOrWatchpoint_system_reg_access)

lemma traces_enabled_AArch64_CheckDebug[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (AArch64_CheckDebug vaddress acctype iswrite size__arg) s"
  unfolding AArch64_CheckDebug_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_AArch64_TranslateAddressWithTag[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (AArch64_TranslateAddressWithTag vaddress acctype iswrite wasaligned size__arg iswritevalidcap) s"
  unfolding AArch64_TranslateAddressWithTag_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_AArch64_TranslateAddress[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (AArch64_TranslateAddress vaddress acctype iswrite wasaligned size__arg) s"
  unfolding AArch64_TranslateAddress_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_AArch64_MemSingle_read[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (AArch64_MemSingle_read address size__arg acctype wasaligned :: 'size_times_p8::len word M) s"
  unfolding AArch64_MemSingle_read_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CheckCapability[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CheckCapability c__arg address size__arg requested_perms acctype) s"
  unfolding CheckCapability_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_AArch64_CheckIllegalState[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (AArch64_CheckIllegalState arg0) s"
  unfolding AArch64_CheckIllegalState_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_AArch64_PCAlignmentFault[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (AArch64_PCAlignmentFault arg0) s"
  unfolding AArch64_PCAlignmentFault_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_AArch64_CheckPCAlignment[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (AArch64_CheckPCAlignment arg0) s"
  unfolding AArch64_CheckPCAlignment_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CheckPCCCapability[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CheckPCCCapability arg0) s"
  unfolding CheckPCCCapability_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_FetchNextInstr[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (FetchNextInstr arg0) s"
  unfolding FetchNextInstr_def bind_assoc
  by (traces_enabledI assms: assms)

end

context Morello_Fetch_Mem_Automaton
begin

lemmas non_cap_exp_traces_enabled[traces_enabledI] = non_cap_expI[THEN non_cap_exp_traces_enabledI]

lemmas non_mem_exp_traces_enabled[traces_enabledI] = non_mem_expI[THEN non_mem_exp_traces_enabledI]


lemma traces_enabled_AArch64_MemSingle_read[traces_enabledI]:
  assumes "translate_address (unat address) \<noteq> None \<longrightarrow> load_enabled s acctype (unat address) size__arg False"
  shows "traces_enabled (AArch64_MemSingle_read address size__arg acctype wasaligned :: 'size_times_p8::len word M) s"
  unfolding AArch64_MemSingle_read_def bind_assoc
  by (traces_enabledI assms: assms simp: exp_fails_if_then_else)

lemma traces_enabled_FetchNextInstr[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (FetchNextInstr arg0) s"
  unfolding FetchNextInstr_def CheckPCCCapability_def bind_assoc
  by (traces_enabledI assms: assms elim: CheckCapability_load_enabled intro: derivable_or_invokedI1)

end

end
