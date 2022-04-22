section \<open>Generated instruction monotonicity proofs\<close>

theory CHERI_Cap_Properties
imports CHERI_Lemmas
begin

context Morello_Instr_Write_Cap_Automaton
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


lemma traces_enabled_R_read[traces_enabledI]:
  "traces_enabled (R_read idx) s"
  unfolding R_read_def bind_assoc
  by (traces_enabledI)

lemma traces_enabled_R_set[traces_enabledI]:
  assumes "c__arg \<in> derivable_caps s"
  shows "traces_enabled (R_set idx c__arg) s"
  unfolding R_set_def bind_assoc
  by (traces_enabledI assms: assms)

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

lemma traces_enabled_AArch64_SystemAccessTrap[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (AArch64_SystemAccessTrap target_el ec) s"
  unfolding AArch64_SystemAccessTrap_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CapIsSystemAccessEnabled[traces_enabledI]:
  "traces_enabled (CapIsSystemAccessEnabled arg0) s"
  unfolding CapIsSystemAccessEnabled_def bind_assoc
  by (traces_enabledI)

lemma traces_enabled_ACTLR_EL1_SysRegRead_56bd4d0367c16236[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ACTLR_EL1_SysRegRead_56bd4d0367c16236 el op0 op1 CRn op2 CRm) s"
  unfolding ACTLR_EL1_SysRegRead_56bd4d0367c16236_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ACTLR_EL2_SysRegRead_ff23cef1b670b9c7[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ACTLR_EL2_SysRegRead_ff23cef1b670b9c7 el op0 op1 CRn op2 CRm) s"
  unfolding ACTLR_EL2_SysRegRead_ff23cef1b670b9c7_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ACTLR_EL3_SysRegRead_397e6c0342e2936b[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ACTLR_EL3_SysRegRead_397e6c0342e2936b el op0 op1 CRn op2 CRm) s"
  unfolding ACTLR_EL3_SysRegRead_397e6c0342e2936b_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_AFSR0_EL12_SysRegRead_2488de32a3f38621[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (AFSR0_EL12_SysRegRead_2488de32a3f38621 el op0 op1 CRn op2 CRm) s"
  unfolding AFSR0_EL12_SysRegRead_2488de32a3f38621_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_AFSR0_EL1_SysRegRead_80a4a0472e0b9142[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (AFSR0_EL1_SysRegRead_80a4a0472e0b9142 el op0 op1 CRn op2 CRm) s"
  unfolding AFSR0_EL1_SysRegRead_80a4a0472e0b9142_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_AFSR0_EL2_SysRegRead_07613e9c4b98061a[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (AFSR0_EL2_SysRegRead_07613e9c4b98061a el op0 op1 CRn op2 CRm) s"
  unfolding AFSR0_EL2_SysRegRead_07613e9c4b98061a_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_AFSR0_EL3_SysRegRead_d2e69d7912ca200c[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (AFSR0_EL3_SysRegRead_d2e69d7912ca200c el op0 op1 CRn op2 CRm) s"
  unfolding AFSR0_EL3_SysRegRead_d2e69d7912ca200c_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_AFSR1_EL12_SysRegRead_39bb62021df07ecc[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (AFSR1_EL12_SysRegRead_39bb62021df07ecc el op0 op1 CRn op2 CRm) s"
  unfolding AFSR1_EL12_SysRegRead_39bb62021df07ecc_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_AFSR1_EL1_SysRegRead_495927b72173c55f[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (AFSR1_EL1_SysRegRead_495927b72173c55f el op0 op1 CRn op2 CRm) s"
  unfolding AFSR1_EL1_SysRegRead_495927b72173c55f_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_AFSR1_EL2_SysRegRead_f7cb9a59387f268f[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (AFSR1_EL2_SysRegRead_f7cb9a59387f268f el op0 op1 CRn op2 CRm) s"
  unfolding AFSR1_EL2_SysRegRead_f7cb9a59387f268f_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_AFSR1_EL3_SysRegRead_a2ad736ad599f2b2[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (AFSR1_EL3_SysRegRead_a2ad736ad599f2b2 el op0 op1 CRn op2 CRm) s"
  unfolding AFSR1_EL3_SysRegRead_a2ad736ad599f2b2_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_AIDR_EL1_SysRegRead_74ea31b1dc6f5c6f[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (AIDR_EL1_SysRegRead_74ea31b1dc6f5c6f el op0 op1 CRn op2 CRm) s"
  unfolding AIDR_EL1_SysRegRead_74ea31b1dc6f5c6f_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_AMAIR_EL12_SysRegRead_87964a33cc1ad0ef[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (AMAIR_EL12_SysRegRead_87964a33cc1ad0ef el op0 op1 CRn op2 CRm) s"
  unfolding AMAIR_EL12_SysRegRead_87964a33cc1ad0ef_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_AMAIR_EL1_SysRegRead_82d01d3808e04ca3[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (AMAIR_EL1_SysRegRead_82d01d3808e04ca3 el op0 op1 CRn op2 CRm) s"
  unfolding AMAIR_EL1_SysRegRead_82d01d3808e04ca3_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_AMAIR_EL2_SysRegRead_3c316bb11b239640[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (AMAIR_EL2_SysRegRead_3c316bb11b239640 el op0 op1 CRn op2 CRm) s"
  unfolding AMAIR_EL2_SysRegRead_3c316bb11b239640_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_AMAIR_EL3_SysRegRead_b1547f511477c529[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (AMAIR_EL3_SysRegRead_b1547f511477c529 el op0 op1 CRn op2 CRm) s"
  unfolding AMAIR_EL3_SysRegRead_b1547f511477c529_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CCSIDR_EL1_SysRegRead_210f94b423761d0b[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CCSIDR_EL1_SysRegRead_210f94b423761d0b el op0 op1 CRn op2 CRm) s"
  unfolding CCSIDR_EL1_SysRegRead_210f94b423761d0b_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CCTLR_EL0_SysRegRead_3baa7e22d96a4ce4[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CCTLR_EL0_SysRegRead_3baa7e22d96a4ce4 el op0 op1 CRn op2 CRm) s"
  unfolding CCTLR_EL0_SysRegRead_3baa7e22d96a4ce4_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CCTLR_EL12_SysRegRead_e8b17aabd47dc7a1[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CCTLR_EL12_SysRegRead_e8b17aabd47dc7a1 el op0 op1 CRn op2 CRm) s"
  unfolding CCTLR_EL12_SysRegRead_e8b17aabd47dc7a1_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CCTLR_EL1_SysRegRead_de402a061eecb9b9[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CCTLR_EL1_SysRegRead_de402a061eecb9b9 el op0 op1 CRn op2 CRm) s"
  unfolding CCTLR_EL1_SysRegRead_de402a061eecb9b9_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CCTLR_EL2_SysRegRead_fca4364f27bb9f9b[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CCTLR_EL2_SysRegRead_fca4364f27bb9f9b el op0 op1 CRn op2 CRm) s"
  unfolding CCTLR_EL2_SysRegRead_fca4364f27bb9f9b_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CCTLR_EL3_SysRegRead_9121a22ebc361586[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CCTLR_EL3_SysRegRead_9121a22ebc361586 el op0 op1 CRn op2 CRm) s"
  unfolding CCTLR_EL3_SysRegRead_9121a22ebc361586_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CHCR_EL2_SysRegRead_7d3c39a46321f1a2[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CHCR_EL2_SysRegRead_7d3c39a46321f1a2 el op0 op1 CRn op2 CRm) s"
  unfolding CHCR_EL2_SysRegRead_7d3c39a46321f1a2_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CLIDR_EL1_SysRegRead_b403ddc99e97c3a8[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CLIDR_EL1_SysRegRead_b403ddc99e97c3a8 el op0 op1 CRn op2 CRm) s"
  unfolding CLIDR_EL1_SysRegRead_b403ddc99e97c3a8_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CNTFRQ_EL0_SysRegRead_891ca00adf0c3783[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CNTFRQ_EL0_SysRegRead_891ca00adf0c3783 el op0 op1 CRn op2 CRm) s"
  unfolding CNTFRQ_EL0_SysRegRead_891ca00adf0c3783_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CNTHCTL_EL2_SysRegRead_5f510d633361c720[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CNTHCTL_EL2_SysRegRead_5f510d633361c720 el op0 op1 CRn op2 CRm) s"
  unfolding CNTHCTL_EL2_SysRegRead_5f510d633361c720_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CNTHP_CTL_EL2_SysRegRead_7103e47839f2c66b[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CNTHP_CTL_EL2_SysRegRead_7103e47839f2c66b el op0 op1 CRn op2 CRm) s"
  unfolding CNTHP_CTL_EL2_SysRegRead_7103e47839f2c66b_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CNTHP_CVAL_EL2_SysRegRead_e25a0257128c640b[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CNTHP_CVAL_EL2_SysRegRead_e25a0257128c640b el op0 op1 CRn op2 CRm) s"
  unfolding CNTHP_CVAL_EL2_SysRegRead_e25a0257128c640b_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CNTHP_TVAL_EL2_SysRegRead_d110a1f1616c9f8f[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CNTHP_TVAL_EL2_SysRegRead_d110a1f1616c9f8f el op0 op1 CRn op2 CRm) s"
  unfolding CNTHP_TVAL_EL2_SysRegRead_d110a1f1616c9f8f_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CNTHV_CTL_EL2_SysRegRead_bc429f3d6b52b800[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CNTHV_CTL_EL2_SysRegRead_bc429f3d6b52b800 el op0 op1 CRn op2 CRm) s"
  unfolding CNTHV_CTL_EL2_SysRegRead_bc429f3d6b52b800_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CNTHV_CVAL_EL2_SysRegRead_2c78392b89702ca9[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CNTHV_CVAL_EL2_SysRegRead_2c78392b89702ca9 el op0 op1 CRn op2 CRm) s"
  unfolding CNTHV_CVAL_EL2_SysRegRead_2c78392b89702ca9_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CNTHV_TVAL_EL2_SysRegRead_2464c0e91db55a22[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CNTHV_TVAL_EL2_SysRegRead_2464c0e91db55a22 el op0 op1 CRn op2 CRm) s"
  unfolding CNTHV_TVAL_EL2_SysRegRead_2464c0e91db55a22_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CNTKCTL_EL12_SysRegRead_c23def3111264258[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CNTKCTL_EL12_SysRegRead_c23def3111264258 el op0 op1 CRn op2 CRm) s"
  unfolding CNTKCTL_EL12_SysRegRead_c23def3111264258_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CNTKCTL_EL1_SysRegRead_6a6cc900bc3c37df[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CNTKCTL_EL1_SysRegRead_6a6cc900bc3c37df el op0 op1 CRn op2 CRm) s"
  unfolding CNTKCTL_EL1_SysRegRead_6a6cc900bc3c37df_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CNTPCT_EL0_SysRegRead_579be4c9ef4e6824[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CNTPCT_EL0_SysRegRead_579be4c9ef4e6824 el op0 op1 CRn op2 CRm) s"
  unfolding CNTPCT_EL0_SysRegRead_579be4c9ef4e6824_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CNTPS_CTL_EL1_SysRegRead_e3bc6e5891147388[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CNTPS_CTL_EL1_SysRegRead_e3bc6e5891147388 el op0 op1 CRn op2 CRm) s"
  unfolding CNTPS_CTL_EL1_SysRegRead_e3bc6e5891147388_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CNTPS_CVAL_EL1_SysRegRead_3e364bd573c45cae[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CNTPS_CVAL_EL1_SysRegRead_3e364bd573c45cae el op0 op1 CRn op2 CRm) s"
  unfolding CNTPS_CVAL_EL1_SysRegRead_3e364bd573c45cae_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CNTPS_TVAL_EL1_SysRegRead_0784a7de0899eff0[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CNTPS_TVAL_EL1_SysRegRead_0784a7de0899eff0 el op0 op1 CRn op2 CRm) s"
  unfolding CNTPS_TVAL_EL1_SysRegRead_0784a7de0899eff0_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CNTP_CTL_EL02_SysRegRead_9d9930274ff7fc36[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CNTP_CTL_EL02_SysRegRead_9d9930274ff7fc36 el op0 op1 CRn op2 CRm) s"
  unfolding CNTP_CTL_EL02_SysRegRead_9d9930274ff7fc36_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CNTP_CTL_EL0_SysRegRead_47237e002d686ac6[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CNTP_CTL_EL0_SysRegRead_47237e002d686ac6 el op0 op1 CRn op2 CRm) s"
  unfolding CNTP_CTL_EL0_SysRegRead_47237e002d686ac6_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CNTP_CVAL_EL02_SysRegRead_8377305437cbebb4[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CNTP_CVAL_EL02_SysRegRead_8377305437cbebb4 el op0 op1 CRn op2 CRm) s"
  unfolding CNTP_CVAL_EL02_SysRegRead_8377305437cbebb4_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CNTP_CVAL_EL0_SysRegRead_4db28ae745612584[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CNTP_CVAL_EL0_SysRegRead_4db28ae745612584 el op0 op1 CRn op2 CRm) s"
  unfolding CNTP_CVAL_EL0_SysRegRead_4db28ae745612584_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CNTP_TVAL_EL02_SysRegRead_6539005e4eb68283[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CNTP_TVAL_EL02_SysRegRead_6539005e4eb68283 el op0 op1 CRn op2 CRm) s"
  unfolding CNTP_TVAL_EL02_SysRegRead_6539005e4eb68283_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CNTP_TVAL_EL0_SysRegRead_54cebb7fbc71b9db[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CNTP_TVAL_EL0_SysRegRead_54cebb7fbc71b9db el op0 op1 CRn op2 CRm) s"
  unfolding CNTP_TVAL_EL0_SysRegRead_54cebb7fbc71b9db_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CNTVCT_EL0_SysRegRead_cd7c8aebed2715e6[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CNTVCT_EL0_SysRegRead_cd7c8aebed2715e6 el op0 op1 CRn op2 CRm) s"
  unfolding CNTVCT_EL0_SysRegRead_cd7c8aebed2715e6_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CNTVOFF_EL2_SysRegRead_5ca7336b54f14c06[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CNTVOFF_EL2_SysRegRead_5ca7336b54f14c06 el op0 op1 CRn op2 CRm) s"
  unfolding CNTVOFF_EL2_SysRegRead_5ca7336b54f14c06_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CNTV_CTL_EL02_SysRegRead_4188a8e2bc5c07aa[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CNTV_CTL_EL02_SysRegRead_4188a8e2bc5c07aa el op0 op1 CRn op2 CRm) s"
  unfolding CNTV_CTL_EL02_SysRegRead_4188a8e2bc5c07aa_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CNTV_CTL_EL0_SysRegRead_bcb2d1b80bdb9c23[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CNTV_CTL_EL0_SysRegRead_bcb2d1b80bdb9c23 el op0 op1 CRn op2 CRm) s"
  unfolding CNTV_CTL_EL0_SysRegRead_bcb2d1b80bdb9c23_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CNTV_CVAL_EL02_SysRegRead_abd2b9f314cb85b2[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CNTV_CVAL_EL02_SysRegRead_abd2b9f314cb85b2 el op0 op1 CRn op2 CRm) s"
  unfolding CNTV_CVAL_EL02_SysRegRead_abd2b9f314cb85b2_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CNTV_CVAL_EL0_SysRegRead_54d5eb0bec99456f[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CNTV_CVAL_EL0_SysRegRead_54d5eb0bec99456f el op0 op1 CRn op2 CRm) s"
  unfolding CNTV_CVAL_EL0_SysRegRead_54d5eb0bec99456f_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CNTV_TVAL_EL02_SysRegRead_f904ccdf39aea128[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CNTV_TVAL_EL02_SysRegRead_f904ccdf39aea128 el op0 op1 CRn op2 CRm) s"
  unfolding CNTV_TVAL_EL02_SysRegRead_f904ccdf39aea128_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CNTV_TVAL_EL0_SysRegRead_919e73a694090e48[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CNTV_TVAL_EL0_SysRegRead_919e73a694090e48 el op0 op1 CRn op2 CRm) s"
  unfolding CNTV_TVAL_EL0_SysRegRead_919e73a694090e48_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CONTEXTIDR_EL12_SysRegRead_2aa676fc0cfd631b[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CONTEXTIDR_EL12_SysRegRead_2aa676fc0cfd631b el op0 op1 CRn op2 CRm) s"
  unfolding CONTEXTIDR_EL12_SysRegRead_2aa676fc0cfd631b_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CONTEXTIDR_EL1_SysRegRead_fa54232c55ea14e3[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CONTEXTIDR_EL1_SysRegRead_fa54232c55ea14e3 el op0 op1 CRn op2 CRm) s"
  unfolding CONTEXTIDR_EL1_SysRegRead_fa54232c55ea14e3_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CONTEXTIDR_EL2_SysRegRead_f7bf9114ce3113a6[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CONTEXTIDR_EL2_SysRegRead_f7bf9114ce3113a6 el op0 op1 CRn op2 CRm) s"
  unfolding CONTEXTIDR_EL2_SysRegRead_f7bf9114ce3113a6_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CPACR_EL12_SysRegRead_0f7867518c4e8e99[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CPACR_EL12_SysRegRead_0f7867518c4e8e99 el op0 op1 CRn op2 CRm) s"
  unfolding CPACR_EL12_SysRegRead_0f7867518c4e8e99_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CPACR_EL1_SysRegRead_63b8f196f3ebba22[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CPACR_EL1_SysRegRead_63b8f196f3ebba22 el op0 op1 CRn op2 CRm) s"
  unfolding CPACR_EL1_SysRegRead_63b8f196f3ebba22_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CPTR_EL2_SysRegRead_d80843789adc6a43[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CPTR_EL2_SysRegRead_d80843789adc6a43 el op0 op1 CRn op2 CRm) s"
  unfolding CPTR_EL2_SysRegRead_d80843789adc6a43_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CPTR_EL3_SysRegRead_33cb1e5ec3c99661[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CPTR_EL3_SysRegRead_33cb1e5ec3c99661 el op0 op1 CRn op2 CRm) s"
  unfolding CPTR_EL3_SysRegRead_33cb1e5ec3c99661_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CSCR_EL3_SysRegRead_3c6b19768f9cd209[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CSCR_EL3_SysRegRead_3c6b19768f9cd209 el op0 op1 CRn op2 CRm) s"
  unfolding CSCR_EL3_SysRegRead_3c6b19768f9cd209_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CSSELR_EL1_SysRegRead_102b4cddc07c9121[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CSSELR_EL1_SysRegRead_102b4cddc07c9121 el op0 op1 CRn op2 CRm) s"
  unfolding CSSELR_EL1_SysRegRead_102b4cddc07c9121_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CTR_EL0_SysRegRead_54ef8c769c3c6bba[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CTR_EL0_SysRegRead_54ef8c769c3c6bba el op0 op1 CRn op2 CRm) s"
  unfolding CTR_EL0_SysRegRead_54ef8c769c3c6bba_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_DACR32_EL2_SysRegRead_9571e2946627a596[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (DACR32_EL2_SysRegRead_9571e2946627a596 el op0 op1 CRn op2 CRm) s"
  unfolding DACR32_EL2_SysRegRead_9571e2946627a596_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_DAIF_SysRegRead_198f3b46fcf6c8f0[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (DAIF_SysRegRead_198f3b46fcf6c8f0 el op0 op1 CRn op2 CRm) s"
  unfolding DAIF_SysRegRead_198f3b46fcf6c8f0_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_DBGAUTHSTATUS_EL1_SysRegRead_6ade6e7a5265bcb7[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (DBGAUTHSTATUS_EL1_SysRegRead_6ade6e7a5265bcb7 el op0 op1 CRn op2 CRm) s"
  unfolding DBGAUTHSTATUS_EL1_SysRegRead_6ade6e7a5265bcb7_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_Halt[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "system_reg_access s"
  shows "traces_enabled (Halt reason) s"
  unfolding Halt_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_DBGBCR_EL1_SysRegRead_2d021994672d40d3[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (DBGBCR_EL1_SysRegRead_2d021994672d40d3 el op0 op1 CRn op2 CRm) s"
  unfolding DBGBCR_EL1_SysRegRead_2d021994672d40d3_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_DBGBVR_EL1_SysRegRead_dc4a8f61b400622f[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (DBGBVR_EL1_SysRegRead_dc4a8f61b400622f el op0 op1 CRn op2 CRm) s"
  unfolding DBGBVR_EL1_SysRegRead_dc4a8f61b400622f_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_DBGCLAIMCLR_EL1_SysRegRead_72ae03c1d5f667da[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (DBGCLAIMCLR_EL1_SysRegRead_72ae03c1d5f667da el op0 op1 CRn op2 CRm) s"
  unfolding DBGCLAIMCLR_EL1_SysRegRead_72ae03c1d5f667da_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_DBGCLAIMSET_EL1_SysRegRead_8557cf3b6272a9e8[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (DBGCLAIMSET_EL1_SysRegRead_8557cf3b6272a9e8 el op0 op1 CRn op2 CRm) s"
  unfolding DBGCLAIMSET_EL1_SysRegRead_8557cf3b6272a9e8_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_DBGDTRRX_EL0_SysRegRead_e7b48d8296f3b86b[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (DBGDTRRX_EL0_SysRegRead_e7b48d8296f3b86b el op0 op1 CRn op2 CRm) s"
  unfolding DBGDTRRX_EL0_SysRegRead_e7b48d8296f3b86b_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_DBGDTR_EL0_read__1[traces_enabledI]:
  assumes "{''CDBGDTR_EL0''} \<subseteq> accessible_regs s"
  shows "traces_enabled (DBGDTR_EL0_read__1 arg0) s"
  unfolding DBGDTR_EL0_read__1_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_DBGDTR_EL0_SysRegRead_537a006eb82c59aa[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (DBGDTR_EL0_SysRegRead_537a006eb82c59aa el op0 op1 CRn op2 CRm) s"
  unfolding DBGDTR_EL0_SysRegRead_537a006eb82c59aa_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_DBGPRCR_EL1_SysRegRead_6b19d62af9619a21[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (DBGPRCR_EL1_SysRegRead_6b19d62af9619a21 el op0 op1 CRn op2 CRm) s"
  unfolding DBGPRCR_EL1_SysRegRead_6b19d62af9619a21_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_DBGVCR32_EL2_SysRegRead_7986b2bdf8df010d[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (DBGVCR32_EL2_SysRegRead_7986b2bdf8df010d el op0 op1 CRn op2 CRm) s"
  unfolding DBGVCR32_EL2_SysRegRead_7986b2bdf8df010d_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_DBGWCR_EL1_SysRegRead_03139d052b544b2f[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (DBGWCR_EL1_SysRegRead_03139d052b544b2f el op0 op1 CRn op2 CRm) s"
  unfolding DBGWCR_EL1_SysRegRead_03139d052b544b2f_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_DBGWVR_EL1_SysRegRead_029de1005ef34888[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (DBGWVR_EL1_SysRegRead_029de1005ef34888 el op0 op1 CRn op2 CRm) s"
  unfolding DBGWVR_EL1_SysRegRead_029de1005ef34888_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_DISR_EL1_SysRegRead_d06ce25101dac895[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (DISR_EL1_SysRegRead_d06ce25101dac895 el op0 op1 CRn op2 CRm) s"
  unfolding DISR_EL1_SysRegRead_d06ce25101dac895_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_DLR_EL0_read[traces_enabledI]:
  assumes "{''CDLR_EL0''} \<subseteq> accessible_regs s"
  shows "traces_enabled (DLR_EL0_read arg0) s"
  unfolding DLR_EL0_read_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_DLR_EL0_SysRegRead_75b9821e3e84ec13[traces_enabledI]:
  "traces_enabled (DLR_EL0_SysRegRead_75b9821e3e84ec13 el op0 op1 CRn op2 CRm) s"
  unfolding DLR_EL0_SysRegRead_75b9821e3e84ec13_def bind_assoc
  by (traces_enabledI)

lemma traces_enabled_ELR_EL12_SysRegRead_e8215c0ae79859bb[traces_enabledI]:
  "traces_enabled (ELR_EL12_SysRegRead_e8215c0ae79859bb el op0 op1 CRn op2 CRm) s"
  unfolding ELR_EL12_SysRegRead_e8215c0ae79859bb_def bind_assoc
  by (traces_enabledI)

lemma traces_enabled_ELR_EL1_SysRegRead_0d3f1ad1483e96c2[traces_enabledI]:
  "traces_enabled (ELR_EL1_SysRegRead_0d3f1ad1483e96c2 el op0 op1 CRn op2 CRm) s"
  unfolding ELR_EL1_SysRegRead_0d3f1ad1483e96c2_def bind_assoc
  by (traces_enabledI)

lemma traces_enabled_ELR_EL2_SysRegRead_00b4dd4251404d91[traces_enabledI]:
  "traces_enabled (ELR_EL2_SysRegRead_00b4dd4251404d91 el op0 op1 CRn op2 CRm) s"
  unfolding ELR_EL2_SysRegRead_00b4dd4251404d91_def bind_assoc
  by (traces_enabledI)

lemma traces_enabled_ELR_EL3_SysRegRead_a7a7cd4e7e805396[traces_enabledI]:
  "traces_enabled (ELR_EL3_SysRegRead_a7a7cd4e7e805396 el op0 op1 CRn op2 CRm) s"
  unfolding ELR_EL3_SysRegRead_a7a7cd4e7e805396_def bind_assoc
  by (traces_enabledI)

lemma traces_enabled_ERRIDR_EL1_SysRegRead_41b56b8d34e51109[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ERRIDR_EL1_SysRegRead_41b56b8d34e51109 el op0 op1 CRn op2 CRm) s"
  unfolding ERRIDR_EL1_SysRegRead_41b56b8d34e51109_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ERRSELR_EL1_SysRegRead_1bcf942400e8d57f[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ERRSELR_EL1_SysRegRead_1bcf942400e8d57f el op0 op1 CRn op2 CRm) s"
  unfolding ERRSELR_EL1_SysRegRead_1bcf942400e8d57f_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ERXADDR_EL1_SysRegRead_7dea05bca757fc1d[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ERXADDR_EL1_SysRegRead_7dea05bca757fc1d el op0 op1 CRn op2 CRm) s"
  unfolding ERXADDR_EL1_SysRegRead_7dea05bca757fc1d_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ERXCTLR_EL1_SysRegRead_e46ed88d092db048[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ERXCTLR_EL1_SysRegRead_e46ed88d092db048 el op0 op1 CRn op2 CRm) s"
  unfolding ERXCTLR_EL1_SysRegRead_e46ed88d092db048_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ERXFR_EL1_SysRegRead_ed2a3c237ae67a43[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ERXFR_EL1_SysRegRead_ed2a3c237ae67a43 el op0 op1 CRn op2 CRm) s"
  unfolding ERXFR_EL1_SysRegRead_ed2a3c237ae67a43_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ERXMISC0_EL1_SysRegRead_a71a4de5f2444f19[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ERXMISC0_EL1_SysRegRead_a71a4de5f2444f19 el op0 op1 CRn op2 CRm) s"
  unfolding ERXMISC0_EL1_SysRegRead_a71a4de5f2444f19_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ERXMISC1_EL1_SysRegRead_bda613f8058b1fd8[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ERXMISC1_EL1_SysRegRead_bda613f8058b1fd8 el op0 op1 CRn op2 CRm) s"
  unfolding ERXMISC1_EL1_SysRegRead_bda613f8058b1fd8_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ERXSTATUS_EL1_SysRegRead_0ab2cfe6937b8b64[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ERXSTATUS_EL1_SysRegRead_0ab2cfe6937b8b64 el op0 op1 CRn op2 CRm) s"
  unfolding ERXSTATUS_EL1_SysRegRead_0ab2cfe6937b8b64_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ESR_EL12_SysRegRead_207d3805d256851a[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ESR_EL12_SysRegRead_207d3805d256851a el op0 op1 CRn op2 CRm) s"
  unfolding ESR_EL12_SysRegRead_207d3805d256851a_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ESR_EL1_SysRegRead_4894753806397624[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ESR_EL1_SysRegRead_4894753806397624 el op0 op1 CRn op2 CRm) s"
  unfolding ESR_EL1_SysRegRead_4894753806397624_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ESR_EL2_SysRegRead_e0558cb255261414[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ESR_EL2_SysRegRead_e0558cb255261414 el op0 op1 CRn op2 CRm) s"
  unfolding ESR_EL2_SysRegRead_e0558cb255261414_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ESR_EL3_SysRegRead_e0eabec0b099e366[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ESR_EL3_SysRegRead_e0eabec0b099e366 el op0 op1 CRn op2 CRm) s"
  unfolding ESR_EL3_SysRegRead_e0eabec0b099e366_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_FAR_EL12_SysRegRead_061fecffb03f9fc5[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (FAR_EL12_SysRegRead_061fecffb03f9fc5 el op0 op1 CRn op2 CRm) s"
  unfolding FAR_EL12_SysRegRead_061fecffb03f9fc5_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_FAR_EL1_SysRegRead_136ac0cc65bd5f9d[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (FAR_EL1_SysRegRead_136ac0cc65bd5f9d el op0 op1 CRn op2 CRm) s"
  unfolding FAR_EL1_SysRegRead_136ac0cc65bd5f9d_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_FAR_EL2_SysRegRead_d686d0a5577f0aae[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (FAR_EL2_SysRegRead_d686d0a5577f0aae el op0 op1 CRn op2 CRm) s"
  unfolding FAR_EL2_SysRegRead_d686d0a5577f0aae_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_FAR_EL3_SysRegRead_d63ec2764f8ffe40[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (FAR_EL3_SysRegRead_d63ec2764f8ffe40 el op0 op1 CRn op2 CRm) s"
  unfolding FAR_EL3_SysRegRead_d63ec2764f8ffe40_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_FPCR_SysRegRead_4176e216195c5686[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (FPCR_SysRegRead_4176e216195c5686 el op0 op1 CRn op2 CRm) s"
  unfolding FPCR_SysRegRead_4176e216195c5686_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_FPEXC32_EL2_SysRegRead_7ee503337da57806[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (FPEXC32_EL2_SysRegRead_7ee503337da57806 el op0 op1 CRn op2 CRm) s"
  unfolding FPEXC32_EL2_SysRegRead_7ee503337da57806_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_FPSR_SysRegRead_c1fde5c387acaca1[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (FPSR_SysRegRead_c1fde5c387acaca1 el op0 op1 CRn op2 CRm) s"
  unfolding FPSR_SysRegRead_c1fde5c387acaca1_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_HACR_EL2_SysRegRead_07bc3864e8ed8264[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (HACR_EL2_SysRegRead_07bc3864e8ed8264 el op0 op1 CRn op2 CRm) s"
  unfolding HACR_EL2_SysRegRead_07bc3864e8ed8264_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_HCR_EL2_SysRegRead_f76ecfdc85c5ff7c[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (HCR_EL2_SysRegRead_f76ecfdc85c5ff7c el op0 op1 CRn op2 CRm) s"
  unfolding HCR_EL2_SysRegRead_f76ecfdc85c5ff7c_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_HPFAR_EL2_SysRegRead_4c322cee424dff18[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (HPFAR_EL2_SysRegRead_4c322cee424dff18 el op0 op1 CRn op2 CRm) s"
  unfolding HPFAR_EL2_SysRegRead_4c322cee424dff18_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_HSTR_EL2_SysRegRead_680380b9028cf399[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (HSTR_EL2_SysRegRead_680380b9028cf399 el op0 op1 CRn op2 CRm) s"
  unfolding HSTR_EL2_SysRegRead_680380b9028cf399_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ICC_AP0R_EL1_SysRegRead_cac9b22dc3786a15[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ICC_AP0R_EL1_SysRegRead_cac9b22dc3786a15 el op0 op1 CRn op2 CRm) s"
  unfolding ICC_AP0R_EL1_SysRegRead_cac9b22dc3786a15_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ICC_AP1R_EL1_SysRegRead_4127418c67790ba3[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ICC_AP1R_EL1_SysRegRead_4127418c67790ba3 el op0 op1 CRn op2 CRm) s"
  unfolding ICC_AP1R_EL1_SysRegRead_4127418c67790ba3_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ICC_BPR0_EL1_SysRegRead_6ada10a9051248c2[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ICC_BPR0_EL1_SysRegRead_6ada10a9051248c2 el op0 op1 CRn op2 CRm) s"
  unfolding ICC_BPR0_EL1_SysRegRead_6ada10a9051248c2_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ICC_BPR1_EL1_SysRegRead_c56bf88f1b4aee37[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ICC_BPR1_EL1_SysRegRead_c56bf88f1b4aee37 el op0 op1 CRn op2 CRm) s"
  unfolding ICC_BPR1_EL1_SysRegRead_c56bf88f1b4aee37_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ICC_CTLR_EL1_SysRegRead_5754830bf787a1e2[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ICC_CTLR_EL1_SysRegRead_5754830bf787a1e2 el op0 op1 CRn op2 CRm) s"
  unfolding ICC_CTLR_EL1_SysRegRead_5754830bf787a1e2_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ICC_CTLR_EL3_SysRegRead_aba1771445e9d51b[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ICC_CTLR_EL3_SysRegRead_aba1771445e9d51b el op0 op1 CRn op2 CRm) s"
  unfolding ICC_CTLR_EL3_SysRegRead_aba1771445e9d51b_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ICC_HPPIR0_EL1_SysRegRead_221f9a6f32464de4[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ICC_HPPIR0_EL1_SysRegRead_221f9a6f32464de4 el op0 op1 CRn op2 CRm) s"
  unfolding ICC_HPPIR0_EL1_SysRegRead_221f9a6f32464de4_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ICC_HPPIR1_EL1_SysRegRead_88ed0889f7d5a37a[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ICC_HPPIR1_EL1_SysRegRead_88ed0889f7d5a37a el op0 op1 CRn op2 CRm) s"
  unfolding ICC_HPPIR1_EL1_SysRegRead_88ed0889f7d5a37a_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ICC_IAR0_EL1_SysRegRead_dcfaf70befc09037[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ICC_IAR0_EL1_SysRegRead_dcfaf70befc09037 el op0 op1 CRn op2 CRm) s"
  unfolding ICC_IAR0_EL1_SysRegRead_dcfaf70befc09037_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ICC_IAR1_EL1_SysRegRead_9f370ba68fd3e44f[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ICC_IAR1_EL1_SysRegRead_9f370ba68fd3e44f el op0 op1 CRn op2 CRm) s"
  unfolding ICC_IAR1_EL1_SysRegRead_9f370ba68fd3e44f_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ICC_IGRPEN0_EL1_SysRegRead_e575448f3c7e7a94[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ICC_IGRPEN0_EL1_SysRegRead_e575448f3c7e7a94 el op0 op1 CRn op2 CRm) s"
  unfolding ICC_IGRPEN0_EL1_SysRegRead_e575448f3c7e7a94_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ICC_IGRPEN1_EL1_SysRegRead_3cfd0733ef9b6efa[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ICC_IGRPEN1_EL1_SysRegRead_3cfd0733ef9b6efa el op0 op1 CRn op2 CRm) s"
  unfolding ICC_IGRPEN1_EL1_SysRegRead_3cfd0733ef9b6efa_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ICC_IGRPEN1_EL3_SysRegRead_d192d252016b4c8d[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ICC_IGRPEN1_EL3_SysRegRead_d192d252016b4c8d el op0 op1 CRn op2 CRm) s"
  unfolding ICC_IGRPEN1_EL3_SysRegRead_d192d252016b4c8d_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ICC_PMR_EL1_SysRegRead_4ab2c9427488fbf4[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ICC_PMR_EL1_SysRegRead_4ab2c9427488fbf4 el op0 op1 CRn op2 CRm) s"
  unfolding ICC_PMR_EL1_SysRegRead_4ab2c9427488fbf4_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ICC_RPR_EL1_SysRegRead_bea9edc41b26aab0[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ICC_RPR_EL1_SysRegRead_bea9edc41b26aab0 el op0 op1 CRn op2 CRm) s"
  unfolding ICC_RPR_EL1_SysRegRead_bea9edc41b26aab0_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ICC_SRE_EL1_SysRegRead_7cf0aa9fc619dea4[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ICC_SRE_EL1_SysRegRead_7cf0aa9fc619dea4 el op0 op1 CRn op2 CRm) s"
  unfolding ICC_SRE_EL1_SysRegRead_7cf0aa9fc619dea4_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ICC_SRE_EL2_SysRegRead_35c9349812c986fe[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ICC_SRE_EL2_SysRegRead_35c9349812c986fe el op0 op1 CRn op2 CRm) s"
  unfolding ICC_SRE_EL2_SysRegRead_35c9349812c986fe_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ICC_SRE_EL3_SysRegRead_c7d421022a5f589d[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ICC_SRE_EL3_SysRegRead_c7d421022a5f589d el op0 op1 CRn op2 CRm) s"
  unfolding ICC_SRE_EL3_SysRegRead_c7d421022a5f589d_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ICH_AP0R_EL2_SysRegRead_a38114229330a389[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ICH_AP0R_EL2_SysRegRead_a38114229330a389 el op0 op1 CRn op2 CRm) s"
  unfolding ICH_AP0R_EL2_SysRegRead_a38114229330a389_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ICH_AP1R_EL2_SysRegRead_3ef1256520a6f18e[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ICH_AP1R_EL2_SysRegRead_3ef1256520a6f18e el op0 op1 CRn op2 CRm) s"
  unfolding ICH_AP1R_EL2_SysRegRead_3ef1256520a6f18e_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ICH_EISR_EL2_SysRegRead_a45d99ec0ef64804[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ICH_EISR_EL2_SysRegRead_a45d99ec0ef64804 el op0 op1 CRn op2 CRm) s"
  unfolding ICH_EISR_EL2_SysRegRead_a45d99ec0ef64804_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ICH_ELRSR_EL2_SysRegRead_93859a236e9efe6d[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ICH_ELRSR_EL2_SysRegRead_93859a236e9efe6d el op0 op1 CRn op2 CRm) s"
  unfolding ICH_ELRSR_EL2_SysRegRead_93859a236e9efe6d_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ICH_HCR_EL2_SysRegRead_bd436f3e91661e3b[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ICH_HCR_EL2_SysRegRead_bd436f3e91661e3b el op0 op1 CRn op2 CRm) s"
  unfolding ICH_HCR_EL2_SysRegRead_bd436f3e91661e3b_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ICH_LR_EL2_SysRegRead_f9d8d38c7064e389[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ICH_LR_EL2_SysRegRead_f9d8d38c7064e389 el op0 op1 CRn op2 CRm) s"
  unfolding ICH_LR_EL2_SysRegRead_f9d8d38c7064e389_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ICH_MISR_EL2_SysRegRead_4e46f86d49bd21cd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ICH_MISR_EL2_SysRegRead_4e46f86d49bd21cd el op0 op1 CRn op2 CRm) s"
  unfolding ICH_MISR_EL2_SysRegRead_4e46f86d49bd21cd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ICH_VMCR_EL2_SysRegRead_3c019711ec735507[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ICH_VMCR_EL2_SysRegRead_3c019711ec735507 el op0 op1 CRn op2 CRm) s"
  unfolding ICH_VMCR_EL2_SysRegRead_3c019711ec735507_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ICH_VTR_EL2_SysRegRead_2ed82d00af03b344[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ICH_VTR_EL2_SysRegRead_2ed82d00af03b344 el op0 op1 CRn op2 CRm) s"
  unfolding ICH_VTR_EL2_SysRegRead_2ed82d00af03b344_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ID_AA64AFR0_EL1_SysRegRead_325547f3ac10431a[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ID_AA64AFR0_EL1_SysRegRead_325547f3ac10431a el op0 op1 CRn op2 CRm) s"
  unfolding ID_AA64AFR0_EL1_SysRegRead_325547f3ac10431a_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ID_AA64AFR1_EL1_SysRegRead_99b67b76121ee706[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ID_AA64AFR1_EL1_SysRegRead_99b67b76121ee706 el op0 op1 CRn op2 CRm) s"
  unfolding ID_AA64AFR1_EL1_SysRegRead_99b67b76121ee706_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ID_AA64DFR0_EL1_SysRegRead_c3e6b049dd70bbab[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ID_AA64DFR0_EL1_SysRegRead_c3e6b049dd70bbab el op0 op1 CRn op2 CRm) s"
  unfolding ID_AA64DFR0_EL1_SysRegRead_c3e6b049dd70bbab_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ID_AA64DFR1_EL1_SysRegRead_2f066031859d7035[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ID_AA64DFR1_EL1_SysRegRead_2f066031859d7035 el op0 op1 CRn op2 CRm) s"
  unfolding ID_AA64DFR1_EL1_SysRegRead_2f066031859d7035_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ID_AA64ISAR0_EL1_SysRegRead_d35f255c04eaab0f[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ID_AA64ISAR0_EL1_SysRegRead_d35f255c04eaab0f el op0 op1 CRn op2 CRm) s"
  unfolding ID_AA64ISAR0_EL1_SysRegRead_d35f255c04eaab0f_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ID_AA64ISAR1_EL1_SysRegRead_1132f371c4707f61[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ID_AA64ISAR1_EL1_SysRegRead_1132f371c4707f61 el op0 op1 CRn op2 CRm) s"
  unfolding ID_AA64ISAR1_EL1_SysRegRead_1132f371c4707f61_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ID_AA64MMFR0_EL1_SysRegRead_836c46ff67ac3f3d[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ID_AA64MMFR0_EL1_SysRegRead_836c46ff67ac3f3d el op0 op1 CRn op2 CRm) s"
  unfolding ID_AA64MMFR0_EL1_SysRegRead_836c46ff67ac3f3d_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ID_AA64MMFR1_EL1_SysRegRead_3abbf4d2af8dd3be[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ID_AA64MMFR1_EL1_SysRegRead_3abbf4d2af8dd3be el op0 op1 CRn op2 CRm) s"
  unfolding ID_AA64MMFR1_EL1_SysRegRead_3abbf4d2af8dd3be_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ID_AA64MMFR2_EL1_SysRegRead_1443648da3ca79dd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ID_AA64MMFR2_EL1_SysRegRead_1443648da3ca79dd el op0 op1 CRn op2 CRm) s"
  unfolding ID_AA64MMFR2_EL1_SysRegRead_1443648da3ca79dd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ID_AA64PFR0_EL1_SysRegRead_fe78f914579c8717[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ID_AA64PFR0_EL1_SysRegRead_fe78f914579c8717 el op0 op1 CRn op2 CRm) s"
  unfolding ID_AA64PFR0_EL1_SysRegRead_fe78f914579c8717_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ID_AA64PFR1_EL1_SysRegRead_3be470f3d1bff138[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ID_AA64PFR1_EL1_SysRegRead_3be470f3d1bff138 el op0 op1 CRn op2 CRm) s"
  unfolding ID_AA64PFR1_EL1_SysRegRead_3be470f3d1bff138_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ID_AA64ZFR0_EL1_SysRegRead_70425f5143f66c9f[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ID_AA64ZFR0_EL1_SysRegRead_70425f5143f66c9f el op0 op1 CRn op2 CRm) s"
  unfolding ID_AA64ZFR0_EL1_SysRegRead_70425f5143f66c9f_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ID_AFR0_EL1_SysRegRead_019e5ec822653217[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ID_AFR0_EL1_SysRegRead_019e5ec822653217 el op0 op1 CRn op2 CRm) s"
  unfolding ID_AFR0_EL1_SysRegRead_019e5ec822653217_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ID_DFR0_EL1_SysRegRead_12146217191b4fee[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ID_DFR0_EL1_SysRegRead_12146217191b4fee el op0 op1 CRn op2 CRm) s"
  unfolding ID_DFR0_EL1_SysRegRead_12146217191b4fee_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ID_ISAR0_EL1_SysRegRead_4e2f04c3a26dddb3[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ID_ISAR0_EL1_SysRegRead_4e2f04c3a26dddb3 el op0 op1 CRn op2 CRm) s"
  unfolding ID_ISAR0_EL1_SysRegRead_4e2f04c3a26dddb3_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ID_ISAR1_EL1_SysRegRead_2f4500748023e22b[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ID_ISAR1_EL1_SysRegRead_2f4500748023e22b el op0 op1 CRn op2 CRm) s"
  unfolding ID_ISAR1_EL1_SysRegRead_2f4500748023e22b_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ID_ISAR2_EL1_SysRegRead_1e8edaee6a0e9ef9[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ID_ISAR2_EL1_SysRegRead_1e8edaee6a0e9ef9 el op0 op1 CRn op2 CRm) s"
  unfolding ID_ISAR2_EL1_SysRegRead_1e8edaee6a0e9ef9_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ID_ISAR3_EL1_SysRegRead_cf9a1aae39d73bdd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ID_ISAR3_EL1_SysRegRead_cf9a1aae39d73bdd el op0 op1 CRn op2 CRm) s"
  unfolding ID_ISAR3_EL1_SysRegRead_cf9a1aae39d73bdd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ID_ISAR4_EL1_SysRegRead_9bffd9dcf4dd4ef4[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ID_ISAR4_EL1_SysRegRead_9bffd9dcf4dd4ef4 el op0 op1 CRn op2 CRm) s"
  unfolding ID_ISAR4_EL1_SysRegRead_9bffd9dcf4dd4ef4_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ID_ISAR5_EL1_SysRegRead_f70928ed2f55c1f0[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ID_ISAR5_EL1_SysRegRead_f70928ed2f55c1f0 el op0 op1 CRn op2 CRm) s"
  unfolding ID_ISAR5_EL1_SysRegRead_f70928ed2f55c1f0_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ID_ISAR6_EL1_SysRegRead_6ce3605912a2db6d[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ID_ISAR6_EL1_SysRegRead_6ce3605912a2db6d el op0 op1 CRn op2 CRm) s"
  unfolding ID_ISAR6_EL1_SysRegRead_6ce3605912a2db6d_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ID_MMFR0_EL1_SysRegRead_b31c5faa39841084[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ID_MMFR0_EL1_SysRegRead_b31c5faa39841084 el op0 op1 CRn op2 CRm) s"
  unfolding ID_MMFR0_EL1_SysRegRead_b31c5faa39841084_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ID_MMFR1_EL1_SysRegRead_b0f4bc0d71c9af14[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ID_MMFR1_EL1_SysRegRead_b0f4bc0d71c9af14 el op0 op1 CRn op2 CRm) s"
  unfolding ID_MMFR1_EL1_SysRegRead_b0f4bc0d71c9af14_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ID_MMFR2_EL1_SysRegRead_b60501193094f759[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ID_MMFR2_EL1_SysRegRead_b60501193094f759 el op0 op1 CRn op2 CRm) s"
  unfolding ID_MMFR2_EL1_SysRegRead_b60501193094f759_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ID_MMFR3_EL1_SysRegRead_dc45af19c356c392[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ID_MMFR3_EL1_SysRegRead_dc45af19c356c392 el op0 op1 CRn op2 CRm) s"
  unfolding ID_MMFR3_EL1_SysRegRead_dc45af19c356c392_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ID_MMFR4_EL1_SysRegRead_237ae4b6fb487f3e[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ID_MMFR4_EL1_SysRegRead_237ae4b6fb487f3e el op0 op1 CRn op2 CRm) s"
  unfolding ID_MMFR4_EL1_SysRegRead_237ae4b6fb487f3e_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ID_MMFR5_EL1_SysRegRead_00dc6140c3593f6a[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ID_MMFR5_EL1_SysRegRead_00dc6140c3593f6a el op0 op1 CRn op2 CRm) s"
  unfolding ID_MMFR5_EL1_SysRegRead_00dc6140c3593f6a_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ID_PFR0_EL1_SysRegRead_ab73eb91d66cfece[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ID_PFR0_EL1_SysRegRead_ab73eb91d66cfece el op0 op1 CRn op2 CRm) s"
  unfolding ID_PFR0_EL1_SysRegRead_ab73eb91d66cfece_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ID_PFR1_EL1_SysRegRead_264075958e26856b[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ID_PFR1_EL1_SysRegRead_264075958e26856b el op0 op1 CRn op2 CRm) s"
  unfolding ID_PFR1_EL1_SysRegRead_264075958e26856b_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ID_PFR2_EL1_SysRegRead_8561b575e8dfcee0[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ID_PFR2_EL1_SysRegRead_8561b575e8dfcee0 el op0 op1 CRn op2 CRm) s"
  unfolding ID_PFR2_EL1_SysRegRead_8561b575e8dfcee0_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_IFSR32_EL2_SysRegRead_3b41290786c143ba[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (IFSR32_EL2_SysRegRead_3b41290786c143ba el op0 op1 CRn op2 CRm) s"
  unfolding IFSR32_EL2_SysRegRead_3b41290786c143ba_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ISR_EL1_SysRegRead_41b7dbf26b89e726[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ISR_EL1_SysRegRead_41b7dbf26b89e726 el op0 op1 CRn op2 CRm) s"
  unfolding ISR_EL1_SysRegRead_41b7dbf26b89e726_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_LORC_EL1_SysRegRead_0067e90ee116c26f[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (LORC_EL1_SysRegRead_0067e90ee116c26f el op0 op1 CRn op2 CRm) s"
  unfolding LORC_EL1_SysRegRead_0067e90ee116c26f_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_LOREA_EL1_SysRegRead_ec495c3c15ed4dbe[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (LOREA_EL1_SysRegRead_ec495c3c15ed4dbe el op0 op1 CRn op2 CRm) s"
  unfolding LOREA_EL1_SysRegRead_ec495c3c15ed4dbe_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_LORID_EL1_SysRegRead_a063108cc96d4baa[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (LORID_EL1_SysRegRead_a063108cc96d4baa el op0 op1 CRn op2 CRm) s"
  unfolding LORID_EL1_SysRegRead_a063108cc96d4baa_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_LORN_EL1_SysRegRead_da981b495b21c400[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (LORN_EL1_SysRegRead_da981b495b21c400 el op0 op1 CRn op2 CRm) s"
  unfolding LORN_EL1_SysRegRead_da981b495b21c400_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_LORSA_EL1_SysRegRead_cdc08dda4115abc7[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (LORSA_EL1_SysRegRead_cdc08dda4115abc7 el op0 op1 CRn op2 CRm) s"
  unfolding LORSA_EL1_SysRegRead_cdc08dda4115abc7_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_MAIR_EL12_SysRegRead_ac3327848e47dda6[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (MAIR_EL12_SysRegRead_ac3327848e47dda6 el op0 op1 CRn op2 CRm) s"
  unfolding MAIR_EL12_SysRegRead_ac3327848e47dda6_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_MAIR_EL1_SysRegRead_ee00b1441fc4a50d[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (MAIR_EL1_SysRegRead_ee00b1441fc4a50d el op0 op1 CRn op2 CRm) s"
  unfolding MAIR_EL1_SysRegRead_ee00b1441fc4a50d_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_MAIR_EL2_SysRegRead_66c03f7cb594c1bd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (MAIR_EL2_SysRegRead_66c03f7cb594c1bd el op0 op1 CRn op2 CRm) s"
  unfolding MAIR_EL2_SysRegRead_66c03f7cb594c1bd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_MAIR_EL3_SysRegRead_0eb4af28a4f9b45a[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (MAIR_EL3_SysRegRead_0eb4af28a4f9b45a el op0 op1 CRn op2 CRm) s"
  unfolding MAIR_EL3_SysRegRead_0eb4af28a4f9b45a_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_MDCCINT_EL1_SysRegRead_12f1a0397d5a3729[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (MDCCINT_EL1_SysRegRead_12f1a0397d5a3729 el op0 op1 CRn op2 CRm) s"
  unfolding MDCCINT_EL1_SysRegRead_12f1a0397d5a3729_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_MDCCSR_EL0_SysRegRead_1ca0d9105cd616c5[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (MDCCSR_EL0_SysRegRead_1ca0d9105cd616c5 el op0 op1 CRn op2 CRm) s"
  unfolding MDCCSR_EL0_SysRegRead_1ca0d9105cd616c5_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_MDCR_EL2_SysRegRead_f2181c815a998208[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (MDCR_EL2_SysRegRead_f2181c815a998208 el op0 op1 CRn op2 CRm) s"
  unfolding MDCR_EL2_SysRegRead_f2181c815a998208_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_MDCR_EL3_SysRegRead_229d5ee95c6e9850[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (MDCR_EL3_SysRegRead_229d5ee95c6e9850 el op0 op1 CRn op2 CRm) s"
  unfolding MDCR_EL3_SysRegRead_229d5ee95c6e9850_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_MDRAR_EL1_SysRegRead_4c6f0d270d3fe56e[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (MDRAR_EL1_SysRegRead_4c6f0d270d3fe56e el op0 op1 CRn op2 CRm) s"
  unfolding MDRAR_EL1_SysRegRead_4c6f0d270d3fe56e_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_MDSCR_EL1_SysRegRead_5184636ced539526[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (MDSCR_EL1_SysRegRead_5184636ced539526 el op0 op1 CRn op2 CRm) s"
  unfolding MDSCR_EL1_SysRegRead_5184636ced539526_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_MIDR_EL1_SysRegRead_d49cc5f604ad167e[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (MIDR_EL1_SysRegRead_d49cc5f604ad167e el op0 op1 CRn op2 CRm) s"
  unfolding MIDR_EL1_SysRegRead_d49cc5f604ad167e_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_MPAM0_EL1_SysRegRead_87af318fd5c9f9f7[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (MPAM0_EL1_SysRegRead_87af318fd5c9f9f7 el op0 op1 CRn op2 CRm) s"
  unfolding MPAM0_EL1_SysRegRead_87af318fd5c9f9f7_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_MPAM1_EL12_SysRegRead_229a253b730e26d9[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (MPAM1_EL12_SysRegRead_229a253b730e26d9 el op0 op1 CRn op2 CRm) s"
  unfolding MPAM1_EL12_SysRegRead_229a253b730e26d9_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_MPAM1_EL1_SysRegRead_770ea23b87b18d99[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (MPAM1_EL1_SysRegRead_770ea23b87b18d99 el op0 op1 CRn op2 CRm) s"
  unfolding MPAM1_EL1_SysRegRead_770ea23b87b18d99_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_MPAM2_EL2_SysRegRead_10b60646fb381bea[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (MPAM2_EL2_SysRegRead_10b60646fb381bea el op0 op1 CRn op2 CRm) s"
  unfolding MPAM2_EL2_SysRegRead_10b60646fb381bea_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_MPAM3_EL3_SysRegRead_989f38b07d8b4265[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (MPAM3_EL3_SysRegRead_989f38b07d8b4265 el op0 op1 CRn op2 CRm) s"
  unfolding MPAM3_EL3_SysRegRead_989f38b07d8b4265_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_MPAMHCR_EL2_SysRegRead_6ee5f61be808e32e[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (MPAMHCR_EL2_SysRegRead_6ee5f61be808e32e el op0 op1 CRn op2 CRm) s"
  unfolding MPAMHCR_EL2_SysRegRead_6ee5f61be808e32e_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_MPAMIDR_EL1_SysRegRead_df4c57d831354b3c[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (MPAMIDR_EL1_SysRegRead_df4c57d831354b3c el op0 op1 CRn op2 CRm) s"
  unfolding MPAMIDR_EL1_SysRegRead_df4c57d831354b3c_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_MPAMVPM0_EL2_SysRegRead_d878a15f2ea1751d[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (MPAMVPM0_EL2_SysRegRead_d878a15f2ea1751d el op0 op1 CRn op2 CRm) s"
  unfolding MPAMVPM0_EL2_SysRegRead_d878a15f2ea1751d_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_MPAMVPM1_EL2_SysRegRead_78ba55a3ef5fc5ba[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (MPAMVPM1_EL2_SysRegRead_78ba55a3ef5fc5ba el op0 op1 CRn op2 CRm) s"
  unfolding MPAMVPM1_EL2_SysRegRead_78ba55a3ef5fc5ba_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_MPAMVPM2_EL2_SysRegRead_590d1577b5eb780d[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (MPAMVPM2_EL2_SysRegRead_590d1577b5eb780d el op0 op1 CRn op2 CRm) s"
  unfolding MPAMVPM2_EL2_SysRegRead_590d1577b5eb780d_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_MPAMVPM3_EL2_SysRegRead_3d93a30deb34ea81[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (MPAMVPM3_EL2_SysRegRead_3d93a30deb34ea81 el op0 op1 CRn op2 CRm) s"
  unfolding MPAMVPM3_EL2_SysRegRead_3d93a30deb34ea81_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_MPAMVPM4_EL2_SysRegRead_c4fa65dba541d8f3[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (MPAMVPM4_EL2_SysRegRead_c4fa65dba541d8f3 el op0 op1 CRn op2 CRm) s"
  unfolding MPAMVPM4_EL2_SysRegRead_c4fa65dba541d8f3_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_MPAMVPM5_EL2_SysRegRead_0f596cf6a35cf124[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (MPAMVPM5_EL2_SysRegRead_0f596cf6a35cf124 el op0 op1 CRn op2 CRm) s"
  unfolding MPAMVPM5_EL2_SysRegRead_0f596cf6a35cf124_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_MPAMVPM6_EL2_SysRegRead_c93ffeb6ea409c71[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (MPAMVPM6_EL2_SysRegRead_c93ffeb6ea409c71 el op0 op1 CRn op2 CRm) s"
  unfolding MPAMVPM6_EL2_SysRegRead_c93ffeb6ea409c71_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_MPAMVPM7_EL2_SysRegRead_ef19c89f1fa31f3e[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (MPAMVPM7_EL2_SysRegRead_ef19c89f1fa31f3e el op0 op1 CRn op2 CRm) s"
  unfolding MPAMVPM7_EL2_SysRegRead_ef19c89f1fa31f3e_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_MPAMVPMV_EL2_SysRegRead_6de5731367257b91[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (MPAMVPMV_EL2_SysRegRead_6de5731367257b91 el op0 op1 CRn op2 CRm) s"
  unfolding MPAMVPMV_EL2_SysRegRead_6de5731367257b91_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_MPIDR_EL1_SysRegRead_1a44c237fc7e90a0[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (MPIDR_EL1_SysRegRead_1a44c237fc7e90a0 el op0 op1 CRn op2 CRm) s"
  unfolding MPIDR_EL1_SysRegRead_1a44c237fc7e90a0_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_MVFR0_EL1_SysRegRead_982614cb681cfbbf[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (MVFR0_EL1_SysRegRead_982614cb681cfbbf el op0 op1 CRn op2 CRm) s"
  unfolding MVFR0_EL1_SysRegRead_982614cb681cfbbf_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_MVFR1_EL1_SysRegRead_1964a95566ab0fcd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (MVFR1_EL1_SysRegRead_1964a95566ab0fcd el op0 op1 CRn op2 CRm) s"
  unfolding MVFR1_EL1_SysRegRead_1964a95566ab0fcd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_MVFR2_EL1_SysRegRead_f6245ffc535897f2[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (MVFR2_EL1_SysRegRead_f6245ffc535897f2 el op0 op1 CRn op2 CRm) s"
  unfolding MVFR2_EL1_SysRegRead_f6245ffc535897f2_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_OSDLR_EL1_SysRegRead_4cb80c508c4cced4[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (OSDLR_EL1_SysRegRead_4cb80c508c4cced4 el op0 op1 CRn op2 CRm) s"
  unfolding OSDLR_EL1_SysRegRead_4cb80c508c4cced4_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_OSDTRRX_EL1_SysRegRead_d4eb07360bc69d28[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (OSDTRRX_EL1_SysRegRead_d4eb07360bc69d28 el op0 op1 CRn op2 CRm) s"
  unfolding OSDTRRX_EL1_SysRegRead_d4eb07360bc69d28_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_OSDTRTX_EL1_SysRegRead_008c22058272684f[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (OSDTRTX_EL1_SysRegRead_008c22058272684f el op0 op1 CRn op2 CRm) s"
  unfolding OSDTRTX_EL1_SysRegRead_008c22058272684f_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_OSECCR_EL1_SysRegRead_264ab12a32fecc30[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (OSECCR_EL1_SysRegRead_264ab12a32fecc30 el op0 op1 CRn op2 CRm) s"
  unfolding OSECCR_EL1_SysRegRead_264ab12a32fecc30_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_OSLSR_EL1_SysRegRead_d99062033a35ccbf[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (OSLSR_EL1_SysRegRead_d99062033a35ccbf el op0 op1 CRn op2 CRm) s"
  unfolding OSLSR_EL1_SysRegRead_d99062033a35ccbf_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_PAR_EL1_SysRegRead_888e7c84935ebac7[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (PAR_EL1_SysRegRead_888e7c84935ebac7 el op0 op1 CRn op2 CRm) s"
  unfolding PAR_EL1_SysRegRead_888e7c84935ebac7_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_PMBIDR_EL1_SysRegRead_306c3f68e41521a3[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (PMBIDR_EL1_SysRegRead_306c3f68e41521a3 el op0 op1 CRn op2 CRm) s"
  unfolding PMBIDR_EL1_SysRegRead_306c3f68e41521a3_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_PMBLIMITR_EL1_SysRegRead_b7c18938ab0566dc[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (PMBLIMITR_EL1_SysRegRead_b7c18938ab0566dc el op0 op1 CRn op2 CRm) s"
  unfolding PMBLIMITR_EL1_SysRegRead_b7c18938ab0566dc_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_PMBPTR_EL1_SysRegRead_fb82e1b6e480bd0a[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (PMBPTR_EL1_SysRegRead_fb82e1b6e480bd0a el op0 op1 CRn op2 CRm) s"
  unfolding PMBPTR_EL1_SysRegRead_fb82e1b6e480bd0a_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_PMBSR_EL1_SysRegRead_87628bec330b9f53[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (PMBSR_EL1_SysRegRead_87628bec330b9f53 el op0 op1 CRn op2 CRm) s"
  unfolding PMBSR_EL1_SysRegRead_87628bec330b9f53_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_PMCCFILTR_EL0_SysRegRead_349918c2333bfc1e[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (PMCCFILTR_EL0_SysRegRead_349918c2333bfc1e el op0 op1 CRn op2 CRm) s"
  unfolding PMCCFILTR_EL0_SysRegRead_349918c2333bfc1e_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_PMCCNTR_EL0_SysRegRead_45fc425eff298404[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (PMCCNTR_EL0_SysRegRead_45fc425eff298404 el op0 op1 CRn op2 CRm) s"
  unfolding PMCCNTR_EL0_SysRegRead_45fc425eff298404_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_PMCEID0_EL0_SysRegRead_1364a10a0c913d82[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (PMCEID0_EL0_SysRegRead_1364a10a0c913d82 el op0 op1 CRn op2 CRm) s"
  unfolding PMCEID0_EL0_SysRegRead_1364a10a0c913d82_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_PMCEID1_EL0_SysRegRead_2db7a3b96735d30a[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (PMCEID1_EL0_SysRegRead_2db7a3b96735d30a el op0 op1 CRn op2 CRm) s"
  unfolding PMCEID1_EL0_SysRegRead_2db7a3b96735d30a_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_PMCNTENCLR_EL0_SysRegRead_5ac431b885c9c5e4[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (PMCNTENCLR_EL0_SysRegRead_5ac431b885c9c5e4 el op0 op1 CRn op2 CRm) s"
  unfolding PMCNTENCLR_EL0_SysRegRead_5ac431b885c9c5e4_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_PMCNTENSET_EL0_SysRegRead_848c3aa603193fb7[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (PMCNTENSET_EL0_SysRegRead_848c3aa603193fb7 el op0 op1 CRn op2 CRm) s"
  unfolding PMCNTENSET_EL0_SysRegRead_848c3aa603193fb7_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_PMCR_EL0_SysRegRead_9a03e454327a1718[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (PMCR_EL0_SysRegRead_9a03e454327a1718 el op0 op1 CRn op2 CRm) s"
  unfolding PMCR_EL0_SysRegRead_9a03e454327a1718_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_PMEVCNTR_EL0_SysRegRead_e0380ad70bc25a0c[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (PMEVCNTR_EL0_SysRegRead_e0380ad70bc25a0c el op0 op1 CRn op2 CRm) s"
  unfolding PMEVCNTR_EL0_SysRegRead_e0380ad70bc25a0c_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_PMEVTYPER_EL0_SysRegRead_b05172ff9d10dad4[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (PMEVTYPER_EL0_SysRegRead_b05172ff9d10dad4 el op0 op1 CRn op2 CRm) s"
  unfolding PMEVTYPER_EL0_SysRegRead_b05172ff9d10dad4_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_PMINTENCLR_EL1_SysRegRead_43b8f4d9b40b2620[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (PMINTENCLR_EL1_SysRegRead_43b8f4d9b40b2620 el op0 op1 CRn op2 CRm) s"
  unfolding PMINTENCLR_EL1_SysRegRead_43b8f4d9b40b2620_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_PMINTENSET_EL1_SysRegRead_a3d4464c2051ff23[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (PMINTENSET_EL1_SysRegRead_a3d4464c2051ff23 el op0 op1 CRn op2 CRm) s"
  unfolding PMINTENSET_EL1_SysRegRead_a3d4464c2051ff23_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_PMOVSCLR_EL0_SysRegRead_300e5dfb491e58fa[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (PMOVSCLR_EL0_SysRegRead_300e5dfb491e58fa el op0 op1 CRn op2 CRm) s"
  unfolding PMOVSCLR_EL0_SysRegRead_300e5dfb491e58fa_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_PMOVSSET_EL0_SysRegRead_e3c0657a6c8b11c8[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (PMOVSSET_EL0_SysRegRead_e3c0657a6c8b11c8 el op0 op1 CRn op2 CRm) s"
  unfolding PMOVSSET_EL0_SysRegRead_e3c0657a6c8b11c8_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_PMSCR_EL12_SysRegRead_624c386ea3cce853[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (PMSCR_EL12_SysRegRead_624c386ea3cce853 el op0 op1 CRn op2 CRm) s"
  unfolding PMSCR_EL12_SysRegRead_624c386ea3cce853_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_PMSCR_EL1_SysRegRead_39ffc554ca37b155[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (PMSCR_EL1_SysRegRead_39ffc554ca37b155 el op0 op1 CRn op2 CRm) s"
  unfolding PMSCR_EL1_SysRegRead_39ffc554ca37b155_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_PMSCR_EL2_SysRegRead_11330bd80566814a[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (PMSCR_EL2_SysRegRead_11330bd80566814a el op0 op1 CRn op2 CRm) s"
  unfolding PMSCR_EL2_SysRegRead_11330bd80566814a_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_PMSELR_EL0_SysRegRead_540b592cb875b32f[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (PMSELR_EL0_SysRegRead_540b592cb875b32f el op0 op1 CRn op2 CRm) s"
  unfolding PMSELR_EL0_SysRegRead_540b592cb875b32f_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_PMSEVFR_EL1_SysRegRead_9e9a58f73d629d59[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (PMSEVFR_EL1_SysRegRead_9e9a58f73d629d59 el op0 op1 CRn op2 CRm) s"
  unfolding PMSEVFR_EL1_SysRegRead_9e9a58f73d629d59_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_PMSFCR_EL1_SysRegRead_30b07ff27088a488[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (PMSFCR_EL1_SysRegRead_30b07ff27088a488 el op0 op1 CRn op2 CRm) s"
  unfolding PMSFCR_EL1_SysRegRead_30b07ff27088a488_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_PMSICR_EL1_SysRegRead_1b4bf4bb07470e4c[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (PMSICR_EL1_SysRegRead_1b4bf4bb07470e4c el op0 op1 CRn op2 CRm) s"
  unfolding PMSICR_EL1_SysRegRead_1b4bf4bb07470e4c_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_PMSIDR_EL1_SysRegRead_062cecff79d24b4d[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (PMSIDR_EL1_SysRegRead_062cecff79d24b4d el op0 op1 CRn op2 CRm) s"
  unfolding PMSIDR_EL1_SysRegRead_062cecff79d24b4d_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_PMSIRR_EL1_SysRegRead_b565329ce30ac491[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (PMSIRR_EL1_SysRegRead_b565329ce30ac491 el op0 op1 CRn op2 CRm) s"
  unfolding PMSIRR_EL1_SysRegRead_b565329ce30ac491_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_PMSLATFR_EL1_SysRegRead_f82542fec2521a41[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (PMSLATFR_EL1_SysRegRead_f82542fec2521a41 el op0 op1 CRn op2 CRm) s"
  unfolding PMSLATFR_EL1_SysRegRead_f82542fec2521a41_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_PMUSERENR_EL0_SysRegRead_7efca1a4be376eb7[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (PMUSERENR_EL0_SysRegRead_7efca1a4be376eb7 el op0 op1 CRn op2 CRm) s"
  unfolding PMUSERENR_EL0_SysRegRead_7efca1a4be376eb7_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_PMXEVCNTR_EL0_SysRegRead_193921f886161922[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (PMXEVCNTR_EL0_SysRegRead_193921f886161922 el op0 op1 CRn op2 CRm) s"
  unfolding PMXEVCNTR_EL0_SysRegRead_193921f886161922_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_PMXEVTYPER_EL0_SysRegRead_a34d7cb6f32074c5[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (PMXEVTYPER_EL0_SysRegRead_a34d7cb6f32074c5 el op0 op1 CRn op2 CRm) s"
  unfolding PMXEVTYPER_EL0_SysRegRead_a34d7cb6f32074c5_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_REVIDR_EL1_SysRegRead_06ac796f098a1e84[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (REVIDR_EL1_SysRegRead_06ac796f098a1e84 el op0 op1 CRn op2 CRm) s"
  unfolding REVIDR_EL1_SysRegRead_06ac796f098a1e84_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_RMR_EL1_SysRegRead_69f4933c1a574580[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (RMR_EL1_SysRegRead_69f4933c1a574580 el op0 op1 CRn op2 CRm) s"
  unfolding RMR_EL1_SysRegRead_69f4933c1a574580_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_RMR_EL2_SysRegRead_75749340e0828f00[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (RMR_EL2_SysRegRead_75749340e0828f00 el op0 op1 CRn op2 CRm) s"
  unfolding RMR_EL2_SysRegRead_75749340e0828f00_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_RMR_EL3_SysRegRead_fa5f18c3b20f8894[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (RMR_EL3_SysRegRead_fa5f18c3b20f8894 el op0 op1 CRn op2 CRm) s"
  unfolding RMR_EL3_SysRegRead_fa5f18c3b20f8894_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_RSP_EL0_SysRegRead_b64c62bd96d973e3[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (RSP_EL0_SysRegRead_b64c62bd96d973e3 el op0 op1 CRn op2 CRm) s"
  unfolding RSP_EL0_SysRegRead_b64c62bd96d973e3_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_RTPIDR_EL0_SysRegRead_0ce5a74dba936523[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (RTPIDR_EL0_SysRegRead_0ce5a74dba936523 el op0 op1 CRn op2 CRm) s"
  unfolding RTPIDR_EL0_SysRegRead_0ce5a74dba936523_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_RVBAR_EL1_SysRegRead_48a958c9250293d1[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (RVBAR_EL1_SysRegRead_48a958c9250293d1 el op0 op1 CRn op2 CRm) s"
  unfolding RVBAR_EL1_SysRegRead_48a958c9250293d1_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_RVBAR_EL2_SysRegRead_2fb802203150f4cc[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (RVBAR_EL2_SysRegRead_2fb802203150f4cc el op0 op1 CRn op2 CRm) s"
  unfolding RVBAR_EL2_SysRegRead_2fb802203150f4cc_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_RVBAR_EL3_SysRegRead_000d1ea4b77ffa21[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (RVBAR_EL3_SysRegRead_000d1ea4b77ffa21 el op0 op1 CRn op2 CRm) s"
  unfolding RVBAR_EL3_SysRegRead_000d1ea4b77ffa21_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_S3_op1_CCn_CCm_op2_SysRegRead_d72a7245384bbc0e[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (S3_op1_CCn_CCm_op2_SysRegRead_d72a7245384bbc0e el op0 op1 CRn op2 CRm) s"
  unfolding S3_op1_CCn_CCm_op2_SysRegRead_d72a7245384bbc0e_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_SCR_EL3_SysRegRead_082a69b26890132d[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (SCR_EL3_SysRegRead_082a69b26890132d el op0 op1 CRn op2 CRm) s"
  unfolding SCR_EL3_SysRegRead_082a69b26890132d_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_SCTLR_EL12_SysRegRead_81ba00bca4ce39dc[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (SCTLR_EL12_SysRegRead_81ba00bca4ce39dc el op0 op1 CRn op2 CRm) s"
  unfolding SCTLR_EL12_SysRegRead_81ba00bca4ce39dc_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_SCTLR_EL1_SysRegRead_cc5fb072b0cb85eb[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (SCTLR_EL1_SysRegRead_cc5fb072b0cb85eb el op0 op1 CRn op2 CRm) s"
  unfolding SCTLR_EL1_SysRegRead_cc5fb072b0cb85eb_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_SCTLR_EL2_SysRegRead_3cc208f3abf97e34[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (SCTLR_EL2_SysRegRead_3cc208f3abf97e34 el op0 op1 CRn op2 CRm) s"
  unfolding SCTLR_EL2_SysRegRead_3cc208f3abf97e34_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_SCTLR_EL3_SysRegRead_9c537c9c01007c3e[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (SCTLR_EL3_SysRegRead_9c537c9c01007c3e el op0 op1 CRn op2 CRm) s"
  unfolding SCTLR_EL3_SysRegRead_9c537c9c01007c3e_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_SCXTNUM_EL0_read[traces_enabledI]:
  "traces_enabled (SCXTNUM_EL0_read arg0) s"
  unfolding SCXTNUM_EL0_read_def bind_assoc
  by (traces_enabledI)

lemma traces_enabled_SCXTNUM_EL0_SysRegRead_ee5b769fc7f044cc[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (SCXTNUM_EL0_SysRegRead_ee5b769fc7f044cc el op0 op1 CRn op2 CRm) s"
  unfolding SCXTNUM_EL0_SysRegRead_ee5b769fc7f044cc_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_SCXTNUM_EL12_SysRegRead_d31f345333a78d48[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (SCXTNUM_EL12_SysRegRead_d31f345333a78d48 el op0 op1 CRn op2 CRm) s"
  unfolding SCXTNUM_EL12_SysRegRead_d31f345333a78d48_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_SCXTNUM_EL1_SysRegRead_dd27b7ad05ded1ab[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (SCXTNUM_EL1_SysRegRead_dd27b7ad05ded1ab el op0 op1 CRn op2 CRm) s"
  unfolding SCXTNUM_EL1_SysRegRead_dd27b7ad05ded1ab_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_SCXTNUM_EL2_SysRegRead_421b17f19f5fdd2a[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (SCXTNUM_EL2_SysRegRead_421b17f19f5fdd2a el op0 op1 CRn op2 CRm) s"
  unfolding SCXTNUM_EL2_SysRegRead_421b17f19f5fdd2a_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_SCXTNUM_EL3_SysRegRead_5f15a3b4da1bd4bb[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (SCXTNUM_EL3_SysRegRead_5f15a3b4da1bd4bb el op0 op1 CRn op2 CRm) s"
  unfolding SCXTNUM_EL3_SysRegRead_5f15a3b4da1bd4bb_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_SDER32_EL3_SysRegRead_e21f871563c7e34e[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (SDER32_EL3_SysRegRead_e21f871563c7e34e el op0 op1 CRn op2 CRm) s"
  unfolding SDER32_EL3_SysRegRead_e21f871563c7e34e_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_SPSel_SysRegRead_ac7632fd1580b15b[traces_enabledI]:
  "traces_enabled (SPSel_SysRegRead_ac7632fd1580b15b el op0 op1 CRn op2 CRm) s"
  unfolding SPSel_SysRegRead_ac7632fd1580b15b_def bind_assoc
  by (traces_enabledI)

lemma traces_enabled_SP_EL0_SysRegRead_4b07157e43cd0456[traces_enabledI]:
  "traces_enabled (SP_EL0_SysRegRead_4b07157e43cd0456 el op0 op1 CRn op2 CRm) s"
  unfolding SP_EL0_SysRegRead_4b07157e43cd0456_def bind_assoc
  by (traces_enabledI)

lemma traces_enabled_SP_EL1_SysRegRead_44ac23d2a7608550[traces_enabledI]:
  "traces_enabled (SP_EL1_SysRegRead_44ac23d2a7608550 el op0 op1 CRn op2 CRm) s"
  unfolding SP_EL1_SysRegRead_44ac23d2a7608550_def bind_assoc
  by (traces_enabledI)

lemma traces_enabled_SP_EL2_SysRegRead_9c4b7d596526b300[traces_enabledI]:
  "traces_enabled (SP_EL2_SysRegRead_9c4b7d596526b300 el op0 op1 CRn op2 CRm) s"
  unfolding SP_EL2_SysRegRead_9c4b7d596526b300_def bind_assoc
  by (traces_enabledI)

lemma traces_enabled_TCR_EL12_SysRegRead_cefcc3f131a70a7f[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (TCR_EL12_SysRegRead_cefcc3f131a70a7f el op0 op1 CRn op2 CRm) s"
  unfolding TCR_EL12_SysRegRead_cefcc3f131a70a7f_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_TCR_EL1_SysRegRead_fbe255888fba9865[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (TCR_EL1_SysRegRead_fbe255888fba9865 el op0 op1 CRn op2 CRm) s"
  unfolding TCR_EL1_SysRegRead_fbe255888fba9865_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_TCR_EL2_SysRegRead_3467687df9c2aec1[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (TCR_EL2_SysRegRead_3467687df9c2aec1 el op0 op1 CRn op2 CRm) s"
  unfolding TCR_EL2_SysRegRead_3467687df9c2aec1_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_TCR_EL3_SysRegRead_7da88d4a232f9451[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (TCR_EL3_SysRegRead_7da88d4a232f9451 el op0 op1 CRn op2 CRm) s"
  unfolding TCR_EL3_SysRegRead_7da88d4a232f9451_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_TPIDRRO_EL0_SysRegRead_3dc5dc323922fcfa[traces_enabledI]:
  "traces_enabled (TPIDRRO_EL0_SysRegRead_3dc5dc323922fcfa el op0 op1 CRn op2 CRm) s"
  unfolding TPIDRRO_EL0_SysRegRead_3dc5dc323922fcfa_def bind_assoc
  by (traces_enabledI)

lemma traces_enabled_TPIDR_EL0_SysRegRead_7b944c4fc3d3f60f[traces_enabledI]:
  "traces_enabled (TPIDR_EL0_SysRegRead_7b944c4fc3d3f60f el op0 op1 CRn op2 CRm) s"
  unfolding TPIDR_EL0_SysRegRead_7b944c4fc3d3f60f_def bind_assoc
  by (traces_enabledI)

lemma traces_enabled_TPIDR_EL1_SysRegRead_8db91ea8b9abc411[traces_enabledI]:
  "traces_enabled (TPIDR_EL1_SysRegRead_8db91ea8b9abc411 el op0 op1 CRn op2 CRm) s"
  unfolding TPIDR_EL1_SysRegRead_8db91ea8b9abc411_def bind_assoc
  by (traces_enabledI)

lemma traces_enabled_TPIDR_EL2_SysRegRead_fc4633f7449b5b4a[traces_enabledI]:
  "traces_enabled (TPIDR_EL2_SysRegRead_fc4633f7449b5b4a el op0 op1 CRn op2 CRm) s"
  unfolding TPIDR_EL2_SysRegRead_fc4633f7449b5b4a_def bind_assoc
  by (traces_enabledI)

lemma traces_enabled_TPIDR_EL3_SysRegRead_c6069d62b310a137[traces_enabledI]:
  "traces_enabled (TPIDR_EL3_SysRegRead_c6069d62b310a137 el op0 op1 CRn op2 CRm) s"
  unfolding TPIDR_EL3_SysRegRead_c6069d62b310a137_def bind_assoc
  by (traces_enabledI)

lemma traces_enabled_TTBR0_EL12_SysRegRead_73f9bd4d027badee[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (TTBR0_EL12_SysRegRead_73f9bd4d027badee el op0 op1 CRn op2 CRm) s"
  unfolding TTBR0_EL12_SysRegRead_73f9bd4d027badee_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_TTBR0_EL1_SysRegRead_2e8a6c25b2e4759a[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (TTBR0_EL1_SysRegRead_2e8a6c25b2e4759a el op0 op1 CRn op2 CRm) s"
  unfolding TTBR0_EL1_SysRegRead_2e8a6c25b2e4759a_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_TTBR0_EL2_SysRegRead_8d4de9e080477354[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (TTBR0_EL2_SysRegRead_8d4de9e080477354 el op0 op1 CRn op2 CRm) s"
  unfolding TTBR0_EL2_SysRegRead_8d4de9e080477354_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_TTBR0_EL3_SysRegRead_a46e35edfe45a273[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (TTBR0_EL3_SysRegRead_a46e35edfe45a273 el op0 op1 CRn op2 CRm) s"
  unfolding TTBR0_EL3_SysRegRead_a46e35edfe45a273_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_TTBR1_EL12_SysRegRead_bfbc2899eb278d2b[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (TTBR1_EL12_SysRegRead_bfbc2899eb278d2b el op0 op1 CRn op2 CRm) s"
  unfolding TTBR1_EL12_SysRegRead_bfbc2899eb278d2b_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_TTBR1_EL1_SysRegRead_2cb2fb59089165c5[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (TTBR1_EL1_SysRegRead_2cb2fb59089165c5 el op0 op1 CRn op2 CRm) s"
  unfolding TTBR1_EL1_SysRegRead_2cb2fb59089165c5_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_TTBR1_EL2_SysRegRead_08cd28a9b17bc317[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (TTBR1_EL2_SysRegRead_08cd28a9b17bc317 el op0 op1 CRn op2 CRm) s"
  unfolding TTBR1_EL2_SysRegRead_08cd28a9b17bc317_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_VBAR_EL12_SysRegRead_2ad4e02fbe99cf3d[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (VBAR_EL12_SysRegRead_2ad4e02fbe99cf3d el op0 op1 CRn op2 CRm) s"
  unfolding VBAR_EL12_SysRegRead_2ad4e02fbe99cf3d_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_VBAR_EL1_SysRegRead_4d14cb3b6fe16ab6[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (VBAR_EL1_SysRegRead_4d14cb3b6fe16ab6 el op0 op1 CRn op2 CRm) s"
  unfolding VBAR_EL1_SysRegRead_4d14cb3b6fe16ab6_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_VBAR_EL2_SysRegRead_1f6b3c94ccfecacf[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (VBAR_EL2_SysRegRead_1f6b3c94ccfecacf el op0 op1 CRn op2 CRm) s"
  unfolding VBAR_EL2_SysRegRead_1f6b3c94ccfecacf_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_VBAR_EL3_SysRegRead_32f42cb574998654[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (VBAR_EL3_SysRegRead_32f42cb574998654 el op0 op1 CRn op2 CRm) s"
  unfolding VBAR_EL3_SysRegRead_32f42cb574998654_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_VDISR_EL2_SysRegRead_14dff4ad4ae8c3a2[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (VDISR_EL2_SysRegRead_14dff4ad4ae8c3a2 el op0 op1 CRn op2 CRm) s"
  unfolding VDISR_EL2_SysRegRead_14dff4ad4ae8c3a2_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_VMPIDR_EL2_SysRegRead_49b7c13dd1b0804c[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (VMPIDR_EL2_SysRegRead_49b7c13dd1b0804c el op0 op1 CRn op2 CRm) s"
  unfolding VMPIDR_EL2_SysRegRead_49b7c13dd1b0804c_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_VPIDR_EL2_SysRegRead_f6520cd6a1f62bd8[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (VPIDR_EL2_SysRegRead_f6520cd6a1f62bd8 el op0 op1 CRn op2 CRm) s"
  unfolding VPIDR_EL2_SysRegRead_f6520cd6a1f62bd8_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_VSESR_EL2_SysRegRead_401c063e57574698[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (VSESR_EL2_SysRegRead_401c063e57574698 el op0 op1 CRn op2 CRm) s"
  unfolding VSESR_EL2_SysRegRead_401c063e57574698_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_VTCR_EL2_SysRegRead_5c8ea980dc5cc1d1[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (VTCR_EL2_SysRegRead_5c8ea980dc5cc1d1 el op0 op1 CRn op2 CRm) s"
  unfolding VTCR_EL2_SysRegRead_5c8ea980dc5cc1d1_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_VTTBR_EL2_SysRegRead_2fbbdccc9485564d[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (VTTBR_EL2_SysRegRead_2fbbdccc9485564d el op0 op1 CRn op2 CRm) s"
  unfolding VTTBR_EL2_SysRegRead_2fbbdccc9485564d_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_AArch64_AutoGen_SysRegRead[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (AArch64_AutoGen_SysRegRead el op0 op1 CRn op2 CRm) s"
  by (unfold AArch64_AutoGen_SysRegRead_def, traces_enabledI intro: assms[THEN subset_trans[rotated]])

lemma traces_enabled_AArch64_SysRegRead[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (AArch64_SysRegRead op0 op1 crn crm op2) s"
  unfolding AArch64_SysRegRead_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CDBGDTR_EL0_CapSysRegRead_8e23daae0e60af34[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CDBGDTR_EL0_CapSysRegRead_8e23daae0e60af34 el op0 op1 CRn op2 CRm) s"
  unfolding CDBGDTR_EL0_CapSysRegRead_8e23daae0e60af34_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CDLR_EL0_CapSysRegRead_619c852c71c0978d[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CDLR_EL0_CapSysRegRead_619c852c71c0978d el op0 op1 CRn op2 CRm) s"
  unfolding CDLR_EL0_CapSysRegRead_619c852c71c0978d_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CELR_EL12_CapSysRegRead_4bf271777fe55d1c[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CELR_EL12_CapSysRegRead_4bf271777fe55d1c el op0 op1 CRn op2 CRm) s"
  unfolding CELR_EL12_CapSysRegRead_4bf271777fe55d1c_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CELR_EL1_CapSysRegRead_da9869d2314a30d5[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CELR_EL1_CapSysRegRead_da9869d2314a30d5 el op0 op1 CRn op2 CRm) s"
  unfolding CELR_EL1_CapSysRegRead_da9869d2314a30d5_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CELR_EL2_CapSysRegRead_a9e9661da428a6d4[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CELR_EL2_CapSysRegRead_a9e9661da428a6d4 el op0 op1 CRn op2 CRm) s"
  unfolding CELR_EL2_CapSysRegRead_a9e9661da428a6d4_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CELR_EL3_CapSysRegRead_d0424a232c45967e[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CELR_EL3_CapSysRegRead_d0424a232c45967e el op0 op1 CRn op2 CRm) s"
  unfolding CELR_EL3_CapSysRegRead_d0424a232c45967e_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CID_EL0_CapSysRegRead_d560f6b1104266f1[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CID_EL0_CapSysRegRead_d560f6b1104266f1 el op0 op1 CRn op2 CRm) s"
  unfolding CID_EL0_CapSysRegRead_d560f6b1104266f1_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CSP_EL0_CapSysRegRead_e5b1ba121f8be4da[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CSP_EL0_CapSysRegRead_e5b1ba121f8be4da el op0 op1 CRn op2 CRm) s"
  unfolding CSP_EL0_CapSysRegRead_e5b1ba121f8be4da_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CSP_EL1_CapSysRegRead_bb8b6c0ba689eafb[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CSP_EL1_CapSysRegRead_bb8b6c0ba689eafb el op0 op1 CRn op2 CRm) s"
  unfolding CSP_EL1_CapSysRegRead_bb8b6c0ba689eafb_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CSP_EL2_CapSysRegRead_9b50d2f92d5520da[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CSP_EL2_CapSysRegRead_9b50d2f92d5520da el op0 op1 CRn op2 CRm) s"
  unfolding CSP_EL2_CapSysRegRead_9b50d2f92d5520da_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CTPIDRRO_EL0_CapSysRegRead_2def4a85803ae7cc[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CTPIDRRO_EL0_CapSysRegRead_2def4a85803ae7cc el op0 op1 CRn op2 CRm) s"
  unfolding CTPIDRRO_EL0_CapSysRegRead_2def4a85803ae7cc_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CTPIDR_EL0_CapSysRegRead_84b933ea55a77369[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CTPIDR_EL0_CapSysRegRead_84b933ea55a77369 el op0 op1 CRn op2 CRm) s"
  unfolding CTPIDR_EL0_CapSysRegRead_84b933ea55a77369_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CTPIDR_EL1_CapSysRegRead_016308c12b886084[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CTPIDR_EL1_CapSysRegRead_016308c12b886084 el op0 op1 CRn op2 CRm) s"
  unfolding CTPIDR_EL1_CapSysRegRead_016308c12b886084_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CTPIDR_EL2_CapSysRegRead_b7d4714a1ce62544[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CTPIDR_EL2_CapSysRegRead_b7d4714a1ce62544 el op0 op1 CRn op2 CRm) s"
  unfolding CTPIDR_EL2_CapSysRegRead_b7d4714a1ce62544_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CTPIDR_EL3_CapSysRegRead_c1307a9bc7bc1449[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CTPIDR_EL3_CapSysRegRead_c1307a9bc7bc1449 el op0 op1 CRn op2 CRm) s"
  unfolding CTPIDR_EL3_CapSysRegRead_c1307a9bc7bc1449_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CVBAR_EL12_CapSysRegRead_845c94ac498ff593[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CVBAR_EL12_CapSysRegRead_845c94ac498ff593 el op0 op1 CRn op2 CRm) s"
  unfolding CVBAR_EL12_CapSysRegRead_845c94ac498ff593_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CVBAR_EL1_CapSysRegRead_c42109445741a0d0[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CVBAR_EL1_CapSysRegRead_c42109445741a0d0 el op0 op1 CRn op2 CRm) s"
  unfolding CVBAR_EL1_CapSysRegRead_c42109445741a0d0_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CVBAR_EL2_CapSysRegRead_537232bbd7d69e00[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CVBAR_EL2_CapSysRegRead_537232bbd7d69e00 el op0 op1 CRn op2 CRm) s"
  unfolding CVBAR_EL2_CapSysRegRead_537232bbd7d69e00_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CVBAR_EL3_CapSysRegRead_587d4a028f8f0ef1[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CVBAR_EL3_CapSysRegRead_587d4a028f8f0ef1 el op0 op1 CRn op2 CRm) s"
  unfolding CVBAR_EL3_CapSysRegRead_587d4a028f8f0ef1_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_DDC_CapSysRegRead_eabc4ea34a10a962[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (DDC_CapSysRegRead_eabc4ea34a10a962 el op0 op1 CRn op2 CRm) s"
  unfolding DDC_CapSysRegRead_eabc4ea34a10a962_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_DDC_EL0_CapSysRegRead_e02bc676dce7fb51[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (DDC_EL0_CapSysRegRead_e02bc676dce7fb51 el op0 op1 CRn op2 CRm) s"
  unfolding DDC_EL0_CapSysRegRead_e02bc676dce7fb51_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_DDC_EL1_CapSysRegRead_08f46354e9afc01e[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (DDC_EL1_CapSysRegRead_08f46354e9afc01e el op0 op1 CRn op2 CRm) s"
  unfolding DDC_EL1_CapSysRegRead_08f46354e9afc01e_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_DDC_EL2_CapSysRegRead_6d2409222a719403[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (DDC_EL2_CapSysRegRead_6d2409222a719403 el op0 op1 CRn op2 CRm) s"
  unfolding DDC_EL2_CapSysRegRead_6d2409222a719403_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_RCSP_EL0_CapSysRegRead_6a9b29b9027548c3[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (RCSP_EL0_CapSysRegRead_6a9b29b9027548c3 el op0 op1 CRn op2 CRm) s"
  unfolding RCSP_EL0_CapSysRegRead_6a9b29b9027548c3_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_RCTPIDR_EL0_CapSysRegRead_0a3ce9d2144ddba7[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (RCTPIDR_EL0_CapSysRegRead_0a3ce9d2144ddba7 el op0 op1 CRn op2 CRm) s"
  unfolding RCTPIDR_EL0_CapSysRegRead_0a3ce9d2144ddba7_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_RDDC_EL0_CapSysRegRead_c188e736aa7b9beb[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (RDDC_EL0_CapSysRegRead_c188e736aa7b9beb el op0 op1 CRn op2 CRm) s"
  unfolding RDDC_EL0_CapSysRegRead_c188e736aa7b9beb_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_AArch64_AutoGen_CapSysRegRead[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (AArch64_AutoGen_CapSysRegRead el op0 op1 CRn op2 CRm) s"
  unfolding AArch64_AutoGen_CapSysRegRead_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_DDC_read[traces_enabledI]:
  "traces_enabled (DDC_read arg0) s"
  unfolding DDC_read_def bind_assoc
  by (traces_enabledI)

lemma traces_enabled_AArch64_CapSysRegRead[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (AArch64_CapSysRegRead op0 op1 crn crm op2) s"
  unfolding AArch64_CapSysRegRead_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ACTLR_EL1_SysRegWrite_338051dbe9bdf650[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ACTLR_EL1_SysRegWrite_338051dbe9bdf650 el op0 op1 CRn op2 CRm val_name) s"
  unfolding ACTLR_EL1_SysRegWrite_338051dbe9bdf650_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ACTLR_EL2_SysRegWrite_416ec7c6fadd122d[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ACTLR_EL2_SysRegWrite_416ec7c6fadd122d el op0 op1 CRn op2 CRm val_name) s"
  unfolding ACTLR_EL2_SysRegWrite_416ec7c6fadd122d_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ACTLR_EL3_SysRegWrite_c797d5a80525afa4[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ACTLR_EL3_SysRegWrite_c797d5a80525afa4 el op0 op1 CRn op2 CRm val_name) s"
  unfolding ACTLR_EL3_SysRegWrite_c797d5a80525afa4_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_AFSR0_EL12_SysRegWrite_9fafb4f6dbddd904[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (AFSR0_EL12_SysRegWrite_9fafb4f6dbddd904 el op0 op1 CRn op2 CRm val_name) s"
  unfolding AFSR0_EL12_SysRegWrite_9fafb4f6dbddd904_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_AFSR0_EL1_SysRegWrite_04474930979e1c86[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (AFSR0_EL1_SysRegWrite_04474930979e1c86 el op0 op1 CRn op2 CRm val_name) s"
  unfolding AFSR0_EL1_SysRegWrite_04474930979e1c86_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_AFSR0_EL2_SysRegWrite_2f9da4789f5b4073[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (AFSR0_EL2_SysRegWrite_2f9da4789f5b4073 el op0 op1 CRn op2 CRm val_name) s"
  unfolding AFSR0_EL2_SysRegWrite_2f9da4789f5b4073_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_AFSR0_EL3_SysRegWrite_e615501306210a25[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (AFSR0_EL3_SysRegWrite_e615501306210a25 el op0 op1 CRn op2 CRm val_name) s"
  unfolding AFSR0_EL3_SysRegWrite_e615501306210a25_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_AFSR1_EL12_SysRegWrite_9dbf207cccd92d9d[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (AFSR1_EL12_SysRegWrite_9dbf207cccd92d9d el op0 op1 CRn op2 CRm val_name) s"
  unfolding AFSR1_EL12_SysRegWrite_9dbf207cccd92d9d_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_AFSR1_EL1_SysRegWrite_6690138c9fdd136c[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (AFSR1_EL1_SysRegWrite_6690138c9fdd136c el op0 op1 CRn op2 CRm val_name) s"
  unfolding AFSR1_EL1_SysRegWrite_6690138c9fdd136c_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_AFSR1_EL2_SysRegWrite_c0ebc4cc65472544[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (AFSR1_EL2_SysRegWrite_c0ebc4cc65472544 el op0 op1 CRn op2 CRm val_name) s"
  unfolding AFSR1_EL2_SysRegWrite_c0ebc4cc65472544_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_AFSR1_EL3_SysRegWrite_d776cc264803f49e[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (AFSR1_EL3_SysRegWrite_d776cc264803f49e el op0 op1 CRn op2 CRm val_name) s"
  unfolding AFSR1_EL3_SysRegWrite_d776cc264803f49e_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_AMAIR_EL12_SysRegWrite_9c44aba2de7c2ff8[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (AMAIR_EL12_SysRegWrite_9c44aba2de7c2ff8 el op0 op1 CRn op2 CRm val_name) s"
  unfolding AMAIR_EL12_SysRegWrite_9c44aba2de7c2ff8_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_AMAIR_EL1_SysRegWrite_0d9c3d92d9a71703[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (AMAIR_EL1_SysRegWrite_0d9c3d92d9a71703 el op0 op1 CRn op2 CRm val_name) s"
  unfolding AMAIR_EL1_SysRegWrite_0d9c3d92d9a71703_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_AMAIR_EL2_SysRegWrite_9345da970d78b298[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (AMAIR_EL2_SysRegWrite_9345da970d78b298 el op0 op1 CRn op2 CRm val_name) s"
  unfolding AMAIR_EL2_SysRegWrite_9345da970d78b298_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_AMAIR_EL3_SysRegWrite_622c473bfedac80a[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (AMAIR_EL3_SysRegWrite_622c473bfedac80a el op0 op1 CRn op2 CRm val_name) s"
  unfolding AMAIR_EL3_SysRegWrite_622c473bfedac80a_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CCTLR_EL0_SysRegWrite_a4d8c57cb436292b[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CCTLR_EL0_SysRegWrite_a4d8c57cb436292b el op0 op1 CRn op2 CRm val_name) s"
  unfolding CCTLR_EL0_SysRegWrite_a4d8c57cb436292b_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CCTLR_EL12_SysRegWrite_c7d9d6463096d910[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CCTLR_EL12_SysRegWrite_c7d9d6463096d910 el op0 op1 CRn op2 CRm val_name) s"
  unfolding CCTLR_EL12_SysRegWrite_c7d9d6463096d910_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CCTLR_EL1_SysRegWrite_dc20ad2a867ac9bf[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CCTLR_EL1_SysRegWrite_dc20ad2a867ac9bf el op0 op1 CRn op2 CRm val_name) s"
  unfolding CCTLR_EL1_SysRegWrite_dc20ad2a867ac9bf_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CCTLR_EL2_SysRegWrite_65620c8ccb1113a5[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CCTLR_EL2_SysRegWrite_65620c8ccb1113a5 el op0 op1 CRn op2 CRm val_name) s"
  unfolding CCTLR_EL2_SysRegWrite_65620c8ccb1113a5_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CCTLR_EL3_SysRegWrite_f5e936c8846e6fc7[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CCTLR_EL3_SysRegWrite_f5e936c8846e6fc7 el op0 op1 CRn op2 CRm val_name) s"
  unfolding CCTLR_EL3_SysRegWrite_f5e936c8846e6fc7_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CHCR_EL2_SysRegWrite_dadda8ecf053e448[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CHCR_EL2_SysRegWrite_dadda8ecf053e448 el op0 op1 CRn op2 CRm val_name) s"
  unfolding CHCR_EL2_SysRegWrite_dadda8ecf053e448_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CNTFRQ_EL0_SysRegWrite_0fac77f077759456[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CNTFRQ_EL0_SysRegWrite_0fac77f077759456 el op0 op1 CRn op2 CRm val_name) s"
  unfolding CNTFRQ_EL0_SysRegWrite_0fac77f077759456_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CNTHCTL_EL2_SysRegWrite_eb0cbec9f9398e0e[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CNTHCTL_EL2_SysRegWrite_eb0cbec9f9398e0e el op0 op1 CRn op2 CRm val_name) s"
  unfolding CNTHCTL_EL2_SysRegWrite_eb0cbec9f9398e0e_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CNTHP_CTL_EL2_SysRegWrite_92034fc54290a7b8[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CNTHP_CTL_EL2_SysRegWrite_92034fc54290a7b8 el op0 op1 CRn op2 CRm val_name) s"
  unfolding CNTHP_CTL_EL2_SysRegWrite_92034fc54290a7b8_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CNTHP_CVAL_EL2_SysRegWrite_36de219faded7cbc[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CNTHP_CVAL_EL2_SysRegWrite_36de219faded7cbc el op0 op1 CRn op2 CRm val_name) s"
  unfolding CNTHP_CVAL_EL2_SysRegWrite_36de219faded7cbc_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CNTHP_TVAL_EL2_SysRegWrite_877bbf4f78f810b9[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CNTHP_TVAL_EL2_SysRegWrite_877bbf4f78f810b9 el op0 op1 CRn op2 CRm val_name) s"
  unfolding CNTHP_TVAL_EL2_SysRegWrite_877bbf4f78f810b9_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CNTHV_CTL_EL2_SysRegWrite_ecc786a588fc8ab9[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CNTHV_CTL_EL2_SysRegWrite_ecc786a588fc8ab9 el op0 op1 CRn op2 CRm val_name) s"
  unfolding CNTHV_CTL_EL2_SysRegWrite_ecc786a588fc8ab9_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CNTHV_CVAL_EL2_SysRegWrite_b3d7c631e2b3eaab[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CNTHV_CVAL_EL2_SysRegWrite_b3d7c631e2b3eaab el op0 op1 CRn op2 CRm val_name) s"
  unfolding CNTHV_CVAL_EL2_SysRegWrite_b3d7c631e2b3eaab_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CNTHV_TVAL_EL2_SysRegWrite_e215d12d330397f1[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CNTHV_TVAL_EL2_SysRegWrite_e215d12d330397f1 el op0 op1 CRn op2 CRm val_name) s"
  unfolding CNTHV_TVAL_EL2_SysRegWrite_e215d12d330397f1_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CNTKCTL_EL12_SysRegWrite_518123f17a6402e4[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CNTKCTL_EL12_SysRegWrite_518123f17a6402e4 el op0 op1 CRn op2 CRm val_name) s"
  unfolding CNTKCTL_EL12_SysRegWrite_518123f17a6402e4_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CNTKCTL_EL1_SysRegWrite_9a7be69aa33bb9c2[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CNTKCTL_EL1_SysRegWrite_9a7be69aa33bb9c2 el op0 op1 CRn op2 CRm val_name) s"
  unfolding CNTKCTL_EL1_SysRegWrite_9a7be69aa33bb9c2_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CNTPS_CTL_EL1_SysRegWrite_a0625fd9f7b035a8[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CNTPS_CTL_EL1_SysRegWrite_a0625fd9f7b035a8 el op0 op1 CRn op2 CRm val_name) s"
  unfolding CNTPS_CTL_EL1_SysRegWrite_a0625fd9f7b035a8_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CNTPS_CVAL_EL1_SysRegWrite_f09243080b7c260d[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CNTPS_CVAL_EL1_SysRegWrite_f09243080b7c260d el op0 op1 CRn op2 CRm val_name) s"
  unfolding CNTPS_CVAL_EL1_SysRegWrite_f09243080b7c260d_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CNTPS_TVAL_EL1_SysRegWrite_a9b16e60037fa746[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CNTPS_TVAL_EL1_SysRegWrite_a9b16e60037fa746 el op0 op1 CRn op2 CRm val_name) s"
  unfolding CNTPS_TVAL_EL1_SysRegWrite_a9b16e60037fa746_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CNTP_CTL_EL02_SysRegWrite_99a9da3e2454714e[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CNTP_CTL_EL02_SysRegWrite_99a9da3e2454714e el op0 op1 CRn op2 CRm val_name) s"
  unfolding CNTP_CTL_EL02_SysRegWrite_99a9da3e2454714e_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CNTP_CTL_EL0_SysRegWrite_137f81090c1357e6[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CNTP_CTL_EL0_SysRegWrite_137f81090c1357e6 el op0 op1 CRn op2 CRm val_name) s"
  unfolding CNTP_CTL_EL0_SysRegWrite_137f81090c1357e6_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CNTP_CVAL_EL02_SysRegWrite_2b3e9ccfce186a4f[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CNTP_CVAL_EL02_SysRegWrite_2b3e9ccfce186a4f el op0 op1 CRn op2 CRm val_name) s"
  unfolding CNTP_CVAL_EL02_SysRegWrite_2b3e9ccfce186a4f_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CNTP_CVAL_EL0_SysRegWrite_d54c08ee0cf9aaf7[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CNTP_CVAL_EL0_SysRegWrite_d54c08ee0cf9aaf7 el op0 op1 CRn op2 CRm val_name) s"
  unfolding CNTP_CVAL_EL0_SysRegWrite_d54c08ee0cf9aaf7_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CNTP_TVAL_EL02_SysRegWrite_caa9f2aa73cb6b96[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CNTP_TVAL_EL02_SysRegWrite_caa9f2aa73cb6b96 el op0 op1 CRn op2 CRm val_name) s"
  unfolding CNTP_TVAL_EL02_SysRegWrite_caa9f2aa73cb6b96_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CNTP_TVAL_EL0_SysRegWrite_d7441eec23c3d524[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CNTP_TVAL_EL0_SysRegWrite_d7441eec23c3d524 el op0 op1 CRn op2 CRm val_name) s"
  unfolding CNTP_TVAL_EL0_SysRegWrite_d7441eec23c3d524_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CNTVOFF_EL2_SysRegWrite_621ada4cfda60bcb[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CNTVOFF_EL2_SysRegWrite_621ada4cfda60bcb el op0 op1 CRn op2 CRm val_name) s"
  unfolding CNTVOFF_EL2_SysRegWrite_621ada4cfda60bcb_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CNTV_CTL_EL02_SysRegWrite_d6cac9cc52dd8fec[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CNTV_CTL_EL02_SysRegWrite_d6cac9cc52dd8fec el op0 op1 CRn op2 CRm val_name) s"
  unfolding CNTV_CTL_EL02_SysRegWrite_d6cac9cc52dd8fec_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CNTV_CTL_EL0_SysRegWrite_e9fd22bae4b06064[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CNTV_CTL_EL0_SysRegWrite_e9fd22bae4b06064 el op0 op1 CRn op2 CRm val_name) s"
  unfolding CNTV_CTL_EL0_SysRegWrite_e9fd22bae4b06064_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CNTV_CVAL_EL02_SysRegWrite_7548964ed28b5abb[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CNTV_CVAL_EL02_SysRegWrite_7548964ed28b5abb el op0 op1 CRn op2 CRm val_name) s"
  unfolding CNTV_CVAL_EL02_SysRegWrite_7548964ed28b5abb_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CNTV_CVAL_EL0_SysRegWrite_f237c5c94ec92951[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CNTV_CVAL_EL0_SysRegWrite_f237c5c94ec92951 el op0 op1 CRn op2 CRm val_name) s"
  unfolding CNTV_CVAL_EL0_SysRegWrite_f237c5c94ec92951_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CNTV_TVAL_EL02_SysRegWrite_dc97f79a5f74078f[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CNTV_TVAL_EL02_SysRegWrite_dc97f79a5f74078f el op0 op1 CRn op2 CRm val_name) s"
  unfolding CNTV_TVAL_EL02_SysRegWrite_dc97f79a5f74078f_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CNTV_TVAL_EL0_SysRegWrite_903191acca729cda[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CNTV_TVAL_EL0_SysRegWrite_903191acca729cda el op0 op1 CRn op2 CRm val_name) s"
  unfolding CNTV_TVAL_EL0_SysRegWrite_903191acca729cda_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CONTEXTIDR_EL12_SysRegWrite_33154953ae1b01d5[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CONTEXTIDR_EL12_SysRegWrite_33154953ae1b01d5 el op0 op1 CRn op2 CRm val_name) s"
  unfolding CONTEXTIDR_EL12_SysRegWrite_33154953ae1b01d5_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CONTEXTIDR_EL1_SysRegWrite_5408e4e72af4e23d[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CONTEXTIDR_EL1_SysRegWrite_5408e4e72af4e23d el op0 op1 CRn op2 CRm val_name) s"
  unfolding CONTEXTIDR_EL1_SysRegWrite_5408e4e72af4e23d_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CONTEXTIDR_EL2_SysRegWrite_27187b6dc7c5a748[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CONTEXTIDR_EL2_SysRegWrite_27187b6dc7c5a748 el op0 op1 CRn op2 CRm val_name) s"
  unfolding CONTEXTIDR_EL2_SysRegWrite_27187b6dc7c5a748_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CPACR_EL12_SysRegWrite_637092a999939f8b[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CPACR_EL12_SysRegWrite_637092a999939f8b el op0 op1 CRn op2 CRm val_name) s"
  unfolding CPACR_EL12_SysRegWrite_637092a999939f8b_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CPACR_EL1_SysRegWrite_00878a1f3e87823c[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CPACR_EL1_SysRegWrite_00878a1f3e87823c el op0 op1 CRn op2 CRm val_name) s"
  unfolding CPACR_EL1_SysRegWrite_00878a1f3e87823c_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CPTR_EL2_SysRegWrite_5a082f460b1b2308[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CPTR_EL2_SysRegWrite_5a082f460b1b2308 el op0 op1 CRn op2 CRm val_name) s"
  unfolding CPTR_EL2_SysRegWrite_5a082f460b1b2308_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CPTR_EL3_SysRegWrite_879d4b1bad53408b[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CPTR_EL3_SysRegWrite_879d4b1bad53408b el op0 op1 CRn op2 CRm val_name) s"
  unfolding CPTR_EL3_SysRegWrite_879d4b1bad53408b_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CSCR_EL3_SysRegWrite_22b95c83b04d6c91[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CSCR_EL3_SysRegWrite_22b95c83b04d6c91 el op0 op1 CRn op2 CRm val_name) s"
  unfolding CSCR_EL3_SysRegWrite_22b95c83b04d6c91_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CSSELR_EL1_SysRegWrite_1f9e1e0300c8783c[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CSSELR_EL1_SysRegWrite_1f9e1e0300c8783c el op0 op1 CRn op2 CRm val_name) s"
  unfolding CSSELR_EL1_SysRegWrite_1f9e1e0300c8783c_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_DACR32_EL2_SysRegWrite_a8bad0131817f121[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (DACR32_EL2_SysRegWrite_a8bad0131817f121 el op0 op1 CRn op2 CRm val_name) s"
  unfolding DACR32_EL2_SysRegWrite_a8bad0131817f121_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_DAIF_SysRegWrite_3d31f214debf624b[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (DAIF_SysRegWrite_3d31f214debf624b el op0 op1 CRn op2 CRm val_name) s"
  unfolding DAIF_SysRegWrite_3d31f214debf624b_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_DBGBCR_EL1_SysRegWrite_6730f3e3839510c5[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (DBGBCR_EL1_SysRegWrite_6730f3e3839510c5 el op0 op1 CRn op2 CRm val_name) s"
  unfolding DBGBCR_EL1_SysRegWrite_6730f3e3839510c5_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_DBGBVR_EL1_SysRegWrite_915752bfd6a41a2b[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (DBGBVR_EL1_SysRegWrite_915752bfd6a41a2b el op0 op1 CRn op2 CRm val_name) s"
  unfolding DBGBVR_EL1_SysRegWrite_915752bfd6a41a2b_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_DBGCLAIMCLR_EL1_SysRegWrite_2a099a67767e57cf[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (DBGCLAIMCLR_EL1_SysRegWrite_2a099a67767e57cf el op0 op1 CRn op2 CRm val_name) s"
  unfolding DBGCLAIMCLR_EL1_SysRegWrite_2a099a67767e57cf_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_DBGCLAIMSET_EL1_SysRegWrite_90e355b6a5730770[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (DBGCLAIMSET_EL1_SysRegWrite_90e355b6a5730770 el op0 op1 CRn op2 CRm val_name) s"
  unfolding DBGCLAIMSET_EL1_SysRegWrite_90e355b6a5730770_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_DBGDTRTX_EL0_SysRegWrite_057e8c91e001a69f[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (DBGDTRTX_EL0_SysRegWrite_057e8c91e001a69f el op0 op1 CRn op2 CRm val_name) s"
  unfolding DBGDTRTX_EL0_SysRegWrite_057e8c91e001a69f_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_DBGDTR_EL0_write[traces_enabledI]:
  assumes "system_reg_access s"
  shows "traces_enabled (DBGDTR_EL0_write val_name) s"
  unfolding DBGDTR_EL0_write_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_DBGDTR_EL0_SysRegWrite_c7246a22e06c7729[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (DBGDTR_EL0_SysRegWrite_c7246a22e06c7729 el op0 op1 CRn op2 CRm val_name) s"
  unfolding DBGDTR_EL0_SysRegWrite_c7246a22e06c7729_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_DBGPRCR_EL1_SysRegWrite_710b60256172548e[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (DBGPRCR_EL1_SysRegWrite_710b60256172548e el op0 op1 CRn op2 CRm val_name) s"
  unfolding DBGPRCR_EL1_SysRegWrite_710b60256172548e_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_DBGVCR32_EL2_SysRegWrite_769fbfe4fa51a4e5[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (DBGVCR32_EL2_SysRegWrite_769fbfe4fa51a4e5 el op0 op1 CRn op2 CRm val_name) s"
  unfolding DBGVCR32_EL2_SysRegWrite_769fbfe4fa51a4e5_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_DBGWCR_EL1_SysRegWrite_6bda3acb5910d354[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (DBGWCR_EL1_SysRegWrite_6bda3acb5910d354 el op0 op1 CRn op2 CRm val_name) s"
  unfolding DBGWCR_EL1_SysRegWrite_6bda3acb5910d354_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_DBGWVR_EL1_SysRegWrite_745b296ee53305ea[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (DBGWVR_EL1_SysRegWrite_745b296ee53305ea el op0 op1 CRn op2 CRm val_name) s"
  unfolding DBGWVR_EL1_SysRegWrite_745b296ee53305ea_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_DISR_EL1_SysRegWrite_64517664b9260065[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (DISR_EL1_SysRegWrite_64517664b9260065 el op0 op1 CRn op2 CRm val_name) s"
  unfolding DISR_EL1_SysRegWrite_64517664b9260065_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_DLR_EL0_write[traces_enabledI]:
  assumes "system_reg_access s"
  shows "traces_enabled (DLR_EL0_write val_name) s"
  unfolding DLR_EL0_write_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_DLR_EL0_SysRegWrite_a2d10a509fed3a63[traces_enabledI]:
  "traces_enabled (DLR_EL0_SysRegWrite_a2d10a509fed3a63 el op0 op1 CRn op2 CRm val_name) s"
  unfolding DLR_EL0_SysRegWrite_a2d10a509fed3a63_def bind_assoc
  by (traces_enabledI)

lemma traces_enabled_ELR_EL12_SysRegWrite_6720e93c266dadea[traces_enabledI]:
  "traces_enabled (ELR_EL12_SysRegWrite_6720e93c266dadea el op0 op1 CRn op2 CRm val_name) s"
  unfolding ELR_EL12_SysRegWrite_6720e93c266dadea_def bind_assoc
  by (traces_enabledI)

lemma traces_enabled_ELR_EL1_SysRegWrite_b6bd589b2dd79575[traces_enabledI]:
  "traces_enabled (ELR_EL1_SysRegWrite_b6bd589b2dd79575 el op0 op1 CRn op2 CRm val_name) s"
  unfolding ELR_EL1_SysRegWrite_b6bd589b2dd79575_def bind_assoc
  by (traces_enabledI)

lemma traces_enabled_ELR_EL2_SysRegWrite_9f4ca59c1a88f1a9[traces_enabledI]:
  "traces_enabled (ELR_EL2_SysRegWrite_9f4ca59c1a88f1a9 el op0 op1 CRn op2 CRm val_name) s"
  unfolding ELR_EL2_SysRegWrite_9f4ca59c1a88f1a9_def bind_assoc
  by (traces_enabledI)

lemma traces_enabled_ELR_EL3_SysRegWrite_8cd0b0c7f61ee7aa[traces_enabledI]:
  "traces_enabled (ELR_EL3_SysRegWrite_8cd0b0c7f61ee7aa el op0 op1 CRn op2 CRm val_name) s"
  unfolding ELR_EL3_SysRegWrite_8cd0b0c7f61ee7aa_def bind_assoc
  by (traces_enabledI)

lemma traces_enabled_ERRSELR_EL1_SysRegWrite_551535eed30e26f9[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ERRSELR_EL1_SysRegWrite_551535eed30e26f9 el op0 op1 CRn op2 CRm val_name) s"
  unfolding ERRSELR_EL1_SysRegWrite_551535eed30e26f9_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ERXADDR_EL1_SysRegWrite_8a1eabc2959662e8[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ERXADDR_EL1_SysRegWrite_8a1eabc2959662e8 el op0 op1 CRn op2 CRm val_name) s"
  unfolding ERXADDR_EL1_SysRegWrite_8a1eabc2959662e8_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ERXCTLR_EL1_SysRegWrite_acca1e102ba86b42[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ERXCTLR_EL1_SysRegWrite_acca1e102ba86b42 el op0 op1 CRn op2 CRm val_name) s"
  unfolding ERXCTLR_EL1_SysRegWrite_acca1e102ba86b42_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ERXMISC0_EL1_SysRegWrite_822ceca9b10b2621[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ERXMISC0_EL1_SysRegWrite_822ceca9b10b2621 el op0 op1 CRn op2 CRm val_name) s"
  unfolding ERXMISC0_EL1_SysRegWrite_822ceca9b10b2621_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ERXMISC1_EL1_SysRegWrite_9a9ef77b5fd82587[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ERXMISC1_EL1_SysRegWrite_9a9ef77b5fd82587 el op0 op1 CRn op2 CRm val_name) s"
  unfolding ERXMISC1_EL1_SysRegWrite_9a9ef77b5fd82587_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ERXSTATUS_EL1_SysRegWrite_f0798b4207ec0193[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ERXSTATUS_EL1_SysRegWrite_f0798b4207ec0193 el op0 op1 CRn op2 CRm val_name) s"
  unfolding ERXSTATUS_EL1_SysRegWrite_f0798b4207ec0193_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ESR_EL12_SysRegWrite_2b2d6012ba438548[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ESR_EL12_SysRegWrite_2b2d6012ba438548 el op0 op1 CRn op2 CRm val_name) s"
  unfolding ESR_EL12_SysRegWrite_2b2d6012ba438548_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ESR_EL1_SysRegWrite_a8ce40896bd70a6b[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ESR_EL1_SysRegWrite_a8ce40896bd70a6b el op0 op1 CRn op2 CRm val_name) s"
  unfolding ESR_EL1_SysRegWrite_a8ce40896bd70a6b_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ESR_EL2_SysRegWrite_a10e84e3bd1020c8[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ESR_EL2_SysRegWrite_a10e84e3bd1020c8 el op0 op1 CRn op2 CRm val_name) s"
  unfolding ESR_EL2_SysRegWrite_a10e84e3bd1020c8_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ESR_EL3_SysRegWrite_195a2e1a5b40464e[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ESR_EL3_SysRegWrite_195a2e1a5b40464e el op0 op1 CRn op2 CRm val_name) s"
  unfolding ESR_EL3_SysRegWrite_195a2e1a5b40464e_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_FAR_EL12_SysRegWrite_78f825940e556299[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (FAR_EL12_SysRegWrite_78f825940e556299 el op0 op1 CRn op2 CRm val_name) s"
  unfolding FAR_EL12_SysRegWrite_78f825940e556299_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_FAR_EL1_SysRegWrite_fc0bd224b62cc089[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (FAR_EL1_SysRegWrite_fc0bd224b62cc089 el op0 op1 CRn op2 CRm val_name) s"
  unfolding FAR_EL1_SysRegWrite_fc0bd224b62cc089_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_FAR_EL2_SysRegWrite_6370aabce83a1613[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (FAR_EL2_SysRegWrite_6370aabce83a1613 el op0 op1 CRn op2 CRm val_name) s"
  unfolding FAR_EL2_SysRegWrite_6370aabce83a1613_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_FAR_EL3_SysRegWrite_397cfda85a093e9d[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (FAR_EL3_SysRegWrite_397cfda85a093e9d el op0 op1 CRn op2 CRm val_name) s"
  unfolding FAR_EL3_SysRegWrite_397cfda85a093e9d_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_FPCR_SysRegWrite_4f255cf55390cebb[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (FPCR_SysRegWrite_4f255cf55390cebb el op0 op1 CRn op2 CRm val_name) s"
  unfolding FPCR_SysRegWrite_4f255cf55390cebb_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_FPEXC32_EL2_SysRegWrite_9f180ead5c4d6735[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (FPEXC32_EL2_SysRegWrite_9f180ead5c4d6735 el op0 op1 CRn op2 CRm val_name) s"
  unfolding FPEXC32_EL2_SysRegWrite_9f180ead5c4d6735_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_FPSR_SysRegWrite_413aed98a94900de[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (FPSR_SysRegWrite_413aed98a94900de el op0 op1 CRn op2 CRm val_name) s"
  unfolding FPSR_SysRegWrite_413aed98a94900de_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_HACR_EL2_SysRegWrite_5b2ca32fcb39ecab[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (HACR_EL2_SysRegWrite_5b2ca32fcb39ecab el op0 op1 CRn op2 CRm val_name) s"
  unfolding HACR_EL2_SysRegWrite_5b2ca32fcb39ecab_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_HCR_EL2_SysRegWrite_6fc18e07a17fd5a2[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (HCR_EL2_SysRegWrite_6fc18e07a17fd5a2 el op0 op1 CRn op2 CRm val_name) s"
  unfolding HCR_EL2_SysRegWrite_6fc18e07a17fd5a2_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_HPFAR_EL2_SysRegWrite_20417eccdd6b4768[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (HPFAR_EL2_SysRegWrite_20417eccdd6b4768 el op0 op1 CRn op2 CRm val_name) s"
  unfolding HPFAR_EL2_SysRegWrite_20417eccdd6b4768_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_HSTR_EL2_SysRegWrite_391a605c0bfb9d1e[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (HSTR_EL2_SysRegWrite_391a605c0bfb9d1e el op0 op1 CRn op2 CRm val_name) s"
  unfolding HSTR_EL2_SysRegWrite_391a605c0bfb9d1e_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ICC_AP0R_EL1_SysRegWrite_949897f971748acc[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ICC_AP0R_EL1_SysRegWrite_949897f971748acc el op0 op1 CRn op2 CRm val_name) s"
  unfolding ICC_AP0R_EL1_SysRegWrite_949897f971748acc_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ICC_AP1R_EL1_SysRegWrite_55167410f7650dea[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ICC_AP1R_EL1_SysRegWrite_55167410f7650dea el op0 op1 CRn op2 CRm val_name) s"
  unfolding ICC_AP1R_EL1_SysRegWrite_55167410f7650dea_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ICC_ASGI1R_EL1_SysRegWrite_c163c25adc1b1354[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ICC_ASGI1R_EL1_SysRegWrite_c163c25adc1b1354 el op0 op1 CRn op2 CRm val_name) s"
  unfolding ICC_ASGI1R_EL1_SysRegWrite_c163c25adc1b1354_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ICC_BPR0_EL1_SysRegWrite_10028206553f3655[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ICC_BPR0_EL1_SysRegWrite_10028206553f3655 el op0 op1 CRn op2 CRm val_name) s"
  unfolding ICC_BPR0_EL1_SysRegWrite_10028206553f3655_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ICC_BPR1_EL1_SysRegWrite_a633b2e9f3626d9b[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ICC_BPR1_EL1_SysRegWrite_a633b2e9f3626d9b el op0 op1 CRn op2 CRm val_name) s"
  unfolding ICC_BPR1_EL1_SysRegWrite_a633b2e9f3626d9b_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ICC_CTLR_EL1_SysRegWrite_8ec3f4b67393eba8[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ICC_CTLR_EL1_SysRegWrite_8ec3f4b67393eba8 el op0 op1 CRn op2 CRm val_name) s"
  unfolding ICC_CTLR_EL1_SysRegWrite_8ec3f4b67393eba8_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ICC_CTLR_EL3_SysRegWrite_ecc8b41b177c53e8[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ICC_CTLR_EL3_SysRegWrite_ecc8b41b177c53e8 el op0 op1 CRn op2 CRm val_name) s"
  unfolding ICC_CTLR_EL3_SysRegWrite_ecc8b41b177c53e8_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ICC_DIR_EL1_SysRegWrite_77fadeda7efde9c5[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ICC_DIR_EL1_SysRegWrite_77fadeda7efde9c5 el op0 op1 CRn op2 CRm val_name) s"
  unfolding ICC_DIR_EL1_SysRegWrite_77fadeda7efde9c5_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ICC_EOIR0_EL1_SysRegWrite_9c0fae08cd7a2444[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ICC_EOIR0_EL1_SysRegWrite_9c0fae08cd7a2444 el op0 op1 CRn op2 CRm val_name) s"
  unfolding ICC_EOIR0_EL1_SysRegWrite_9c0fae08cd7a2444_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ICC_EOIR1_EL1_SysRegWrite_f065db56e179bf6e[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ICC_EOIR1_EL1_SysRegWrite_f065db56e179bf6e el op0 op1 CRn op2 CRm val_name) s"
  unfolding ICC_EOIR1_EL1_SysRegWrite_f065db56e179bf6e_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ICC_IGRPEN0_EL1_SysRegWrite_b94e4d10f7a33382[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ICC_IGRPEN0_EL1_SysRegWrite_b94e4d10f7a33382 el op0 op1 CRn op2 CRm val_name) s"
  unfolding ICC_IGRPEN0_EL1_SysRegWrite_b94e4d10f7a33382_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ICC_IGRPEN1_EL1_SysRegWrite_c36dfa556252f6b4[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ICC_IGRPEN1_EL1_SysRegWrite_c36dfa556252f6b4 el op0 op1 CRn op2 CRm val_name) s"
  unfolding ICC_IGRPEN1_EL1_SysRegWrite_c36dfa556252f6b4_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ICC_IGRPEN1_EL3_SysRegWrite_6f1db000a53b40ca[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ICC_IGRPEN1_EL3_SysRegWrite_6f1db000a53b40ca el op0 op1 CRn op2 CRm val_name) s"
  unfolding ICC_IGRPEN1_EL3_SysRegWrite_6f1db000a53b40ca_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ICC_PMR_EL1_SysRegWrite_8bb2caa31e7d5e1b[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ICC_PMR_EL1_SysRegWrite_8bb2caa31e7d5e1b el op0 op1 CRn op2 CRm val_name) s"
  unfolding ICC_PMR_EL1_SysRegWrite_8bb2caa31e7d5e1b_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ICC_SGI0R_EL1_SysRegWrite_ba6d1066ea6fbbb7[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ICC_SGI0R_EL1_SysRegWrite_ba6d1066ea6fbbb7 el op0 op1 CRn op2 CRm val_name) s"
  unfolding ICC_SGI0R_EL1_SysRegWrite_ba6d1066ea6fbbb7_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ICC_SGI1R_EL1_SysRegWrite_0da31fe6c2e1b098[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ICC_SGI1R_EL1_SysRegWrite_0da31fe6c2e1b098 el op0 op1 CRn op2 CRm val_name) s"
  unfolding ICC_SGI1R_EL1_SysRegWrite_0da31fe6c2e1b098_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ICC_SRE_EL1_SysRegWrite_d2efb75caa67d019[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ICC_SRE_EL1_SysRegWrite_d2efb75caa67d019 el op0 op1 CRn op2 CRm val_name) s"
  unfolding ICC_SRE_EL1_SysRegWrite_d2efb75caa67d019_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ICC_SRE_EL2_SysRegWrite_39c314f677b8ec2e[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ICC_SRE_EL2_SysRegWrite_39c314f677b8ec2e el op0 op1 CRn op2 CRm val_name) s"
  unfolding ICC_SRE_EL2_SysRegWrite_39c314f677b8ec2e_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ICC_SRE_EL3_SysRegWrite_c0af2dd58a7e1d22[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ICC_SRE_EL3_SysRegWrite_c0af2dd58a7e1d22 el op0 op1 CRn op2 CRm val_name) s"
  unfolding ICC_SRE_EL3_SysRegWrite_c0af2dd58a7e1d22_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ICH_AP0R_EL2_SysRegWrite_9517857bb550d699[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ICH_AP0R_EL2_SysRegWrite_9517857bb550d699 el op0 op1 CRn op2 CRm val_name) s"
  unfolding ICH_AP0R_EL2_SysRegWrite_9517857bb550d699_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ICH_AP1R_EL2_SysRegWrite_20f46016b54a3395[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ICH_AP1R_EL2_SysRegWrite_20f46016b54a3395 el op0 op1 CRn op2 CRm val_name) s"
  unfolding ICH_AP1R_EL2_SysRegWrite_20f46016b54a3395_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ICH_HCR_EL2_SysRegWrite_2fea52a15cd7dbe5[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ICH_HCR_EL2_SysRegWrite_2fea52a15cd7dbe5 el op0 op1 CRn op2 CRm val_name) s"
  unfolding ICH_HCR_EL2_SysRegWrite_2fea52a15cd7dbe5_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ICH_LR_EL2_SysRegWrite_8b291f94259261d2[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ICH_LR_EL2_SysRegWrite_8b291f94259261d2 el op0 op1 CRn op2 CRm val_name) s"
  unfolding ICH_LR_EL2_SysRegWrite_8b291f94259261d2_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ICH_VMCR_EL2_SysRegWrite_86a315374f6b5205[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ICH_VMCR_EL2_SysRegWrite_86a315374f6b5205 el op0 op1 CRn op2 CRm val_name) s"
  unfolding ICH_VMCR_EL2_SysRegWrite_86a315374f6b5205_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_IFSR32_EL2_SysRegWrite_6ce25b2b11e30403[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (IFSR32_EL2_SysRegWrite_6ce25b2b11e30403 el op0 op1 CRn op2 CRm val_name) s"
  unfolding IFSR32_EL2_SysRegWrite_6ce25b2b11e30403_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_LORC_EL1_SysRegWrite_7100b979c23fc52e[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (LORC_EL1_SysRegWrite_7100b979c23fc52e el op0 op1 CRn op2 CRm val_name) s"
  unfolding LORC_EL1_SysRegWrite_7100b979c23fc52e_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_LOREA_EL1_SysRegWrite_2d068511b7f5ce7b[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (LOREA_EL1_SysRegWrite_2d068511b7f5ce7b el op0 op1 CRn op2 CRm val_name) s"
  unfolding LOREA_EL1_SysRegWrite_2d068511b7f5ce7b_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_LORN_EL1_SysRegWrite_bde03c74e878b099[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (LORN_EL1_SysRegWrite_bde03c74e878b099 el op0 op1 CRn op2 CRm val_name) s"
  unfolding LORN_EL1_SysRegWrite_bde03c74e878b099_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_LORSA_EL1_SysRegWrite_9ba633e967136731[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (LORSA_EL1_SysRegWrite_9ba633e967136731 el op0 op1 CRn op2 CRm val_name) s"
  unfolding LORSA_EL1_SysRegWrite_9ba633e967136731_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_MAIR_EL12_SysRegWrite_da2526ed2008ed50[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (MAIR_EL12_SysRegWrite_da2526ed2008ed50 el op0 op1 CRn op2 CRm val_name) s"
  unfolding MAIR_EL12_SysRegWrite_da2526ed2008ed50_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_MAIR_EL1_SysRegWrite_45d8150aaf31e3b9[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (MAIR_EL1_SysRegWrite_45d8150aaf31e3b9 el op0 op1 CRn op2 CRm val_name) s"
  unfolding MAIR_EL1_SysRegWrite_45d8150aaf31e3b9_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_MAIR_EL2_SysRegWrite_4e3422c1776528f5[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (MAIR_EL2_SysRegWrite_4e3422c1776528f5 el op0 op1 CRn op2 CRm val_name) s"
  unfolding MAIR_EL2_SysRegWrite_4e3422c1776528f5_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_MAIR_EL3_SysRegWrite_d15af780e0b4e771[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (MAIR_EL3_SysRegWrite_d15af780e0b4e771 el op0 op1 CRn op2 CRm val_name) s"
  unfolding MAIR_EL3_SysRegWrite_d15af780e0b4e771_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_MDCCINT_EL1_SysRegWrite_1e6a37984aec7145[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (MDCCINT_EL1_SysRegWrite_1e6a37984aec7145 el op0 op1 CRn op2 CRm val_name) s"
  unfolding MDCCINT_EL1_SysRegWrite_1e6a37984aec7145_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_MDCR_EL2_SysRegWrite_3f12005c8c459bf3[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (MDCR_EL2_SysRegWrite_3f12005c8c459bf3 el op0 op1 CRn op2 CRm val_name) s"
  unfolding MDCR_EL2_SysRegWrite_3f12005c8c459bf3_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_MDCR_EL3_SysRegWrite_37dff5fa83ad16ed[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (MDCR_EL3_SysRegWrite_37dff5fa83ad16ed el op0 op1 CRn op2 CRm val_name) s"
  unfolding MDCR_EL3_SysRegWrite_37dff5fa83ad16ed_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_MDSCR_EL1_SysRegWrite_94ddb1e46aff4dfa[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (MDSCR_EL1_SysRegWrite_94ddb1e46aff4dfa el op0 op1 CRn op2 CRm val_name) s"
  unfolding MDSCR_EL1_SysRegWrite_94ddb1e46aff4dfa_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_MPAM0_EL1_SysRegWrite_88f6c0c61a59ac23[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (MPAM0_EL1_SysRegWrite_88f6c0c61a59ac23 el op0 op1 CRn op2 CRm val_name) s"
  unfolding MPAM0_EL1_SysRegWrite_88f6c0c61a59ac23_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_MPAM2_EL2_write[traces_enabledI]:
  assumes "system_reg_access s"
  shows "traces_enabled (MPAM2_EL2_write val_name) s"
  unfolding MPAM2_EL2_write_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_MPAM1_EL1_write[traces_enabledI]:
  assumes "system_reg_access s"
  shows "traces_enabled (MPAM1_EL1_write val_name) s"
  unfolding MPAM1_EL1_write_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_MPAM1_EL12_SysRegWrite_2cbbb0edf5787671[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (MPAM1_EL12_SysRegWrite_2cbbb0edf5787671 el op0 op1 CRn op2 CRm val_name) s"
  unfolding MPAM1_EL12_SysRegWrite_2cbbb0edf5787671_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_MPAM1_EL1_SysRegWrite_cd02720a3298b1c6[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (MPAM1_EL1_SysRegWrite_cd02720a3298b1c6 el op0 op1 CRn op2 CRm val_name) s"
  unfolding MPAM1_EL1_SysRegWrite_cd02720a3298b1c6_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_MPAM2_EL2_SysRegWrite_d6bae8d18aebb554[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (MPAM2_EL2_SysRegWrite_d6bae8d18aebb554 el op0 op1 CRn op2 CRm val_name) s"
  unfolding MPAM2_EL2_SysRegWrite_d6bae8d18aebb554_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_MPAM3_EL3_SysRegWrite_bb55d8a9d90e05e3[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (MPAM3_EL3_SysRegWrite_bb55d8a9d90e05e3 el op0 op1 CRn op2 CRm val_name) s"
  unfolding MPAM3_EL3_SysRegWrite_bb55d8a9d90e05e3_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_MPAMHCR_EL2_SysRegWrite_e38755d6111336b8[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (MPAMHCR_EL2_SysRegWrite_e38755d6111336b8 el op0 op1 CRn op2 CRm val_name) s"
  unfolding MPAMHCR_EL2_SysRegWrite_e38755d6111336b8_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_MPAMVPM0_EL2_SysRegWrite_c00108111630aa84[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (MPAMVPM0_EL2_SysRegWrite_c00108111630aa84 el op0 op1 CRn op2 CRm val_name) s"
  unfolding MPAMVPM0_EL2_SysRegWrite_c00108111630aa84_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_MPAMVPM1_EL2_SysRegWrite_81a739cc4bd1cd46[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (MPAMVPM1_EL2_SysRegWrite_81a739cc4bd1cd46 el op0 op1 CRn op2 CRm val_name) s"
  unfolding MPAMVPM1_EL2_SysRegWrite_81a739cc4bd1cd46_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_MPAMVPM2_EL2_SysRegWrite_20a1b54bc18980b1[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (MPAMVPM2_EL2_SysRegWrite_20a1b54bc18980b1 el op0 op1 CRn op2 CRm val_name) s"
  unfolding MPAMVPM2_EL2_SysRegWrite_20a1b54bc18980b1_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_MPAMVPM3_EL2_SysRegWrite_d2a71d8e23cc67af[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (MPAMVPM3_EL2_SysRegWrite_d2a71d8e23cc67af el op0 op1 CRn op2 CRm val_name) s"
  unfolding MPAMVPM3_EL2_SysRegWrite_d2a71d8e23cc67af_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_MPAMVPM4_EL2_SysRegWrite_2d0a10731399829d[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (MPAMVPM4_EL2_SysRegWrite_2d0a10731399829d el op0 op1 CRn op2 CRm val_name) s"
  unfolding MPAMVPM4_EL2_SysRegWrite_2d0a10731399829d_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_MPAMVPM5_EL2_SysRegWrite_ec98ca57d40ac9ec[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (MPAMVPM5_EL2_SysRegWrite_ec98ca57d40ac9ec el op0 op1 CRn op2 CRm val_name) s"
  unfolding MPAMVPM5_EL2_SysRegWrite_ec98ca57d40ac9ec_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_MPAMVPM6_EL2_SysRegWrite_0934853fee68e9bd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (MPAMVPM6_EL2_SysRegWrite_0934853fee68e9bd el op0 op1 CRn op2 CRm val_name) s"
  unfolding MPAMVPM6_EL2_SysRegWrite_0934853fee68e9bd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_MPAMVPM7_EL2_SysRegWrite_dfb7f68750df7012[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (MPAMVPM7_EL2_SysRegWrite_dfb7f68750df7012 el op0 op1 CRn op2 CRm val_name) s"
  unfolding MPAMVPM7_EL2_SysRegWrite_dfb7f68750df7012_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_MPAMVPMV_EL2_SysRegWrite_abd8d27e91fadf85[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (MPAMVPMV_EL2_SysRegWrite_abd8d27e91fadf85 el op0 op1 CRn op2 CRm val_name) s"
  unfolding MPAMVPMV_EL2_SysRegWrite_abd8d27e91fadf85_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_OSDLR_EL1_SysRegWrite_591fd96d91652c64[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (OSDLR_EL1_SysRegWrite_591fd96d91652c64 el op0 op1 CRn op2 CRm val_name) s"
  unfolding OSDLR_EL1_SysRegWrite_591fd96d91652c64_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_OSDTRRX_EL1_SysRegWrite_6dc5d8521b60df8a[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (OSDTRRX_EL1_SysRegWrite_6dc5d8521b60df8a el op0 op1 CRn op2 CRm val_name) s"
  unfolding OSDTRRX_EL1_SysRegWrite_6dc5d8521b60df8a_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_OSDTRTX_EL1_SysRegWrite_9ba0c4a85d0c1de5[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (OSDTRTX_EL1_SysRegWrite_9ba0c4a85d0c1de5 el op0 op1 CRn op2 CRm val_name) s"
  unfolding OSDTRTX_EL1_SysRegWrite_9ba0c4a85d0c1de5_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_OSECCR_EL1_SysRegWrite_cabf381bfb822732[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (OSECCR_EL1_SysRegWrite_cabf381bfb822732 el op0 op1 CRn op2 CRm val_name) s"
  unfolding OSECCR_EL1_SysRegWrite_cabf381bfb822732_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_OSLAR_EL1_SysRegWrite_582d77c57653b2c4[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (OSLAR_EL1_SysRegWrite_582d77c57653b2c4 el op0 op1 CRn op2 CRm val_name) s"
  unfolding OSLAR_EL1_SysRegWrite_582d77c57653b2c4_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_PAR_EL1_SysRegWrite_aa92c70a4b5d5873[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (PAR_EL1_SysRegWrite_aa92c70a4b5d5873 el op0 op1 CRn op2 CRm val_name) s"
  unfolding PAR_EL1_SysRegWrite_aa92c70a4b5d5873_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_PMBLIMITR_EL1_SysRegWrite_ddfe2ba603df6628[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (PMBLIMITR_EL1_SysRegWrite_ddfe2ba603df6628 el op0 op1 CRn op2 CRm val_name) s"
  unfolding PMBLIMITR_EL1_SysRegWrite_ddfe2ba603df6628_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_PMBPTR_EL1_SysRegWrite_32441d8a7a2b9601[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (PMBPTR_EL1_SysRegWrite_32441d8a7a2b9601 el op0 op1 CRn op2 CRm val_name) s"
  unfolding PMBPTR_EL1_SysRegWrite_32441d8a7a2b9601_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_PMBSR_EL1_SysRegWrite_ff19dc948509312f[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (PMBSR_EL1_SysRegWrite_ff19dc948509312f el op0 op1 CRn op2 CRm val_name) s"
  unfolding PMBSR_EL1_SysRegWrite_ff19dc948509312f_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_PMCCFILTR_EL0_SysRegWrite_42277f001664525c[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (PMCCFILTR_EL0_SysRegWrite_42277f001664525c el op0 op1 CRn op2 CRm val_name) s"
  unfolding PMCCFILTR_EL0_SysRegWrite_42277f001664525c_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_PMCCNTR_EL0_SysRegWrite_1d21e0789830cbf9[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (PMCCNTR_EL0_SysRegWrite_1d21e0789830cbf9 el op0 op1 CRn op2 CRm val_name) s"
  unfolding PMCCNTR_EL0_SysRegWrite_1d21e0789830cbf9_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_PMCNTENCLR_EL0_SysRegWrite_bf2c4fae1a891e1b[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (PMCNTENCLR_EL0_SysRegWrite_bf2c4fae1a891e1b el op0 op1 CRn op2 CRm val_name) s"
  unfolding PMCNTENCLR_EL0_SysRegWrite_bf2c4fae1a891e1b_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_PMCNTENSET_EL0_SysRegWrite_227af2773d320cb1[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (PMCNTENSET_EL0_SysRegWrite_227af2773d320cb1 el op0 op1 CRn op2 CRm val_name) s"
  unfolding PMCNTENSET_EL0_SysRegWrite_227af2773d320cb1_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_PMCR_EL0_SysRegWrite_87ae64466e09f89a[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (PMCR_EL0_SysRegWrite_87ae64466e09f89a el op0 op1 CRn op2 CRm val_name) s"
  unfolding PMCR_EL0_SysRegWrite_87ae64466e09f89a_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_PMEVCNTR_EL0_SysRegWrite_c197579331ed9cbb[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (PMEVCNTR_EL0_SysRegWrite_c197579331ed9cbb el op0 op1 CRn op2 CRm val_name) s"
  unfolding PMEVCNTR_EL0_SysRegWrite_c197579331ed9cbb_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_PMEVTYPER_EL0_SysRegWrite_3e6ae16cd645ec0d[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (PMEVTYPER_EL0_SysRegWrite_3e6ae16cd645ec0d el op0 op1 CRn op2 CRm val_name) s"
  unfolding PMEVTYPER_EL0_SysRegWrite_3e6ae16cd645ec0d_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_PMINTENCLR_EL1_SysRegWrite_1ebd7bf3738fe872[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (PMINTENCLR_EL1_SysRegWrite_1ebd7bf3738fe872 el op0 op1 CRn op2 CRm val_name) s"
  unfolding PMINTENCLR_EL1_SysRegWrite_1ebd7bf3738fe872_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_PMINTENSET_EL1_SysRegWrite_dd2481ad892e3441[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (PMINTENSET_EL1_SysRegWrite_dd2481ad892e3441 el op0 op1 CRn op2 CRm val_name) s"
  unfolding PMINTENSET_EL1_SysRegWrite_dd2481ad892e3441_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_PMOVSCLR_EL0_SysRegWrite_9dfa73cda394af99[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (PMOVSCLR_EL0_SysRegWrite_9dfa73cda394af99 el op0 op1 CRn op2 CRm val_name) s"
  unfolding PMOVSCLR_EL0_SysRegWrite_9dfa73cda394af99_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_PMOVSSET_EL0_SysRegWrite_cfbbfe3b81fe4290[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (PMOVSSET_EL0_SysRegWrite_cfbbfe3b81fe4290 el op0 op1 CRn op2 CRm val_name) s"
  unfolding PMOVSSET_EL0_SysRegWrite_cfbbfe3b81fe4290_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_PMSCR_EL12_SysRegWrite_fef9a94f50c2763b[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (PMSCR_EL12_SysRegWrite_fef9a94f50c2763b el op0 op1 CRn op2 CRm val_name) s"
  unfolding PMSCR_EL12_SysRegWrite_fef9a94f50c2763b_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_PMSCR_EL1_SysRegWrite_9798a89ab6804fe0[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (PMSCR_EL1_SysRegWrite_9798a89ab6804fe0 el op0 op1 CRn op2 CRm val_name) s"
  unfolding PMSCR_EL1_SysRegWrite_9798a89ab6804fe0_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_PMSCR_EL2_SysRegWrite_02cd14dd325ed94b[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (PMSCR_EL2_SysRegWrite_02cd14dd325ed94b el op0 op1 CRn op2 CRm val_name) s"
  unfolding PMSCR_EL2_SysRegWrite_02cd14dd325ed94b_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_PMSELR_EL0_SysRegWrite_18613307de8564a3[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (PMSELR_EL0_SysRegWrite_18613307de8564a3 el op0 op1 CRn op2 CRm val_name) s"
  unfolding PMSELR_EL0_SysRegWrite_18613307de8564a3_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_PMSEVFR_EL1_SysRegWrite_6524c56cd8a10057[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (PMSEVFR_EL1_SysRegWrite_6524c56cd8a10057 el op0 op1 CRn op2 CRm val_name) s"
  unfolding PMSEVFR_EL1_SysRegWrite_6524c56cd8a10057_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_PMSFCR_EL1_SysRegWrite_44d58271848f0db1[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (PMSFCR_EL1_SysRegWrite_44d58271848f0db1 el op0 op1 CRn op2 CRm val_name) s"
  unfolding PMSFCR_EL1_SysRegWrite_44d58271848f0db1_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_PMSICR_EL1_SysRegWrite_1e74423ea1c96ae7[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (PMSICR_EL1_SysRegWrite_1e74423ea1c96ae7 el op0 op1 CRn op2 CRm val_name) s"
  unfolding PMSICR_EL1_SysRegWrite_1e74423ea1c96ae7_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_PMSIRR_EL1_SysRegWrite_bb25878486c35a36[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (PMSIRR_EL1_SysRegWrite_bb25878486c35a36 el op0 op1 CRn op2 CRm val_name) s"
  unfolding PMSIRR_EL1_SysRegWrite_bb25878486c35a36_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_PMSLATFR_EL1_SysRegWrite_5c8b43a6a65c8272[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (PMSLATFR_EL1_SysRegWrite_5c8b43a6a65c8272 el op0 op1 CRn op2 CRm val_name) s"
  unfolding PMSLATFR_EL1_SysRegWrite_5c8b43a6a65c8272_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_PMSWINC_EL0_SysRegWrite_cce1d915b163d5e3[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (PMSWINC_EL0_SysRegWrite_cce1d915b163d5e3 el op0 op1 CRn op2 CRm val_name) s"
  unfolding PMSWINC_EL0_SysRegWrite_cce1d915b163d5e3_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_PMUSERENR_EL0_SysRegWrite_e7535626e3360c36[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (PMUSERENR_EL0_SysRegWrite_e7535626e3360c36 el op0 op1 CRn op2 CRm val_name) s"
  unfolding PMUSERENR_EL0_SysRegWrite_e7535626e3360c36_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_PMXEVCNTR_EL0_SysRegWrite_20b0a6df43a7d4ef[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (PMXEVCNTR_EL0_SysRegWrite_20b0a6df43a7d4ef el op0 op1 CRn op2 CRm val_name) s"
  unfolding PMXEVCNTR_EL0_SysRegWrite_20b0a6df43a7d4ef_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_PMXEVTYPER_EL0_SysRegWrite_82fb55a6e723e983[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (PMXEVTYPER_EL0_SysRegWrite_82fb55a6e723e983 el op0 op1 CRn op2 CRm val_name) s"
  unfolding PMXEVTYPER_EL0_SysRegWrite_82fb55a6e723e983_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_RMR_EL1_SysRegWrite_0ae19f794f511c7a[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (RMR_EL1_SysRegWrite_0ae19f794f511c7a el op0 op1 CRn op2 CRm val_name) s"
  unfolding RMR_EL1_SysRegWrite_0ae19f794f511c7a_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_RMR_EL2_SysRegWrite_df7b9a989e2495d2[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (RMR_EL2_SysRegWrite_df7b9a989e2495d2 el op0 op1 CRn op2 CRm val_name) s"
  unfolding RMR_EL2_SysRegWrite_df7b9a989e2495d2_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_RMR_EL3_SysRegWrite_2849130fc457929e[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (RMR_EL3_SysRegWrite_2849130fc457929e el op0 op1 CRn op2 CRm val_name) s"
  unfolding RMR_EL3_SysRegWrite_2849130fc457929e_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_RSP_EL0_SysRegWrite_5b2edb6edd27507d[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (RSP_EL0_SysRegWrite_5b2edb6edd27507d el op0 op1 CRn op2 CRm val_name) s"
  unfolding RSP_EL0_SysRegWrite_5b2edb6edd27507d_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_RTPIDR_EL0_SysRegWrite_74d55919bd0ab5f3[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (RTPIDR_EL0_SysRegWrite_74d55919bd0ab5f3 el op0 op1 CRn op2 CRm val_name) s"
  unfolding RTPIDR_EL0_SysRegWrite_74d55919bd0ab5f3_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_S3_op1_CCn_CCm_op2_SysRegWrite_22dd63287f599042[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (S3_op1_CCn_CCm_op2_SysRegWrite_22dd63287f599042 el op0 op1 CRn op2 CRm val_name) s"
  unfolding S3_op1_CCn_CCm_op2_SysRegWrite_22dd63287f599042_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_SCR_EL3_SysRegWrite_020d082781fa9b72[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (SCR_EL3_SysRegWrite_020d082781fa9b72 el op0 op1 CRn op2 CRm val_name) s"
  unfolding SCR_EL3_SysRegWrite_020d082781fa9b72_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_SCTLR_EL12_SysRegWrite_302de25977d2a0ca[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (SCTLR_EL12_SysRegWrite_302de25977d2a0ca el op0 op1 CRn op2 CRm val_name) s"
  unfolding SCTLR_EL12_SysRegWrite_302de25977d2a0ca_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_SCTLR_EL1_SysRegWrite_711b0546c662c54d[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (SCTLR_EL1_SysRegWrite_711b0546c662c54d el op0 op1 CRn op2 CRm val_name) s"
  unfolding SCTLR_EL1_SysRegWrite_711b0546c662c54d_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_SCTLR_EL2_SysRegWrite_ff61a6f00288b28a[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (SCTLR_EL2_SysRegWrite_ff61a6f00288b28a el op0 op1 CRn op2 CRm val_name) s"
  unfolding SCTLR_EL2_SysRegWrite_ff61a6f00288b28a_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_SCTLR_EL3_SysRegWrite_5b7cc79e5ea93a8f[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (SCTLR_EL3_SysRegWrite_5b7cc79e5ea93a8f el op0 op1 CRn op2 CRm val_name) s"
  unfolding SCTLR_EL3_SysRegWrite_5b7cc79e5ea93a8f_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_SCXTNUM_EL0_write[traces_enabledI]:
  "traces_enabled (SCXTNUM_EL0_write val_name) s"
  unfolding SCXTNUM_EL0_write_def bind_assoc
  by (traces_enabledI)

lemma traces_enabled_SCXTNUM_EL0_SysRegWrite_9dbee2793d69c02e[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (SCXTNUM_EL0_SysRegWrite_9dbee2793d69c02e el op0 op1 CRn op2 CRm val_name) s"
  unfolding SCXTNUM_EL0_SysRegWrite_9dbee2793d69c02e_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_SCXTNUM_EL12_SysRegWrite_ba74367909393c9b[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (SCXTNUM_EL12_SysRegWrite_ba74367909393c9b el op0 op1 CRn op2 CRm val_name) s"
  unfolding SCXTNUM_EL12_SysRegWrite_ba74367909393c9b_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_SCXTNUM_EL1_SysRegWrite_6467f6f26a31cece[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (SCXTNUM_EL1_SysRegWrite_6467f6f26a31cece el op0 op1 CRn op2 CRm val_name) s"
  unfolding SCXTNUM_EL1_SysRegWrite_6467f6f26a31cece_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_SCXTNUM_EL2_SysRegWrite_2fcbb6503badb23c[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (SCXTNUM_EL2_SysRegWrite_2fcbb6503badb23c el op0 op1 CRn op2 CRm val_name) s"
  unfolding SCXTNUM_EL2_SysRegWrite_2fcbb6503badb23c_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_SCXTNUM_EL3_SysRegWrite_b39fe9ab09a67ecd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (SCXTNUM_EL3_SysRegWrite_b39fe9ab09a67ecd el op0 op1 CRn op2 CRm val_name) s"
  unfolding SCXTNUM_EL3_SysRegWrite_b39fe9ab09a67ecd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_SDER32_EL3_SysRegWrite_69011ff5e95ac923[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (SDER32_EL3_SysRegWrite_69011ff5e95ac923 el op0 op1 CRn op2 CRm val_name) s"
  unfolding SDER32_EL3_SysRegWrite_69011ff5e95ac923_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_SPSel_SysRegWrite_c849e120e8533c8c[traces_enabledI]:
  "traces_enabled (SPSel_SysRegWrite_c849e120e8533c8c el op0 op1 CRn op2 CRm val_name) s"
  unfolding SPSel_SysRegWrite_c849e120e8533c8c_def bind_assoc
  by (traces_enabledI)

lemma traces_enabled_SP_EL0_SysRegWrite_78f870c69d82f9e2[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (SP_EL0_SysRegWrite_78f870c69d82f9e2 el op0 op1 CRn op2 CRm val_name) s"
  unfolding SP_EL0_SysRegWrite_78f870c69d82f9e2_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_SP_EL1_SysRegWrite_84ae51cf4bf77caa[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (SP_EL1_SysRegWrite_84ae51cf4bf77caa el op0 op1 CRn op2 CRm val_name) s"
  unfolding SP_EL1_SysRegWrite_84ae51cf4bf77caa_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_SP_EL2_SysRegWrite_a29ffeac6d3856e5[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (SP_EL2_SysRegWrite_a29ffeac6d3856e5 el op0 op1 CRn op2 CRm val_name) s"
  unfolding SP_EL2_SysRegWrite_a29ffeac6d3856e5_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_TCR_EL12_SysRegWrite_64a7f44c6ddaa0f8[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (TCR_EL12_SysRegWrite_64a7f44c6ddaa0f8 el op0 op1 CRn op2 CRm val_name) s"
  unfolding TCR_EL12_SysRegWrite_64a7f44c6ddaa0f8_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_TCR_EL1_SysRegWrite_c27e6fc190bb0f0b[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (TCR_EL1_SysRegWrite_c27e6fc190bb0f0b el op0 op1 CRn op2 CRm val_name) s"
  unfolding TCR_EL1_SysRegWrite_c27e6fc190bb0f0b_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_TCR_EL2_SysRegWrite_5e38279a245750c4[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (TCR_EL2_SysRegWrite_5e38279a245750c4 el op0 op1 CRn op2 CRm val_name) s"
  unfolding TCR_EL2_SysRegWrite_5e38279a245750c4_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_TCR_EL3_SysRegWrite_3b3587015a3d20f4[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (TCR_EL3_SysRegWrite_3b3587015a3d20f4 el op0 op1 CRn op2 CRm val_name) s"
  unfolding TCR_EL3_SysRegWrite_3b3587015a3d20f4_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_TPIDRRO_EL0_SysRegWrite_20bedffb2581e57d[traces_enabledI]:
  "traces_enabled (TPIDRRO_EL0_SysRegWrite_20bedffb2581e57d el op0 op1 CRn op2 CRm val_name) s"
  unfolding TPIDRRO_EL0_SysRegWrite_20bedffb2581e57d_def bind_assoc
  by (traces_enabledI)

lemma traces_enabled_TPIDR_EL0_SysRegWrite_6b1ef76c828f0bf5[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (TPIDR_EL0_SysRegWrite_6b1ef76c828f0bf5 el op0 op1 CRn op2 CRm val_name) s"
  unfolding TPIDR_EL0_SysRegWrite_6b1ef76c828f0bf5_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_TPIDR_EL1_SysRegWrite_566127c19bf948d1[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (TPIDR_EL1_SysRegWrite_566127c19bf948d1 el op0 op1 CRn op2 CRm val_name) s"
  unfolding TPIDR_EL1_SysRegWrite_566127c19bf948d1_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_TPIDR_EL2_SysRegWrite_adfab02a898d4b19[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (TPIDR_EL2_SysRegWrite_adfab02a898d4b19 el op0 op1 CRn op2 CRm val_name) s"
  unfolding TPIDR_EL2_SysRegWrite_adfab02a898d4b19_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_TPIDR_EL3_SysRegWrite_08e0e9cc5d3f6f5c[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (TPIDR_EL3_SysRegWrite_08e0e9cc5d3f6f5c el op0 op1 CRn op2 CRm val_name) s"
  unfolding TPIDR_EL3_SysRegWrite_08e0e9cc5d3f6f5c_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_TTBR0_EL12_SysRegWrite_fd9df8519bfad5c0[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (TTBR0_EL12_SysRegWrite_fd9df8519bfad5c0 el op0 op1 CRn op2 CRm val_name) s"
  unfolding TTBR0_EL12_SysRegWrite_fd9df8519bfad5c0_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_TTBR0_EL1_SysRegWrite_8a149790a79e2eab[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (TTBR0_EL1_SysRegWrite_8a149790a79e2eab el op0 op1 CRn op2 CRm val_name) s"
  unfolding TTBR0_EL1_SysRegWrite_8a149790a79e2eab_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_TTBR0_EL2_SysRegWrite_7cd39d4a24a70e7f[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (TTBR0_EL2_SysRegWrite_7cd39d4a24a70e7f el op0 op1 CRn op2 CRm val_name) s"
  unfolding TTBR0_EL2_SysRegWrite_7cd39d4a24a70e7f_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_TTBR0_EL3_SysRegWrite_7e091a8effc9ee7f[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (TTBR0_EL3_SysRegWrite_7e091a8effc9ee7f el op0 op1 CRn op2 CRm val_name) s"
  unfolding TTBR0_EL3_SysRegWrite_7e091a8effc9ee7f_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_TTBR1_EL12_SysRegWrite_4fbeb1f28c2e8107[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (TTBR1_EL12_SysRegWrite_4fbeb1f28c2e8107 el op0 op1 CRn op2 CRm val_name) s"
  unfolding TTBR1_EL12_SysRegWrite_4fbeb1f28c2e8107_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_TTBR1_EL1_SysRegWrite_89690e4d3c87217b[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (TTBR1_EL1_SysRegWrite_89690e4d3c87217b el op0 op1 CRn op2 CRm val_name) s"
  unfolding TTBR1_EL1_SysRegWrite_89690e4d3c87217b_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_TTBR1_EL2_SysRegWrite_59fad32bc548b47a[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (TTBR1_EL2_SysRegWrite_59fad32bc548b47a el op0 op1 CRn op2 CRm val_name) s"
  unfolding TTBR1_EL2_SysRegWrite_59fad32bc548b47a_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_VBAR_EL12_SysRegWrite_a20f8f7f07b5cf7a[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (VBAR_EL12_SysRegWrite_a20f8f7f07b5cf7a el op0 op1 CRn op2 CRm val_name) s"
  unfolding VBAR_EL12_SysRegWrite_a20f8f7f07b5cf7a_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_VBAR_EL1_SysRegWrite_29ba7540e032fce6[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (VBAR_EL1_SysRegWrite_29ba7540e032fce6 el op0 op1 CRn op2 CRm val_name) s"
  unfolding VBAR_EL1_SysRegWrite_29ba7540e032fce6_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_VBAR_EL2_SysRegWrite_d5657e8591e8e22a[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (VBAR_EL2_SysRegWrite_d5657e8591e8e22a el op0 op1 CRn op2 CRm val_name) s"
  unfolding VBAR_EL2_SysRegWrite_d5657e8591e8e22a_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_VBAR_EL3_SysRegWrite_1da603c27eb5f668[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (VBAR_EL3_SysRegWrite_1da603c27eb5f668 el op0 op1 CRn op2 CRm val_name) s"
  unfolding VBAR_EL3_SysRegWrite_1da603c27eb5f668_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_VDISR_EL2_SysRegWrite_8b2c23874e253f64[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (VDISR_EL2_SysRegWrite_8b2c23874e253f64 el op0 op1 CRn op2 CRm val_name) s"
  unfolding VDISR_EL2_SysRegWrite_8b2c23874e253f64_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_VMPIDR_EL2_SysRegWrite_c153d7c8b5628bd5[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (VMPIDR_EL2_SysRegWrite_c153d7c8b5628bd5 el op0 op1 CRn op2 CRm val_name) s"
  unfolding VMPIDR_EL2_SysRegWrite_c153d7c8b5628bd5_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_VPIDR_EL2_SysRegWrite_0dbf139af5a73d1f[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (VPIDR_EL2_SysRegWrite_0dbf139af5a73d1f el op0 op1 CRn op2 CRm val_name) s"
  unfolding VPIDR_EL2_SysRegWrite_0dbf139af5a73d1f_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_VSESR_EL2_SysRegWrite_e989f4bcf0ae8aa6[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (VSESR_EL2_SysRegWrite_e989f4bcf0ae8aa6 el op0 op1 CRn op2 CRm val_name) s"
  unfolding VSESR_EL2_SysRegWrite_e989f4bcf0ae8aa6_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_VTCR_EL2_SysRegWrite_d49abb8b3aa0eff3[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (VTCR_EL2_SysRegWrite_d49abb8b3aa0eff3 el op0 op1 CRn op2 CRm val_name) s"
  unfolding VTCR_EL2_SysRegWrite_d49abb8b3aa0eff3_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_VTTBR_EL2_SysRegWrite_5198ee0e793550a5[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (VTTBR_EL2_SysRegWrite_5198ee0e793550a5 el op0 op1 CRn op2 CRm val_name) s"
  unfolding VTTBR_EL2_SysRegWrite_5198ee0e793550a5_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_AArch64_AutoGen_SysRegWrite[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (AArch64_AutoGen_SysRegWrite el op0 op1 CRn op2 CRm val_name) s"
  unfolding AArch64_AutoGen_SysRegWrite_def bind_assoc
  by (traces_enabled_step intro: assms)+

lemma traces_enabled_C_set[traces_enabledI]:
  assumes "value_name \<in> derivable_caps s"
  shows "traces_enabled (C_set n value_name) s"
  unfolding C_set_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_AArch64_ResetGeneralRegisters[traces_enabledI]:
  "traces_enabled (AArch64_ResetGeneralRegisters arg0) s"
  unfolding AArch64_ResetGeneralRegisters_def bind_assoc
  by (traces_enabledI)

lemma traces_enabled_AArch64_SysRegWrite[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "(op0 = 3 \<and> op1 \<in> {0, 4, 6} \<and> op2 = 2 \<and> crn = 12 \<and> crm = 0) \<longrightarrow> no_system_reg_access"
  shows "traces_enabled (AArch64_SysRegWrite op0 op1 crn crm op2 val) s"
  unfolding AArch64_SysRegWrite_def bind_assoc
  by (traces_enabledI assms: assms Run_AArch64_AutoGen_SysRegWrite_RMR_EL_system_reg_access[OF _ inv_sysreg_trace_assms]; blast)

lemma traces_enabled_CDBGDTR_EL0_CapSysRegWrite_336052f10e4a36b7[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "val_name \<in> derivable_caps s"
  shows "traces_enabled (CDBGDTR_EL0_CapSysRegWrite_336052f10e4a36b7 el op0 op1 CRn op2 CRm val_name) s"
  unfolding CDBGDTR_EL0_CapSysRegWrite_336052f10e4a36b7_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CDLR_EL0_CapSysRegWrite_2763be7daadf3c03[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "val_name \<in> derivable_caps s"
  shows "traces_enabled (CDLR_EL0_CapSysRegWrite_2763be7daadf3c03 el op0 op1 CRn op2 CRm val_name) s"
  unfolding CDLR_EL0_CapSysRegWrite_2763be7daadf3c03_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CELR_EL12_CapSysRegWrite_a1507df00ba9d725[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "val_name \<in> derivable_caps s"
  shows "traces_enabled (CELR_EL12_CapSysRegWrite_a1507df00ba9d725 el op0 op1 CRn op2 CRm val_name) s"
  unfolding CELR_EL12_CapSysRegWrite_a1507df00ba9d725_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CELR_EL1_CapSysRegWrite_33a9b4f0fad89fe8[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "val_name \<in> derivable_caps s"
  shows "traces_enabled (CELR_EL1_CapSysRegWrite_33a9b4f0fad89fe8 el op0 op1 CRn op2 CRm val_name) s"
  unfolding CELR_EL1_CapSysRegWrite_33a9b4f0fad89fe8_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CELR_EL2_CapSysRegWrite_8d32fe1dd5ad0417[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "val_name \<in> derivable_caps s"
  shows "traces_enabled (CELR_EL2_CapSysRegWrite_8d32fe1dd5ad0417 el op0 op1 CRn op2 CRm val_name) s"
  unfolding CELR_EL2_CapSysRegWrite_8d32fe1dd5ad0417_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CELR_EL3_CapSysRegWrite_55e82fec5d907003[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "val_name \<in> derivable_caps s"
  shows "traces_enabled (CELR_EL3_CapSysRegWrite_55e82fec5d907003 el op0 op1 CRn op2 CRm val_name) s"
  unfolding CELR_EL3_CapSysRegWrite_55e82fec5d907003_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CID_EL0_CapSysRegWrite_8c1c5cf69181759f[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "val_name \<in> derivable_caps s"
  shows "traces_enabled (CID_EL0_CapSysRegWrite_8c1c5cf69181759f el op0 op1 CRn op2 CRm val_name) s"
  unfolding CID_EL0_CapSysRegWrite_8c1c5cf69181759f_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CSP_EL0_CapSysRegWrite_ee1d127810ef0f04[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "val_name \<in> derivable_caps s"
  shows "traces_enabled (CSP_EL0_CapSysRegWrite_ee1d127810ef0f04 el op0 op1 CRn op2 CRm val_name) s"
  unfolding CSP_EL0_CapSysRegWrite_ee1d127810ef0f04_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CSP_EL1_CapSysRegWrite_f4579d836810c21a[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "val_name \<in> derivable_caps s"
  shows "traces_enabled (CSP_EL1_CapSysRegWrite_f4579d836810c21a el op0 op1 CRn op2 CRm val_name) s"
  unfolding CSP_EL1_CapSysRegWrite_f4579d836810c21a_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CSP_EL2_CapSysRegWrite_59c69d74679ef283[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "val_name \<in> derivable_caps s"
  shows "traces_enabled (CSP_EL2_CapSysRegWrite_59c69d74679ef283 el op0 op1 CRn op2 CRm val_name) s"
  unfolding CSP_EL2_CapSysRegWrite_59c69d74679ef283_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CTPIDRRO_EL0_CapSysRegWrite_e64109ff95ad4800[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "val_name \<in> derivable_caps s"
  shows "traces_enabled (CTPIDRRO_EL0_CapSysRegWrite_e64109ff95ad4800 el op0 op1 CRn op2 CRm val_name) s"
  unfolding CTPIDRRO_EL0_CapSysRegWrite_e64109ff95ad4800_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CTPIDR_EL0_CapSysRegWrite_8f94c4d256adadf0[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "val_name \<in> derivable_caps s"
  shows "traces_enabled (CTPIDR_EL0_CapSysRegWrite_8f94c4d256adadf0 el op0 op1 CRn op2 CRm val_name) s"
  unfolding CTPIDR_EL0_CapSysRegWrite_8f94c4d256adadf0_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CTPIDR_EL1_CapSysRegWrite_3190df090d2d128f[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "val_name \<in> derivable_caps s"
  shows "traces_enabled (CTPIDR_EL1_CapSysRegWrite_3190df090d2d128f el op0 op1 CRn op2 CRm val_name) s"
  unfolding CTPIDR_EL1_CapSysRegWrite_3190df090d2d128f_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CTPIDR_EL2_CapSysRegWrite_a740113e578c9b32[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "val_name \<in> derivable_caps s"
  shows "traces_enabled (CTPIDR_EL2_CapSysRegWrite_a740113e578c9b32 el op0 op1 CRn op2 CRm val_name) s"
  unfolding CTPIDR_EL2_CapSysRegWrite_a740113e578c9b32_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CTPIDR_EL3_CapSysRegWrite_376b7d525b15b21b[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "val_name \<in> derivable_caps s"
  shows "traces_enabled (CTPIDR_EL3_CapSysRegWrite_376b7d525b15b21b el op0 op1 CRn op2 CRm val_name) s"
  unfolding CTPIDR_EL3_CapSysRegWrite_376b7d525b15b21b_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CVBAR_EL12_CapSysRegWrite_3fd157cf974c31e5[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "val_name \<in> derivable_caps s"
  shows "traces_enabled (CVBAR_EL12_CapSysRegWrite_3fd157cf974c31e5 el op0 op1 CRn op2 CRm val_name) s"
  unfolding CVBAR_EL12_CapSysRegWrite_3fd157cf974c31e5_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CVBAR_EL1_CapSysRegWrite_bbad0575f41fce2f[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "val_name \<in> derivable_caps s"
  shows "traces_enabled (CVBAR_EL1_CapSysRegWrite_bbad0575f41fce2f el op0 op1 CRn op2 CRm val_name) s"
  unfolding CVBAR_EL1_CapSysRegWrite_bbad0575f41fce2f_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CVBAR_EL2_CapSysRegWrite_2a412e2b2c0a0a2b[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "val_name \<in> derivable_caps s"
  shows "traces_enabled (CVBAR_EL2_CapSysRegWrite_2a412e2b2c0a0a2b el op0 op1 CRn op2 CRm val_name) s"
  unfolding CVBAR_EL2_CapSysRegWrite_2a412e2b2c0a0a2b_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CVBAR_EL3_CapSysRegWrite_f3c8bbee84b292db[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "val_name \<in> derivable_caps s"
  shows "traces_enabled (CVBAR_EL3_CapSysRegWrite_f3c8bbee84b292db el op0 op1 CRn op2 CRm val_name) s"
  unfolding CVBAR_EL3_CapSysRegWrite_f3c8bbee84b292db_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_DDC_CapSysRegWrite_9bc98e4e82148914[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "val_name \<in> derivable_caps s"
  shows "traces_enabled (DDC_CapSysRegWrite_9bc98e4e82148914 el op0 op1 CRn op2 CRm val_name) s"
  unfolding DDC_CapSysRegWrite_9bc98e4e82148914_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_DDC_EL0_CapSysRegWrite_1a928678ff9b43a6[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "val_name \<in> derivable_caps s"
  shows "traces_enabled (DDC_EL0_CapSysRegWrite_1a928678ff9b43a6 el op0 op1 CRn op2 CRm val_name) s"
  unfolding DDC_EL0_CapSysRegWrite_1a928678ff9b43a6_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_DDC_EL1_CapSysRegWrite_e7ecb5b1f0c49d28[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "val_name \<in> derivable_caps s"
  shows "traces_enabled (DDC_EL1_CapSysRegWrite_e7ecb5b1f0c49d28 el op0 op1 CRn op2 CRm val_name) s"
  unfolding DDC_EL1_CapSysRegWrite_e7ecb5b1f0c49d28_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_DDC_EL2_CapSysRegWrite_b4142a2dcadf2a34[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "val_name \<in> derivable_caps s"
  shows "traces_enabled (DDC_EL2_CapSysRegWrite_b4142a2dcadf2a34 el op0 op1 CRn op2 CRm val_name) s"
  unfolding DDC_EL2_CapSysRegWrite_b4142a2dcadf2a34_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_RCSP_EL0_CapSysRegWrite_d8f83400674fbeeb[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "val_name \<in> derivable_caps s"
  shows "traces_enabled (RCSP_EL0_CapSysRegWrite_d8f83400674fbeeb el op0 op1 CRn op2 CRm val_name) s"
  unfolding RCSP_EL0_CapSysRegWrite_d8f83400674fbeeb_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_RCTPIDR_EL0_CapSysRegWrite_27f7c47e137c72f8[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "val_name \<in> derivable_caps s"
  shows "traces_enabled (RCTPIDR_EL0_CapSysRegWrite_27f7c47e137c72f8 el op0 op1 CRn op2 CRm val_name) s"
  unfolding RCTPIDR_EL0_CapSysRegWrite_27f7c47e137c72f8_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_RDDC_EL0_CapSysRegWrite_c528d1b2eb785ad7[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "val_name \<in> derivable_caps s"
  shows "traces_enabled (RDDC_EL0_CapSysRegWrite_c528d1b2eb785ad7 el op0 op1 CRn op2 CRm val_name) s"
  unfolding RDDC_EL0_CapSysRegWrite_c528d1b2eb785ad7_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_AArch64_AutoGen_CapSysRegWrite[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "val_name \<in> derivable_caps s"
  shows "traces_enabled (AArch64_AutoGen_CapSysRegWrite el op0 op1 CRn op2 CRm val_name) s"
  unfolding AArch64_AutoGen_CapSysRegWrite_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_DDC_set[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "value_name \<in> derivable_caps s"
  shows "traces_enabled (DDC_set value_name) s"
  unfolding DDC_set_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_AArch64_CapSysRegWrite[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "val_name \<in> derivable_caps s"
  shows "traces_enabled (AArch64_CapSysRegWrite op0 op1 crn crm op2 val_name) s"
  unfolding AArch64_CapSysRegWrite_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ALLE1IS_SysOpsWrite_8b81b55e2116aad3[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ALLE1IS_SysOpsWrite_8b81b55e2116aad3 el op0 op1 CRn op2 CRm val_name) s"
  unfolding ALLE1IS_SysOpsWrite_8b81b55e2116aad3_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ALLE1_SysOpsWrite_69364bedc72cbe96[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ALLE1_SysOpsWrite_69364bedc72cbe96 el op0 op1 CRn op2 CRm val_name) s"
  unfolding ALLE1_SysOpsWrite_69364bedc72cbe96_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_AArch64_UndefinedFault[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (AArch64_UndefinedFault arg0) s"
  unfolding AArch64_UndefinedFault_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_UndefinedFault[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (UndefinedFault arg0) s"
  unfolding UndefinedFault_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_TLBI_ALLE2IS[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (TLBI_ALLE2IS arg0) s"
  unfolding TLBI_ALLE2IS_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ALLE2IS_SysOpsWrite_3a173239947b2c25[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ALLE2IS_SysOpsWrite_3a173239947b2c25 el op0 op1 CRn op2 CRm val_name) s"
  unfolding ALLE2IS_SysOpsWrite_3a173239947b2c25_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_TLBI_ALLE2[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (TLBI_ALLE2 arg0) s"
  unfolding TLBI_ALLE2_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ALLE2_SysOpsWrite_19c7b5110a5efe1d[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ALLE2_SysOpsWrite_19c7b5110a5efe1d el op0 op1 CRn op2 CRm val_name) s"
  unfolding ALLE2_SysOpsWrite_19c7b5110a5efe1d_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ALLE3IS_SysOpsWrite_e64b79b4c41910fb[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ALLE3IS_SysOpsWrite_e64b79b4c41910fb el op0 op1 CRn op2 CRm val_name) s"
  unfolding ALLE3IS_SysOpsWrite_e64b79b4c41910fb_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ALLE3_SysOpsWrite_5835ce2f987f3d36[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ALLE3_SysOpsWrite_5835ce2f987f3d36 el op0 op1 CRn op2 CRm val_name) s"
  unfolding ALLE3_SysOpsWrite_5835ce2f987f3d36_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ASIDE1IS_SysOpsWrite_5a5dff91f113e41e[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ASIDE1IS_SysOpsWrite_5a5dff91f113e41e el op0 op1 CRn op2 CRm val_name) s"
  unfolding ASIDE1IS_SysOpsWrite_5a5dff91f113e41e_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ASIDE1_SysOpsWrite_7ba7a3df395925e0[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ASIDE1_SysOpsWrite_7ba7a3df395925e0 el op0 op1 CRn op2 CRm val_name) s"
  unfolding ASIDE1_SysOpsWrite_7ba7a3df395925e0_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_DC_CISW[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (DC_CISW val_name) s"
  unfolding DC_CISW_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CISW_SysOpsWrite_5321b1c3157dccce[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CISW_SysOpsWrite_5321b1c3157dccce el op0 op1 CRn op2 CRm val_name) s"
  unfolding CISW_SysOpsWrite_5321b1c3157dccce_def bind_assoc
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

lemma traces_enabled_DC_CIVAC[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (DC_CIVAC val_name) s"
  unfolding DC_CIVAC_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_VAddress[traces_enabledI]:
  "traces_enabled (VAddress addr) s"
  unfolding VAddress_def bind_assoc
  by (traces_enabledI)

lemma traces_enabled_MorelloCheckForCMO[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "cval \<in> derivable_caps s"
  shows "traces_enabled (MorelloCheckForCMO cval requested_perms acctype) s"
  unfolding MorelloCheckForCMO_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_DC_CIVAC0[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (DC_CIVAC0 val_name__arg) s"
  unfolding DC_CIVAC0_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CIVAC_SysOpsWrite_47ad60ecb930d217[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CIVAC_SysOpsWrite_47ad60ecb930d217 el op0 op1 CRn op2 CRm val_name) s"
  unfolding CIVAC_SysOpsWrite_47ad60ecb930d217_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_DC_CSW[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (DC_CSW val_name) s"
  unfolding DC_CSW_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CSW_SysOpsWrite_9544819da3ebaa1b[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CSW_SysOpsWrite_9544819da3ebaa1b el op0 op1 CRn op2 CRm val_name) s"
  unfolding CSW_SysOpsWrite_9544819da3ebaa1b_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_DC_CVAC[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (DC_CVAC val_name) s"
  unfolding DC_CVAC_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_DC_CVAC0[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (DC_CVAC0 val_name__arg) s"
  unfolding DC_CVAC0_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CVAC_SysOpsWrite_c7d2e911c691cc6b[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CVAC_SysOpsWrite_c7d2e911c691cc6b el op0 op1 CRn op2 CRm val_name) s"
  unfolding CVAC_SysOpsWrite_c7d2e911c691cc6b_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_DC_CVAP[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (DC_CVAP val_name) s"
  unfolding DC_CVAP_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_DC_CVADP[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (DC_CVADP val_name) s"
  unfolding DC_CVADP_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CVADP_SysOpsWrite_9953ef108c01d34a[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CVADP_SysOpsWrite_9953ef108c01d34a el op0 op1 CRn op2 CRm val_name) s"
  unfolding CVADP_SysOpsWrite_9953ef108c01d34a_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CVAP_SysOpsWrite_a43f75867888e74a[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CVAP_SysOpsWrite_a43f75867888e74a el op0 op1 CRn op2 CRm val_name) s"
  unfolding CVAP_SysOpsWrite_a43f75867888e74a_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_DC_CVAU[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (DC_CVAU val_name) s"
  unfolding DC_CVAU_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_DC_CVAU0[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (DC_CVAU0 val_name__arg) s"
  unfolding DC_CVAU0_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CVAU_SysOpsWrite_4a72bbc98a17973c[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CVAU_SysOpsWrite_4a72bbc98a17973c el op0 op1 CRn op2 CRm val_name) s"
  unfolding CVAU_SysOpsWrite_4a72bbc98a17973c_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_IC_IALLUIS[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (IC_IALLUIS arg0) s"
  unfolding IC_IALLUIS_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_IALLUIS_SysOpsWrite_9a906c8365100aff[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (IALLUIS_SysOpsWrite_9a906c8365100aff el op0 op1 CRn op2 CRm val_name) s"
  unfolding IALLUIS_SysOpsWrite_9a906c8365100aff_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_IC_IALLU[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (IC_IALLU arg0) s"
  unfolding IC_IALLU_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_IALLU_SysOpsWrite_81563797a4921929[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (IALLU_SysOpsWrite_81563797a4921929 el op0 op1 CRn op2 CRm val_name) s"
  unfolding IALLU_SysOpsWrite_81563797a4921929_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_IPAS2E1IS_SysOpsWrite_ed4be1feae90b987[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (IPAS2E1IS_SysOpsWrite_ed4be1feae90b987 el op0 op1 CRn op2 CRm val_name) s"
  unfolding IPAS2E1IS_SysOpsWrite_ed4be1feae90b987_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_IPAS2E1_SysOpsWrite_a65fef0d99f9428f[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (IPAS2E1_SysOpsWrite_a65fef0d99f9428f el op0 op1 CRn op2 CRm val_name) s"
  unfolding IPAS2E1_SysOpsWrite_a65fef0d99f9428f_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_IPAS2LE1IS_SysOpsWrite_5a72848dfefa19f3[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (IPAS2LE1IS_SysOpsWrite_5a72848dfefa19f3 el op0 op1 CRn op2 CRm val_name) s"
  unfolding IPAS2LE1IS_SysOpsWrite_5a72848dfefa19f3_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_IPAS2LE1_SysOpsWrite_10ca7ac6abdfed50[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (IPAS2LE1_SysOpsWrite_10ca7ac6abdfed50 el op0 op1 CRn op2 CRm val_name) s"
  unfolding IPAS2LE1_SysOpsWrite_10ca7ac6abdfed50_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_DC_ISW[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (DC_ISW val_name) s"
  unfolding DC_ISW_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ISW_SysOpsWrite_d5fceb001aa0aa7a[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ISW_SysOpsWrite_d5fceb001aa0aa7a el op0 op1 CRn op2 CRm val_name) s"
  unfolding ISW_SysOpsWrite_d5fceb001aa0aa7a_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_DC_IVAC[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (DC_IVAC val_name) s"
  unfolding DC_IVAC_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_DC_IVAC0[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (DC_IVAC0 val_name__arg) s"
  unfolding DC_IVAC0_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_IVAC_SysOpsWrite_41b93e0e56e4f107[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (IVAC_SysOpsWrite_41b93e0e56e4f107 el op0 op1 CRn op2 CRm val_name) s"
  unfolding IVAC_SysOpsWrite_41b93e0e56e4f107_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_IC_IVAU[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (IC_IVAU val_name) s"
  unfolding IC_IVAU_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_IVAU_SysOpsWrite_2dfe97b748dd324e[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (IVAU_SysOpsWrite_2dfe97b748dd324e el op0 op1 CRn op2 CRm val_name) s"
  unfolding IVAU_SysOpsWrite_2dfe97b748dd324e_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_RCTX_SysOpsWrite_bcc8cd10f2e68999[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (RCTX_SysOpsWrite_bcc8cd10f2e68999 el op0 op1 CRn op2 CRm val_name) s"
  unfolding RCTX_SysOpsWrite_bcc8cd10f2e68999_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_RCTX_SysOpsWrite_c287513d0d3e8e92[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (RCTX_SysOpsWrite_c287513d0d3e8e92 el op0 op1 CRn op2 CRm val_name) s"
  unfolding RCTX_SysOpsWrite_c287513d0d3e8e92_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_RCTX_SysOpsWrite_d614ec87236c038f[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (RCTX_SysOpsWrite_d614ec87236c038f el op0 op1 CRn op2 CRm val_name) s"
  unfolding RCTX_SysOpsWrite_d614ec87236c038f_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_AArch64_AT_S1Ex[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (AArch64_AT_S1Ex val_name el iswrite) s"
  unfolding AArch64_AT_S1Ex_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_AArch64_AT_S12Ex[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (AArch64_AT_S12Ex val_name el iswrite) s"
  unfolding AArch64_AT_S12Ex_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_AT_S12E0R[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (AT_S12E0R val_name) s"
  unfolding AT_S12E0R_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_AT_S1E0R[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (AT_S1E0R val_name) s"
  unfolding AT_S1E0R_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_S12E0R_SysOpsWrite_4df3d544cba811b7[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (S12E0R_SysOpsWrite_4df3d544cba811b7 el op0 op1 CRn op2 CRm val_name) s"
  unfolding S12E0R_SysOpsWrite_4df3d544cba811b7_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_AT_S12E0W[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (AT_S12E0W val_name) s"
  unfolding AT_S12E0W_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_AT_S1E0W[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (AT_S1E0W val_name) s"
  unfolding AT_S1E0W_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_S12E0W_SysOpsWrite_1dbb37d4af097406[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (S12E0W_SysOpsWrite_1dbb37d4af097406 el op0 op1 CRn op2 CRm val_name) s"
  unfolding S12E0W_SysOpsWrite_1dbb37d4af097406_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_AT_S12E1R[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (AT_S12E1R val_name) s"
  unfolding AT_S12E1R_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_AT_S1E1R[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (AT_S1E1R val_name) s"
  unfolding AT_S1E1R_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_S12E1R_SysOpsWrite_e44276c8f24d398f[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (S12E1R_SysOpsWrite_e44276c8f24d398f el op0 op1 CRn op2 CRm val_name) s"
  unfolding S12E1R_SysOpsWrite_e44276c8f24d398f_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_AT_S12E1W[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (AT_S12E1W val_name) s"
  unfolding AT_S12E1W_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_AT_S1E1W[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (AT_S1E1W val_name) s"
  unfolding AT_S1E1W_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_S12E1W_SysOpsWrite_c8b72d75cad90601[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (S12E1W_SysOpsWrite_c8b72d75cad90601 el op0 op1 CRn op2 CRm val_name) s"
  unfolding S12E1W_SysOpsWrite_c8b72d75cad90601_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_S1E0R_SysOpsWrite_0a1e21ea5b4c8722[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (S1E0R_SysOpsWrite_0a1e21ea5b4c8722 el op0 op1 CRn op2 CRm val_name) s"
  unfolding S1E0R_SysOpsWrite_0a1e21ea5b4c8722_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_S1E0W_SysOpsWrite_d102d49fd92af65a[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (S1E0W_SysOpsWrite_d102d49fd92af65a el op0 op1 CRn op2 CRm val_name) s"
  unfolding S1E0W_SysOpsWrite_d102d49fd92af65a_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_AT_S1E1RP[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (AT_S1E1RP val_name) s"
  unfolding AT_S1E1RP_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_S1E1RP_SysOpsWrite_4a6b1f71ee0182ab[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (S1E1RP_SysOpsWrite_4a6b1f71ee0182ab el op0 op1 CRn op2 CRm val_name) s"
  unfolding S1E1RP_SysOpsWrite_4a6b1f71ee0182ab_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_S1E1R_SysOpsWrite_018a577644c5d23c[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (S1E1R_SysOpsWrite_018a577644c5d23c el op0 op1 CRn op2 CRm val_name) s"
  unfolding S1E1R_SysOpsWrite_018a577644c5d23c_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_AT_S1E1WP[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (AT_S1E1WP val_name) s"
  unfolding AT_S1E1WP_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_S1E1WP_SysOpsWrite_bb1ddb9112effe2a[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (S1E1WP_SysOpsWrite_bb1ddb9112effe2a el op0 op1 CRn op2 CRm val_name) s"
  unfolding S1E1WP_SysOpsWrite_bb1ddb9112effe2a_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_S1E1W_SysOpsWrite_df64f2f63c0911fd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (S1E1W_SysOpsWrite_df64f2f63c0911fd el op0 op1 CRn op2 CRm val_name) s"
  unfolding S1E1W_SysOpsWrite_df64f2f63c0911fd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_AT_S1E2R[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (AT_S1E2R val_name) s"
  unfolding AT_S1E2R_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_S1E2R_SysOpsWrite_5e865a96c06417c8[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (S1E2R_SysOpsWrite_5e865a96c06417c8 el op0 op1 CRn op2 CRm val_name) s"
  unfolding S1E2R_SysOpsWrite_5e865a96c06417c8_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_AT_S1E2W[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (AT_S1E2W val_name) s"
  unfolding AT_S1E2W_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_S1E2W_SysOpsWrite_1649806418453f02[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (S1E2W_SysOpsWrite_1649806418453f02 el op0 op1 CRn op2 CRm val_name) s"
  unfolding S1E2W_SysOpsWrite_1649806418453f02_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_AT_S1E3R[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (AT_S1E3R val_name) s"
  unfolding AT_S1E3R_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_S1E3R_SysOpsWrite_6476f20e79e358be[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (S1E3R_SysOpsWrite_6476f20e79e358be el op0 op1 CRn op2 CRm val_name) s"
  unfolding S1E3R_SysOpsWrite_6476f20e79e358be_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_AT_S1E3W[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (AT_S1E3W val_name) s"
  unfolding AT_S1E3W_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_S1E3W_SysOpsWrite_e92e083e28fa4dd0[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (S1E3W_SysOpsWrite_e92e083e28fa4dd0 el op0 op1 CRn op2 CRm val_name) s"
  unfolding S1E3W_SysOpsWrite_e92e083e28fa4dd0_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_S1_op1_Cn_Cm_op2_SysOpsWrite_d6b17d94c0df44bc[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (S1_op1_Cn_Cm_op2_SysOpsWrite_d6b17d94c0df44bc el op0 op1 CRn op2 CRm val_name) s"
  unfolding S1_op1_Cn_Cm_op2_SysOpsWrite_d6b17d94c0df44bc_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_VAAE1IS_SysOpsWrite_c22cd5a1dc8e7320[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (VAAE1IS_SysOpsWrite_c22cd5a1dc8e7320 el op0 op1 CRn op2 CRm val_name) s"
  unfolding VAAE1IS_SysOpsWrite_c22cd5a1dc8e7320_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_VAAE1_SysOpsWrite_8498b4db5afbed38[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (VAAE1_SysOpsWrite_8498b4db5afbed38 el op0 op1 CRn op2 CRm val_name) s"
  unfolding VAAE1_SysOpsWrite_8498b4db5afbed38_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_VAALE1IS_SysOpsWrite_5c8056a5b649fe2e[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (VAALE1IS_SysOpsWrite_5c8056a5b649fe2e el op0 op1 CRn op2 CRm val_name) s"
  unfolding VAALE1IS_SysOpsWrite_5c8056a5b649fe2e_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_VAALE1_SysOpsWrite_d3bec3a19881fb1c[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (VAALE1_SysOpsWrite_d3bec3a19881fb1c el op0 op1 CRn op2 CRm val_name) s"
  unfolding VAALE1_SysOpsWrite_d3bec3a19881fb1c_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_VAE1IS_SysOpsWrite_5eac1ac5cb4e76ff[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (VAE1IS_SysOpsWrite_5eac1ac5cb4e76ff el op0 op1 CRn op2 CRm val_name) s"
  unfolding VAE1IS_SysOpsWrite_5eac1ac5cb4e76ff_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_VAE1_SysOpsWrite_09dbfc0bf1b19b11[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (VAE1_SysOpsWrite_09dbfc0bf1b19b11 el op0 op1 CRn op2 CRm val_name) s"
  unfolding VAE1_SysOpsWrite_09dbfc0bf1b19b11_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_TLBI_VAE2IS[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (TLBI_VAE2IS val_name) s"
  unfolding TLBI_VAE2IS_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_VAE2IS_SysOpsWrite_f81411101129df7b[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (VAE2IS_SysOpsWrite_f81411101129df7b el op0 op1 CRn op2 CRm val_name) s"
  unfolding VAE2IS_SysOpsWrite_f81411101129df7b_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_TLBI_VAE2[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (TLBI_VAE2 val_name) s"
  unfolding TLBI_VAE2_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_VAE2_SysOpsWrite_78002df18993a4b5[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (VAE2_SysOpsWrite_78002df18993a4b5 el op0 op1 CRn op2 CRm val_name) s"
  unfolding VAE2_SysOpsWrite_78002df18993a4b5_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_VAE3IS_SysOpsWrite_7dc759c51bb69ced[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (VAE3IS_SysOpsWrite_7dc759c51bb69ced el op0 op1 CRn op2 CRm val_name) s"
  unfolding VAE3IS_SysOpsWrite_7dc759c51bb69ced_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_VAE3_SysOpsWrite_90b5c3b60d3bd152[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (VAE3_SysOpsWrite_90b5c3b60d3bd152 el op0 op1 CRn op2 CRm val_name) s"
  unfolding VAE3_SysOpsWrite_90b5c3b60d3bd152_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_VALE1IS_SysOpsWrite_7bb7ad05a900b833[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (VALE1IS_SysOpsWrite_7bb7ad05a900b833 el op0 op1 CRn op2 CRm val_name) s"
  unfolding VALE1IS_SysOpsWrite_7bb7ad05a900b833_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_VALE1_SysOpsWrite_c1766c627b3960ca[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (VALE1_SysOpsWrite_c1766c627b3960ca el op0 op1 CRn op2 CRm val_name) s"
  unfolding VALE1_SysOpsWrite_c1766c627b3960ca_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_TLBI_VALE2IS[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (TLBI_VALE2IS val_name) s"
  unfolding TLBI_VALE2IS_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_VALE2IS_SysOpsWrite_a1084cefbce599af[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (VALE2IS_SysOpsWrite_a1084cefbce599af el op0 op1 CRn op2 CRm val_name) s"
  unfolding VALE2IS_SysOpsWrite_a1084cefbce599af_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_TLBI_VALE2[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (TLBI_VALE2 val_name) s"
  unfolding TLBI_VALE2_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_VALE2_SysOpsWrite_dce4b2b057d036da[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (VALE2_SysOpsWrite_dce4b2b057d036da el op0 op1 CRn op2 CRm val_name) s"
  unfolding VALE2_SysOpsWrite_dce4b2b057d036da_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_VALE3IS_SysOpsWrite_8b70cb86db2abfcd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (VALE3IS_SysOpsWrite_8b70cb86db2abfcd el op0 op1 CRn op2 CRm val_name) s"
  unfolding VALE3IS_SysOpsWrite_8b70cb86db2abfcd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_VALE3_SysOpsWrite_df1f91b1bea42ec8[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (VALE3_SysOpsWrite_df1f91b1bea42ec8 el op0 op1 CRn op2 CRm val_name) s"
  unfolding VALE3_SysOpsWrite_df1f91b1bea42ec8_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_VMALLE1IS_SysOpsWrite_08cfba716c4ca8db[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (VMALLE1IS_SysOpsWrite_08cfba716c4ca8db el op0 op1 CRn op2 CRm val_name) s"
  unfolding VMALLE1IS_SysOpsWrite_08cfba716c4ca8db_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_VMALLE1_SysOpsWrite_c64f2572b311d9b9[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (VMALLE1_SysOpsWrite_c64f2572b311d9b9 el op0 op1 CRn op2 CRm val_name) s"
  unfolding VMALLE1_SysOpsWrite_c64f2572b311d9b9_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_VMALLS12E1IS_SysOpsWrite_92a1ba1461a19d4c[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (VMALLS12E1IS_SysOpsWrite_92a1ba1461a19d4c el op0 op1 CRn op2 CRm val_name) s"
  unfolding VMALLS12E1IS_SysOpsWrite_92a1ba1461a19d4c_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_VMALLS12E1_SysOpsWrite_8f5c303094061f20[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (VMALLS12E1_SysOpsWrite_8f5c303094061f20 el op0 op1 CRn op2 CRm val_name) s"
  unfolding VMALLS12E1_SysOpsWrite_8f5c303094061f20_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_DC_ZVA[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (DC_ZVA val_name) s"
  unfolding DC_ZVA_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_DC_ZVA0[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (DC_ZVA0 val_name__arg) s"
  unfolding DC_ZVA0_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ZVA_SysOpsWrite_b40574bff0ba4354[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ZVA_SysOpsWrite_b40574bff0ba4354 el op0 op1 CRn op2 CRm val_name) s"
  unfolding ZVA_SysOpsWrite_b40574bff0ba4354_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_AArch64_AutoGen_SysOpsWrite[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (AArch64_AutoGen_SysOpsWrite el op0 op1 CRn op2 CRm val_name) s"
  unfolding AArch64_AutoGen_SysOpsWrite_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_AArch64_SysInstr[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (AArch64_SysInstr op0 op1 crn crm op2 val_name) s"
  unfolding AArch64_SysInstr_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_AArch64_SysInstrWithResult[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (AArch64_SysInstrWithResult op0 op1 crn crm op2) s"
  unfolding AArch64_SysInstrWithResult_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_AArch64_FPTrappedException[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (AArch64_FPTrappedException is_ase element accumulated_exceptions) s"
  unfolding AArch64_FPTrappedException_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_FPProcessException[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (FPProcessException exception fpcr) s"
  unfolding FPProcessException_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_FPRoundBase[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (FPRoundBase arg0 arg1 arg2 arg3 arg4 :: 'N::len word M) s"
  unfolding FPRoundBase_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_FPRound[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (FPRound N op fpcr__arg rounding :: 'N::len word M) s"
  unfolding FPRound_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_FPRound__1[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (FPRound__1 N op fpcr :: 'N::len word M) s"
  unfolding FPRound__1_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_FixedToFP[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "int (size op) \<in> {16, 32, 64}"
  shows "traces_enabled (FixedToFP N op fbits is_unsigned fpcr rounding :: 'N::len word M) s"
  unfolding FixedToFP_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_FPProcessNaN[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "int (size op) \<in> {16, 32, 64}"
  shows "traces_enabled (FPProcessNaN fptype op fpcr :: 'N::len word M) s"
  unfolding FPProcessNaN_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_FPProcessNaNs[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "int (size op1) \<in> {16, 32, 64}" and "int (size op2) = int (size op1)"
  shows "traces_enabled (FPProcessNaNs type1 type2 op1 op2 fpcr) s"
  unfolding FPProcessNaNs_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_FPUnpackBase[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "int (size fpval) \<in> {16, 32, 64}"
  shows "traces_enabled (FPUnpackBase fpval fpcr) s"
  unfolding FPUnpackBase_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_FPUnpack[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "int (size fpval) \<in> {16, 32, 64}"
  shows "traces_enabled (FPUnpack fpval fpcr__arg) s"
  unfolding FPUnpack_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_FPAdd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "int (size op1) \<in> {16, 32, 64}" and "int (size op2) = int (size op1)"
  shows "traces_enabled (FPAdd op1 op2 fpcr :: 'N::len word M) s"
  unfolding FPAdd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_FPCompare[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "int (size op1) \<in> {16, 32, 64}" and "int (size op2) = int (size op1)"
  shows "traces_enabled (FPCompare op1 op2 signal_nans fpcr) s"
  unfolding FPCompare_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_FPCompareEQ[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "int (size op1) \<in> {16, 32, 64}" and "int (size op2) = int (size op1)"
  shows "traces_enabled (FPCompareEQ op1 op2 fpcr) s"
  unfolding FPCompareEQ_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_FPCompareGE[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "int (size op1) \<in> {16, 32, 64}" and "int (size op2) = int (size op1)"
  shows "traces_enabled (FPCompareGE op1 op2 fpcr) s"
  unfolding FPCompareGE_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_FPCompareGT[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "int (size op1) \<in> {16, 32, 64}" and "int (size op2) = int (size op1)"
  shows "traces_enabled (FPCompareGT op1 op2 fpcr) s"
  unfolding FPCompareGT_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_FPRoundCV[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (FPRoundCV N op fpcr__arg rounding :: 'N::len word M) s"
  unfolding FPRoundCV_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_FPUnpackCV[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "int (size fpval) \<in> {16, 32, 64}"
  shows "traces_enabled (FPUnpackCV fpval fpcr__arg) s"
  unfolding FPUnpackCV_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_FPConvert[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "int (size op) \<in> {16, 32, 64}"
  shows "traces_enabled (FPConvert l__604 op fpcr rounding :: 'M::len word M) s"
  unfolding FPConvert_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_FPConvert__1[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "int (size op) \<in> {16, 32, 64}"
  shows "traces_enabled (FPConvert__1 M op fpcr :: 'M::len word M) s"
  unfolding FPConvert__1_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_FPDiv[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "int (size op1) \<in> {16, 32, 64}" and "int (size op2) = int (size op1)"
  shows "traces_enabled (FPDiv op1 op2 fpcr :: 'N::len word M) s"
  unfolding FPDiv_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_FPMax[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "int (size op1) \<in> {16, 32, 64}" and "int (size op2) = int (size op1)"
  shows "traces_enabled (FPMax op1 op2 fpcr :: 'N::len word M) s"
  unfolding FPMax_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_FPMaxNum[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "int (size op1__arg) \<in> {16, 32, 64}" and "int (size op2__arg) = int (size op1__arg)"
  shows "traces_enabled (FPMaxNum op1__arg op2__arg fpcr :: 'N::len word M) s"
  unfolding FPMaxNum_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_FPMin[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "int (size op1) \<in> {16, 32, 64}" and "int (size op2) = int (size op1)"
  shows "traces_enabled (FPMin op1 op2 fpcr :: 'N::len word M) s"
  unfolding FPMin_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_FPMinNum[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "int (size op1__arg) \<in> {16, 32, 64}" and "int (size op2__arg) = int (size op1__arg)"
  shows "traces_enabled (FPMinNum op1__arg op2__arg fpcr :: 'N::len word M) s"
  unfolding FPMinNum_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_FPMul[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "int (size op1) \<in> {16, 32, 64}" and "int (size op2) = int (size op1)"
  shows "traces_enabled (FPMul op1 op2 fpcr :: 'N::len word M) s"
  unfolding FPMul_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_FPProcessNaNs3[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "int (size op1) \<in> {16, 32, 64}" and "int (size op3) = int (size op1)" and "int (size op2) = int (size op1)"
  shows "traces_enabled (FPProcessNaNs3 type1 type2 type3 op1 op2 op3 fpcr) s"
  unfolding FPProcessNaNs3_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_FPMulAdd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "int (size addend) \<in> {16, 32, 64}" and "int (size op2) = int (size addend)" and "int (size op1) = int (size addend)"
  shows "traces_enabled (FPMulAdd addend op1 op2 fpcr :: 'N::len word M) s"
  unfolding FPMulAdd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_FPMulX[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "int (size op1) \<in> {16, 32, 64}" and "int (size op2) = int (size op1)"
  shows "traces_enabled (FPMulX op1 op2 fpcr :: 'N::len word M) s"
  unfolding FPMulX_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_FPRecipEstimate[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "int (size operand) \<in> {16, 32, 64}"
  shows "traces_enabled (FPRecipEstimate operand fpcr :: 'N::len word M) s"
  unfolding FPRecipEstimate_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_FPRecpX[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "int (size op) \<in> {16, 32, 64}"
  shows "traces_enabled (FPRecpX l__583 op fpcr :: 'N::len word M) s"
  unfolding FPRecpX_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_FPRoundInt[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "int (size op) \<in> {16, 32, 64}"
  shows "traces_enabled (FPRoundInt op fpcr rounding exact :: 'N::len word M) s"
  unfolding FPRoundInt_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_FPRSqrtEstimate[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "int (size operand) \<in> {16, 32, 64}"
  shows "traces_enabled (FPRSqrtEstimate operand fpcr :: 'N::len word M) s"
  unfolding FPRSqrtEstimate_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_FPSqrt[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "int (size op) \<in> {16, 32, 64}"
  shows "traces_enabled (FPSqrt op fpcr :: 'N::len word M) s"
  unfolding FPSqrt_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_FPSub[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "int (size op1) \<in> {16, 32, 64}" and "int (size op2) = int (size op1)"
  shows "traces_enabled (FPSub op1 op2 fpcr :: 'N::len word M) s"
  unfolding FPSub_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_FPToFixed[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "int (size op) \<in> {16, 32, 64}"
  shows "traces_enabled (FPToFixed M op fbits is_unsigned fpcr rounding :: 'M::len word M) s"
  unfolding FPToFixed_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_BranchXToCapability[traces_enabledI]:
  assumes "target__arg \<in> derivable_caps s"
  shows "traces_enabled (BranchXToCapability target__arg branch_type) s"
  unfolding BranchXToCapability_def bind_assoc
  by (traces_enabledI assms: assms intro: enabled_branch_target_set_0th derivable_enabled_branch_target)

lemma traces_enabled_BranchToOffset[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (BranchToOffset offset branch_type) s"
  unfolding BranchToOffset_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_X_set[traces_enabledI]:
  assumes "LENGTH('a) \<in> {32, 64}"
  shows "traces_enabled (X_set width n (value_name :: 'a::len word)) s"
  unfolding X_set_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_X_read[traces_enabledI]:
  "traces_enabled (X_read width n :: 'width::len word M) s"
  unfolding X_read_def bind_assoc
  by (traces_enabledI)

lemma traces_enabled_C_read[traces_enabledI]:
  "traces_enabled (C_read n) s"
  unfolding C_read_def bind_assoc
  by (traces_enabledI)

lemma traces_enabled_SP_set[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "LENGTH('a) \<in> {32, 64}"
  shows "traces_enabled (SP_set width (value_name :: 'a::len word)) s"
  unfolding SP_set_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_SP_read[traces_enabledI]:
  "traces_enabled (SP_read width :: 'width::len word M) s"
  unfolding SP_read_def bind_assoc
  by (traces_enabledI)

lemma traces_enabled_CSP_set[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "value_name \<in> derivable_caps s"
  shows "traces_enabled (CSP_set value_name) s"
  unfolding CSP_set_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CSP_read[traces_enabledI]:
  "traces_enabled (CSP_read arg0) s"
  unfolding CSP_read_def bind_assoc
  by (traces_enabledI)

lemma traces_enabled_PC_read[traces_enabledI]:
  "traces_enabled (PC_read arg0) s"
  unfolding PC_read_def bind_assoc
  by (traces_enabledI)

lemma traces_enabled_AArch64_SPAlignmentFault[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (AArch64_SPAlignmentFault arg0) s"
  unfolding AArch64_SPAlignmentFault_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CheckSPAlignment[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CheckSPAlignment arg0) s"
  unfolding CheckSPAlignment_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_BaseReg_read[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (BaseReg_read n is_prefetch) s"
  unfolding BaseReg_read_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_BaseReg_read__1[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (BaseReg_read__1 n) s"
  unfolding BaseReg_read__1_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_AltBaseReg_read[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (AltBaseReg_read n is_prefetch) s"
  unfolding AltBaseReg_read_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_AltBaseReg_read__1[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (AltBaseReg_read__1 n) s"
  unfolding AltBaseReg_read__1_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_BaseReg_set[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "VA_derivable address s"
  shows "traces_enabled (BaseReg_set n address) s"
  unfolding BaseReg_set_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ELR_read[traces_enabledI]:
  "traces_enabled (ELR_read el) s"
  unfolding ELR_read_def bind_assoc
  by (traces_enabledI)

lemma traces_enabled_ELR_read__1[traces_enabledI]:
  "traces_enabled (ELR_read__1 arg0) s"
  unfolding ELR_read__1_def bind_assoc
  by (traces_enabledI)

lemma traces_enabled_CELR_read[traces_enabledI]:
  "traces_enabled (CELR_read el) s"
  unfolding CELR_read_def bind_assoc
  by (traces_enabledI)

lemma traces_enabled_CELR_read__1[traces_enabledI]:
  "traces_enabled (CELR_read__1 arg0) s"
  unfolding CELR_read__1_def bind_assoc
  by (traces_enabledI)

lemma traces_enabled_AArch64_CheckSystemAccess[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (AArch64_CheckSystemAccess op0 op1 crn crm op2 rt read) s"
  unfolding AArch64_CheckSystemAccess_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_AArch64_CheckAlignment[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (AArch64_CheckAlignment address alignment acctype iswrite) s"
  unfolding AArch64_CheckAlignment_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_AArch64_MemSingle_read[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (AArch64_MemSingle_read address size__arg acctype wasaligned :: 'size_times_p8::len word M) s"
  unfolding AArch64_MemSingle_read_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_AArch64_MemSingle_set[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (AArch64_MemSingle_set address size__arg acctype wasaligned value_name) s"
  unfolding AArch64_MemSingle_set_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CheckLoadTagsPermission[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CheckLoadTagsPermission desc acctype) s"
  unfolding CheckLoadTagsPermission_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CheckStoreTagsPermission[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CheckStoreTagsPermission desc acctype) s"
  unfolding CheckStoreTagsPermission_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_AArch64_TaggedMemSingle[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (AArch64_TaggedMemSingle address size__arg acctype wasaligned) s"
  unfolding AArch64_TaggedMemSingle_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_AArch64_TaggedMemSingle__1[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "Capability_of_tag_word (tags !! 0) (ucast data) \<in> derivable_caps s" and "sz = 32 \<Longrightarrow> Capability_of_tag_word (tags !! 1) (Word.slice 128 data) \<in> derivable_caps s"
  shows "traces_enabled (AArch64_TaggedMemSingle__1 addr sz acctype wasaligned (tags :: 't::len word) (data :: 'd::len word)) s"
  unfolding AArch64_TaggedMemSingle__1_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CheckCapabilityAlignment[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CheckCapabilityAlignment address acctype iswrite) s"
  unfolding CheckCapabilityAlignment_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_AArch64_CapabilityTag[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (AArch64_CapabilityTag address acctype) s"
  unfolding AArch64_CapabilityTag_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_AArch64_CapabilityTag_set[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "tag = 0"
  shows "traces_enabled (AArch64_CapabilityTag_set address acctype tag) s"
  unfolding AArch64_CapabilityTag_set_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_Mem_read0[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (Mem_read0 address size__arg acctype :: 'size_times_p8::len word M) s"
  unfolding Mem_read0_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_Mem_set0[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (Mem_set0 address size__arg acctype value_name__arg) s"
  unfolding Mem_set0_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CheckCapabilityStorePairAlignment[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CheckCapabilityStorePairAlignment address acctype iswrite) s"
  unfolding CheckCapabilityStorePairAlignment_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_MemC_read[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (MemC_read address acctype) s"
  unfolding MemC_read_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_MemC_set[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "value_name \<in> derivable_caps s"
  shows "traces_enabled (MemC_set address acctype value_name) s"
  unfolding MemC_set_def bind_assoc
  by (traces_enabledI assms: assms simp: update_subrange_vec_dec_test_bit)

lemma traces_enabled_MemCP__1[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "value1_name \<in> derivable_caps s" and "value2_name \<in> derivable_caps s"
  shows "traces_enabled (MemCP__1 address acctype value1_name value2_name) s"
  unfolding MemCP__1_def bind_assoc
  by (traces_enabledI assms: assms simp: update_subrange_vec_dec_test_bit update_subrange_vec_dec_word_cat_cap_pair slice_128_cat_cap_pair)

lemma traces_enabled_AArch64_TranslateAddressForAtomicAccess[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (AArch64_TranslateAddressForAtomicAccess address sizeinbits) s"
  unfolding AArch64_TranslateAddressForAtomicAccess_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CheckCapability[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CheckCapability c__arg address size__arg requested_perms acctype) s"
  unfolding CheckCapability_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_VACheckAddress[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (VACheckAddress base addr64 size__arg requested_perms acctype) s"
  unfolding VACheckAddress_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_MemAtomicCompareAndSwap[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (MemAtomicCompareAndSwap base expectedvalue newvalue__arg ldacctype stacctype :: 'size::len word M) s"
  unfolding MemAtomicCompareAndSwap_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_MemAtomic[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (MemAtomic base op value_name ldacctype stacctype :: 'size::len word M) s"
  unfolding MemAtomic_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CapSquashPostLoadCap[traces_enabledI]:
  "traces_enabled (CapSquashPostLoadCap data__arg addr) s"
  unfolding CapSquashPostLoadCap_def bind_assoc
  by (traces_enabledI)

lemma traces_enabled_MemAtomicCompareAndSwapC[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "expectedcap \<in> derivable_caps s" and "newcap \<in> derivable_caps s"
  shows "traces_enabled (MemAtomicCompareAndSwapC vaddr address expectedcap newcap ldacctype stacctype) s"
  unfolding MemAtomicCompareAndSwapC_def bind_assoc
  by (traces_enabledI assms: assms simp: update_subrange_vec_dec_test_bit)

lemma traces_enabled_MemAtomicC[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "value_name \<in> derivable_caps s"
  shows "traces_enabled (MemAtomicC address op value_name ldacctype stacctype) s"
  unfolding MemAtomicC_def bind_assoc
  by (traces_enabledI assms: assms simp: update_subrange_vec_dec_test_bit)

lemma traces_enabled_AArch64_SetExclusiveMonitors[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (AArch64_SetExclusiveMonitors address size__arg) s"
  unfolding AArch64_SetExclusiveMonitors_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_AArch64_ExclusiveMonitorsPass[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (AArch64_ExclusiveMonitorsPass address size__arg) s"
  unfolding AArch64_ExclusiveMonitorsPass_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_FPRecipStepFused[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "int (size op1__arg) \<in> {16, 32, 64}" and "int (size op2) = int (size op1__arg)"
  shows "traces_enabled (FPRecipStepFused op1__arg op2 :: 'N::len word M) s"
  unfolding FPRecipStepFused_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_FPRSqrtStepFused[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "int (size op1__arg) \<in> {16, 32, 64}" and "int (size op2) = int (size op1__arg)"
  shows "traces_enabled (FPRSqrtStepFused op1__arg op2 :: 'N::len word M) s"
  unfolding FPRSqrtStepFused_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_AArch64_CallSecureMonitor[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (AArch64_CallSecureMonitor immediate) s"
  unfolding AArch64_CallSecureMonitor_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_AArch64_CallHypervisor[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (AArch64_CallHypervisor immediate) s"
  unfolding AArch64_CallHypervisor_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_AArch64_CallSupervisor[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (AArch64_CallSupervisor immediate) s"
  unfolding AArch64_CallSupervisor_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_AArch64_CheckForSMCUndefOrTrap[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (AArch64_CheckForSMCUndefOrTrap imm) s"
  unfolding AArch64_CheckForSMCUndefOrTrap_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_AArch64_WFxTrap[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (AArch64_WFxTrap target_el is_wfe) s"
  unfolding AArch64_WFxTrap_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_AArch64_CheckForWFxTrap[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (AArch64_CheckForWFxTrap target_el is_wfe) s"
  unfolding AArch64_CheckForWFxTrap_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_AArch64_AdvSIMDFPAccessTrap[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (AArch64_AdvSIMDFPAccessTrap target_el) s"
  unfolding AArch64_AdvSIMDFPAccessTrap_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_AArch64_CheckFPAdvSIMDTrap[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (AArch64_CheckFPAdvSIMDTrap arg0) s"
  unfolding AArch64_CheckFPAdvSIMDTrap_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_AArch64_CheckFPAdvSIMDEnabled[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (AArch64_CheckFPAdvSIMDEnabled arg0) s"
  unfolding AArch64_CheckFPAdvSIMDEnabled_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CheckFPAdvSIMDEnabled64[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CheckFPAdvSIMDEnabled64 arg0) s"
  unfolding CheckFPAdvSIMDEnabled64_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CapabilityAccessTrap[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CapabilityAccessTrap target_el) s"
  unfolding CapabilityAccessTrap_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CheckCapabilitiesEnabled[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (CheckCapabilitiesEnabled arg0) s"
  unfolding CheckCapabilitiesEnabled_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_AArch64_SoftwareBreakpoint[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (AArch64_SoftwareBreakpoint immediate) s"
  unfolding AArch64_SoftwareBreakpoint_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_AArch64_ExceptionReturnToCapability[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "new_pcc__arg \<in> derivable_caps s"
  shows "traces_enabled (AArch64_ExceptionReturnToCapability new_pcc__arg spsr) s"
  unfolding AArch64_ExceptionReturnToCapability_def bind_assoc
  by (traces_enabledI assms: assms intro: derivable_enabled_branch_target)

lemma traces_enabled_ExtendReg[traces_enabledI]:
  "traces_enabled (ExtendReg N reg exttype shift :: 'N::len word M) s"
  unfolding ExtendReg_def bind_assoc
  by (traces_enabledI)

lemma traces_enabled_ShiftReg[traces_enabledI]:
  assumes "amount \<ge> 0"
  shows "traces_enabled (ShiftReg N reg shiftype amount :: 'N::len word M) s"
  unfolding ShiftReg_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ReduceCombine[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "int (size lo) \<in> {8, 16, 32, 64}" and "int (size hi) = int (size lo)"
  shows "traces_enabled (ReduceCombine op lo hi :: 'esize::len word M) s"
  unfolding ReduceCombine_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_Reduce16[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "esize \<in> {8, 16}" and "int LENGTH('esize) = esize"
  shows "traces_enabled (Reduce16 op input esize :: 'esize::len word M) s"
  unfolding Reduce16_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_Reduce32[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "esize \<in> {8, 16, 32}" and "int LENGTH('esize) = esize"
  shows "traces_enabled (Reduce32 op input esize :: 'esize::len word M) s"
  unfolding Reduce32_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_Reduce64[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "esize \<in> {8, 16, 32, 64}" and "int LENGTH('esize) = esize"
  shows "traces_enabled (Reduce64 op input esize :: 'esize::len word M) s"
  unfolding Reduce64_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_Reduce128[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "esize \<in> {8, 16, 32, 64}" and "int LENGTH('esize) = esize"
  shows "traces_enabled (Reduce128 op input esize :: 'esize::len word M) s"
  unfolding Reduce128_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_Reduce256[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "esize \<in> {8, 16, 32, 64}" and "int LENGTH('esize) = esize"
  shows "traces_enabled (Reduce256 op input esize :: 'esize::len word M) s"
  unfolding Reduce256_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_Reduce512[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "esize \<in> {8, 16, 32, 64}" and "int LENGTH('esize) = esize"
  shows "traces_enabled (Reduce512 op input esize :: 'esize::len word M) s"
  unfolding Reduce512_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_Reduce1024[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "esize \<in> {8, 16, 32, 64}" and "int LENGTH('esize) = esize"
  shows "traces_enabled (Reduce1024 op input esize :: 'esize::len word M) s"
  unfolding Reduce1024_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_Reduce2048[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "esize \<in> {8, 16, 32, 64}" and "int LENGTH('esize) = esize"
  shows "traces_enabled (Reduce2048 op input esize :: 'esize::len word M) s"
  unfolding Reduce2048_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_Reduce[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "esize \<in> {8, 16, 32, 64}" and "nat esize \<le> size input" and "LENGTH('esize) = nat esize"
  shows "traces_enabled (Reduce op input esize :: 'esize::len word M) s"
  unfolding Reduce_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_DCPSInstruction[traces_enabledI]:
  "traces_enabled (DCPSInstruction target_el) s"
  unfolding DCPSInstruction_def bind_assoc
  by (traces_enabledI simp: HaveCapabilitiesExt_def)

lemma traces_enabled_DRPSInstruction[traces_enabledI]:
  "traces_enabled (DRPSInstruction arg0) s"
  unfolding DRPSInstruction_def bind_assoc
  by (traces_enabledI simp: HaveCapabilitiesExt_def)

lemma traces_enabled_VACheckPerm[traces_enabledI]:
  "traces_enabled (VACheckPerm base requested_perms) s"
  unfolding VACheckPerm_def bind_assoc
  by (traces_enabledI)

lemma traces_enabled_CAP_DC_CIVAC[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "cval \<in> derivable_caps s"
  shows "traces_enabled (CAP_DC_CIVAC cval) s"
  unfolding CAP_DC_CIVAC_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CAP_DC_CVAC[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "cval \<in> derivable_caps s"
  shows "traces_enabled (CAP_DC_CVAC cval) s"
  unfolding CAP_DC_CVAC_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CAP_DC_CVADP[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "cval \<in> derivable_caps s"
  shows "traces_enabled (CAP_DC_CVADP cval) s"
  unfolding CAP_DC_CVADP_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CAP_DC_CVAP[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "cval \<in> derivable_caps s"
  shows "traces_enabled (CAP_DC_CVAP cval) s"
  unfolding CAP_DC_CVAP_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CAP_DC_CVAU[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "cval \<in> derivable_caps s"
  shows "traces_enabled (CAP_DC_CVAU cval) s"
  unfolding CAP_DC_CVAU_def bind_assoc
  by (traces_enabledI assms: assms intro: traces_enabled_bind)

lemma traces_enabled_CAP_DC_IVAC[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "cval \<in> derivable_caps s"
  shows "traces_enabled (CAP_DC_IVAC cval) s"
  unfolding CAP_DC_IVAC_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CAP_DC_ZVA[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "cval \<in> derivable_caps s"
  shows "traces_enabled (CAP_DC_ZVA cval) s"
  unfolding CAP_DC_ZVA_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_CAP_IC_IVAU[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "cval \<in> derivable_caps s"
  shows "traces_enabled (CAP_IC_IVAU cval) s"
  unfolding CAP_IC_IVAU_def bind_assoc
  by (traces_enabledI assms: assms intro: traces_enabled_bind)

lemma traces_enabled_AArch64_SysInstrWithCapability[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "val_name \<in> derivable_caps s"
  shows "traces_enabled (AArch64_SysInstrWithCapability op0 op1 crn crm op2 val_name) s"
  unfolding AArch64_SysInstrWithCapability_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_Step_PC[traces_enabledI]:
  "traces_enabled (Step_PC arg0) s"
  unfolding Step_PC_def bind_assoc
  by (traces_enabledI elim: BranchTaken_or_PCC_accessible)

lemma traces_enabled_execute_ADD_C_CIS_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_ADD_C_CIS_C d imm n) s"
  unfolding execute_ADD_C_CIS_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ADD_C_CIS_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ADD_C_CIS_C A sh imm12 Cn Cd) s"
  unfolding decode_ADD_C_CIS_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_ADD_C_CRI_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "shift \<in> {0, 1, 2, 3, 4, 5, 6, 7}" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_ADD_C_CRI_C d extend_type m n shift) s"
  unfolding execute_ADD_C_CRI_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ADD_C_CRI_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ADD_C_CRI_C Rm option_name imm3 Cn Cd) s"
  unfolding decode_ADD_C_CRI_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_ADRDP_C_ID_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_ADRDP_C_ID_C P d imm) s"
  unfolding execute_ADRDP_C_ID_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ADRDP_C_ID_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ADRDP_C_ID_C op immlo P immhi Rd) s"
  unfolding decode_ADRDP_C_ID_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_ADRP_C_IP_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_ADRP_C_IP_C P d imm) s"
  unfolding execute_ADRP_C_IP_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ADRP_C_IP_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ADRP_C_IP_C op immlo P immhi Rd) s"
  unfolding decode_ADRP_C_IP_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_ADRP_C_I_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_ADRP_C_I_C P d imm) s"
  unfolding execute_ADRP_C_I_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ADRP_C_I_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ADRP_C_I_C op immlo P immhi Rd) s"
  unfolding decode_ADRP_C_I_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_ADR_C_I_C[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_ADR_C_I_C d imm) s"
  unfolding execute_ADR_C_I_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ADR_C_I_C[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ADR_C_I_C op immlo P immhi Rd) s"
  unfolding decode_ADR_C_I_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_ALDARB_R_R_B[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "regsize = 32" and "0 \<le> n" and "n \<le> 31" and "datasize = 8"
  shows "traces_enabled (execute_ALDARB_R_R_B acctype datasize n regsize t__arg) s"
  unfolding execute_ALDARB_R_R_B_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ALDARB_R_R_B[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ALDARB_R_R_B L Rn Rt) s"
  unfolding decode_ALDARB_R_R_B_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_ALDAR_C_R_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "0 \<le> n" and "n \<le> 31" and "\<not>invokes_indirect_caps" and "AltBaseRegAuth n \<in> load_auths"
  shows "traces_enabled (execute_ALDAR_C_R_C acctype n t__arg) s"
  unfolding execute_ALDAR_C_R_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ALDAR_C_R_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "\<not>invokes_indirect_caps" and "AltBaseRegAuth (uint Rn) \<in> load_auths"
  shows "traces_enabled (decode_ALDAR_C_R_C L Rn Ct) s"
  unfolding decode_ALDAR_C_R_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_ALDAR_R_R_32[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "regsize = 32" and "0 \<le> n" and "n \<le> 31" and "datasize = 32"
  shows "traces_enabled (execute_ALDAR_R_R_32 acctype datasize n regsize t__arg) s"
  unfolding execute_ALDAR_R_R_32_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ALDAR_R_R_32[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ALDAR_R_R_32 L Rn Rt) s"
  unfolding decode_ALDAR_R_R_32_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_ALDRB_R_RRB_B[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "shift = 0" and "l__550 = 0" and "regsize = 32" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31"
  shows "traces_enabled (execute_ALDRB_R_RRB_B extend_type m n regsize l__550 shift t__arg) s"
  unfolding execute_ALDRB_R_RRB_B_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ALDRB_R_RRB_B[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ALDRB_R_RRB_B L Rm sign sz S opc Rn Rt) s"
  unfolding decode_ALDRB_R_RRB_B_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_ALDRB_R_RUI_B[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "regsize = 32" and "0 \<le> n" and "n \<le> 31" and "datasize = 8"
  shows "traces_enabled (execute_ALDRB_R_RUI_B datasize n offset regsize t__arg) s"
  unfolding execute_ALDRB_R_RUI_B_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ALDRB_R_RUI_B[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ALDRB_R_RUI_B L imm9 op Rn Rt) s"
  unfolding decode_ALDRB_R_RUI_B_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_ALDRH_R_RRB_32[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "shift \<in> {0, 1}" and "l__549 = 1" and "regsize = 32" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31"
  shows "traces_enabled (execute_ALDRH_R_RRB_32 extend_type m n regsize l__549 shift t__arg) s"
  unfolding execute_ALDRH_R_RRB_32_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ALDRH_R_RRB_32[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ALDRH_R_RRB_32 L Rm sign sz S opc Rn Rt) s"
  unfolding decode_ALDRH_R_RRB_32_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_ALDRSB_R_RRB_32[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "shift = 0" and "l__545 = 0" and "regsize = 32" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31"
  shows "traces_enabled (execute_ALDRSB_R_RRB_32 extend_type m n regsize l__545 shift t__arg) s"
  unfolding execute_ALDRSB_R_RRB_32_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ALDRSB_R_RRB_32[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ALDRSB_R_RRB_32 L Rm sign sz S opc Rn Rt) s"
  unfolding decode_ALDRSB_R_RRB_32_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_ALDRSB_R_RRB_64[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "shift = 0" and "l__546 = 0" and "regsize = 64" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31"
  shows "traces_enabled (execute_ALDRSB_R_RRB_64 extend_type m n regsize l__546 shift t__arg) s"
  unfolding execute_ALDRSB_R_RRB_64_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ALDRSB_R_RRB_64[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ALDRSB_R_RRB_64 L Rm sign sz S opc Rn Rt) s"
  unfolding decode_ALDRSB_R_RRB_64_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_ALDRSH_R_RRB_32[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "shift \<in> {0, 1}" and "l__543 = 1" and "regsize = 32" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31"
  shows "traces_enabled (execute_ALDRSH_R_RRB_32 extend_type m n regsize l__543 shift t__arg) s"
  unfolding execute_ALDRSH_R_RRB_32_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ALDRSH_R_RRB_32[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ALDRSH_R_RRB_32 L Rm sign sz S opc Rn Rt) s"
  unfolding decode_ALDRSH_R_RRB_32_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_ALDRSH_R_RRB_64[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "shift \<in> {0, 1}" and "l__544 = 1" and "regsize = 64" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31"
  shows "traces_enabled (execute_ALDRSH_R_RRB_64 extend_type m n regsize l__544 shift t__arg) s"
  unfolding execute_ALDRSH_R_RRB_64_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ALDRSH_R_RRB_64[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ALDRSH_R_RRB_64 L Rm sign sz S opc Rn Rt) s"
  unfolding decode_ALDRSH_R_RRB_64_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_ALDR_C_RRB_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "\<not>invokes_indirect_caps" and "AltBaseRegAuth n \<in> load_auths"
  shows "traces_enabled (execute_ALDR_C_RRB_C extend_type m n shift t__arg) s"
  unfolding execute_ALDR_C_RRB_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ALDR_C_RRB_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "\<not>invokes_indirect_caps" and "AltBaseRegAuth (uint Rn) \<in> load_auths"
  shows "traces_enabled (decode_ALDR_C_RRB_C Rm sign sz S L Rn Ct) s"
  unfolding decode_ALDR_C_RRB_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_ALDR_C_RUI_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "0 \<le> n" and "n \<le> 31" and "\<not>invokes_indirect_caps" and "AltBaseRegAuth n \<in> load_auths"
  shows "traces_enabled (execute_ALDR_C_RUI_C n offset t__arg) s"
  unfolding execute_ALDR_C_RUI_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ALDR_C_RUI_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "\<not>invokes_indirect_caps" and "AltBaseRegAuth (uint Rn) \<in> load_auths"
  shows "traces_enabled (decode_ALDR_C_RUI_C L imm9 op Rn Ct) s"
  unfolding decode_ALDR_C_RUI_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_ALDR_R_RRB_32[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "shift \<in> {0, 2}" and "l__548 = 2" and "regsize = 32" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31"
  shows "traces_enabled (execute_ALDR_R_RRB_32 extend_type m n regsize l__548 shift t__arg) s"
  unfolding execute_ALDR_R_RRB_32_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ALDR_R_RRB_32[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ALDR_R_RRB_32 L Rm sign sz S opc Rn Rt) s"
  unfolding decode_ALDR_R_RRB_32_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_ALDR_R_RRB_64[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "shift \<in> {0, 3}" and "l__547 = 3" and "regsize = 64" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31"
  shows "traces_enabled (execute_ALDR_R_RRB_64 extend_type m n regsize l__547 shift t__arg) s"
  unfolding execute_ALDR_R_RRB_64_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ALDR_R_RRB_64[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ALDR_R_RRB_64 L Rm sign sz S opc Rn Rt) s"
  unfolding decode_ALDR_R_RRB_64_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_ALDR_R_RUI_32[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "regsize = 32" and "0 \<le> n" and "n \<le> 31" and "datasize = 32"
  shows "traces_enabled (execute_ALDR_R_RUI_32 datasize n offset regsize t__arg) s"
  unfolding execute_ALDR_R_RUI_32_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ALDR_R_RUI_32[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ALDR_R_RUI_32 L imm9 op Rn Rt) s"
  unfolding decode_ALDR_R_RUI_32_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_ALDR_R_RUI_64[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "regsize = 64" and "0 \<le> n" and "n \<le> 31" and "datasize = 64"
  shows "traces_enabled (execute_ALDR_R_RUI_64 datasize n offset regsize t__arg) s"
  unfolding execute_ALDR_R_RUI_64_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ALDR_R_RUI_64[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ALDR_R_RUI_64 L imm9 op Rn Rt) s"
  unfolding decode_ALDR_R_RUI_64_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_ALDR_V_RRB_D[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "shift \<in> {0, 3}" and "l__542 = 3" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31"
  shows "traces_enabled (execute_ALDR_V_RRB_D extend_type m n l__542 shift t__arg) s"
  unfolding execute_ALDR_V_RRB_D_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ALDR_V_RRB_D[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ALDR_V_RRB_D L Rm sign sz S opc Rn Rt) s"
  unfolding decode_ALDR_V_RRB_D_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_ALDR_V_RRB_S[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "shift \<in> {0, 2}" and "l__541 = 2" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31"
  shows "traces_enabled (execute_ALDR_V_RRB_S extend_type m n l__541 shift t__arg) s"
  unfolding execute_ALDR_V_RRB_S_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ALDR_V_RRB_S[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ALDR_V_RRB_S L Rm sign sz S opc Rn Rt) s"
  unfolding decode_ALDR_V_RRB_S_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_ALDURB_R_RI_32[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "regsize = 32" and "0 \<le> n" and "n \<le> 31" and "datasize = 8"
  shows "traces_enabled (execute_ALDURB_R_RI_32 datasize n offset regsize t__arg) s"
  unfolding execute_ALDURB_R_RI_32_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ALDURB_R_RI_32[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ALDURB_R_RI_32 op1 V imm9 op2 Rn Rt) s"
  unfolding decode_ALDURB_R_RI_32_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_ALDURH_R_RI_32[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "regsize = 32" and "0 \<le> n" and "n \<le> 31" and "datasize = 16"
  shows "traces_enabled (execute_ALDURH_R_RI_32 datasize n offset regsize t__arg) s"
  unfolding execute_ALDURH_R_RI_32_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ALDURH_R_RI_32[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ALDURH_R_RI_32 op1 V imm9 op2 Rn Rt) s"
  unfolding decode_ALDURH_R_RI_32_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_ALDURSB_R_RI_32[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "regsize = 32" and "0 \<le> n" and "n \<le> 31" and "datasize = 8"
  shows "traces_enabled (execute_ALDURSB_R_RI_32 datasize n offset regsize t__arg) s"
  unfolding execute_ALDURSB_R_RI_32_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ALDURSB_R_RI_32[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ALDURSB_R_RI_32 op1 V imm9 op2 Rn Rt) s"
  unfolding decode_ALDURSB_R_RI_32_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_ALDURSB_R_RI_64[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "regsize = 64" and "0 \<le> n" and "n \<le> 31" and "datasize = 8"
  shows "traces_enabled (execute_ALDURSB_R_RI_64 datasize n offset regsize t__arg) s"
  unfolding execute_ALDURSB_R_RI_64_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ALDURSB_R_RI_64[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ALDURSB_R_RI_64 op1 V imm9 op2 Rn Rt) s"
  unfolding decode_ALDURSB_R_RI_64_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_ALDURSH_R_RI_32[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "regsize = 32" and "0 \<le> n" and "n \<le> 31" and "datasize = 16"
  shows "traces_enabled (execute_ALDURSH_R_RI_32 datasize n offset regsize t__arg) s"
  unfolding execute_ALDURSH_R_RI_32_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ALDURSH_R_RI_32[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ALDURSH_R_RI_32 op1 V imm9 op2 Rn Rt) s"
  unfolding decode_ALDURSH_R_RI_32_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_ALDURSH_R_RI_64[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "regsize = 64" and "0 \<le> n" and "n \<le> 31" and "datasize = 16"
  shows "traces_enabled (execute_ALDURSH_R_RI_64 datasize n offset regsize t__arg) s"
  unfolding execute_ALDURSH_R_RI_64_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ALDURSH_R_RI_64[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ALDURSH_R_RI_64 op1 V imm9 op2 Rn Rt) s"
  unfolding decode_ALDURSH_R_RI_64_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_ALDURSW_R_RI_64[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "regsize = 64" and "0 \<le> n" and "n \<le> 31" and "datasize = 32"
  shows "traces_enabled (execute_ALDURSW_R_RI_64 datasize n offset regsize t__arg) s"
  unfolding execute_ALDURSW_R_RI_64_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ALDURSW_R_RI_64[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ALDURSW_R_RI_64 op1 V imm9 op2 Rn Rt) s"
  unfolding decode_ALDURSW_R_RI_64_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_ALDUR_C_RI_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "0 \<le> n" and "n \<le> 31" and "\<not>invokes_indirect_caps" and "AltBaseRegAuth n \<in> load_auths"
  shows "traces_enabled (execute_ALDUR_C_RI_C n offset t__arg) s"
  unfolding execute_ALDUR_C_RI_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ALDUR_C_RI_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "\<not>invokes_indirect_caps" and "AltBaseRegAuth (uint Rn) \<in> load_auths"
  shows "traces_enabled (decode_ALDUR_C_RI_C op1 V imm9 op2 Rn Ct) s"
  unfolding decode_ALDUR_C_RI_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_ALDUR_R_RI_32[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "regsize = 32" and "0 \<le> n" and "n \<le> 31" and "datasize = 32"
  shows "traces_enabled (execute_ALDUR_R_RI_32 datasize n offset regsize t__arg) s"
  unfolding execute_ALDUR_R_RI_32_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ALDUR_R_RI_32[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ALDUR_R_RI_32 op1 V imm9 op2 Rn Rt) s"
  unfolding decode_ALDUR_R_RI_32_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_ALDUR_R_RI_64[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "regsize = 64" and "0 \<le> n" and "n \<le> 31" and "datasize = 64"
  shows "traces_enabled (execute_ALDUR_R_RI_64 datasize n offset regsize t__arg) s"
  unfolding execute_ALDUR_R_RI_64_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ALDUR_R_RI_64[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ALDUR_R_RI_64 op1 V imm9 op2 Rn Rt) s"
  unfolding decode_ALDUR_R_RI_64_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_ALDUR_V_RI_B[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "0 \<le> n" and "n \<le> 31" and "datasize = 8"
  shows "traces_enabled (execute_ALDUR_V_RI_B datasize n offset t__arg) s"
  unfolding execute_ALDUR_V_RI_B_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ALDUR_V_RI_B[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ALDUR_V_RI_B op1 V imm9 op2 Rn Rt) s"
  unfolding decode_ALDUR_V_RI_B_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_ALDUR_V_RI_D[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "0 \<le> n" and "n \<le> 31" and "datasize = 64"
  shows "traces_enabled (execute_ALDUR_V_RI_D datasize n offset t__arg) s"
  unfolding execute_ALDUR_V_RI_D_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ALDUR_V_RI_D[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ALDUR_V_RI_D op1 V imm9 op2 Rn Rt) s"
  unfolding decode_ALDUR_V_RI_D_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_ALDUR_V_RI_H[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "0 \<le> n" and "n \<le> 31" and "datasize = 16"
  shows "traces_enabled (execute_ALDUR_V_RI_H datasize n offset t__arg) s"
  unfolding execute_ALDUR_V_RI_H_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ALDUR_V_RI_H[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ALDUR_V_RI_H op1 V imm9 op2 Rn Rt) s"
  unfolding decode_ALDUR_V_RI_H_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_ALDUR_V_RI_Q[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "0 \<le> n" and "n \<le> 31" and "datasize = 128"
  shows "traces_enabled (execute_ALDUR_V_RI_Q datasize n offset t__arg) s"
  unfolding execute_ALDUR_V_RI_Q_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ALDUR_V_RI_Q[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ALDUR_V_RI_Q op1 V imm9 op2 Rn Rt) s"
  unfolding decode_ALDUR_V_RI_Q_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_ALDUR_V_RI_S[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "0 \<le> n" and "n \<le> 31" and "datasize = 32"
  shows "traces_enabled (execute_ALDUR_V_RI_S datasize n offset t__arg) s"
  unfolding execute_ALDUR_V_RI_S_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ALDUR_V_RI_S[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ALDUR_V_RI_S op1 V imm9 op2 Rn Rt) s"
  unfolding decode_ALDUR_V_RI_S_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_ALIGND_C_CI_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> d" and "d \<le> 31" and "0 \<le> align" and "align \<le> 63"
  shows "traces_enabled (execute_ALIGND_C_CI_C align d n) s"
  unfolding execute_ALIGND_C_CI_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ALIGND_C_CI_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ALIGND_C_CI_C imm6 U Cn Cd) s"
  unfolding decode_ALIGND_C_CI_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_ALIGNU_C_CI_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> d" and "d \<le> 31" and "0 \<le> align" and "align \<le> 63"
  shows "traces_enabled (execute_ALIGNU_C_CI_C align d n) s"
  unfolding execute_ALIGNU_C_CI_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ALIGNU_C_CI_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ALIGNU_C_CI_C imm6 U Cn Cd) s"
  unfolding decode_ALIGNU_C_CI_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_ASTLRB_R_R_B[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "0 \<le> n" and "n \<le> 31" and "datasize = 8"
  shows "traces_enabled (execute_ASTLRB_R_R_B acctype datasize n t__arg) s"
  unfolding execute_ASTLRB_R_R_B_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ASTLRB_R_R_B[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ASTLRB_R_R_B L Rn Rt) s"
  unfolding decode_ASTLRB_R_R_B_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_ASTLR_C_R_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "0 \<le> n" and "n \<le> 31"
  shows "traces_enabled (execute_ASTLR_C_R_C acctype n t__arg) s"
  unfolding execute_ASTLR_C_R_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ASTLR_C_R_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ASTLR_C_R_C L Rn Ct) s"
  unfolding decode_ASTLR_C_R_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_ASTLR_R_R_32[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "0 \<le> n" and "n \<le> 31" and "datasize = 32"
  shows "traces_enabled (execute_ASTLR_R_R_32 acctype datasize n t__arg) s"
  unfolding execute_ASTLR_R_R_32_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ASTLR_R_R_32[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ASTLR_R_R_32 L Rn Rt) s"
  unfolding decode_ASTLR_R_R_32_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_ASTRB_R_RRB_B[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "shift = 0" and "l__556 = 0" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31"
  shows "traces_enabled (execute_ASTRB_R_RRB_B extend_type m n l__556 shift t__arg) s"
  unfolding execute_ASTRB_R_RRB_B_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ASTRB_R_RRB_B[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ASTRB_R_RRB_B L Rm sign sz S opc Rn Rt) s"
  unfolding decode_ASTRB_R_RRB_B_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_ASTRB_R_RUI_B[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "0 \<le> n" and "n \<le> 31" and "datasize = 8"
  shows "traces_enabled (execute_ASTRB_R_RUI_B datasize n offset t__arg) s"
  unfolding execute_ASTRB_R_RUI_B_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ASTRB_R_RUI_B[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ASTRB_R_RUI_B L imm9 op Rn Rt) s"
  unfolding decode_ASTRB_R_RUI_B_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_ASTRH_R_RRB_32[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "shift \<in> {0, 1}" and "l__555 = 1" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31"
  shows "traces_enabled (execute_ASTRH_R_RRB_32 extend_type m n l__555 shift t__arg) s"
  unfolding execute_ASTRH_R_RRB_32_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ASTRH_R_RRB_32[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ASTRH_R_RRB_32 L Rm sign sz S opc Rn Rt) s"
  unfolding decode_ASTRH_R_RRB_32_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_ASTR_C_RRB_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31"
  shows "traces_enabled (execute_ASTR_C_RRB_C extend_type m n shift t__arg) s"
  unfolding execute_ASTR_C_RRB_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ASTR_C_RRB_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ASTR_C_RRB_C Rm sign sz S L Rn Ct) s"
  unfolding decode_ASTR_C_RRB_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_ASTR_C_RUI_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "0 \<le> n" and "n \<le> 31"
  shows "traces_enabled (execute_ASTR_C_RUI_C n offset t__arg) s"
  unfolding execute_ASTR_C_RUI_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ASTR_C_RUI_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ASTR_C_RUI_C L imm9 op Rn Ct) s"
  unfolding decode_ASTR_C_RUI_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_ASTR_R_RRB_32[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "shift \<in> {0, 2}" and "l__554 = 2" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31"
  shows "traces_enabled (execute_ASTR_R_RRB_32 extend_type m n l__554 shift t__arg) s"
  unfolding execute_ASTR_R_RRB_32_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ASTR_R_RRB_32[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ASTR_R_RRB_32 L Rm sign sz S opc Rn Rt) s"
  unfolding decode_ASTR_R_RRB_32_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_ASTR_R_RRB_64[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "shift \<in> {0, 3}" and "l__553 = 3" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31"
  shows "traces_enabled (execute_ASTR_R_RRB_64 extend_type m n l__553 shift t__arg) s"
  unfolding execute_ASTR_R_RRB_64_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ASTR_R_RRB_64[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ASTR_R_RRB_64 L Rm sign sz S opc Rn Rt) s"
  unfolding decode_ASTR_R_RRB_64_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_ASTR_R_RUI_32[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "0 \<le> n" and "n \<le> 31" and "datasize = 32"
  shows "traces_enabled (execute_ASTR_R_RUI_32 datasize n offset t__arg) s"
  unfolding execute_ASTR_R_RUI_32_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ASTR_R_RUI_32[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ASTR_R_RUI_32 L imm9 op Rn Rt) s"
  unfolding decode_ASTR_R_RUI_32_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_ASTR_R_RUI_64[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "0 \<le> n" and "n \<le> 31" and "datasize = 64"
  shows "traces_enabled (execute_ASTR_R_RUI_64 datasize n offset t__arg) s"
  unfolding execute_ASTR_R_RUI_64_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ASTR_R_RUI_64[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ASTR_R_RUI_64 L imm9 op Rn Rt) s"
  unfolding decode_ASTR_R_RUI_64_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_ASTR_V_RRB_D[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "shift \<in> {0, 3}" and "l__552 = 3" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31"
  shows "traces_enabled (execute_ASTR_V_RRB_D extend_type m n l__552 shift t__arg) s"
  unfolding execute_ASTR_V_RRB_D_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ASTR_V_RRB_D[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ASTR_V_RRB_D L Rm sign sz S opc Rn Rt) s"
  unfolding decode_ASTR_V_RRB_D_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_ASTR_V_RRB_S[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "shift \<in> {0, 2}" and "l__551 = 2" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31"
  shows "traces_enabled (execute_ASTR_V_RRB_S extend_type m n l__551 shift t__arg) s"
  unfolding execute_ASTR_V_RRB_S_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ASTR_V_RRB_S[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ASTR_V_RRB_S L Rm sign sz S opc Rn Rt) s"
  unfolding decode_ASTR_V_RRB_S_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_ASTURB_R_RI_32[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "0 \<le> n" and "n \<le> 31" and "datasize = 8"
  shows "traces_enabled (execute_ASTURB_R_RI_32 datasize n offset t__arg) s"
  unfolding execute_ASTURB_R_RI_32_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ASTURB_R_RI_32[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ASTURB_R_RI_32 op1 V imm9 op2 Rn Rt) s"
  unfolding decode_ASTURB_R_RI_32_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_ASTURH_R_RI_32[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "0 \<le> n" and "n \<le> 31" and "datasize = 16"
  shows "traces_enabled (execute_ASTURH_R_RI_32 datasize n offset t__arg) s"
  unfolding execute_ASTURH_R_RI_32_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ASTURH_R_RI_32[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ASTURH_R_RI_32 op1 V imm9 op2 Rn Rt) s"
  unfolding decode_ASTURH_R_RI_32_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_ASTUR_C_RI_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "0 \<le> n" and "n \<le> 31"
  shows "traces_enabled (execute_ASTUR_C_RI_C n offset t__arg) s"
  unfolding execute_ASTUR_C_RI_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ASTUR_C_RI_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ASTUR_C_RI_C op1 V imm9 op2 Rn Ct) s"
  unfolding decode_ASTUR_C_RI_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_ASTUR_R_RI_32[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "0 \<le> n" and "n \<le> 31" and "datasize = 32"
  shows "traces_enabled (execute_ASTUR_R_RI_32 datasize n offset t__arg) s"
  unfolding execute_ASTUR_R_RI_32_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ASTUR_R_RI_32[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ASTUR_R_RI_32 op1 V imm9 op2 Rn Rt) s"
  unfolding decode_ASTUR_R_RI_32_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_ASTUR_R_RI_64[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "0 \<le> n" and "n \<le> 31" and "datasize = 64"
  shows "traces_enabled (execute_ASTUR_R_RI_64 datasize n offset t__arg) s"
  unfolding execute_ASTUR_R_RI_64_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ASTUR_R_RI_64[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ASTUR_R_RI_64 op1 V imm9 op2 Rn Rt) s"
  unfolding decode_ASTUR_R_RI_64_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_ASTUR_V_RI_B[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "0 \<le> n" and "n \<le> 31" and "datasize = 8"
  shows "traces_enabled (execute_ASTUR_V_RI_B datasize n offset t__arg) s"
  unfolding execute_ASTUR_V_RI_B_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ASTUR_V_RI_B[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ASTUR_V_RI_B op1 V imm9 op2 Rn Rt) s"
  unfolding decode_ASTUR_V_RI_B_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_ASTUR_V_RI_D[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "0 \<le> n" and "n \<le> 31" and "datasize = 64"
  shows "traces_enabled (execute_ASTUR_V_RI_D datasize n offset t__arg) s"
  unfolding execute_ASTUR_V_RI_D_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ASTUR_V_RI_D[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ASTUR_V_RI_D op1 V imm9 op2 Rn Rt) s"
  unfolding decode_ASTUR_V_RI_D_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_ASTUR_V_RI_H[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "0 \<le> n" and "n \<le> 31" and "datasize = 16"
  shows "traces_enabled (execute_ASTUR_V_RI_H datasize n offset t__arg) s"
  unfolding execute_ASTUR_V_RI_H_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ASTUR_V_RI_H[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ASTUR_V_RI_H op1 V imm9 op2 Rn Rt) s"
  unfolding decode_ASTUR_V_RI_H_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_ASTUR_V_RI_Q[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "0 \<le> n" and "n \<le> 31" and "datasize = 128"
  shows "traces_enabled (execute_ASTUR_V_RI_Q datasize n offset t__arg) s"
  unfolding execute_ASTUR_V_RI_Q_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ASTUR_V_RI_Q[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ASTUR_V_RI_Q op1 V imm9 op2 Rn Rt) s"
  unfolding decode_ASTUR_V_RI_Q_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_ASTUR_V_RI_S[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "0 \<le> n" and "n \<le> 31" and "datasize = 32"
  shows "traces_enabled (execute_ASTUR_V_RI_S datasize n offset t__arg) s"
  unfolding execute_ASTUR_V_RI_S_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ASTUR_V_RI_S[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ASTUR_V_RI_S op1 V imm9 op2 Rn Rt) s"
  unfolding decode_ASTUR_V_RI_S_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_BICFLGS_C_CI_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_BICFLGS_C_CI_C d mask__arg n) s"
  unfolding execute_BICFLGS_C_CI_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_BICFLGS_C_CI_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_BICFLGS_C_CI_C imm8 Cn Cd) s"
  unfolding decode_BICFLGS_C_CI_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_BICFLGS_C_CR_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_BICFLGS_C_CR_C d m n) s"
  unfolding execute_BICFLGS_C_CR_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_BICFLGS_C_CR_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_BICFLGS_C_CR_C Rm opc Cn Cd) s"
  unfolding decode_BICFLGS_C_CR_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_BLRR_C_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "n \<in> invoked_regs"
  shows "traces_enabled (execute_BLRR_C_C branch_type n) s"
  unfolding execute_BLRR_C_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_BLRR_C_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "uint Cn \<in> invoked_regs"
  shows "traces_enabled (decode_BLRR_C_C opc Cn) s"
  unfolding decode_BLRR_C_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_BLRS_C_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "n \<in> invoked_regs"
  shows "traces_enabled (execute_BLRS_C_C branch_type n) s"
  unfolding execute_BLRS_C_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_BLRS_C_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "uint Cn \<in> invoked_regs"
  shows "traces_enabled (decode_BLRS_C_C opc Cn) s"
  unfolding decode_BLRS_C_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_BLRS_C_C_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "m \<in> invoked_regs" and "n \<in> invoked_regs"
  shows "traces_enabled (execute_BLRS_C_C_C branch_type m n) s"
  unfolding execute_BLRS_C_C_C_def bind_assoc
  by (traces_enabledI assms: assms intro: enabled_branch_target_CapUnseal_if_clear elim: branch_sealed_pair_enabled_pcc traces_enabled_C_set_29_branch_sealed_pair)

lemma traces_enabled_decode_BLRS_C_C_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "uint Cm \<in> invoked_regs" and "uint Cn \<in> invoked_regs"
  shows "traces_enabled (decode_BLRS_C_C_C Cm opc Cn) s"
  unfolding decode_BLRS_C_C_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_BLR_CI_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "n = 29 \<longrightarrow> 29 \<in> invoked_indirect_regs" and "RegAuth n \<in> load_auths" and "is_indirect_branch"
  shows "traces_enabled (execute_BLR_CI_C branch_type n offset) s"
  unfolding execute_BLR_CI_C_def bind_assoc
  by (traces_enabledI assms: assms intro: traces_enabled_C_set_if_sentry elim: enabled_branch_target_CapUnseal_mem_cap enabled_branch_target_CapSquashPostLoadCap Run_CSP_or_C_read_invoked_indirect_caps)

lemma traces_enabled_decode_BLR_CI_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "uint Cn = 29 \<longrightarrow> 29 \<in> invoked_indirect_regs" and "RegAuth (uint Cn) \<in> load_auths" and "is_indirect_branch"
  shows "traces_enabled (decode_BLR_CI_C imm7 Cn) s"
  unfolding decode_BLR_CI_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_BLR_C_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "n \<in> invoked_regs"
  shows "traces_enabled (execute_BLR_C_C branch_type n) s"
  unfolding execute_BLR_C_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_BLR_C_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "uint Cn \<in> invoked_regs"
  shows "traces_enabled (decode_BLR_C_C opc Cn) s"
  unfolding decode_BLR_C_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_BRR_C_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "n \<in> invoked_regs"
  shows "traces_enabled (execute_BRR_C_C branch_type n) s"
  unfolding execute_BRR_C_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_BRR_C_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "uint Cn \<in> invoked_regs"
  shows "traces_enabled (decode_BRR_C_C opc Cn) s"
  unfolding decode_BRR_C_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_BRS_C_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "n \<in> invoked_regs"
  shows "traces_enabled (execute_BRS_C_C branch_type n) s"
  unfolding execute_BRS_C_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_BRS_C_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "uint Cn \<in> invoked_regs"
  shows "traces_enabled (decode_BRS_C_C opc Cn) s"
  unfolding decode_BRS_C_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_BRS_C_C_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "m \<in> invoked_regs" and "n \<in> invoked_regs"
  shows "traces_enabled (execute_BRS_C_C_C branch_type m n) s"
  unfolding execute_BRS_C_C_C_def bind_assoc
  by (traces_enabledI assms: assms intro: enabled_branch_target_CapUnseal_if_clear elim: branch_sealed_pair_enabled_pcc traces_enabled_C_set_29_branch_sealed_pair)

lemma traces_enabled_decode_BRS_C_C_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "uint Cm \<in> invoked_regs" and "uint Cn \<in> invoked_regs"
  shows "traces_enabled (decode_BRS_C_C_C Cm opc Cn) s"
  unfolding decode_BRS_C_C_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_BR_CI_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "n = 29 \<longrightarrow> 29 \<in> invoked_indirect_regs" and "RegAuth n \<in> load_auths" and "is_indirect_branch"
  shows "traces_enabled (execute_BR_CI_C branch_type n offset) s"
  unfolding execute_BR_CI_C_def bind_assoc
  by (traces_enabledI assms: assms intro: traces_enabled_C_set_if_sentry elim: enabled_branch_target_CapUnseal_mem_cap enabled_branch_target_CapSquashPostLoadCap Run_CSP_or_C_read_invoked_indirect_caps)

lemma traces_enabled_decode_BR_CI_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "uint Cn = 29 \<longrightarrow> 29 \<in> invoked_indirect_regs" and "RegAuth (uint Cn) \<in> load_auths" and "is_indirect_branch"
  shows "traces_enabled (decode_BR_CI_C imm7 Cn) s"
  unfolding decode_BR_CI_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_BR_C_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "n \<in> invoked_regs"
  shows "traces_enabled (execute_BR_C_C branch_type n) s"
  unfolding execute_BR_C_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_BR_C_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "uint Cn \<in> invoked_regs"
  shows "traces_enabled (decode_BR_C_C opc Cn) s"
  unfolding decode_BR_C_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_BUILD_C_C_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_BUILD_C_C_C d m n) s"
  unfolding execute_BUILD_C_C_C_def bind_assoc
  by (traces_enabledI assms: assms elim: CapIsSubSetOf_WithTagSet_derivable Run_or_boolM_E Run_bindE simp: CapIsBaseAboveLimit_get_base_leq_get_limit)

lemma traces_enabled_decode_BUILD_C_C_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_BUILD_C_C_C Cm opc Cn Cd) s"
  unfolding decode_BUILD_C_C_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_BX___C[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_BX___C branch_type) s"
  unfolding execute_BX___C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_BX___C[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_BX___C opc) s"
  unfolding decode_BX___C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_CASAL_C_R_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "0 \<le> s__arg" and "s__arg \<le> 31" and "0 \<le> n" and "n \<le> 31" and "\<not>invokes_indirect_caps" and "BaseRegAuth n \<in> load_auths"
  shows "traces_enabled (execute_CASAL_C_R_C ldacctype n s__arg stacctype t__arg) s"
  unfolding execute_CASAL_C_R_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_CASAL_C_R_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "\<not>invokes_indirect_caps" and "BaseRegAuth (uint Rn) \<in> load_auths"
  shows "traces_enabled (decode_CASAL_C_R_C L Cs R Rn Ct) s"
  unfolding decode_CASAL_C_R_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_CASA_C_R_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "0 \<le> s__arg" and "s__arg \<le> 31" and "0 \<le> n" and "n \<le> 31" and "\<not>invokes_indirect_caps" and "BaseRegAuth n \<in> load_auths"
  shows "traces_enabled (execute_CASA_C_R_C ldacctype n s__arg stacctype t__arg) s"
  unfolding execute_CASA_C_R_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_CASA_C_R_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "\<not>invokes_indirect_caps" and "BaseRegAuth (uint Rn) \<in> load_auths"
  shows "traces_enabled (decode_CASA_C_R_C L Cs R Rn Ct) s"
  unfolding decode_CASA_C_R_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_CASL_C_R_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "0 \<le> s__arg" and "s__arg \<le> 31" and "0 \<le> n" and "n \<le> 31" and "\<not>invokes_indirect_caps" and "BaseRegAuth n \<in> load_auths"
  shows "traces_enabled (execute_CASL_C_R_C ldacctype n s__arg stacctype t__arg) s"
  unfolding execute_CASL_C_R_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_CASL_C_R_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "\<not>invokes_indirect_caps" and "BaseRegAuth (uint Rn) \<in> load_auths"
  shows "traces_enabled (decode_CASL_C_R_C L Cs R Rn Ct) s"
  unfolding decode_CASL_C_R_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_CAS_C_R_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "0 \<le> s__arg" and "s__arg \<le> 31" and "0 \<le> n" and "n \<le> 31" and "\<not>invokes_indirect_caps" and "BaseRegAuth n \<in> load_auths"
  shows "traces_enabled (execute_CAS_C_R_C ldacctype n s__arg stacctype t__arg) s"
  unfolding execute_CAS_C_R_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_CAS_C_R_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "\<not>invokes_indirect_caps" and "BaseRegAuth (uint Rn) \<in> load_auths"
  shows "traces_enabled (decode_CAS_C_R_C L Cs R Rn Ct) s"
  unfolding decode_CAS_C_R_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_CFHI_R_C_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_CFHI_R_C_C d n) s"
  unfolding execute_CFHI_R_C_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_CFHI_R_C_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_CFHI_R_C_C opc Cn Rd) s"
  unfolding decode_CFHI_R_C_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_CHKEQ___CC_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31"
  shows "traces_enabled (execute_CHKEQ___CC_C m n) s"
  unfolding execute_CHKEQ___CC_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_CHKEQ___CC_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_CHKEQ___CC_C Cm opc Cn) s"
  unfolding decode_CHKEQ___CC_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_CHKSLD_C_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31"
  shows "traces_enabled (execute_CHKSLD_C_C n) s"
  unfolding execute_CHKSLD_C_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_CHKSLD_C_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_CHKSLD_C_C opc Cn) s"
  unfolding decode_CHKSLD_C_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_CHKSSU_C_CC_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_CHKSSU_C_CC_C d m n) s"
  unfolding execute_CHKSSU_C_CC_C_def bind_assoc
  by (traces_enabledI assms: assms elim: CapIsSubSetOf_CapUnseal_derivable Run_and_boolM_E)

lemma traces_enabled_decode_CHKSSU_C_CC_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_CHKSSU_C_CC_C Cm opc Cn Cd) s"
  unfolding decode_CHKSSU_C_CC_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_CHKSS___CC_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31"
  shows "traces_enabled (execute_CHKSS___CC_C m n) s"
  unfolding execute_CHKSS___CC_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_CHKSS___CC_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_CHKSS___CC_C Cm opc Cn) s"
  unfolding decode_CHKSS___CC_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_CHKTGD_C_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31"
  shows "traces_enabled (execute_CHKTGD_C_C n) s"
  unfolding execute_CHKTGD_C_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_CHKTGD_C_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_CHKTGD_C_C opc Cn) s"
  unfolding decode_CHKTGD_C_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_CLRPERM_C_CI_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_CLRPERM_C_CI_C d imm n) s"
  unfolding execute_CLRPERM_C_CI_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_CLRPERM_C_CI_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_CLRPERM_C_CI_C perm__arg Cn Cd) s"
  unfolding decode_CLRPERM_C_CI_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_CLRPERM_C_CR_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_CLRPERM_C_CR_C d m n) s"
  unfolding execute_CLRPERM_C_CR_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_CLRPERM_C_CR_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_CLRPERM_C_CR_C Rm Cn Cd) s"
  unfolding decode_CLRPERM_C_CR_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_CLRTAG_C_C_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_CLRTAG_C_C_C d n) s"
  unfolding execute_CLRTAG_C_C_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_CLRTAG_C_C_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_CLRTAG_C_C_C opc Cn Cd) s"
  unfolding decode_CLRTAG_C_C_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_CPYTYPE_C_C_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_CPYTYPE_C_C_C d m n) s"
  unfolding execute_CPYTYPE_C_C_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_CPYTYPE_C_C_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_CPYTYPE_C_C_C Cm opc Cn Cd) s"
  unfolding decode_CPYTYPE_C_C_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_CPYVALUE_C_C_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_CPYVALUE_C_C_C d m n) s"
  unfolding execute_CPYVALUE_C_C_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_CPYVALUE_C_C_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_CPYVALUE_C_C_C Cm opc Cn Cd) s"
  unfolding decode_CPYVALUE_C_C_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_CPY_C_C_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_CPY_C_C_C d n) s"
  unfolding execute_CPY_C_C_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_CPY_C_C_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_CPY_C_C_C opc Cn Cd) s"
  unfolding decode_CPY_C_C_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_CSEAL_C_C_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_CSEAL_C_C_C d m n) s"
  unfolding execute_CSEAL_C_C_C_def bind_assoc
  by (traces_enabledI assms: assms elim: Run_and_boolM_E CapIsInBounds_cursor_in_mem_region)

lemma traces_enabled_decode_CSEAL_C_C_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_CSEAL_C_C_C Cm opc Cn Cd) s"
  unfolding decode_CSEAL_C_C_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_CSEL_C_CI_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_CSEL_C_CI_C cond d m n) s"
  unfolding execute_CSEL_C_CI_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_CSEL_C_CI_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_CSEL_C_CI_C Cm cond Cn Cd) s"
  unfolding decode_CSEL_C_CI_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_CTHI_C_CR_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_CTHI_C_CR_C d m n) s"
  unfolding execute_CTHI_C_CR_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_CTHI_C_CR_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_CTHI_C_CR_C Rm opc Cn Cd) s"
  unfolding decode_CTHI_C_CR_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_CVTDZ_C_R_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_CVTDZ_C_R_C d n) s"
  unfolding execute_CVTDZ_C_R_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_CVTDZ_C_R_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_CVTDZ_C_R_C opc Rn Cd) s"
  unfolding decode_CVTDZ_C_R_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_CVTD_C_R_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_CVTD_C_R_C d n) s"
  unfolding execute_CVTD_C_R_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_CVTD_C_R_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_CVTD_C_R_C opc Rn Cd) s"
  unfolding decode_CVTD_C_R_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_CVTD_R_C_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_CVTD_R_C_C d n) s"
  unfolding execute_CVTD_R_C_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_CVTD_R_C_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_CVTD_R_C_C opc Cn Rd) s"
  unfolding decode_CVTD_R_C_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_CVTPZ_C_R_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_CVTPZ_C_R_C d n) s"
  unfolding execute_CVTPZ_C_R_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_CVTPZ_C_R_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_CVTPZ_C_R_C opc Rn Cd) s"
  unfolding decode_CVTPZ_C_R_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_CVTP_C_R_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_CVTP_C_R_C d n) s"
  unfolding execute_CVTP_C_R_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_CVTP_C_R_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_CVTP_C_R_C opc Rn Cd) s"
  unfolding decode_CVTP_C_R_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_CVTP_R_C_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_CVTP_R_C_C d n) s"
  unfolding execute_CVTP_R_C_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_CVTP_R_C_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_CVTP_R_C_C opc Cn Rd) s"
  unfolding decode_CVTP_R_C_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_CVTZ_C_CR_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_CVTZ_C_CR_C d m n) s"
  unfolding execute_CVTZ_C_CR_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_CVTZ_C_CR_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_CVTZ_C_CR_C Rm Cn Cd) s"
  unfolding decode_CVTZ_C_CR_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_CVT_C_CR_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_CVT_C_CR_C d m n) s"
  unfolding execute_CVT_C_CR_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_CVT_C_CR_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_CVT_C_CR_C Rm Cn Cd) s"
  unfolding decode_CVT_C_CR_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_CVT_R_CC_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_CVT_R_CC_C d m n) s"
  unfolding execute_CVT_R_CC_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_CVT_R_CC_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_CVT_R_CC_C Cm Cn Rd) s"
  unfolding decode_CVT_R_CC_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_EORFLGS_C_CI_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_EORFLGS_C_CI_C d mask__arg n) s"
  unfolding execute_EORFLGS_C_CI_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_EORFLGS_C_CI_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_EORFLGS_C_CI_C imm8 Cn Cd) s"
  unfolding decode_EORFLGS_C_CI_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_EORFLGS_C_CR_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_EORFLGS_C_CR_C d m n) s"
  unfolding execute_EORFLGS_C_CR_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_EORFLGS_C_CR_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_EORFLGS_C_CR_C Rm opc Cn Cd) s"
  unfolding decode_EORFLGS_C_CR_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_GCBASE_R_C_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_GCBASE_R_C_C d n) s"
  unfolding execute_GCBASE_R_C_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_GCBASE_R_C_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_GCBASE_R_C_C opc Cn Rd) s"
  unfolding decode_GCBASE_R_C_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_GCFLGS_R_C_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_GCFLGS_R_C_C d n) s"
  unfolding execute_GCFLGS_R_C_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_GCFLGS_R_C_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_GCFLGS_R_C_C opc Cn Rd) s"
  unfolding decode_GCFLGS_R_C_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_GCLEN_R_C_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_GCLEN_R_C_C d n) s"
  unfolding execute_GCLEN_R_C_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_GCLEN_R_C_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_GCLEN_R_C_C opc Cn Rd) s"
  unfolding decode_GCLEN_R_C_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_GCLIM_R_C_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_GCLIM_R_C_C d n) s"
  unfolding execute_GCLIM_R_C_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_GCLIM_R_C_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_GCLIM_R_C_C opc Cn Rd) s"
  unfolding decode_GCLIM_R_C_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_GCOFF_R_C_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_GCOFF_R_C_C d n) s"
  unfolding execute_GCOFF_R_C_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_GCOFF_R_C_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_GCOFF_R_C_C opc Cn Rd) s"
  unfolding decode_GCOFF_R_C_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_GCPERM_R_C_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_GCPERM_R_C_C d n) s"
  unfolding execute_GCPERM_R_C_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_GCPERM_R_C_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_GCPERM_R_C_C opc Cn Rd) s"
  unfolding decode_GCPERM_R_C_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_GCSEAL_R_C_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_GCSEAL_R_C_C d n) s"
  unfolding execute_GCSEAL_R_C_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_GCSEAL_R_C_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_GCSEAL_R_C_C opc Cn Rd) s"
  unfolding decode_GCSEAL_R_C_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_GCTAG_R_C_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_GCTAG_R_C_C d n) s"
  unfolding execute_GCTAG_R_C_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_GCTAG_R_C_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_GCTAG_R_C_C opc Cn Rd) s"
  unfolding decode_GCTAG_R_C_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_GCTYPE_R_C_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_GCTYPE_R_C_C d n) s"
  unfolding execute_GCTYPE_R_C_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_GCTYPE_R_C_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_GCTYPE_R_C_C opc Cn Rd) s"
  unfolding decode_GCTYPE_R_C_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_GCVALUE_R_C_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_GCVALUE_R_C_C d n) s"
  unfolding execute_GCVALUE_R_C_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_GCVALUE_R_C_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_GCVALUE_R_C_C opc Cn Rd) s"
  unfolding decode_GCVALUE_R_C_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_LDAPR_C_R_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "0 \<le> n" and "n \<le> 31" and "\<not>invokes_indirect_caps" and "BaseRegAuth n \<in> load_auths"
  shows "traces_enabled (execute_LDAPR_C_R_C acctype n t__arg) s"
  unfolding execute_LDAPR_C_R_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_LDAPR_C_R_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "\<not>invokes_indirect_caps" and "BaseRegAuth (uint Rn) \<in> load_auths"
  shows "traces_enabled (decode_LDAPR_C_R_C Rn Ct) s"
  unfolding decode_LDAPR_C_R_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_LDAR_C_R_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "0 \<le> n" and "n \<le> 31" and "\<not>invokes_indirect_caps" and "BaseRegAuth n \<in> load_auths"
  shows "traces_enabled (execute_LDAR_C_R_C acctype n t__arg) s"
  unfolding execute_LDAR_C_R_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_LDAR_C_R_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "\<not>invokes_indirect_caps" and "BaseRegAuth (uint Rn) \<in> load_auths"
  shows "traces_enabled (decode_LDAR_C_R_C L Rn Ct) s"
  unfolding decode_LDAR_C_R_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_LDAXP_C_R_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t2" and "t2 \<le> 31" and "0 \<le> t__arg" and "t__arg \<le> 31" and "0 \<le> n" and "n \<le> 31" and "\<not>invokes_indirect_caps" and "BaseRegAuth n \<in> load_auths"
  shows "traces_enabled (execute_LDAXP_C_R_C acctype n t__arg t2) s"
  unfolding execute_LDAXP_C_R_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_LDAXP_C_R_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "\<not>invokes_indirect_caps" and "BaseRegAuth (uint Rn) \<in> load_auths"
  shows "traces_enabled (decode_LDAXP_C_R_C L Ct2 Rn Ct) s"
  unfolding decode_LDAXP_C_R_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_LDAXR_C_R_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "0 \<le> n" and "n \<le> 31" and "\<not>invokes_indirect_caps" and "BaseRegAuth n \<in> load_auths"
  shows "traces_enabled (execute_LDAXR_C_R_C acctype n t__arg) s"
  unfolding execute_LDAXR_C_R_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_LDAXR_C_R_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "\<not>invokes_indirect_caps" and "BaseRegAuth (uint Rn) \<in> load_auths"
  shows "traces_enabled (decode_LDAXR_C_R_C L Rn Ct) s"
  unfolding decode_LDAXR_C_R_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_LDCT_R_R[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "0 \<le> n" and "n \<le> 31" and "BaseRegAuth n \<in> load_auths"
  shows "traces_enabled (execute_LDCT_R_R n t__arg) s"
  unfolding execute_LDCT_R_R_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_LDCT_R_R[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "BaseRegAuth (uint Rn) \<in> load_auths"
  shows "traces_enabled (decode_LDCT_R_R opc Rn Rt) s"
  unfolding decode_LDCT_R_R_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_LDNP_C_RIB_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t2" and "t2 \<le> 31" and "0 \<le> t__arg" and "t__arg \<le> 31" and "0 \<le> n" and "n \<le> 31" and "\<not>invokes_indirect_caps" and "BaseRegAuth n \<in> load_auths"
  shows "traces_enabled (execute_LDNP_C_RIB_C acctype n offset t__arg t2) s"
  unfolding execute_LDNP_C_RIB_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_LDNP_C_RIB_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "\<not>invokes_indirect_caps" and "BaseRegAuth (uint Rn) \<in> load_auths"
  shows "traces_enabled (decode_LDNP_C_RIB_C L imm7 Ct2 Rn Ct) s"
  unfolding decode_LDNP_C_RIB_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_LDPBLR_C_C_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "0 \<le> n" and "n \<le> 31" and "t__arg = 29 \<longrightarrow> n \<in> invoked_indirect_regs" and "RegAuth n \<in> load_auths" and "t__arg \<noteq> 29 \<longrightarrow> \<not>invokes_indirect_caps" and "is_indirect_branch"
  shows "traces_enabled (execute_LDPBLR_C_C_C branch_type n t__arg) s"
  unfolding execute_LDPBLR_C_C_C_def bind_assoc
  by (traces_enabledI assms: assms elim: traces_enabled_C_set_mem_cap[where n = t__arg] traces_enabled_C_set_mem_cap[where n = 29] enabled_branch_target_CapUnseal_mem_cap enabled_branch_target_CapSquashPostLoadCap)

lemma traces_enabled_decode_LDPBLR_C_C_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "uint Ct = 29 \<longrightarrow> uint Cn \<in> invoked_indirect_regs" and "RegAuth (uint Cn) \<in> load_auths" and "uint Ct \<noteq> 29 \<longrightarrow> \<not>invokes_indirect_caps" and "is_indirect_branch"
  shows "traces_enabled (decode_LDPBLR_C_C_C opc Cn Ct) s"
  unfolding decode_LDPBLR_C_C_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_LDPBR_C_C_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "0 \<le> n" and "n \<le> 31" and "t__arg = 29 \<longrightarrow> n \<in> invoked_indirect_regs" and "RegAuth n \<in> load_auths" and "t__arg \<noteq> 29 \<longrightarrow> \<not>invokes_indirect_caps" and "is_indirect_branch"
  shows "traces_enabled (execute_LDPBR_C_C_C branch_type n t__arg) s"
  unfolding execute_LDPBR_C_C_C_def bind_assoc
  by (traces_enabledI assms: assms elim: traces_enabled_C_set_mem_cap enabled_branch_target_CapUnseal_mem_cap enabled_branch_target_CapSquashPostLoadCap)

lemma traces_enabled_decode_LDPBR_C_C_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "uint Ct = 29 \<longrightarrow> uint Cn \<in> invoked_indirect_regs" and "RegAuth (uint Cn) \<in> load_auths" and "uint Ct \<noteq> 29 \<longrightarrow> \<not>invokes_indirect_caps" and "is_indirect_branch"
  shows "traces_enabled (decode_LDPBR_C_C_C opc Cn Ct) s"
  unfolding decode_LDPBR_C_C_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_LDP_CC_RIAW_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t2" and "t2 \<le> 31" and "0 \<le> t__arg" and "t__arg \<le> 31" and "0 \<le> n" and "n \<le> 31" and "\<not>invokes_indirect_caps" and "BaseRegAuth n \<in> load_auths"
  shows "traces_enabled (execute_LDP_CC_RIAW_C acctype n offset t__arg t2) s"
  unfolding execute_LDP_CC_RIAW_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_LDP_CC_RIAW_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "\<not>invokes_indirect_caps" and "BaseRegAuth (uint Rn) \<in> load_auths"
  shows "traces_enabled (decode_LDP_CC_RIAW_C L imm7 Ct2 Rn Ct) s"
  unfolding decode_LDP_CC_RIAW_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_LDP_C_RIBW_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t2" and "t2 \<le> 31" and "0 \<le> t__arg" and "t__arg \<le> 31" and "0 \<le> n" and "n \<le> 31" and "\<not>invokes_indirect_caps" and "BaseRegAuth n \<in> load_auths"
  shows "traces_enabled (execute_LDP_C_RIBW_C acctype n offset t__arg t2) s"
  unfolding execute_LDP_C_RIBW_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_LDP_C_RIBW_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "\<not>invokes_indirect_caps" and "BaseRegAuth (uint Rn) \<in> load_auths"
  shows "traces_enabled (decode_LDP_C_RIBW_C L imm7 Ct2 Rn Ct) s"
  unfolding decode_LDP_C_RIBW_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_LDP_C_RIB_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t2" and "t2 \<le> 31" and "0 \<le> t__arg" and "t__arg \<le> 31" and "0 \<le> n" and "n \<le> 31" and "\<not>invokes_indirect_caps" and "BaseRegAuth n \<in> load_auths"
  shows "traces_enabled (execute_LDP_C_RIB_C acctype n offset t__arg t2) s"
  unfolding execute_LDP_C_RIB_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_LDP_C_RIB_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "\<not>invokes_indirect_caps" and "BaseRegAuth (uint Rn) \<in> load_auths"
  shows "traces_enabled (decode_LDP_C_RIB_C L imm7 Ct2 Rn Ct) s"
  unfolding decode_LDP_C_RIB_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_LDR_C_I_C[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "\<not>invokes_indirect_caps" and "PCCAuth \<in> load_auths"
  shows "traces_enabled (execute_LDR_C_I_C offset t__arg) s"
  unfolding execute_LDR_C_I_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_LDR_C_I_C[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "\<not>invokes_indirect_caps" and "PCCAuth \<in> load_auths"
  shows "traces_enabled (decode_LDR_C_I_C imm17 Ct) s"
  unfolding decode_LDR_C_I_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_LDR_C_RIAW_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "0 \<le> n" and "n \<le> 31" and "\<not>invokes_indirect_caps" and "BaseRegAuth n \<in> load_auths"
  shows "traces_enabled (execute_LDR_C_RIAW_C n offset t__arg) s"
  unfolding execute_LDR_C_RIAW_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_LDR_C_RIAW_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "\<not>invokes_indirect_caps" and "BaseRegAuth (uint Rn) \<in> load_auths"
  shows "traces_enabled (decode_LDR_C_RIAW_C opc imm9 Rn Ct) s"
  unfolding decode_LDR_C_RIAW_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_LDR_C_RIBW_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "0 \<le> n" and "n \<le> 31" and "\<not>invokes_indirect_caps" and "BaseRegAuth n \<in> load_auths"
  shows "traces_enabled (execute_LDR_C_RIBW_C n offset t__arg) s"
  unfolding execute_LDR_C_RIBW_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_LDR_C_RIBW_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "\<not>invokes_indirect_caps" and "BaseRegAuth (uint Rn) \<in> load_auths"
  shows "traces_enabled (decode_LDR_C_RIBW_C opc imm9 Rn Ct) s"
  unfolding decode_LDR_C_RIBW_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_LDR_C_RRB_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "\<not>invokes_indirect_caps" and "BaseRegAuth n \<in> load_auths"
  shows "traces_enabled (execute_LDR_C_RRB_C extend_type m n shift t__arg) s"
  unfolding execute_LDR_C_RRB_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_LDR_C_RRB_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "\<not>invokes_indirect_caps" and "BaseRegAuth (uint Rn) \<in> load_auths"
  shows "traces_enabled (decode_LDR_C_RRB_C opc Rm sign sz S Rn Ct) s"
  unfolding decode_LDR_C_RRB_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_LDR_C_RUIB_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "0 \<le> n" and "n \<le> 31" and "\<not>invokes_indirect_caps" and "BaseRegAuth n \<in> load_auths"
  shows "traces_enabled (execute_LDR_C_RUIB_C n offset t__arg) s"
  unfolding execute_LDR_C_RUIB_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_LDR_C_RUIB_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "\<not>invokes_indirect_caps" and "BaseRegAuth (uint Rn) \<in> load_auths"
  shows "traces_enabled (decode_LDR_C_RUIB_C L imm12 Rn Ct) s"
  unfolding decode_LDR_C_RUIB_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_LDTR_C_RIB_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "0 \<le> n" and "n \<le> 31" and "\<not>invokes_indirect_caps" and "BaseRegAuth n \<in> load_auths"
  shows "traces_enabled (execute_LDTR_C_RIB_C n offset t__arg) s"
  unfolding execute_LDTR_C_RIB_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_LDTR_C_RIB_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "\<not>invokes_indirect_caps" and "BaseRegAuth (uint Rn) \<in> load_auths"
  shows "traces_enabled (decode_LDTR_C_RIB_C opc imm9 Rn Ct) s"
  unfolding decode_LDTR_C_RIB_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_LDUR_C_RI_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "0 \<le> n" and "n \<le> 31" and "\<not>invokes_indirect_caps" and "BaseRegAuth n \<in> load_auths"
  shows "traces_enabled (execute_LDUR_C_RI_C n offset t__arg) s"
  unfolding execute_LDUR_C_RI_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_LDUR_C_RI_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "\<not>invokes_indirect_caps" and "BaseRegAuth (uint Rn) \<in> load_auths"
  shows "traces_enabled (decode_LDUR_C_RI_C opc imm9 Rn Ct) s"
  unfolding decode_LDUR_C_RI_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_LDXP_C_R_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t2" and "t2 \<le> 31" and "0 \<le> t__arg" and "t__arg \<le> 31" and "0 \<le> n" and "n \<le> 31" and "\<not>invokes_indirect_caps" and "BaseRegAuth n \<in> load_auths"
  shows "traces_enabled (execute_LDXP_C_R_C acctype n t__arg t2) s"
  unfolding execute_LDXP_C_R_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_LDXP_C_R_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "\<not>invokes_indirect_caps" and "BaseRegAuth (uint Rn) \<in> load_auths"
  shows "traces_enabled (decode_LDXP_C_R_C L Ct2 Rn Ct) s"
  unfolding decode_LDXP_C_R_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_LDXR_C_R_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "0 \<le> n" and "n \<le> 31" and "\<not>invokes_indirect_caps" and "BaseRegAuth n \<in> load_auths"
  shows "traces_enabled (execute_LDXR_C_R_C acctype n t__arg) s"
  unfolding execute_LDXR_C_R_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_LDXR_C_R_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "\<not>invokes_indirect_caps" and "BaseRegAuth (uint Rn) \<in> load_auths"
  shows "traces_enabled (decode_LDXR_C_R_C L Rn Ct) s"
  unfolding decode_LDXR_C_R_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_MRS_C_I_C[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "sys_op2 \<in> {0, 1, 2, 3, 4, 5, 6, 7}" and "sys_op1 \<in> {0, 1, 2, 3, 4, 5, 6, 7}" and "sys_op0 \<in> {2, 3}" and "0 \<le> sys_crn" and "sys_crn \<le> 15" and "0 \<le> sys_crm" and "sys_crm \<le> 15"
  shows "traces_enabled (execute_MRS_C_I_C sys_crm sys_crn sys_op0 sys_op1 sys_op2 t__arg) s"
  unfolding execute_MRS_C_I_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_MRS_C_I_C[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_MRS_C_I_C L o0 op1 CRn CRm op2 Ct) s"
  unfolding decode_MRS_C_I_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_MSR_C_I_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "sys_op2 \<in> {0, 1, 2, 3, 4, 5, 6, 7}" and "sys_op1 \<in> {0, 1, 2, 3, 4, 5, 6, 7}" and "sys_op0 \<in> {2, 3}" and "0 \<le> sys_crn" and "sys_crn \<le> 15" and "0 \<le> sys_crm" and "sys_crm \<le> 15"
  shows "traces_enabled (execute_MSR_C_I_C sys_crm sys_crn sys_op0 sys_op1 sys_op2 t__arg) s"
  unfolding execute_MSR_C_I_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_MSR_C_I_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_MSR_C_I_C L o0 op1 CRn CRm op2 Ct) s"
  unfolding decode_MSR_C_I_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_ORRFLGS_C_CI_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_ORRFLGS_C_CI_C d mask__arg n) s"
  unfolding execute_ORRFLGS_C_CI_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ORRFLGS_C_CI_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ORRFLGS_C_CI_C imm8 Cn Cd) s"
  unfolding decode_ORRFLGS_C_CI_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_ORRFLGS_C_CR_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_ORRFLGS_C_CR_C d m n) s"
  unfolding execute_ORRFLGS_C_CR_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ORRFLGS_C_CR_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ORRFLGS_C_CR_C Rm opc Cn Cd) s"
  unfolding decode_ORRFLGS_C_CR_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_RETR_C_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "n \<in> invoked_regs"
  shows "traces_enabled (execute_RETR_C_C branch_type n) s"
  unfolding execute_RETR_C_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_RETR_C_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "uint Cn \<in> invoked_regs"
  shows "traces_enabled (decode_RETR_C_C opc Cn) s"
  unfolding decode_RETR_C_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_RETS_C_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "n \<in> invoked_regs"
  shows "traces_enabled (execute_RETS_C_C branch_type n) s"
  unfolding execute_RETS_C_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_RETS_C_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "uint Cn \<in> invoked_regs"
  shows "traces_enabled (decode_RETS_C_C opc Cn) s"
  unfolding decode_RETS_C_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_RETS_C_C_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "m \<in> invoked_regs" and "n \<in> invoked_regs"
  shows "traces_enabled (execute_RETS_C_C_C branch_type m n) s"
  unfolding execute_RETS_C_C_C_def bind_assoc
  by (traces_enabledI assms: assms intro: enabled_branch_target_CapUnseal_if_clear elim: branch_sealed_pair_enabled_pcc traces_enabled_C_set_29_branch_sealed_pair)

lemma traces_enabled_decode_RETS_C_C_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "uint Cm \<in> invoked_regs" and "uint Cn \<in> invoked_regs"
  shows "traces_enabled (decode_RETS_C_C_C Cm opc Cn) s"
  unfolding decode_RETS_C_C_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_RET_C_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "n \<in> invoked_regs"
  shows "traces_enabled (execute_RET_C_C branch_type n) s"
  unfolding execute_RET_C_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_RET_C_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "uint Cn \<in> invoked_regs"
  shows "traces_enabled (decode_RET_C_C opc Cn) s"
  unfolding decode_RET_C_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_RRLEN_R_R_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_RRLEN_R_R_C d n) s"
  unfolding execute_RRLEN_R_R_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_RRLEN_R_R_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_RRLEN_R_R_C opc Rn Rd) s"
  unfolding decode_RRLEN_R_R_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_RRMASK_R_R_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_RRMASK_R_R_C d n) s"
  unfolding execute_RRMASK_R_R_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_RRMASK_R_R_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_RRMASK_R_R_C opc Rn Rd) s"
  unfolding decode_RRMASK_R_R_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_SCBNDSE_C_CR_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_SCBNDSE_C_CR_C d m n) s"
  unfolding execute_SCBNDSE_C_CR_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_SCBNDSE_C_CR_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_SCBNDSE_C_CR_C Rm opc Cn Cd) s"
  unfolding decode_SCBNDSE_C_CR_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_SCBNDS_C_CI_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> d" and "d \<le> 31" and "length__arg \<le> 2^64"
  shows "traces_enabled (execute_SCBNDS_C_CI_C d length__arg n) s"
  unfolding execute_SCBNDS_C_CI_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_SCBNDS_C_CI_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_SCBNDS_C_CI_C imm6 S Cn Cd) s"
  unfolding decode_SCBNDS_C_CI_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_SCBNDS_C_CI_S[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> d" and "d \<le> 31" and "length__arg \<le> 2^64"
  shows "traces_enabled (execute_SCBNDS_C_CI_S d length__arg n) s"
  unfolding execute_SCBNDS_C_CI_S_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_SCBNDS_C_CI_S[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_SCBNDS_C_CI_S imm6 S Cn Cd) s"
  unfolding decode_SCBNDS_C_CI_S_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_SCBNDS_C_CR_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_SCBNDS_C_CR_C d m n) s"
  unfolding execute_SCBNDS_C_CR_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_SCBNDS_C_CR_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_SCBNDS_C_CR_C Rm opc Cn Cd) s"
  unfolding decode_SCBNDS_C_CR_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_SCFLGS_C_CR_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_SCFLGS_C_CR_C d m n) s"
  unfolding execute_SCFLGS_C_CR_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_SCFLGS_C_CR_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_SCFLGS_C_CR_C Rm Cn Cd) s"
  unfolding decode_SCFLGS_C_CR_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_SCOFF_C_CR_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_SCOFF_C_CR_C d m n) s"
  unfolding execute_SCOFF_C_CR_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_SCOFF_C_CR_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_SCOFF_C_CR_C Rm opc Cn Cd) s"
  unfolding decode_SCOFF_C_CR_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_SCTAG_C_CR_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_SCTAG_C_CR_C d m n) s"
  unfolding execute_SCTAG_C_CR_C_def bind_assoc
  by (traces_enabledI assms: assms elim: and_exp_SystemAccessEnabled_TagSettingEnabledE[where thesis = "(if a then x else y) \<in> derivable_caps s" and a = a for a x y s])

lemma traces_enabled_decode_SCTAG_C_CR_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_SCTAG_C_CR_C Rm Cn Cd) s"
  unfolding decode_SCTAG_C_CR_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_SCVALUE_C_CR_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_SCVALUE_C_CR_C d m n) s"
  unfolding execute_SCVALUE_C_CR_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_SCVALUE_C_CR_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_SCVALUE_C_CR_C Rm opc Cn Cd) s"
  unfolding decode_SCVALUE_C_CR_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_SEAL_C_CC_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_SEAL_C_CC_C d m n) s"
  unfolding execute_SEAL_C_CC_C_def bind_assoc
  by (traces_enabledI assms: assms simp: Run_and_boolM_True_iff elim: CapIsInBounds_cursor_in_mem_region)

lemma traces_enabled_decode_SEAL_C_CC_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_SEAL_C_CC_C Cm opc Cn Cd) s"
  unfolding decode_SEAL_C_CC_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_SEAL_C_CI_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "f \<in> {0, 1, 2, 3}"
  shows "traces_enabled (execute_SEAL_C_CI_C d f n) s"
  unfolding execute_SEAL_C_CI_C_def bind_assoc
  by (traces_enabledI assms: assms intro: CapSetObjectType_sentry_derivable)

lemma traces_enabled_decode_SEAL_C_CI_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_SEAL_C_CI_C form Cn Cd) s"
  unfolding decode_SEAL_C_CI_C_def bind_assoc
  by (cases form rule: exhaustive_2_word) (use assms in \<open>auto intro: traces_enabled_execute_SEAL_C_CI_C\<close>)

lemma traces_enabled_execute_STCT_R_R[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "0 \<le> n" and "n \<le> 31"
  shows "traces_enabled (execute_STCT_R_R n t__arg) s"
  unfolding execute_STCT_R_R_def bind_assoc
  by (traces_enabledI assms: assms elim: and_SystemAccessEnabled_TagSettingEnabledE[where thesis = "(if a then x else y) = z" and a = a for a x y z])

lemma traces_enabled_decode_STCT_R_R[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_STCT_R_R opc Rn Rt) s"
  unfolding decode_STCT_R_R_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_STLR_C_R_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "0 \<le> n" and "n \<le> 31"
  shows "traces_enabled (execute_STLR_C_R_C acctype n t__arg) s"
  unfolding execute_STLR_C_R_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_STLR_C_R_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_STLR_C_R_C L Rn Ct) s"
  unfolding decode_STLR_C_R_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_STLXP_R_CR_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t2" and "t2 \<le> 31" and "0 \<le> t__arg" and "t__arg \<le> 31" and "0 \<le> s__arg" and "s__arg \<le> 31" and "0 \<le> n" and "n \<le> 31"
  shows "traces_enabled (execute_STLXP_R_CR_C acctype n s__arg t__arg t2) s"
  unfolding execute_STLXP_R_CR_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_STLXP_R_CR_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_STLXP_R_CR_C L Rs Ct2 Rn Ct) s"
  unfolding decode_STLXP_R_CR_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_STLXR_R_CR_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "0 \<le> s__arg" and "s__arg \<le> 31" and "0 \<le> n" and "n \<le> 31"
  shows "traces_enabled (execute_STLXR_R_CR_C acctype n s__arg t__arg) s"
  unfolding execute_STLXR_R_CR_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_STLXR_R_CR_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_STLXR_R_CR_C L Rs Rn Ct) s"
  unfolding decode_STLXR_R_CR_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_STNP_C_RIB_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t2" and "t2 \<le> 31" and "0 \<le> t__arg" and "t__arg \<le> 31" and "0 \<le> n" and "n \<le> 31"
  shows "traces_enabled (execute_STNP_C_RIB_C acctype n offset t__arg t2) s"
  unfolding execute_STNP_C_RIB_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_STNP_C_RIB_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_STNP_C_RIB_C L imm7 Ct2 Rn Ct) s"
  unfolding decode_STNP_C_RIB_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_STP_CC_RIAW_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t2" and "t2 \<le> 31" and "0 \<le> t__arg" and "t__arg \<le> 31" and "0 \<le> n" and "n \<le> 31"
  shows "traces_enabled (execute_STP_CC_RIAW_C acctype n offset t__arg t2) s"
  unfolding execute_STP_CC_RIAW_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_STP_CC_RIAW_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_STP_CC_RIAW_C L imm7 Ct2 Rn Ct) s"
  unfolding decode_STP_CC_RIAW_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_STP_C_RIBW_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t2" and "t2 \<le> 31" and "0 \<le> t__arg" and "t__arg \<le> 31" and "0 \<le> n" and "n \<le> 31"
  shows "traces_enabled (execute_STP_C_RIBW_C acctype n offset t__arg t2) s"
  unfolding execute_STP_C_RIBW_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_STP_C_RIBW_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_STP_C_RIBW_C L imm7 Ct2 Rn Ct) s"
  unfolding decode_STP_C_RIBW_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_STP_C_RIB_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t2" and "t2 \<le> 31" and "0 \<le> t__arg" and "t__arg \<le> 31" and "0 \<le> n" and "n \<le> 31"
  shows "traces_enabled (execute_STP_C_RIB_C acctype n offset t__arg t2) s"
  unfolding execute_STP_C_RIB_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_STP_C_RIB_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_STP_C_RIB_C L imm7 Ct2 Rn Ct) s"
  unfolding decode_STP_C_RIB_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_STR_C_RIAW_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "0 \<le> n" and "n \<le> 31"
  shows "traces_enabled (execute_STR_C_RIAW_C n offset t__arg) s"
  unfolding execute_STR_C_RIAW_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_STR_C_RIAW_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_STR_C_RIAW_C opc imm9 Rn Ct) s"
  unfolding decode_STR_C_RIAW_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_STR_C_RIBW_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "0 \<le> n" and "n \<le> 31"
  shows "traces_enabled (execute_STR_C_RIBW_C n offset t__arg) s"
  unfolding execute_STR_C_RIBW_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_STR_C_RIBW_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_STR_C_RIBW_C opc imm9 Rn Ct) s"
  unfolding decode_STR_C_RIBW_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_STR_C_RRB_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31"
  shows "traces_enabled (execute_STR_C_RRB_C extend_type m n shift t__arg) s"
  unfolding execute_STR_C_RRB_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_STR_C_RRB_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_STR_C_RRB_C opc Rm sign sz S Rn Ct) s"
  unfolding decode_STR_C_RRB_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_STR_C_RUIB_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "0 \<le> n" and "n \<le> 31"
  shows "traces_enabled (execute_STR_C_RUIB_C n offset t__arg) s"
  unfolding execute_STR_C_RUIB_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_STR_C_RUIB_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_STR_C_RUIB_C L imm12 Rn Ct) s"
  unfolding decode_STR_C_RUIB_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_STTR_C_RIB_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "0 \<le> n" and "n \<le> 31"
  shows "traces_enabled (execute_STTR_C_RIB_C n offset t__arg) s"
  unfolding execute_STTR_C_RIB_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_STTR_C_RIB_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_STTR_C_RIB_C opc imm9 Rn Ct) s"
  unfolding decode_STTR_C_RIB_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_STUR_C_RI_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "0 \<le> n" and "n \<le> 31"
  shows "traces_enabled (execute_STUR_C_RI_C n offset t__arg) s"
  unfolding execute_STUR_C_RI_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_STUR_C_RI_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_STUR_C_RI_C opc imm9 Rn Ct) s"
  unfolding decode_STUR_C_RI_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_STXP_R_CR_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t2" and "t2 \<le> 31" and "0 \<le> t__arg" and "t__arg \<le> 31" and "0 \<le> s__arg" and "s__arg \<le> 31" and "0 \<le> n" and "n \<le> 31"
  shows "traces_enabled (execute_STXP_R_CR_C acctype n s__arg t__arg t2) s"
  unfolding execute_STXP_R_CR_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_STXP_R_CR_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_STXP_R_CR_C L Rs Ct2 Rn Ct) s"
  unfolding decode_STXP_R_CR_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_STXR_R_CR_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "0 \<le> s__arg" and "s__arg \<le> 31" and "0 \<le> n" and "n \<le> 31"
  shows "traces_enabled (execute_STXR_R_CR_C acctype n s__arg t__arg) s"
  unfolding execute_STXR_R_CR_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_STXR_R_CR_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_STXR_R_CR_C L Rs Rn Ct) s"
  unfolding decode_STXR_R_CR_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_SUBS_R_CC_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_SUBS_R_CC_C d m n) s"
  unfolding execute_SUBS_R_CC_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_SUBS_R_CC_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_SUBS_R_CC_C Cm Cn Rd) s"
  unfolding decode_SUBS_R_CC_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_SUB_C_CIS_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_SUB_C_CIS_C d imm n) s"
  unfolding execute_SUB_C_CIS_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_SUB_C_CIS_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_SUB_C_CIS_C A sh imm12 Cn Cd) s"
  unfolding decode_SUB_C_CIS_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_SWPAL_CC_R_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "0 \<le> s__arg" and "s__arg \<le> 31" and "0 \<le> n" and "n \<le> 31" and "\<not>invokes_indirect_caps" and "BaseRegAuth n \<in> load_auths"
  shows "traces_enabled (execute_SWPAL_CC_R_C ldacctype n s__arg stacctype t__arg) s"
  unfolding execute_SWPAL_CC_R_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_SWPAL_CC_R_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "\<not>invokes_indirect_caps" and "BaseRegAuth (uint Rn) \<in> load_auths"
  shows "traces_enabled (decode_SWPAL_CC_R_C A R Cs Rn Ct) s"
  unfolding decode_SWPAL_CC_R_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_SWPA_CC_R_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "0 \<le> s__arg" and "s__arg \<le> 31" and "0 \<le> n" and "n \<le> 31" and "\<not>invokes_indirect_caps" and "BaseRegAuth n \<in> load_auths"
  shows "traces_enabled (execute_SWPA_CC_R_C ldacctype n s__arg stacctype t__arg) s"
  unfolding execute_SWPA_CC_R_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_SWPA_CC_R_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "\<not>invokes_indirect_caps" and "BaseRegAuth (uint Rn) \<in> load_auths"
  shows "traces_enabled (decode_SWPA_CC_R_C A R Cs Rn Ct) s"
  unfolding decode_SWPA_CC_R_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_SWPL_CC_R_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "0 \<le> s__arg" and "s__arg \<le> 31" and "0 \<le> n" and "n \<le> 31" and "\<not>invokes_indirect_caps" and "BaseRegAuth n \<in> load_auths"
  shows "traces_enabled (execute_SWPL_CC_R_C ldacctype n s__arg stacctype t__arg) s"
  unfolding execute_SWPL_CC_R_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_SWPL_CC_R_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "\<not>invokes_indirect_caps" and "BaseRegAuth (uint Rn) \<in> load_auths"
  shows "traces_enabled (decode_SWPL_CC_R_C A R Cs Rn Ct) s"
  unfolding decode_SWPL_CC_R_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_SWP_CC_R_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "0 \<le> s__arg" and "s__arg \<le> 31" and "0 \<le> n" and "n \<le> 31" and "\<not>invokes_indirect_caps" and "BaseRegAuth n \<in> load_auths"
  shows "traces_enabled (execute_SWP_CC_R_C ldacctype n s__arg stacctype t__arg) s"
  unfolding execute_SWP_CC_R_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_SWP_CC_R_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "\<not>invokes_indirect_caps" and "BaseRegAuth (uint Rn) \<in> load_auths"
  shows "traces_enabled (decode_SWP_CC_R_C A R Cs Rn Ct) s"
  unfolding decode_SWP_CC_R_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_UNSEAL_C_CC_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_UNSEAL_C_CC_C d m n) s"
  unfolding execute_UNSEAL_C_CC_C_def bind_assoc
  by (traces_enabledI assms: assms intro: CapUnseal_check_global_derivable simp: Run_and_boolM_True_iff)

lemma traces_enabled_decode_UNSEAL_C_CC_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_UNSEAL_C_CC_C Cm opc Cn Cd) s"
  unfolding decode_UNSEAL_C_CC_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_arithmetic_unary_diff_neg_int_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "int LENGTH('esize) \<in> {8, 16, 32, 64}" and "int LENGTH('datasize) \<in> {8, 16, 32, 64, 128}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_arithmetic_unary_diff_neg_int_sisd d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) n neg) s"
  unfolding execute_aarch64_instrs_vector_arithmetic_unary_diff_neg_int_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_abs_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_int_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_abs_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_int_simd Rd Rn b__0 U b__1) s"
  unfolding decode_abs_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_int_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_abs_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_int_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_abs_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_int_sisd Rd Rn b__0 U) s"
  unfolding decode_abs_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_int_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_integer_arithmetic_add_sub_carry[traces_enabledI]:
  assumes "{''_R29''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "int LENGTH('datasize) \<in> {32, 64}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_integer_arithmetic_add_sub_carry d (datasize :: 'datasize::len itself) m n setflags sub_op) s"
  unfolding execute_aarch64_instrs_integer_arithmetic_add_sub_carry_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_adc_aarch64_instrs_integer_arithmetic_add_sub_carry[traces_enabledI]:
  assumes "{''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_adc_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn Rm S op b__0) s"
  unfolding decode_adc_aarch64_instrs_integer_arithmetic_add_sub_carry_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_adcs_aarch64_instrs_integer_arithmetic_add_sub_carry[traces_enabledI]:
  assumes "{''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_adcs_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn Rm S op b__0) s"
  unfolding decode_adcs_aarch64_instrs_integer_arithmetic_add_sub_carry_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_integer_arithmetic_add_sub_extendedreg[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "shift \<in> {0, 1, 2, 3, 4, 5, 6, 7}" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "int LENGTH('datasize) \<in> {32, 64}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_integer_arithmetic_add_sub_extendedreg d (datasize :: 'datasize::len itself) extend_type m n setflags shift sub_op) s"
  unfolding execute_aarch64_instrs_integer_arithmetic_add_sub_extendedreg_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_add_addsub_ext_aarch64_instrs_integer_arithmetic_add_sub_extendedreg[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_add_addsub_ext_aarch64_instrs_integer_arithmetic_add_sub_extendedreg Rd Rn imm3 option_name Rm S op b__0) s"
  unfolding decode_add_addsub_ext_aarch64_instrs_integer_arithmetic_add_sub_extendedreg_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_integer_arithmetic_add_sub_immediate[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "datasize \<in> {32, 64}" and "0 \<le> d" and "d \<le> 31" and "int (size imm) = datasize"
  shows "traces_enabled (execute_aarch64_instrs_integer_arithmetic_add_sub_immediate d datasize imm n setflags sub_op) s"
  unfolding execute_aarch64_instrs_integer_arithmetic_add_sub_immediate_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_add_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_add_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate Rd Rn imm12 sh S op b__0) s"
  unfolding decode_add_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg[traces_enabledI]:
  assumes "{''_R29''} \<subseteq> accessible_regs s" and "0 \<le> shift_amount" and "shift_amount \<le> 63" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "int LENGTH('datasize) \<in> {32, 64}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg d (datasize :: 'datasize::len itself) m n setflags shift_amount shift_type sub_op) s"
  unfolding execute_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_add_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg[traces_enabledI]:
  assumes "{''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_add_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg Rd Rn imm6 Rm shift S op b__0) s"
  unfolding decode_add_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_arithmetic_binary_uniform_add_wrapping_single_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "int LENGTH('esize) \<in> {8, 16, 32, 64}" and "int LENGTH('datasize) \<in> {8, 16, 32, 64, 128}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_arithmetic_binary_uniform_add_wrapping_single_sisd d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) m n sub_op) s"
  unfolding execute_aarch64_instrs_vector_arithmetic_binary_uniform_add_wrapping_single_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_add_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_wrapping_single_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_add_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_wrapping_single_simd Rd Rn Rm b__0 U b__1) s"
  unfolding decode_add_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_wrapping_single_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_add_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_wrapping_single_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_add_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_wrapping_single_sisd Rd Rn Rm b__0 U) s"
  unfolding decode_add_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_wrapping_single_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_narrow[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "part \<in> {0, 1}" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "l__40 \<in> {8, 16, 32, 64}" and "datasize = 64" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_narrow d datasize elements l__40 m n part round__arg sub_op) s"
  unfolding execute_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_narrow_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_addhn_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_narrow[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_addhn_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_narrow Rd Rn o1 Rm b__0 U Q) s"
  unfolding decode_addhn_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_narrow_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_reduce_add_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "int LENGTH('esize) \<in> {8, 16, 32, 64}" and "int LENGTH('datasize) \<in> {16, 32, 64, 128}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_reduce_add_sisd d (datasize :: 'datasize::len itself) (esize :: 'esize::len itself) n op) s"
  unfolding execute_aarch64_instrs_vector_reduce_add_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_addp_advsimd_pair_aarch64_instrs_vector_reduce_add_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_addp_advsimd_pair_aarch64_instrs_vector_reduce_add_sisd Rd Rn b__0) s"
  unfolding decode_addp_advsimd_pair_aarch64_instrs_vector_reduce_add_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_arithmetic_binary_uniform_add_wrapping_pair[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "int LENGTH('esize) \<in> {8, 16, 32, 64}" and "l__179 \<in> {64, 128}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_arithmetic_binary_uniform_add_wrapping_pair d l__179 elements (esize :: 'esize::len itself) m n) s"
  unfolding execute_aarch64_instrs_vector_arithmetic_binary_uniform_add_wrapping_pair_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_addp_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_add_wrapping_pair[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_addp_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_add_wrapping_pair Rd Rn Rm b__0 b__1) s"
  unfolding decode_addp_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_add_wrapping_pair_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_adds_addsub_ext_aarch64_instrs_integer_arithmetic_add_sub_extendedreg[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_adds_addsub_ext_aarch64_instrs_integer_arithmetic_add_sub_extendedreg Rd Rn imm3 option_name Rm S op b__0) s"
  unfolding decode_adds_addsub_ext_aarch64_instrs_integer_arithmetic_add_sub_extendedreg_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_adds_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_adds_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate Rd Rn imm12 sh S op b__0) s"
  unfolding decode_adds_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_adds_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg[traces_enabledI]:
  assumes "{''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_adds_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg Rd Rn imm6 Rm shift S op b__0) s"
  unfolding decode_adds_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_reduce_add_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "int LENGTH('esize) \<in> {8, 16, 32, 64}" and "int LENGTH('datasize) \<in> {64, 128}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_reduce_add_simd d (datasize :: 'datasize::len itself) (esize :: 'esize::len itself) n op) s"
  unfolding execute_aarch64_instrs_vector_reduce_add_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_addv_advsimd_aarch64_instrs_vector_reduce_add_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_addv_advsimd_aarch64_instrs_vector_reduce_add_simd Rd Rn b__0 b__1) s"
  unfolding decode_addv_advsimd_aarch64_instrs_vector_reduce_add_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_crypto_aes_round[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_crypto_aes_round d decrypt n) s"
  unfolding execute_aarch64_instrs_vector_crypto_aes_round_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_aesd_advsimd_aarch64_instrs_vector_crypto_aes_round[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_aesd_advsimd_aarch64_instrs_vector_crypto_aes_round Rd Rn D) s"
  unfolding decode_aesd_advsimd_aarch64_instrs_vector_crypto_aes_round_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_aese_advsimd_aarch64_instrs_vector_crypto_aes_round[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_aese_advsimd_aarch64_instrs_vector_crypto_aes_round Rd Rn D) s"
  unfolding decode_aese_advsimd_aarch64_instrs_vector_crypto_aes_round_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_crypto_aes_mix[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_crypto_aes_mix d decrypt n) s"
  unfolding execute_aarch64_instrs_vector_crypto_aes_mix_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_aesimc_advsimd_aarch64_instrs_vector_crypto_aes_mix[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_aesimc_advsimd_aarch64_instrs_vector_crypto_aes_mix Rd Rn D) s"
  unfolding decode_aesimc_advsimd_aarch64_instrs_vector_crypto_aes_mix_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_aesmc_advsimd_aarch64_instrs_vector_crypto_aes_mix[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_aesmc_advsimd_aarch64_instrs_vector_crypto_aes_mix Rd Rn D) s"
  unfolding decode_aesmc_advsimd_aarch64_instrs_vector_crypto_aes_mix_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_arithmetic_binary_uniform_logical_and_orr[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "int LENGTH('datasize) \<in> {64, 128}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_arithmetic_binary_uniform_logical_and_orr d (datasize :: 'datasize::len itself) invert m n op) s"
  unfolding execute_aarch64_instrs_vector_arithmetic_binary_uniform_logical_and_orr_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_and_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_logical_and_orr[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_and_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_logical_and_orr Rd Rn Rm size__arg b__0) s"
  unfolding decode_and_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_logical_and_orr_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_integer_logical_immediate[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "datasize \<in> {32, 64}" and "0 \<le> d" and "d \<le> 31" and "int (size imm) = datasize"
  shows "traces_enabled (execute_aarch64_instrs_integer_logical_immediate d datasize imm n op setflags) s"
  unfolding execute_aarch64_instrs_integer_logical_immediate_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_and_log_imm_aarch64_instrs_integer_logical_immediate[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_and_log_imm_aarch64_instrs_integer_logical_immediate Rd Rn imms immr N opc b__0) s"
  unfolding decode_and_log_imm_aarch64_instrs_integer_logical_immediate_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_integer_logical_shiftedreg[traces_enabledI]:
  assumes "{''_R29''} \<subseteq> accessible_regs s" and "0 \<le> shift_amount" and "shift_amount \<le> 63" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "int LENGTH('datasize) \<in> {32, 64}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_integer_logical_shiftedreg d (datasize :: 'datasize::len itself) invert m n op setflags shift_amount shift_type) s"
  unfolding execute_aarch64_instrs_integer_logical_shiftedreg_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_and_log_shift_aarch64_instrs_integer_logical_shiftedreg[traces_enabledI]:
  assumes "{''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_and_log_shift_aarch64_instrs_integer_logical_shiftedreg Rd Rn imm6 Rm N shift opc b__0) s"
  unfolding decode_and_log_shift_aarch64_instrs_integer_logical_shiftedreg_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ands_log_imm_aarch64_instrs_integer_logical_immediate[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ands_log_imm_aarch64_instrs_integer_logical_immediate Rd Rn imms immr N opc b__0) s"
  unfolding decode_ands_log_imm_aarch64_instrs_integer_logical_immediate_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ands_log_shift_aarch64_instrs_integer_logical_shiftedreg[traces_enabledI]:
  assumes "{''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ands_log_shift_aarch64_instrs_integer_logical_shiftedreg Rd Rn imm6 Rm N shift opc b__0) s"
  unfolding decode_ands_log_shift_aarch64_instrs_integer_logical_shiftedreg_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_integer_shift_variable[traces_enabledI]:
  assumes "{''_R29''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "int LENGTH('datasize) \<in> {32, 64}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_integer_shift_variable d (datasize :: 'datasize::len itself) m n shift_type) s"
  unfolding execute_aarch64_instrs_integer_shift_variable_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_asrv_aarch64_instrs_integer_shift_variable[traces_enabledI]:
  assumes "{''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_asrv_aarch64_instrs_integer_shift_variable Rd Rn op2 Rm b__0) s"
  unfolding decode_asrv_aarch64_instrs_integer_shift_variable_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_branch_conditional_cond[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_aarch64_instrs_branch_conditional_cond condition offset) s"
  unfolding execute_aarch64_instrs_branch_conditional_cond_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_b_cond_aarch64_instrs_branch_conditional_cond[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_b_cond_aarch64_instrs_branch_conditional_cond cond imm19) s"
  unfolding decode_b_cond_aarch64_instrs_branch_conditional_cond_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_branch_unconditional_immediate[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_aarch64_instrs_branch_unconditional_immediate branch_type offset) s"
  unfolding execute_aarch64_instrs_branch_unconditional_immediate_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_b_uncond_aarch64_instrs_branch_unconditional_immediate[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_b_uncond_aarch64_instrs_branch_unconditional_immediate imm26 op) s"
  unfolding decode_b_uncond_aarch64_instrs_branch_unconditional_immediate_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_crypto_sha3_bcax[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "0 \<le> d" and "d \<le> 31" and "0 \<le> a" and "a \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_crypto_sha3_bcax a d m n) s"
  unfolding execute_aarch64_instrs_vector_crypto_sha3_bcax_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_bcax_advsimd_aarch64_instrs_vector_crypto_sha3_bcax[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_bcax_advsimd_aarch64_instrs_vector_crypto_sha3_bcax Rd Rn Ra Rm) s"
  unfolding decode_bcax_advsimd_aarch64_instrs_vector_crypto_sha3_bcax_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_integer_bitfield[traces_enabledI]:
  assumes "{''_R29''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "datasize \<in> {32, 64}" and "0 \<le> d" and "d \<le> 31" and "0 \<le> S" and "S \<le> 63" and "0 \<le> R" and "R \<le> 63" and "int (size wmask) = datasize" and "int (size tmask) = datasize"
  shows "traces_enabled (execute_aarch64_instrs_integer_bitfield R S d datasize extend__arg inzero n tmask wmask) s"
  unfolding execute_aarch64_instrs_integer_bitfield_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_bfm_aarch64_instrs_integer_bitfield[traces_enabledI]:
  assumes "{''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_bfm_aarch64_instrs_integer_bitfield Rd Rn imms immr N opc b__0) s"
  unfolding decode_bfm_aarch64_instrs_integer_bitfield_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_logical[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> rd" and "rd \<le> 31" and "datasize \<in> {64, 128}" and "int (size imm) = datasize"
  shows "traces_enabled (execute_aarch64_instrs_vector_logical datasize imm operation rd) s"
  unfolding execute_aarch64_instrs_vector_logical_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_bic_advsimd_imm_aarch64_instrs_vector_logical[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_bic_advsimd_imm_aarch64_instrs_vector_logical Rd h g f e d cmode c__arg b a op b__0) s"
  unfolding decode_bic_advsimd_imm_aarch64_instrs_vector_logical_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_bic_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_logical_and_orr[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_bic_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_logical_and_orr Rd Rn Rm size__arg b__0) s"
  unfolding decode_bic_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_logical_and_orr_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_bic_log_shift_aarch64_instrs_integer_logical_shiftedreg[traces_enabledI]:
  assumes "{''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_bic_log_shift_aarch64_instrs_integer_logical_shiftedreg Rd Rn imm6 Rm N shift opc b__0) s"
  unfolding decode_bic_log_shift_aarch64_instrs_integer_logical_shiftedreg_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_bics_aarch64_instrs_integer_logical_shiftedreg[traces_enabledI]:
  assumes "{''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_bics_aarch64_instrs_integer_logical_shiftedreg Rd Rn imm6 Rm N shift opc b__0) s"
  unfolding decode_bics_aarch64_instrs_integer_logical_shiftedreg_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_arithmetic_binary_uniform_logical_bsl_eor[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "int LENGTH('datasize) \<in> {64, 128}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_arithmetic_binary_uniform_logical_bsl_eor d (datasize :: 'datasize::len itself) m n op) s"
  unfolding execute_aarch64_instrs_vector_arithmetic_binary_uniform_logical_bsl_eor_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_bif_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_logical_bsl_eor[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_bif_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_logical_bsl_eor Rd Rn Rm opc2 b__0) s"
  unfolding decode_bif_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_logical_bsl_eor_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_bit_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_logical_bsl_eor[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_bit_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_logical_bsl_eor Rd Rn Rm opc2 b__0) s"
  unfolding decode_bit_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_logical_bsl_eor_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_bl_aarch64_instrs_branch_unconditional_immediate[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_bl_aarch64_instrs_branch_unconditional_immediate imm26 op) s"
  unfolding decode_bl_aarch64_instrs_branch_unconditional_immediate_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_branch_unconditional_register[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_branch_unconditional_register branch_type n) s"
  unfolding execute_aarch64_instrs_branch_unconditional_register_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_blr_aarch64_instrs_branch_unconditional_register[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_blr_aarch64_instrs_branch_unconditional_register Rm Rn M A op Z) s"
  unfolding decode_blr_aarch64_instrs_branch_unconditional_register_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_blra_aarch64_instrs_branch_unconditional_register[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_blra_aarch64_instrs_branch_unconditional_register Rm Rn M A op Z) s"
  unfolding decode_blra_aarch64_instrs_branch_unconditional_register_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_br_aarch64_instrs_branch_unconditional_register[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_br_aarch64_instrs_branch_unconditional_register Rm Rn M A op Z) s"
  unfolding decode_br_aarch64_instrs_branch_unconditional_register_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_bra_aarch64_instrs_branch_unconditional_register[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_bra_aarch64_instrs_branch_unconditional_register Rm Rn M A op Z) s"
  unfolding decode_bra_aarch64_instrs_branch_unconditional_register_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_system_exceptions_debug_breakpoint[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_aarch64_instrs_system_exceptions_debug_breakpoint comment) s"
  unfolding execute_aarch64_instrs_system_exceptions_debug_breakpoint_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_brk_aarch64_instrs_system_exceptions_debug_breakpoint[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_brk_aarch64_instrs_system_exceptions_debug_breakpoint imm16) s"
  unfolding decode_brk_aarch64_instrs_system_exceptions_debug_breakpoint_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_bsl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_logical_bsl_eor[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_bsl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_logical_bsl_eor Rd Rn Rm opc2 b__0) s"
  unfolding decode_bsl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_logical_bsl_eor_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_memory_atomicops_cas_single[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "0 \<le> s__arg" and "s__arg \<le> 31" and "int LENGTH('regsize) \<in> {32, 64}" and "0 \<le> n" and "n \<le> 31" and "int LENGTH('datasize) \<in> {8, 16, 32, 64}"
  shows "traces_enabled (execute_aarch64_instrs_memory_atomicops_cas_single (datasize :: 'datasize::len itself) ldacctype n (regsize :: 'regsize::len itself) s__arg stacctype t__arg) s"
  unfolding execute_aarch64_instrs_memory_atomicops_cas_single_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_cas_aarch64_instrs_memory_atomicops_cas_single[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_cas_aarch64_instrs_memory_atomicops_cas_single Rt Rn o0 Rs L b__0) s"
  unfolding decode_cas_aarch64_instrs_memory_atomicops_cas_single_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_casb_aarch64_instrs_memory_atomicops_cas_single[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_casb_aarch64_instrs_memory_atomicops_cas_single Rt Rn o0 Rs L b__0) s"
  unfolding decode_casb_aarch64_instrs_memory_atomicops_cas_single_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_cash_aarch64_instrs_memory_atomicops_cas_single[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_cash_aarch64_instrs_memory_atomicops_cas_single Rt Rn o0 Rs L b__0) s"
  unfolding decode_cash_aarch64_instrs_memory_atomicops_cas_single_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_memory_atomicops_cas_pair[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "0 \<le> s__arg" and "s__arg \<le> 31" and "int LENGTH('regsize) \<in> {32, 64}" and "0 \<le> n" and "n \<le> 31" and "l__38 \<in> {32, 64}"
  shows "traces_enabled (execute_aarch64_instrs_memory_atomicops_cas_pair l__38 ldacctype n (regsize :: 'regsize::len itself) s__arg stacctype t__arg) s"
  unfolding execute_aarch64_instrs_memory_atomicops_cas_pair_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_casp_aarch64_instrs_memory_atomicops_cas_pair[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_casp_aarch64_instrs_memory_atomicops_cas_pair Rt Rn Rt2 o0 Rs L b__0) s"
  unfolding decode_casp_aarch64_instrs_memory_atomicops_cas_pair_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_branch_conditional_compare[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "int LENGTH('datasize) \<in> {32, 64}"
  shows "traces_enabled (execute_aarch64_instrs_branch_conditional_compare (datasize :: 'datasize::len itself) iszero__arg offset t__arg) s"
  unfolding execute_aarch64_instrs_branch_conditional_compare_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_cbnz_aarch64_instrs_branch_conditional_compare[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_cbnz_aarch64_instrs_branch_conditional_compare Rt imm19 op b__0) s"
  unfolding decode_cbnz_aarch64_instrs_branch_conditional_compare_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_cbz_aarch64_instrs_branch_conditional_compare[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_cbz_aarch64_instrs_branch_conditional_compare Rt imm19 op b__0) s"
  unfolding decode_cbz_aarch64_instrs_branch_conditional_compare_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_integer_conditional_compare_immediate[traces_enabledI]:
  assumes "0 \<le> n" and "n \<le> 31" and "datasize \<in> {32, 64}" and "int (size imm) = datasize"
  shows "traces_enabled (execute_aarch64_instrs_integer_conditional_compare_immediate condition datasize flags__arg imm n sub_op) s"
  unfolding execute_aarch64_instrs_integer_conditional_compare_immediate_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ccmn_imm_aarch64_instrs_integer_conditional_compare_immediate[traces_enabledI]:
  "traces_enabled (decode_ccmn_imm_aarch64_instrs_integer_conditional_compare_immediate nzcv Rn cond imm5 op b__0) s"
  unfolding decode_ccmn_imm_aarch64_instrs_integer_conditional_compare_immediate_def bind_assoc
  by (traces_enabledI)

lemma traces_enabled_execute_aarch64_instrs_integer_conditional_compare_register[traces_enabledI]:
  assumes "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "int LENGTH('datasize) \<in> {32, 64}"
  shows "traces_enabled (execute_aarch64_instrs_integer_conditional_compare_register condition (datasize :: 'datasize::len itself) flags__arg m n sub_op) s"
  unfolding execute_aarch64_instrs_integer_conditional_compare_register_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ccmn_reg_aarch64_instrs_integer_conditional_compare_register[traces_enabledI]:
  "traces_enabled (decode_ccmn_reg_aarch64_instrs_integer_conditional_compare_register nzcv Rn cond Rm op b__0) s"
  unfolding decode_ccmn_reg_aarch64_instrs_integer_conditional_compare_register_def bind_assoc
  by (traces_enabledI)

lemma traces_enabled_decode_ccmp_imm_aarch64_instrs_integer_conditional_compare_immediate[traces_enabledI]:
  "traces_enabled (decode_ccmp_imm_aarch64_instrs_integer_conditional_compare_immediate nzcv Rn cond imm5 op b__0) s"
  unfolding decode_ccmp_imm_aarch64_instrs_integer_conditional_compare_immediate_def bind_assoc
  by (traces_enabledI)

lemma traces_enabled_decode_ccmp_reg_aarch64_instrs_integer_conditional_compare_register[traces_enabledI]:
  "traces_enabled (decode_ccmp_reg_aarch64_instrs_integer_conditional_compare_register nzcv Rn cond Rm op b__0) s"
  unfolding decode_ccmp_reg_aarch64_instrs_integer_conditional_compare_register_def bind_assoc
  by (traces_enabledI)

lemma traces_enabled_execute_aarch64_instrs_vector_arithmetic_unary_clsz[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "int LENGTH('esize) \<in> {8, 16, 32, 64}" and "int LENGTH('datasize) \<in> {64, 128}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_arithmetic_unary_clsz countop d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) n) s"
  unfolding execute_aarch64_instrs_vector_arithmetic_unary_clsz_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_cls_advsimd_aarch64_instrs_vector_arithmetic_unary_clsz[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_cls_advsimd_aarch64_instrs_vector_arithmetic_unary_clsz Rd Rn b__0 U b__1) s"
  unfolding decode_cls_advsimd_aarch64_instrs_vector_arithmetic_unary_clsz_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_integer_arithmetic_cnt[traces_enabledI]:
  assumes "{''_R29''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "int LENGTH('datasize) \<in> {32, 64}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_integer_arithmetic_cnt d (datasize :: 'datasize::len itself) n opcode) s"
  unfolding execute_aarch64_instrs_integer_arithmetic_cnt_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_cls_int_aarch64_instrs_integer_arithmetic_cnt[traces_enabledI]:
  assumes "{''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_cls_int_aarch64_instrs_integer_arithmetic_cnt Rd Rn op b__0) s"
  unfolding decode_cls_int_aarch64_instrs_integer_arithmetic_cnt_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_clz_advsimd_aarch64_instrs_vector_arithmetic_unary_clsz[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_clz_advsimd_aarch64_instrs_vector_arithmetic_unary_clsz Rd Rn b__0 U b__1) s"
  unfolding decode_clz_advsimd_aarch64_instrs_vector_arithmetic_unary_clsz_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_clz_int_aarch64_instrs_integer_arithmetic_cnt[traces_enabledI]:
  assumes "{''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_clz_int_aarch64_instrs_integer_arithmetic_cnt Rd Rn op b__0) s"
  unfolding decode_clz_int_aarch64_instrs_integer_arithmetic_cnt_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_bitwise_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "int LENGTH('esize) \<in> {8, 16, 32, 64}" and "int LENGTH('datasize) \<in> {8, 16, 32, 64, 128}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_bitwise_sisd and_test d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) m n) s"
  unfolding execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_bitwise_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_cmeq_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_bitwise_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_cmeq_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_bitwise_simd Rd Rn Rm b__0 U b__1) s"
  unfolding decode_cmeq_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_bitwise_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_cmeq_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_bitwise_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_cmeq_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_bitwise_sisd Rd Rn Rm b__0 U) s"
  unfolding decode_cmeq_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_bitwise_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "int LENGTH('esize) \<in> {8, 16, 32, 64}" and "int LENGTH('datasize) \<in> {8, 16, 32, 64, 128}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_sisd comparison d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) n) s"
  unfolding execute_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_cmeq_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_cmeq_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_simd Rd Rn op b__0 U b__1) s"
  unfolding decode_cmeq_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_cmeq_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_cmeq_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_sisd Rd Rn op b__0 U) s"
  unfolding decode_cmeq_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "int LENGTH('esize) \<in> {8, 16, 32, 64}" and "int LENGTH('datasize) \<in> {8, 16, 32, 64, 128}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_sisd cmp_eq d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) m n is_unsigned) s"
  unfolding execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_cmge_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_cmge_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_simd Rd Rn eq Rm b__0 U b__1) s"
  unfolding decode_cmge_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_cmge_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_cmge_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_sisd Rd Rn eq Rm b__0 U) s"
  unfolding decode_cmge_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_cmge_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_cmge_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_simd Rd Rn op b__0 U b__1) s"
  unfolding decode_cmge_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_cmge_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_cmge_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_sisd Rd Rn op b__0 U) s"
  unfolding decode_cmge_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_cmgt_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_cmgt_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_simd Rd Rn eq Rm b__0 U b__1) s"
  unfolding decode_cmgt_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_cmgt_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_cmgt_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_sisd Rd Rn eq Rm b__0 U) s"
  unfolding decode_cmgt_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_cmgt_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_cmgt_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_simd Rd Rn op b__0 U b__1) s"
  unfolding decode_cmgt_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_cmgt_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_cmgt_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_sisd Rd Rn op b__0 U) s"
  unfolding decode_cmgt_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_cmhi_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_cmhi_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_simd Rd Rn eq Rm b__0 U b__1) s"
  unfolding decode_cmhi_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_cmhi_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_cmhi_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_sisd Rd Rn eq Rm b__0 U) s"
  unfolding decode_cmhi_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_cmhs_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_cmhs_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_simd Rd Rn eq Rm b__0 U b__1) s"
  unfolding decode_cmhs_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_cmhs_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_cmhs_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_sisd Rd Rn eq Rm b__0 U) s"
  unfolding decode_cmhs_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_cmle_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_cmle_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_simd Rd Rn op b__0 U b__1) s"
  unfolding decode_cmle_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_cmle_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_cmle_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_sisd Rd Rn op b__0 U) s"
  unfolding decode_cmle_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_arithmetic_unary_cmp_int_lessthan_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "int LENGTH('esize) \<in> {8, 16, 32, 64}" and "int LENGTH('datasize) \<in> {8, 16, 32, 64, 128}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_arithmetic_unary_cmp_int_lessthan_sisd comparison d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) n) s"
  unfolding execute_aarch64_instrs_vector_arithmetic_unary_cmp_int_lessthan_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_cmlt_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_int_lessthan_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_cmlt_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_int_lessthan_simd Rd Rn b__0 b__1) s"
  unfolding decode_cmlt_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_int_lessthan_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_cmlt_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_int_lessthan_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_cmlt_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_int_lessthan_sisd Rd Rn b__0) s"
  unfolding decode_cmlt_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_int_lessthan_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_cmtst_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_bitwise_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_cmtst_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_bitwise_simd Rd Rn Rm b__0 U b__1) s"
  unfolding decode_cmtst_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_bitwise_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_cmtst_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_bitwise_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_cmtst_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_bitwise_sisd Rd Rn Rm b__0 U) s"
  unfolding decode_cmtst_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_bitwise_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_arithmetic_unary_cnt[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "esize = 8" and "elements \<in> {8, 16}" and "int LENGTH('datasize) \<in> {64, 128}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_arithmetic_unary_cnt d (datasize :: 'datasize::len itself) elements esize n) s"
  unfolding execute_aarch64_instrs_vector_arithmetic_unary_cnt_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_cnt_advsimd_aarch64_instrs_vector_arithmetic_unary_cnt[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_cnt_advsimd_aarch64_instrs_vector_arithmetic_unary_cnt Rd Rn size__arg b__0) s"
  unfolding decode_cnt_advsimd_aarch64_instrs_vector_arithmetic_unary_cnt_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_integer_crc[traces_enabledI]:
  assumes "{''_R29''} \<subseteq> accessible_regs s" and "l__155 \<in> {8, 16, 32, 64}" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_integer_crc crc32c d m n l__155) s"
  unfolding execute_aarch64_instrs_integer_crc_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_crc32_aarch64_instrs_integer_crc[traces_enabledI]:
  assumes "{''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_crc32_aarch64_instrs_integer_crc Rd Rn b__0 C Rm sf) s"
  unfolding decode_crc32_aarch64_instrs_integer_crc_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_crc32c_aarch64_instrs_integer_crc[traces_enabledI]:
  assumes "{''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_crc32c_aarch64_instrs_integer_crc Rd Rn b__0 C Rm sf) s"
  unfolding decode_crc32c_aarch64_instrs_integer_crc_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_integer_conditional_select[traces_enabledI]:
  assumes "{''_R29''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "int LENGTH('datasize) \<in> {32, 64}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_integer_conditional_select condition d (datasize :: 'datasize::len itself) else_inc else_inv m n) s"
  unfolding execute_aarch64_instrs_integer_conditional_select_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_csel_aarch64_instrs_integer_conditional_select[traces_enabledI]:
  assumes "{''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_csel_aarch64_instrs_integer_conditional_select Rd Rn o2 cond Rm op b__0) s"
  unfolding decode_csel_aarch64_instrs_integer_conditional_select_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_csinc_aarch64_instrs_integer_conditional_select[traces_enabledI]:
  assumes "{''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_csinc_aarch64_instrs_integer_conditional_select Rd Rn o2 cond Rm op b__0) s"
  unfolding decode_csinc_aarch64_instrs_integer_conditional_select_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_csinv_aarch64_instrs_integer_conditional_select[traces_enabledI]:
  assumes "{''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_csinv_aarch64_instrs_integer_conditional_select Rd Rn o2 cond Rm op b__0) s"
  unfolding decode_csinv_aarch64_instrs_integer_conditional_select_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_csneg_aarch64_instrs_integer_conditional_select[traces_enabledI]:
  assumes "{''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_csneg_aarch64_instrs_integer_conditional_select Rd Rn o2 cond Rm op b__0) s"
  unfolding decode_csneg_aarch64_instrs_integer_conditional_select_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_system_exceptions_debug_exception[traces_enabledI]:
  "traces_enabled (execute_aarch64_instrs_system_exceptions_debug_exception target_level) s"
  unfolding execute_aarch64_instrs_system_exceptions_debug_exception_def bind_assoc
  by (traces_enabledI)

lemma traces_enabled_decode_dcps1_aarch64_instrs_system_exceptions_debug_exception[traces_enabledI]:
  "traces_enabled (decode_dcps1_aarch64_instrs_system_exceptions_debug_exception LL imm16) s"
  unfolding decode_dcps1_aarch64_instrs_system_exceptions_debug_exception_def bind_assoc
  by (traces_enabledI)

lemma traces_enabled_decode_dcps2_aarch64_instrs_system_exceptions_debug_exception[traces_enabledI]:
  "traces_enabled (decode_dcps2_aarch64_instrs_system_exceptions_debug_exception LL imm16) s"
  unfolding decode_dcps2_aarch64_instrs_system_exceptions_debug_exception_def bind_assoc
  by (traces_enabledI)

lemma traces_enabled_decode_dcps3_aarch64_instrs_system_exceptions_debug_exception[traces_enabledI]:
  "traces_enabled (decode_dcps3_aarch64_instrs_system_exceptions_debug_exception LL imm16) s"
  unfolding decode_dcps3_aarch64_instrs_system_exceptions_debug_exception_def bind_assoc
  by (traces_enabledI)

lemma traces_enabled_execute_aarch64_instrs_branch_unconditional_dret[traces_enabledI]:
  "traces_enabled (execute_aarch64_instrs_branch_unconditional_dret arg0) s"
  unfolding execute_aarch64_instrs_branch_unconditional_dret_def bind_assoc
  by (traces_enabledI)

lemma traces_enabled_decode_drps_aarch64_instrs_branch_unconditional_dret[traces_enabledI]:
  "traces_enabled (decode_drps_aarch64_instrs_branch_unconditional_dret arg0) s"
  unfolding decode_drps_aarch64_instrs_branch_unconditional_dret_def bind_assoc
  by (traces_enabledI)

lemma traces_enabled_execute_aarch64_instrs_vector_transfer_vector_cpy_dup_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "int LENGTH('idxdsize) \<in> {64, 128}" and "int LENGTH('esize) \<in> {8, 16, 32, 64, 128, 256}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_transfer_vector_cpy_dup_sisd d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) (idxdsize :: 'idxdsize::len itself) index__arg n) s"
  unfolding execute_aarch64_instrs_vector_transfer_vector_cpy_dup_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_dup_advsimd_elt_aarch64_instrs_vector_transfer_vector_cpy_dup_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_dup_advsimd_elt_aarch64_instrs_vector_transfer_vector_cpy_dup_simd Rd Rn b__0 b__1) s"
  unfolding decode_dup_advsimd_elt_aarch64_instrs_vector_transfer_vector_cpy_dup_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_dup_advsimd_elt_aarch64_instrs_vector_transfer_vector_cpy_dup_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_dup_advsimd_elt_aarch64_instrs_vector_transfer_vector_cpy_dup_sisd Rd Rn b__0) s"
  unfolding decode_dup_advsimd_elt_aarch64_instrs_vector_transfer_vector_cpy_dup_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_transfer_integer_dup[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "int LENGTH('esize) \<in> {8, 16, 32, 64, 128, 256}" and "int LENGTH('datasize) \<in> {64, 128}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_transfer_integer_dup d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) n) s"
  unfolding execute_aarch64_instrs_vector_transfer_integer_dup_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_dup_advsimd_gen_aarch64_instrs_vector_transfer_integer_dup[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_dup_advsimd_gen_aarch64_instrs_vector_transfer_integer_dup Rd Rn b__0 b__1) s"
  unfolding decode_dup_advsimd_gen_aarch64_instrs_vector_transfer_integer_dup_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_eon_aarch64_instrs_integer_logical_shiftedreg[traces_enabledI]:
  assumes "{''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_eon_aarch64_instrs_integer_logical_shiftedreg Rd Rn imm6 Rm N shift opc b__0) s"
  unfolding decode_eon_aarch64_instrs_integer_logical_shiftedreg_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_crypto_sha3_eor3[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "0 \<le> d" and "d \<le> 31" and "0 \<le> a" and "a \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_crypto_sha3_eor3 a d m n) s"
  unfolding execute_aarch64_instrs_vector_crypto_sha3_eor3_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_eor3_advsimd_aarch64_instrs_vector_crypto_sha3_eor3[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_eor3_advsimd_aarch64_instrs_vector_crypto_sha3_eor3 Rd Rn Ra Rm) s"
  unfolding decode_eor3_advsimd_aarch64_instrs_vector_crypto_sha3_eor3_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_eor_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_logical_bsl_eor[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_eor_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_logical_bsl_eor Rd Rn Rm opc2 b__0) s"
  unfolding decode_eor_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_logical_bsl_eor_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_eor_log_imm_aarch64_instrs_integer_logical_immediate[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_eor_log_imm_aarch64_instrs_integer_logical_immediate Rd Rn imms immr N opc b__0) s"
  unfolding decode_eor_log_imm_aarch64_instrs_integer_logical_immediate_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_eor_log_shift_aarch64_instrs_integer_logical_shiftedreg[traces_enabledI]:
  assumes "{''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_eor_log_shift_aarch64_instrs_integer_logical_shiftedreg Rd Rn imm6 Rm N shift opc b__0) s"
  unfolding decode_eor_log_shift_aarch64_instrs_integer_logical_shiftedreg_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_branch_unconditional_eret[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_aarch64_instrs_branch_unconditional_eret arg0) s"
  unfolding execute_aarch64_instrs_branch_unconditional_eret_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_eret_aarch64_instrs_branch_unconditional_eret[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_eret_aarch64_instrs_branch_unconditional_eret op4 Rn M A) s"
  unfolding decode_eret_aarch64_instrs_branch_unconditional_eret_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ereta_aarch64_instrs_branch_unconditional_eret[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ereta_aarch64_instrs_branch_unconditional_eret op4 Rn M A) s"
  unfolding decode_ereta_aarch64_instrs_branch_unconditional_eret_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_system_hints[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_aarch64_instrs_system_hints op) s"
  by (cases op; simp; traces_enabledI assms: assms)

lemma traces_enabled_decode_esb_aarch64_instrs_system_hints[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_esb_aarch64_instrs_system_hints op2 CRm) s"
  unfolding decode_esb_aarch64_instrs_system_hints_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_transfer_vector_extract[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "l__47 \<in> {64, 128}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_transfer_vector_extract d l__47 m n position) s"
  unfolding execute_aarch64_instrs_vector_transfer_vector_extract_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ext_advsimd_aarch64_instrs_vector_transfer_vector_extract[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ext_advsimd_aarch64_instrs_vector_transfer_vector_extract Rd Rn imm4 Rm b__0) s"
  unfolding decode_ext_advsimd_aarch64_instrs_vector_transfer_vector_extract_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_integer_ins_ext_extract_immediate[traces_enabledI]:
  assumes "{''_R29''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "0 \<le> lsb__arg" and "lsb__arg \<le> 63" and "l__36 \<in> {32, 64}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_integer_ins_ext_extract_immediate d l__36 lsb__arg m n) s"
  unfolding execute_aarch64_instrs_integer_ins_ext_extract_immediate_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_extr_aarch64_instrs_integer_ins_ext_extract_immediate[traces_enabledI]:
  assumes "{''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_extr_aarch64_instrs_integer_ins_ext_extract_immediate Rd Rn imms Rm N b__0) s"
  unfolding decode_extr_aarch64_instrs_integer_ins_ext_extract_immediate_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_arithmetic_binary_uniform_sub_fp16_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "int LENGTH('esize) \<in> {16, 32, 64}" and "int LENGTH('datasize) \<in> {16, 32, 64, 128}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_arithmetic_binary_uniform_sub_fp16_sisd abs__arg d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) m n) s"
  unfolding execute_aarch64_instrs_vector_arithmetic_binary_uniform_sub_fp16_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fabd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_fp16_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fabd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_fp16_simd Rd Rn Rm U b__0) s"
  unfolding decode_fabd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_fp16_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fabd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_fp16_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fabd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_fp16_sisd Rd Rn Rm) s"
  unfolding decode_fabd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_fp16_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fabd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_fp_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fabd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_fp_simd Rd Rn Rm b__0 U b__1) s"
  unfolding decode_fabd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_fp_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fabd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_fp_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fabd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_fp_sisd Rd Rn Rm b__0) s"
  unfolding decode_fabd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_fp_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_arithmetic_unary_diff_neg_fp16[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "int LENGTH('esize) \<in> {16, 32, 64}" and "int LENGTH('datasize) \<in> {64, 128}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_arithmetic_unary_diff_neg_fp16 d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) n neg) s"
  unfolding execute_aarch64_instrs_vector_arithmetic_unary_diff_neg_fp16_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fabs_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_float[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fabs_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_float Rd Rn b__0 U b__1) s"
  unfolding decode_fabs_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_float_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fabs_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_fp16[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fabs_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_fp16 Rd Rn U b__0) s"
  unfolding decode_fabs_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_fp16_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_float_arithmetic_unary[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "int LENGTH('datasize) \<in> {16, 32, 64}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_float_arithmetic_unary d (datasize :: 'datasize::len itself) fpop n) s"
  unfolding execute_aarch64_instrs_float_arithmetic_unary_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fabs_float_aarch64_instrs_float_arithmetic_unary[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fabs_float_aarch64_instrs_float_arithmetic_unary Rd Rn opc b__0) s"
  unfolding decode_fabs_float_aarch64_instrs_float_arithmetic_unary_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "int LENGTH('esize) \<in> {16, 32, 64}" and "int LENGTH('datasize) \<in> {16, 32, 64, 128}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_sisd abs__arg cmp d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) m n) s"
  unfolding execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_facge_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_facge_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_simd Rd Rn ac Rm E U b__0) s"
  unfolding decode_facge_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_facge_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_facge_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_sisd Rd Rn ac Rm E U) s"
  unfolding decode_facge_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_facge_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_facge_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp_simd Rd Rn ac Rm b__0 E U b__1) s"
  unfolding decode_facge_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_facge_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_facge_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp_sisd Rd Rn ac Rm b__0 E U) s"
  unfolding decode_facge_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_facgt_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_facgt_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_simd Rd Rn ac Rm E U b__0) s"
  unfolding decode_facgt_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_facgt_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_facgt_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_sisd Rd Rn ac Rm E U) s"
  unfolding decode_facgt_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_facgt_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_facgt_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp_simd Rd Rn ac Rm b__0 E U b__1) s"
  unfolding decode_facgt_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_facgt_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_facgt_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp_sisd Rd Rn ac Rm b__0 E U) s"
  unfolding decode_facgt_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_arithmetic_binary_uniform_add_fp16[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "int LENGTH('esize) \<in> {16, 32, 64}" and "l__163 \<in> {64, 128}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_arithmetic_binary_uniform_add_fp16 d l__163 elements (esize :: 'esize::len itself) m n pair) s"
  unfolding execute_aarch64_instrs_vector_arithmetic_binary_uniform_add_fp16_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_fp[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_fp Rd Rn Rm b__0 U b__1) s"
  unfolding decode_fadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_fp_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_fp16[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_fp16 Rd Rn Rm U b__0) s"
  unfolding decode_fadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_fp16_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_float_arithmetic_add_sub[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "int LENGTH('datasize) \<in> {16, 32, 64}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_float_arithmetic_add_sub d (datasize :: 'datasize::len itself) m n sub_op) s"
  unfolding execute_aarch64_instrs_float_arithmetic_add_sub_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fadd_float_aarch64_instrs_float_arithmetic_add_sub[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fadd_float_aarch64_instrs_float_arithmetic_add_sub Rd Rn op Rm b__0) s"
  unfolding decode_fadd_float_aarch64_instrs_float_arithmetic_add_sub_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_reduce_fp16_add_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "int LENGTH('esize) \<in> {16, 32, 64}" and "int LENGTH('datasize) \<in> {32, 64, 128}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_reduce_fp16_add_sisd d (datasize :: 'datasize::len itself) (esize :: 'esize::len itself) n op) s"
  unfolding execute_aarch64_instrs_vector_reduce_fp16_add_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_faddp_advsimd_pair_aarch64_instrs_vector_reduce_fp16_add_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_faddp_advsimd_pair_aarch64_instrs_vector_reduce_fp16_add_sisd Rd Rn sz) s"
  unfolding decode_faddp_advsimd_pair_aarch64_instrs_vector_reduce_fp16_add_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_faddp_advsimd_pair_aarch64_instrs_vector_reduce_fp_add_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_faddp_advsimd_pair_aarch64_instrs_vector_reduce_fp_add_sisd Rd Rn b__0) s"
  unfolding decode_faddp_advsimd_pair_aarch64_instrs_vector_reduce_fp_add_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_faddp_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_add_fp[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_faddp_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_add_fp Rd Rn Rm b__0 U b__1) s"
  unfolding decode_faddp_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_add_fp_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_faddp_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_add_fp16[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_faddp_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_add_fp16 Rd Rn Rm U b__0) s"
  unfolding decode_faddp_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_add_fp16_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_float_compare_cond[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "int LENGTH('datasize) \<in> {16, 32, 64}"
  shows "traces_enabled (execute_aarch64_instrs_float_compare_cond condition (datasize :: 'datasize::len itself) flags__arg m n signal_all_nans) s"
  unfolding execute_aarch64_instrs_float_compare_cond_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fccmp_float_aarch64_instrs_float_compare_cond[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fccmp_float_aarch64_instrs_float_compare_cond nzcv op Rn cond Rm b__0) s"
  unfolding decode_fccmp_float_aarch64_instrs_float_compare_cond_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fccmpe_float_aarch64_instrs_float_compare_cond[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fccmpe_float_aarch64_instrs_float_compare_cond nzcv op Rn cond Rm b__0) s"
  unfolding decode_fccmpe_float_aarch64_instrs_float_compare_cond_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fcmeq_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fcmeq_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_simd Rd Rn ac Rm E U b__0) s"
  unfolding decode_fcmeq_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fcmeq_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fcmeq_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_sisd Rd Rn ac Rm E U) s"
  unfolding decode_fcmeq_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fcmeq_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fcmeq_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp_simd Rd Rn ac Rm b__0 E U b__1) s"
  unfolding decode_fcmeq_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fcmeq_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fcmeq_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp_sisd Rd Rn ac Rm b__0 E U) s"
  unfolding decode_fcmeq_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "int LENGTH('esize) \<in> {16, 32, 64}" and "int LENGTH('datasize) \<in> {16, 32, 64, 128}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_sisd comparison d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) n) s"
  unfolding execute_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fcmeq_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_float_bulk_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fcmeq_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_float_bulk_simd Rd Rn op b__0 U b__1) s"
  unfolding decode_fcmeq_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_float_bulk_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fcmeq_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_float_bulk_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fcmeq_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_float_bulk_sisd Rd Rn op b__0 U) s"
  unfolding decode_fcmeq_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_float_bulk_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fcmeq_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fcmeq_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_simd Rd Rn op U b__0) s"
  unfolding decode_fcmeq_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fcmeq_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fcmeq_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_sisd Rd Rn op U) s"
  unfolding decode_fcmeq_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fcmge_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fcmge_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_simd Rd Rn ac Rm E U b__0) s"
  unfolding decode_fcmge_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fcmge_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fcmge_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_sisd Rd Rn ac Rm E U) s"
  unfolding decode_fcmge_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fcmge_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fcmge_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp_simd Rd Rn ac Rm b__0 E U b__1) s"
  unfolding decode_fcmge_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fcmge_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fcmge_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp_sisd Rd Rn ac Rm b__0 E U) s"
  unfolding decode_fcmge_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fcmge_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_float_bulk_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fcmge_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_float_bulk_simd Rd Rn op b__0 U b__1) s"
  unfolding decode_fcmge_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_float_bulk_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fcmge_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_float_bulk_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fcmge_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_float_bulk_sisd Rd Rn op b__0 U) s"
  unfolding decode_fcmge_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_float_bulk_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fcmge_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fcmge_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_simd Rd Rn op U b__0) s"
  unfolding decode_fcmge_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fcmge_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fcmge_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_sisd Rd Rn op U) s"
  unfolding decode_fcmge_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fcmgt_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fcmgt_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_simd Rd Rn ac Rm E U b__0) s"
  unfolding decode_fcmgt_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fcmgt_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fcmgt_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_sisd Rd Rn ac Rm E U) s"
  unfolding decode_fcmgt_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fcmgt_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fcmgt_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp_simd Rd Rn ac Rm b__0 E U b__1) s"
  unfolding decode_fcmgt_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fcmgt_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fcmgt_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp_sisd Rd Rn ac Rm b__0 E U) s"
  unfolding decode_fcmgt_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fcmgt_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_float_bulk_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fcmgt_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_float_bulk_simd Rd Rn op b__0 U b__1) s"
  unfolding decode_fcmgt_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_float_bulk_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fcmgt_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_float_bulk_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fcmgt_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_float_bulk_sisd Rd Rn op b__0 U) s"
  unfolding decode_fcmgt_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_float_bulk_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fcmgt_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fcmgt_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_simd Rd Rn op U b__0) s"
  unfolding decode_fcmgt_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fcmgt_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fcmgt_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_sisd Rd Rn op U) s"
  unfolding decode_fcmgt_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fcmle_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_float_bulk_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fcmle_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_float_bulk_simd Rd Rn op b__0 U b__1) s"
  unfolding decode_fcmle_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_float_bulk_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fcmle_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_float_bulk_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fcmle_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_float_bulk_sisd Rd Rn op b__0 U) s"
  unfolding decode_fcmle_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_float_bulk_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fcmle_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fcmle_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_simd Rd Rn op U b__0) s"
  unfolding decode_fcmle_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fcmle_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fcmle_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_sisd Rd Rn op U) s"
  unfolding decode_fcmle_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_lessthan_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "int LENGTH('esize) \<in> {16, 32, 64}" and "int LENGTH('datasize) \<in> {16, 32, 64, 128}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_lessthan_sisd comparison d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) n) s"
  unfolding execute_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_lessthan_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fcmlt_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_float_lessthan_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fcmlt_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_float_lessthan_simd Rd Rn b__0 b__1) s"
  unfolding decode_fcmlt_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_float_lessthan_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fcmlt_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_float_lessthan_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fcmlt_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_float_lessthan_sisd Rd Rn b__0) s"
  unfolding decode_fcmlt_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_float_lessthan_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fcmlt_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_lessthan_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fcmlt_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_lessthan_simd Rd Rn b__0) s"
  unfolding decode_fcmlt_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_lessthan_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fcmlt_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_lessthan_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fcmlt_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_lessthan_sisd Rd Rn) s"
  unfolding decode_fcmlt_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_lessthan_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_float_compare_uncond[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "int LENGTH('datasize) \<in> {16, 32, 64}"
  shows "traces_enabled (execute_aarch64_instrs_float_compare_uncond cmp_with_zero (datasize :: 'datasize::len itself) m n signal_all_nans) s"
  unfolding execute_aarch64_instrs_float_compare_uncond_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fcmp_float_aarch64_instrs_float_compare_uncond[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fcmp_float_aarch64_instrs_float_compare_uncond opc Rn Rm b__0) s"
  unfolding decode_fcmp_float_aarch64_instrs_float_compare_uncond_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fcmpe_float_aarch64_instrs_float_compare_uncond[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fcmpe_float_aarch64_instrs_float_compare_uncond opc Rn Rm b__0) s"
  unfolding decode_fcmpe_float_aarch64_instrs_float_compare_uncond_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_float_move_fp_select[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "int LENGTH('datasize) \<in> {16, 32, 64}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_float_move_fp_select condition d (datasize :: 'datasize::len itself) m n) s"
  unfolding execute_aarch64_instrs_float_move_fp_select_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fcsel_float_aarch64_instrs_float_move_fp_select[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fcsel_float_aarch64_instrs_float_move_fp_select Rd Rn cond Rm b__0) s"
  unfolding decode_fcsel_float_aarch64_instrs_float_move_fp_select_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_float_convert_fp[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "int LENGTH('srcsize) \<in> {16, 32, 64}" and "0 \<le> n" and "n \<le> 31" and "int LENGTH('dstsize) \<in> {16, 32, 64}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_float_convert_fp d (dstsize :: 'dstsize::len itself) n (srcsize :: 'srcsize::len itself)) s"
  unfolding execute_aarch64_instrs_float_convert_fp_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fcvt_float_aarch64_instrs_float_convert_fp[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fcvt_float_aarch64_instrs_float_convert_fp Rd Rn b__0 b__1) s"
  unfolding decode_fcvt_float_aarch64_instrs_float_convert_fp_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_tieaway_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "int LENGTH('esize) \<in> {16, 32, 64}" and "int LENGTH('datasize) \<in> {16, 32, 64, 128}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_tieaway_sisd d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) n rounding is_unsigned) s"
  unfolding execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_tieaway_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fcvtas_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_tieaway_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fcvtas_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_tieaway_simd Rd Rn b__0 U b__1) s"
  unfolding decode_fcvtas_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_tieaway_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fcvtas_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_tieaway_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fcvtas_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_tieaway_sisd Rd Rn b__0 U) s"
  unfolding decode_fcvtas_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_tieaway_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fcvtas_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_tieaway_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fcvtas_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_tieaway_simd Rd Rn U b__0) s"
  unfolding decode_fcvtas_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_tieaway_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fcvtas_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_tieaway_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fcvtas_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_tieaway_sisd Rd Rn U) s"
  unfolding decode_fcvtas_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_tieaway_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_float_convert_int[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "part \<in> {0, 1}" and "0 \<le> n" and "n \<le> 31" and "int LENGTH('intsize) \<in> {32, 64}" and "int LENGTH('fltsize) \<in> {16, 32, 64, 128}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_float_convert_int d (fltsize :: 'fltsize::len itself) (intsize :: 'intsize::len itself) n op part rounding is_unsigned) s"
  unfolding execute_aarch64_instrs_float_convert_int_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fcvtas_float_aarch64_instrs_float_convert_int[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fcvtas_float_aarch64_instrs_float_convert_int Rd Rn opcode rmode ftype b__0) s"
  unfolding decode_fcvtas_float_aarch64_instrs_float_convert_int_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fcvtau_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_tieaway_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fcvtau_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_tieaway_simd Rd Rn b__0 U b__1) s"
  unfolding decode_fcvtau_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_tieaway_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fcvtau_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_tieaway_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fcvtau_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_tieaway_sisd Rd Rn b__0 U) s"
  unfolding decode_fcvtau_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_tieaway_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fcvtau_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_tieaway_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fcvtau_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_tieaway_simd Rd Rn U b__0) s"
  unfolding decode_fcvtau_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_tieaway_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fcvtau_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_tieaway_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fcvtau_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_tieaway_sisd Rd Rn U) s"
  unfolding decode_fcvtau_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_tieaway_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fcvtau_float_aarch64_instrs_float_convert_int[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fcvtau_float_aarch64_instrs_float_convert_int Rd Rn opcode rmode ftype b__0) s"
  unfolding decode_fcvtau_float_aarch64_instrs_float_convert_int_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_arithmetic_unary_float_widen[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "part \<in> {0, 1}" and "0 \<le> n" and "n \<le> 31" and "l__177 \<in> {16, 32}" and "datasize = 64" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_arithmetic_unary_float_widen d datasize elements l__177 n part) s"
  unfolding execute_aarch64_instrs_vector_arithmetic_unary_float_widen_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fcvtl_advsimd_aarch64_instrs_vector_arithmetic_unary_float_widen[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fcvtl_advsimd_aarch64_instrs_vector_arithmetic_unary_float_widen Rd Rn b__0 Q) s"
  unfolding decode_fcvtl_advsimd_aarch64_instrs_vector_arithmetic_unary_float_widen_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "int LENGTH('esize) \<in> {16, 32, 64}" and "int LENGTH('datasize) \<in> {16, 32, 64, 128}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) n rounding is_unsigned) s"
  unfolding execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fcvtms_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fcvtms_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd Rd Rn o1 b__0 o2 U b__1) s"
  unfolding decode_fcvtms_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fcvtms_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fcvtms_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd Rd Rn o1 b__0 o2 U) s"
  unfolding decode_fcvtms_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fcvtms_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fcvtms_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd Rd Rn o1 o2 U b__0) s"
  unfolding decode_fcvtms_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fcvtms_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fcvtms_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd Rd Rn o1 o2 U) s"
  unfolding decode_fcvtms_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fcvtms_float_aarch64_instrs_float_convert_int[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fcvtms_float_aarch64_instrs_float_convert_int Rd Rn opcode rmode ftype b__0) s"
  unfolding decode_fcvtms_float_aarch64_instrs_float_convert_int_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fcvtmu_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fcvtmu_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd Rd Rn o1 b__0 o2 U b__1) s"
  unfolding decode_fcvtmu_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fcvtmu_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fcvtmu_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd Rd Rn o1 b__0 o2 U) s"
  unfolding decode_fcvtmu_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fcvtmu_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fcvtmu_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd Rd Rn o1 o2 U b__0) s"
  unfolding decode_fcvtmu_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fcvtmu_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fcvtmu_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd Rd Rn o1 o2 U) s"
  unfolding decode_fcvtmu_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fcvtmu_float_aarch64_instrs_float_convert_int[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fcvtmu_float_aarch64_instrs_float_convert_int Rd Rn opcode rmode ftype b__0) s"
  unfolding decode_fcvtmu_float_aarch64_instrs_float_convert_int_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_arithmetic_unary_float_narrow[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "part \<in> {0, 1}" and "0 \<le> n" and "n \<le> 31" and "l__202 \<in> {16, 32}" and "datasize = 64" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_arithmetic_unary_float_narrow d datasize elements l__202 n part) s"
  unfolding execute_aarch64_instrs_vector_arithmetic_unary_float_narrow_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fcvtn_advsimd_aarch64_instrs_vector_arithmetic_unary_float_narrow[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fcvtn_advsimd_aarch64_instrs_vector_arithmetic_unary_float_narrow Rd Rn b__0 Q) s"
  unfolding decode_fcvtn_advsimd_aarch64_instrs_vector_arithmetic_unary_float_narrow_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fcvtns_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fcvtns_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd Rd Rn o1 b__0 o2 U b__1) s"
  unfolding decode_fcvtns_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fcvtns_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fcvtns_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd Rd Rn o1 b__0 o2 U) s"
  unfolding decode_fcvtns_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fcvtns_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fcvtns_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd Rd Rn o1 o2 U b__0) s"
  unfolding decode_fcvtns_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fcvtns_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fcvtns_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd Rd Rn o1 o2 U) s"
  unfolding decode_fcvtns_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fcvtns_float_aarch64_instrs_float_convert_int[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fcvtns_float_aarch64_instrs_float_convert_int Rd Rn opcode rmode ftype b__0) s"
  unfolding decode_fcvtns_float_aarch64_instrs_float_convert_int_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fcvtnu_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fcvtnu_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd Rd Rn o1 b__0 o2 U b__1) s"
  unfolding decode_fcvtnu_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fcvtnu_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fcvtnu_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd Rd Rn o1 b__0 o2 U) s"
  unfolding decode_fcvtnu_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fcvtnu_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fcvtnu_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd Rd Rn o1 o2 U b__0) s"
  unfolding decode_fcvtnu_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fcvtnu_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fcvtnu_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd Rd Rn o1 o2 U) s"
  unfolding decode_fcvtnu_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fcvtnu_float_aarch64_instrs_float_convert_int[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fcvtnu_float_aarch64_instrs_float_convert_int Rd Rn opcode rmode ftype b__0) s"
  unfolding decode_fcvtnu_float_aarch64_instrs_float_convert_int_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fcvtps_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fcvtps_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd Rd Rn o1 b__0 o2 U b__1) s"
  unfolding decode_fcvtps_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fcvtps_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fcvtps_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd Rd Rn o1 b__0 o2 U) s"
  unfolding decode_fcvtps_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fcvtps_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fcvtps_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd Rd Rn o1 o2 U b__0) s"
  unfolding decode_fcvtps_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fcvtps_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fcvtps_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd Rd Rn o1 o2 U) s"
  unfolding decode_fcvtps_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fcvtps_float_aarch64_instrs_float_convert_int[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fcvtps_float_aarch64_instrs_float_convert_int Rd Rn opcode rmode ftype b__0) s"
  unfolding decode_fcvtps_float_aarch64_instrs_float_convert_int_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fcvtpu_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fcvtpu_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd Rd Rn o1 b__0 o2 U b__1) s"
  unfolding decode_fcvtpu_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fcvtpu_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fcvtpu_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd Rd Rn o1 b__0 o2 U) s"
  unfolding decode_fcvtpu_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fcvtpu_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fcvtpu_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd Rd Rn o1 o2 U b__0) s"
  unfolding decode_fcvtpu_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fcvtpu_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fcvtpu_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd Rd Rn o1 o2 U) s"
  unfolding decode_fcvtpu_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fcvtpu_float_aarch64_instrs_float_convert_int[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fcvtpu_float_aarch64_instrs_float_convert_int Rd Rn opcode rmode ftype b__0) s"
  unfolding decode_fcvtpu_float_aarch64_instrs_float_convert_int_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_arithmetic_unary_float_xtn_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "part \<in> {0, 1}" and "0 \<le> n" and "n \<le> 31" and "esize = 32" and "elements \<in> {1, 2}" and "l__53 \<in> {32, 64}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_arithmetic_unary_float_xtn_sisd d l__53 elements esize n part) s"
  unfolding execute_aarch64_instrs_vector_arithmetic_unary_float_xtn_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fcvtxn_advsimd_aarch64_instrs_vector_arithmetic_unary_float_xtn_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fcvtxn_advsimd_aarch64_instrs_vector_arithmetic_unary_float_xtn_simd Rd Rn sz Q) s"
  unfolding decode_fcvtxn_advsimd_aarch64_instrs_vector_arithmetic_unary_float_xtn_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fcvtxn_advsimd_aarch64_instrs_vector_arithmetic_unary_float_xtn_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fcvtxn_advsimd_aarch64_instrs_vector_arithmetic_unary_float_xtn_sisd Rd Rn sz) s"
  unfolding decode_fcvtxn_advsimd_aarch64_instrs_vector_arithmetic_unary_float_xtn_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_shift_conv_float_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "int LENGTH('esize) \<in> {16, 32, 64}" and "int LENGTH('datasize) \<in> {16, 32, 64, 128}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_shift_conv_float_sisd d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) fracbits n rounding is_unsigned) s"
  unfolding execute_aarch64_instrs_vector_shift_conv_float_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fcvtzs_advsimd_fix_aarch64_instrs_vector_shift_conv_float_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fcvtzs_advsimd_fix_aarch64_instrs_vector_shift_conv_float_simd Rd Rn immb b__0 U b__1) s"
  unfolding decode_fcvtzs_advsimd_fix_aarch64_instrs_vector_shift_conv_float_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fcvtzs_advsimd_fix_aarch64_instrs_vector_shift_conv_float_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fcvtzs_advsimd_fix_aarch64_instrs_vector_shift_conv_float_sisd Rd Rn immb b__0 U) s"
  unfolding decode_fcvtzs_advsimd_fix_aarch64_instrs_vector_shift_conv_float_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fcvtzs_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fcvtzs_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd Rd Rn o1 b__0 o2 U b__1) s"
  unfolding decode_fcvtzs_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fcvtzs_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fcvtzs_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd Rd Rn o1 b__0 o2 U) s"
  unfolding decode_fcvtzs_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fcvtzs_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fcvtzs_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd Rd Rn o1 o2 U b__0) s"
  unfolding decode_fcvtzs_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fcvtzs_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fcvtzs_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd Rd Rn o1 o2 U) s"
  unfolding decode_fcvtzs_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_float_convert_fix[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "int LENGTH('intsize) \<in> {32, 64}" and "1 \<le> fracbits" and "fracbits \<le> 64" and "int LENGTH('fltsize) \<in> {16, 32, 64}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_float_convert_fix d (fltsize :: 'fltsize::len itself) fracbits (intsize :: 'intsize::len itself) n op rounding is_unsigned) s"
  unfolding execute_aarch64_instrs_float_convert_fix_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fcvtzs_float_fix_aarch64_instrs_float_convert_fix[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fcvtzs_float_fix_aarch64_instrs_float_convert_fix Rd Rn scale opcode rmode b__0 b__1) s"
  unfolding decode_fcvtzs_float_fix_aarch64_instrs_float_convert_fix_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fcvtzs_float_int_aarch64_instrs_float_convert_int[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fcvtzs_float_int_aarch64_instrs_float_convert_int Rd Rn opcode rmode ftype b__0) s"
  unfolding decode_fcvtzs_float_int_aarch64_instrs_float_convert_int_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fcvtzu_advsimd_fix_aarch64_instrs_vector_shift_conv_float_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fcvtzu_advsimd_fix_aarch64_instrs_vector_shift_conv_float_simd Rd Rn immb b__0 U b__1) s"
  unfolding decode_fcvtzu_advsimd_fix_aarch64_instrs_vector_shift_conv_float_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fcvtzu_advsimd_fix_aarch64_instrs_vector_shift_conv_float_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fcvtzu_advsimd_fix_aarch64_instrs_vector_shift_conv_float_sisd Rd Rn immb b__0 U) s"
  unfolding decode_fcvtzu_advsimd_fix_aarch64_instrs_vector_shift_conv_float_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fcvtzu_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fcvtzu_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd Rd Rn o1 b__0 o2 U b__1) s"
  unfolding decode_fcvtzu_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fcvtzu_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fcvtzu_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd Rd Rn o1 b__0 o2 U) s"
  unfolding decode_fcvtzu_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fcvtzu_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fcvtzu_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd Rd Rn o1 o2 U b__0) s"
  unfolding decode_fcvtzu_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fcvtzu_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fcvtzu_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd Rd Rn o1 o2 U) s"
  unfolding decode_fcvtzu_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fcvtzu_float_fix_aarch64_instrs_float_convert_fix[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fcvtzu_float_fix_aarch64_instrs_float_convert_fix Rd Rn scale opcode rmode b__0 b__1) s"
  unfolding decode_fcvtzu_float_fix_aarch64_instrs_float_convert_fix_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fcvtzu_float_int_aarch64_instrs_float_convert_int[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fcvtzu_float_int_aarch64_instrs_float_convert_int Rd Rn opcode rmode ftype b__0) s"
  unfolding decode_fcvtzu_float_int_aarch64_instrs_float_convert_int_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_arithmetic_binary_uniform_div_fp16[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "int LENGTH('esize) \<in> {16, 32, 64}" and "int LENGTH('datasize) \<in> {64, 128}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_arithmetic_binary_uniform_div_fp16 d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) m n) s"
  unfolding execute_aarch64_instrs_vector_arithmetic_binary_uniform_div_fp16_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fdiv_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_div[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fdiv_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_div Rd Rn Rm b__0 b__1) s"
  unfolding decode_fdiv_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_div_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fdiv_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_div_fp16[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fdiv_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_div_fp16 Rd Rn Rm b__0) s"
  unfolding decode_fdiv_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_div_fp16_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_float_arithmetic_div[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "int LENGTH('datasize) \<in> {16, 32, 64}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_float_arithmetic_div d (datasize :: 'datasize::len itself) m n) s"
  unfolding execute_aarch64_instrs_float_arithmetic_div_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fdiv_float_aarch64_instrs_float_arithmetic_div[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fdiv_float_aarch64_instrs_float_arithmetic_div Rd Rn Rm b__0) s"
  unfolding decode_fdiv_float_aarch64_instrs_float_arithmetic_div_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fjcvtzs_aarch64_instrs_float_convert_int[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fjcvtzs_aarch64_instrs_float_convert_int Rd Rn opcode rmode ftype b__0) s"
  unfolding decode_fjcvtzs_aarch64_instrs_float_convert_int_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_float_arithmetic_mul_add_sub[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "int LENGTH('datasize) \<in> {16, 32, 64}" and "0 \<le> d" and "d \<le> 31" and "0 \<le> a" and "a \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_float_arithmetic_mul_add_sub a d (datasize :: 'datasize::len itself) m n op1_neg opa_neg) s"
  unfolding execute_aarch64_instrs_float_arithmetic_mul_add_sub_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fmadd_float_aarch64_instrs_float_arithmetic_mul_add_sub[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fmadd_float_aarch64_instrs_float_arithmetic_mul_add_sub Rd Rn Ra o0 Rm o1 b__0) s"
  unfolding decode_fmadd_float_aarch64_instrs_float_arithmetic_mul_add_sub_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp16_1985[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "int LENGTH('esize) \<in> {16, 32, 64}" and "l__401 \<in> {64, 128}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp16_1985 d l__401 elements (esize :: 'esize::len itself) m minimum n pair) s"
  unfolding execute_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp16_1985_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fmax_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp16_1985[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fmax_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp16_1985 Rd Rn Rm o1 U b__0) s"
  unfolding decode_fmax_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp16_1985_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fmax_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp_1985[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fmax_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp_1985 Rd Rn Rm b__0 o1 U b__1) s"
  unfolding decode_fmax_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp_1985_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_float_arithmetic_max_min[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "int LENGTH('datasize) \<in> {16, 32, 64}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_float_arithmetic_max_min d (datasize :: 'datasize::len itself) m n operation) s"
  unfolding execute_aarch64_instrs_float_arithmetic_max_min_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fmax_float_aarch64_instrs_float_arithmetic_max_min[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fmax_float_aarch64_instrs_float_arithmetic_max_min Rd Rn op Rm b__0) s"
  unfolding decode_fmax_float_aarch64_instrs_float_arithmetic_max_min_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp16_2008[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "int LENGTH('esize) \<in> {16, 32, 64}" and "l__435 \<in> {64, 128}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp16_2008 d l__435 elements (esize :: 'esize::len itself) m minimum n pair) s"
  unfolding execute_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp16_2008_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fmaxnm_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp16_2008[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fmaxnm_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp16_2008 Rd Rn Rm a U b__0) s"
  unfolding decode_fmaxnm_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp16_2008_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fmaxnm_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp_2008[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fmaxnm_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp_2008 Rd Rn Rm b__0 o1 U b__1) s"
  unfolding decode_fmaxnm_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp_2008_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fmaxnm_float_aarch64_instrs_float_arithmetic_max_min[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fmaxnm_float_aarch64_instrs_float_arithmetic_max_min Rd Rn op Rm b__0) s"
  unfolding decode_fmaxnm_float_aarch64_instrs_float_arithmetic_max_min_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_reduce_fp16_maxnm_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "int LENGTH('esize) \<in> {16, 32, 64}" and "int LENGTH('datasize) \<in> {32, 64, 128}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_reduce_fp16_maxnm_sisd d (datasize :: 'datasize::len itself) (esize :: 'esize::len itself) n op) s"
  unfolding execute_aarch64_instrs_vector_reduce_fp16_maxnm_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fmaxnmp_advsimd_pair_aarch64_instrs_vector_reduce_fp16_maxnm_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fmaxnmp_advsimd_pair_aarch64_instrs_vector_reduce_fp16_maxnm_sisd Rd Rn sz o1) s"
  unfolding decode_fmaxnmp_advsimd_pair_aarch64_instrs_vector_reduce_fp16_maxnm_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fmaxnmp_advsimd_pair_aarch64_instrs_vector_reduce_fp_maxnm_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fmaxnmp_advsimd_pair_aarch64_instrs_vector_reduce_fp_maxnm_sisd Rd Rn b__0 o1) s"
  unfolding decode_fmaxnmp_advsimd_pair_aarch64_instrs_vector_reduce_fp_maxnm_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fmaxnmp_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp16_2008[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fmaxnmp_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp16_2008 Rd Rn Rm a U b__0) s"
  unfolding decode_fmaxnmp_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp16_2008_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fmaxnmp_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp_2008[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fmaxnmp_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp_2008 Rd Rn Rm b__0 o1 U b__1) s"
  unfolding decode_fmaxnmp_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp_2008_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_reduce_fp16_maxnm_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "int LENGTH('esize) \<in> {16, 32, 64}" and "int LENGTH('datasize) \<in> {64, 128}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_reduce_fp16_maxnm_simd d (datasize :: 'datasize::len itself) (esize :: 'esize::len itself) n op) s"
  unfolding execute_aarch64_instrs_vector_reduce_fp16_maxnm_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fmaxnmv_advsimd_aarch64_instrs_vector_reduce_fp16_maxnm_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fmaxnmv_advsimd_aarch64_instrs_vector_reduce_fp16_maxnm_simd Rd Rn o1 b__0) s"
  unfolding decode_fmaxnmv_advsimd_aarch64_instrs_vector_reduce_fp16_maxnm_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fmaxnmv_advsimd_aarch64_instrs_vector_reduce_fp_maxnm_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fmaxnmv_advsimd_aarch64_instrs_vector_reduce_fp_maxnm_simd Rd Rn b__0 o1 b__1) s"
  unfolding decode_fmaxnmv_advsimd_aarch64_instrs_vector_reduce_fp_maxnm_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_reduce_fp16_max_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "int LENGTH('esize) \<in> {16, 32, 64}" and "int LENGTH('datasize) \<in> {32, 64, 128}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_reduce_fp16_max_sisd d (datasize :: 'datasize::len itself) (esize :: 'esize::len itself) n op) s"
  unfolding execute_aarch64_instrs_vector_reduce_fp16_max_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fmaxp_advsimd_pair_aarch64_instrs_vector_reduce_fp16_max_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fmaxp_advsimd_pair_aarch64_instrs_vector_reduce_fp16_max_sisd Rd Rn sz o1) s"
  unfolding decode_fmaxp_advsimd_pair_aarch64_instrs_vector_reduce_fp16_max_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fmaxp_advsimd_pair_aarch64_instrs_vector_reduce_fp_max_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fmaxp_advsimd_pair_aarch64_instrs_vector_reduce_fp_max_sisd Rd Rn b__0 o1) s"
  unfolding decode_fmaxp_advsimd_pair_aarch64_instrs_vector_reduce_fp_max_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fmaxp_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp16_1985[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fmaxp_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp16_1985 Rd Rn Rm o1 U b__0) s"
  unfolding decode_fmaxp_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp16_1985_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fmaxp_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp_1985[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fmaxp_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp_1985 Rd Rn Rm b__0 o1 U b__1) s"
  unfolding decode_fmaxp_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp_1985_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_reduce_fp16_max_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "int LENGTH('esize) \<in> {16, 32, 64}" and "int LENGTH('datasize) \<in> {64, 128}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_reduce_fp16_max_simd d (datasize :: 'datasize::len itself) (esize :: 'esize::len itself) n op) s"
  unfolding execute_aarch64_instrs_vector_reduce_fp16_max_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fmaxv_advsimd_aarch64_instrs_vector_reduce_fp16_max_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fmaxv_advsimd_aarch64_instrs_vector_reduce_fp16_max_simd Rd Rn o1 b__0) s"
  unfolding decode_fmaxv_advsimd_aarch64_instrs_vector_reduce_fp16_max_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fmaxv_advsimd_aarch64_instrs_vector_reduce_fp_max_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fmaxv_advsimd_aarch64_instrs_vector_reduce_fp_max_simd Rd Rn b__0 o1 b__1) s"
  unfolding decode_fmaxv_advsimd_aarch64_instrs_vector_reduce_fp_max_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fmin_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp16_1985[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fmin_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp16_1985 Rd Rn Rm o1 U b__0) s"
  unfolding decode_fmin_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp16_1985_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fmin_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp_1985[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fmin_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp_1985 Rd Rn Rm b__0 o1 U b__1) s"
  unfolding decode_fmin_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp_1985_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fmin_float_aarch64_instrs_float_arithmetic_max_min[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fmin_float_aarch64_instrs_float_arithmetic_max_min Rd Rn op Rm b__0) s"
  unfolding decode_fmin_float_aarch64_instrs_float_arithmetic_max_min_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fminnm_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp16_2008[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fminnm_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp16_2008 Rd Rn Rm a U b__0) s"
  unfolding decode_fminnm_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp16_2008_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fminnm_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp_2008[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fminnm_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp_2008 Rd Rn Rm b__0 o1 U b__1) s"
  unfolding decode_fminnm_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp_2008_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fminnm_float_aarch64_instrs_float_arithmetic_max_min[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fminnm_float_aarch64_instrs_float_arithmetic_max_min Rd Rn op Rm b__0) s"
  unfolding decode_fminnm_float_aarch64_instrs_float_arithmetic_max_min_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fminnmp_advsimd_pair_aarch64_instrs_vector_reduce_fp16_maxnm_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fminnmp_advsimd_pair_aarch64_instrs_vector_reduce_fp16_maxnm_sisd Rd Rn sz o1) s"
  unfolding decode_fminnmp_advsimd_pair_aarch64_instrs_vector_reduce_fp16_maxnm_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fminnmp_advsimd_pair_aarch64_instrs_vector_reduce_fp_maxnm_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fminnmp_advsimd_pair_aarch64_instrs_vector_reduce_fp_maxnm_sisd Rd Rn b__0 o1) s"
  unfolding decode_fminnmp_advsimd_pair_aarch64_instrs_vector_reduce_fp_maxnm_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fminnmp_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp16_2008[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fminnmp_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp16_2008 Rd Rn Rm a U b__0) s"
  unfolding decode_fminnmp_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp16_2008_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fminnmp_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp_2008[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fminnmp_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp_2008 Rd Rn Rm b__0 o1 U b__1) s"
  unfolding decode_fminnmp_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp_2008_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fminnmv_advsimd_aarch64_instrs_vector_reduce_fp16_maxnm_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fminnmv_advsimd_aarch64_instrs_vector_reduce_fp16_maxnm_simd Rd Rn o1 b__0) s"
  unfolding decode_fminnmv_advsimd_aarch64_instrs_vector_reduce_fp16_maxnm_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fminnmv_advsimd_aarch64_instrs_vector_reduce_fp_maxnm_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fminnmv_advsimd_aarch64_instrs_vector_reduce_fp_maxnm_simd Rd Rn b__0 o1 b__1) s"
  unfolding decode_fminnmv_advsimd_aarch64_instrs_vector_reduce_fp_maxnm_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fminp_advsimd_pair_aarch64_instrs_vector_reduce_fp16_max_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fminp_advsimd_pair_aarch64_instrs_vector_reduce_fp16_max_sisd Rd Rn sz o1) s"
  unfolding decode_fminp_advsimd_pair_aarch64_instrs_vector_reduce_fp16_max_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fminp_advsimd_pair_aarch64_instrs_vector_reduce_fp_max_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fminp_advsimd_pair_aarch64_instrs_vector_reduce_fp_max_sisd Rd Rn b__0 o1) s"
  unfolding decode_fminp_advsimd_pair_aarch64_instrs_vector_reduce_fp_max_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fminp_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp16_1985[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fminp_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp16_1985 Rd Rn Rm o1 U b__0) s"
  unfolding decode_fminp_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp16_1985_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fminp_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp_1985[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fminp_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp_1985 Rd Rn Rm b__0 o1 U b__1) s"
  unfolding decode_fminp_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp_1985_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fminv_advsimd_aarch64_instrs_vector_reduce_fp16_max_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fminv_advsimd_aarch64_instrs_vector_reduce_fp16_max_simd Rd Rn o1 b__0) s"
  unfolding decode_fminv_advsimd_aarch64_instrs_vector_reduce_fp16_max_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fminv_advsimd_aarch64_instrs_vector_reduce_fp_max_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fminv_advsimd_aarch64_instrs_vector_reduce_fp_max_simd Rd Rn b__0 o1 b__1) s"
  unfolding decode_fminv_advsimd_aarch64_instrs_vector_reduce_fp_max_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_fp16_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "index__arg \<in> {0, 1, 2, 3, 4, 5, 6, 7}" and "int LENGTH('idxdsize) \<in> {64, 128}" and "int LENGTH('esize) \<in> {16, 32, 64}" and "int LENGTH('datasize) \<in> {16, 32, 64, 128}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_fp16_sisd d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) (idxdsize :: 'idxdsize::len itself) index__arg m n sub_op) s"
  unfolding execute_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_fp16_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fmla_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_fp16_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fmla_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_fp16_simd Rd Rn b__0 o2 Rm M L b__1) s"
  unfolding decode_fmla_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_fp16_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fmla_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_fp16_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fmla_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_fp16_sisd Rd Rn b__0 o2 Rm M L) s"
  unfolding decode_fmla_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_fp16_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fmla_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_fp_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fmla_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_fp_simd Rd Rn b__0 o2 Rm M L b__1 b__2) s"
  unfolding decode_fmla_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_fp_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fmla_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_fp_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fmla_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_fp_sisd Rd Rn b__0 o2 Rm M L b__1) s"
  unfolding decode_fmla_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_fp_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp16_fused[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "int LENGTH('esize) \<in> {16, 32, 64}" and "int LENGTH('datasize) \<in> {64, 128}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp16_fused d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) m n sub_op) s"
  unfolding execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp16_fused_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fmla_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp16_fused[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fmla_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp16_fused Rd Rn Rm a b__0) s"
  unfolding decode_fmla_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp16_fused_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fmla_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp_fused[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fmla_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp_fused Rd Rn Rm b__0 op b__1) s"
  unfolding decode_fmla_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp_fused_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fmls_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_fp16_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fmls_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_fp16_simd Rd Rn b__0 o2 Rm M L b__1) s"
  unfolding decode_fmls_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_fp16_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fmls_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_fp16_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fmls_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_fp16_sisd Rd Rn b__0 o2 Rm M L) s"
  unfolding decode_fmls_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_fp16_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fmls_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_fp_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fmls_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_fp_simd Rd Rn b__0 o2 Rm M L b__1 b__2) s"
  unfolding decode_fmls_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_fp_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fmls_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_fp_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fmls_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_fp_sisd Rd Rn b__0 o2 Rm M L b__1) s"
  unfolding decode_fmls_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_fp_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fmls_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp16_fused[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fmls_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp16_fused Rd Rn Rm a b__0) s"
  unfolding decode_fmls_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp16_fused_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fmls_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp_fused[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fmls_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp_fused Rd Rn Rm b__0 op b__1) s"
  unfolding decode_fmls_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp_fused_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_fp16_movi[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> rd" and "rd \<le> 31" and "datasize \<in> {64, 128}" and "int (size imm) = datasize"
  shows "traces_enabled (execute_aarch64_instrs_vector_fp16_movi datasize imm rd) s"
  unfolding execute_aarch64_instrs_vector_fp16_movi_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fmov_advsimd_aarch64_instrs_vector_fp16_movi[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fmov_advsimd_aarch64_instrs_vector_fp16_movi Rd h g f e d c__arg b a b__0) s"
  unfolding decode_fmov_advsimd_aarch64_instrs_vector_fp16_movi_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fmov_advsimd_aarch64_instrs_vector_logical[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fmov_advsimd_aarch64_instrs_vector_logical Rd h g f e d cmode c__arg b a op b__0) s"
  unfolding decode_fmov_advsimd_aarch64_instrs_vector_logical_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fmov_float_aarch64_instrs_float_arithmetic_unary[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fmov_float_aarch64_instrs_float_arithmetic_unary Rd Rn opc b__0) s"
  unfolding decode_fmov_float_aarch64_instrs_float_arithmetic_unary_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fmov_float_gen_aarch64_instrs_float_convert_int[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fmov_float_gen_aarch64_instrs_float_convert_int Rd Rn opcode rmode ftype b__0) s"
  unfolding decode_fmov_float_gen_aarch64_instrs_float_convert_int_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_float_move_fp_imm[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "datasize \<in> {16, 32, 64}" and "0 \<le> d" and "d \<le> 31" and "int (size imm) = datasize"
  shows "traces_enabled (execute_aarch64_instrs_float_move_fp_imm d datasize imm) s"
  unfolding execute_aarch64_instrs_float_move_fp_imm_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fmov_float_imm_aarch64_instrs_float_move_fp_imm[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fmov_float_imm_aarch64_instrs_float_move_fp_imm Rd imm8 b__0) s"
  unfolding decode_fmov_float_imm_aarch64_instrs_float_move_fp_imm_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fmsub_float_aarch64_instrs_float_arithmetic_mul_add_sub[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fmsub_float_aarch64_instrs_float_arithmetic_mul_add_sub Rd Rn Ra o0 Rm o1 b__0) s"
  unfolding decode_fmsub_float_aarch64_instrs_float_arithmetic_mul_add_sub_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_arithmetic_binary_element_mul_fp16_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "index__arg \<in> {0, 1, 2, 3, 4, 5, 6, 7}" and "int LENGTH('idxdsize) \<in> {64, 128}" and "int LENGTH('esize) \<in> {16, 32, 64}" and "int LENGTH('datasize) \<in> {16, 32, 64, 128}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_fp16_sisd d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) (idxdsize :: 'idxdsize::len itself) index__arg m mulx_op n) s"
  unfolding execute_aarch64_instrs_vector_arithmetic_binary_element_mul_fp16_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fmul_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_fp16_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fmul_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_fp16_simd Rd Rn b__0 Rm M L U b__1) s"
  unfolding decode_fmul_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_fp16_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fmul_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_fp16_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fmul_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_fp16_sisd Rd Rn b__0 Rm M L U) s"
  unfolding decode_fmul_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_fp16_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fmul_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_fp_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fmul_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_fp_simd Rd Rn b__0 Rm M L b__1 U b__2) s"
  unfolding decode_fmul_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_fp_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fmul_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_fp_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fmul_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_fp_sisd Rd Rn b__0 Rm M L b__1 U) s"
  unfolding decode_fmul_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_fp_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp16_product[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "int LENGTH('esize) \<in> {16, 32, 64}" and "int LENGTH('datasize) \<in> {64, 128}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp16_product d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) m n) s"
  unfolding execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp16_product_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fmul_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp16_product[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fmul_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp16_product Rd Rn Rm b__0) s"
  unfolding decode_fmul_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp16_product_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fmul_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp_product[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fmul_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp_product Rd Rn Rm b__0 b__1) s"
  unfolding decode_fmul_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp_product_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_float_arithmetic_mul_product[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "int LENGTH('datasize) \<in> {16, 32, 64}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_float_arithmetic_mul_product d (datasize :: 'datasize::len itself) m n negated) s"
  unfolding execute_aarch64_instrs_float_arithmetic_mul_product_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fmul_float_aarch64_instrs_float_arithmetic_mul_product[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fmul_float_aarch64_instrs_float_arithmetic_mul_product Rd Rn op Rm b__0) s"
  unfolding decode_fmul_float_aarch64_instrs_float_arithmetic_mul_product_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fmulx_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_fp16_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fmulx_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_fp16_simd Rd Rn b__0 Rm M L U b__1) s"
  unfolding decode_fmulx_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_fp16_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fmulx_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_fp16_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fmulx_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_fp16_sisd Rd Rn b__0 Rm M L U) s"
  unfolding decode_fmulx_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_fp16_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fmulx_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_fp_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fmulx_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_fp_simd Rd Rn b__0 Rm M L b__1 U b__2) s"
  unfolding decode_fmulx_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_fp_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fmulx_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_fp_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fmulx_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_fp_sisd Rd Rn b__0 Rm M L b__1 U) s"
  unfolding decode_fmulx_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_fp_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp16_extended_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "int LENGTH('esize) \<in> {16, 32, 64}" and "int LENGTH('datasize) \<in> {16, 32, 64, 128}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp16_extended_sisd d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) m n) s"
  unfolding execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp16_extended_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fmulx_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp16_extended_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fmulx_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp16_extended_simd Rd Rn Rm b__0) s"
  unfolding decode_fmulx_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp16_extended_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fmulx_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp16_extended_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fmulx_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp16_extended_sisd Rd Rn Rm) s"
  unfolding decode_fmulx_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp16_extended_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fmulx_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp_extended_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fmulx_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp_extended_simd Rd Rn Rm b__0 b__1) s"
  unfolding decode_fmulx_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp_extended_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fmulx_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp_extended_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fmulx_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp_extended_sisd Rd Rn Rm b__0) s"
  unfolding decode_fmulx_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp_extended_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fneg_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_float[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fneg_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_float Rd Rn b__0 U b__1) s"
  unfolding decode_fneg_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_float_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fneg_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_fp16[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fneg_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_fp16 Rd Rn U b__0) s"
  unfolding decode_fneg_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_fp16_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fneg_float_aarch64_instrs_float_arithmetic_unary[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fneg_float_aarch64_instrs_float_arithmetic_unary Rd Rn opc b__0) s"
  unfolding decode_fneg_float_aarch64_instrs_float_arithmetic_unary_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fnmadd_float_aarch64_instrs_float_arithmetic_mul_add_sub[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fnmadd_float_aarch64_instrs_float_arithmetic_mul_add_sub Rd Rn Ra o0 Rm o1 b__0) s"
  unfolding decode_fnmadd_float_aarch64_instrs_float_arithmetic_mul_add_sub_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fnmsub_float_aarch64_instrs_float_arithmetic_mul_add_sub[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fnmsub_float_aarch64_instrs_float_arithmetic_mul_add_sub Rd Rn Ra o0 Rm o1 b__0) s"
  unfolding decode_fnmsub_float_aarch64_instrs_float_arithmetic_mul_add_sub_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fnmul_float_aarch64_instrs_float_arithmetic_mul_product[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fnmul_float_aarch64_instrs_float_arithmetic_mul_product Rd Rn op Rm b__0) s"
  unfolding decode_fnmul_float_aarch64_instrs_float_arithmetic_mul_product_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_arithmetic_unary_special_recip_fp16_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "int LENGTH('esize) \<in> {16, 32, 64}" and "int LENGTH('datasize) \<in> {16, 32, 64, 128}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_arithmetic_unary_special_recip_fp16_sisd d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) n) s"
  unfolding execute_aarch64_instrs_vector_arithmetic_unary_special_recip_fp16_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_frecpe_advsimd_aarch64_instrs_vector_arithmetic_unary_special_recip_float_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_frecpe_advsimd_aarch64_instrs_vector_arithmetic_unary_special_recip_float_simd Rd Rn b__0 b__1) s"
  unfolding decode_frecpe_advsimd_aarch64_instrs_vector_arithmetic_unary_special_recip_float_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_frecpe_advsimd_aarch64_instrs_vector_arithmetic_unary_special_recip_float_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_frecpe_advsimd_aarch64_instrs_vector_arithmetic_unary_special_recip_float_sisd Rd Rn b__0) s"
  unfolding decode_frecpe_advsimd_aarch64_instrs_vector_arithmetic_unary_special_recip_float_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_frecpe_advsimd_aarch64_instrs_vector_arithmetic_unary_special_recip_fp16_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_frecpe_advsimd_aarch64_instrs_vector_arithmetic_unary_special_recip_fp16_simd Rd Rn b__0) s"
  unfolding decode_frecpe_advsimd_aarch64_instrs_vector_arithmetic_unary_special_recip_fp16_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_frecpe_advsimd_aarch64_instrs_vector_arithmetic_unary_special_recip_fp16_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_frecpe_advsimd_aarch64_instrs_vector_arithmetic_unary_special_recip_fp16_sisd Rd Rn) s"
  unfolding decode_frecpe_advsimd_aarch64_instrs_vector_arithmetic_unary_special_recip_fp16_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_arithmetic_binary_uniform_recps_fp16_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "int LENGTH('esize) \<in> {16, 32, 64}" and "int LENGTH('datasize) \<in> {16, 32, 64, 128}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_arithmetic_binary_uniform_recps_fp16_sisd d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) m n) s"
  unfolding execute_aarch64_instrs_vector_arithmetic_binary_uniform_recps_fp16_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_frecps_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_recps_fp16_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_frecps_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_recps_fp16_simd Rd Rn Rm b__0) s"
  unfolding decode_frecps_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_recps_fp16_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_frecps_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_recps_fp16_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_frecps_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_recps_fp16_sisd Rd Rn Rm) s"
  unfolding decode_frecps_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_recps_fp16_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_frecps_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_recps_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_frecps_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_recps_simd Rd Rn Rm b__0 b__1) s"
  unfolding decode_frecps_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_recps_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_frecps_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_recps_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_frecps_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_recps_sisd Rd Rn Rm b__0) s"
  unfolding decode_frecps_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_recps_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_arithmetic_unary_special_frecpx_fp16[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "int LENGTH('esize) \<in> {16, 32, 64}" and "elements = 1" and "int LENGTH('datasize) \<in> {16, 32, 64}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_arithmetic_unary_special_frecpx_fp16 d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) n) s"
  unfolding execute_aarch64_instrs_vector_arithmetic_unary_special_frecpx_fp16_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_frecpx_advsimd_aarch64_instrs_vector_arithmetic_unary_special_frecpx[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_frecpx_advsimd_aarch64_instrs_vector_arithmetic_unary_special_frecpx Rd Rn b__0) s"
  unfolding decode_frecpx_advsimd_aarch64_instrs_vector_arithmetic_unary_special_frecpx_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_frecpx_advsimd_aarch64_instrs_vector_arithmetic_unary_special_frecpx_fp16[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_frecpx_advsimd_aarch64_instrs_vector_arithmetic_unary_special_frecpx_fp16 Rd Rn) s"
  unfolding decode_frecpx_advsimd_aarch64_instrs_vector_arithmetic_unary_special_frecpx_fp16_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_arithmetic_unary_fp16_round[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "int LENGTH('esize) \<in> {16, 32, 64}" and "int LENGTH('datasize) \<in> {64, 128}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_arithmetic_unary_fp16_round d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) exact n rounding) s"
  unfolding execute_aarch64_instrs_vector_arithmetic_unary_fp16_round_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_frinta_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_frinta_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round Rd Rn o1 b__0 o2 U b__1) s"
  unfolding decode_frinta_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_frinta_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_frinta_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round Rd Rn o1 o2 U b__0) s"
  unfolding decode_frinta_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_float_arithmetic_round_frint[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "int LENGTH('datasize) \<in> {16, 32, 64}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_float_arithmetic_round_frint d (datasize :: 'datasize::len itself) exact n rounding) s"
  unfolding execute_aarch64_instrs_float_arithmetic_round_frint_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_frinta_float_aarch64_instrs_float_arithmetic_round_frint[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_frinta_float_aarch64_instrs_float_arithmetic_round_frint Rd Rn rmode b__0 S M) s"
  unfolding decode_frinta_float_aarch64_instrs_float_arithmetic_round_frint_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_frinti_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_frinti_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round Rd Rn o1 b__0 o2 U b__1) s"
  unfolding decode_frinti_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_frinti_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_frinti_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round Rd Rn o1 o2 U b__0) s"
  unfolding decode_frinti_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_frinti_float_aarch64_instrs_float_arithmetic_round_frint[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_frinti_float_aarch64_instrs_float_arithmetic_round_frint Rd Rn rmode b__0 S M) s"
  unfolding decode_frinti_float_aarch64_instrs_float_arithmetic_round_frint_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_frintm_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_frintm_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round Rd Rn o1 b__0 o2 U b__1) s"
  unfolding decode_frintm_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_frintm_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_frintm_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round Rd Rn o1 o2 U b__0) s"
  unfolding decode_frintm_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_frintm_float_aarch64_instrs_float_arithmetic_round_frint[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_frintm_float_aarch64_instrs_float_arithmetic_round_frint Rd Rn rmode b__0 S M) s"
  unfolding decode_frintm_float_aarch64_instrs_float_arithmetic_round_frint_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_frintn_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_frintn_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round Rd Rn o1 b__0 o2 U b__1) s"
  unfolding decode_frintn_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_frintn_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_frintn_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round Rd Rn o1 o2 U b__0) s"
  unfolding decode_frintn_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_frintn_float_aarch64_instrs_float_arithmetic_round_frint[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_frintn_float_aarch64_instrs_float_arithmetic_round_frint Rd Rn rmode b__0 S M) s"
  unfolding decode_frintn_float_aarch64_instrs_float_arithmetic_round_frint_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_frintp_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_frintp_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round Rd Rn o1 b__0 o2 U b__1) s"
  unfolding decode_frintp_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_frintp_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_frintp_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round Rd Rn o1 o2 U b__0) s"
  unfolding decode_frintp_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_frintp_float_aarch64_instrs_float_arithmetic_round_frint[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_frintp_float_aarch64_instrs_float_arithmetic_round_frint Rd Rn rmode b__0 S M) s"
  unfolding decode_frintp_float_aarch64_instrs_float_arithmetic_round_frint_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_frintx_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_frintx_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round Rd Rn o1 b__0 o2 U b__1) s"
  unfolding decode_frintx_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_frintx_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_frintx_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round Rd Rn o1 o2 U b__0) s"
  unfolding decode_frintx_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_frintx_float_aarch64_instrs_float_arithmetic_round_frint[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_frintx_float_aarch64_instrs_float_arithmetic_round_frint Rd Rn rmode b__0 S M) s"
  unfolding decode_frintx_float_aarch64_instrs_float_arithmetic_round_frint_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_frintz_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_frintz_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round Rd Rn o1 b__0 o2 U b__1) s"
  unfolding decode_frintz_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_frintz_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_frintz_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round Rd Rn o1 o2 U b__0) s"
  unfolding decode_frintz_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_frintz_float_aarch64_instrs_float_arithmetic_round_frint[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_frintz_float_aarch64_instrs_float_arithmetic_round_frint Rd Rn rmode b__0 S M) s"
  unfolding decode_frintz_float_aarch64_instrs_float_arithmetic_round_frint_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_arithmetic_unary_special_sqrt_est_fp16_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "int LENGTH('esize) \<in> {16, 32, 64}" and "int LENGTH('datasize) \<in> {16, 32, 64, 128}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_arithmetic_unary_special_sqrt_est_fp16_sisd d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) n) s"
  unfolding execute_aarch64_instrs_vector_arithmetic_unary_special_sqrt_est_fp16_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_frsqrte_advsimd_aarch64_instrs_vector_arithmetic_unary_special_sqrt_est_float_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_frsqrte_advsimd_aarch64_instrs_vector_arithmetic_unary_special_sqrt_est_float_simd Rd Rn b__0 b__1) s"
  unfolding decode_frsqrte_advsimd_aarch64_instrs_vector_arithmetic_unary_special_sqrt_est_float_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_frsqrte_advsimd_aarch64_instrs_vector_arithmetic_unary_special_sqrt_est_float_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_frsqrte_advsimd_aarch64_instrs_vector_arithmetic_unary_special_sqrt_est_float_sisd Rd Rn b__0) s"
  unfolding decode_frsqrte_advsimd_aarch64_instrs_vector_arithmetic_unary_special_sqrt_est_float_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_frsqrte_advsimd_aarch64_instrs_vector_arithmetic_unary_special_sqrt_est_fp16_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_frsqrte_advsimd_aarch64_instrs_vector_arithmetic_unary_special_sqrt_est_fp16_simd Rd Rn b__0) s"
  unfolding decode_frsqrte_advsimd_aarch64_instrs_vector_arithmetic_unary_special_sqrt_est_fp16_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_frsqrte_advsimd_aarch64_instrs_vector_arithmetic_unary_special_sqrt_est_fp16_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_frsqrte_advsimd_aarch64_instrs_vector_arithmetic_unary_special_sqrt_est_fp16_sisd Rd Rn) s"
  unfolding decode_frsqrte_advsimd_aarch64_instrs_vector_arithmetic_unary_special_sqrt_est_fp16_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_arithmetic_binary_uniform_rsqrts_fp16_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "int LENGTH('esize) \<in> {16, 32, 64}" and "int LENGTH('datasize) \<in> {16, 32, 64, 128}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_arithmetic_binary_uniform_rsqrts_fp16_sisd d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) m n) s"
  unfolding execute_aarch64_instrs_vector_arithmetic_binary_uniform_rsqrts_fp16_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_frsqrts_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_rsqrts_fp16_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_frsqrts_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_rsqrts_fp16_simd Rd Rn Rm b__0) s"
  unfolding decode_frsqrts_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_rsqrts_fp16_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_frsqrts_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_rsqrts_fp16_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_frsqrts_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_rsqrts_fp16_sisd Rd Rn Rm) s"
  unfolding decode_frsqrts_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_rsqrts_fp16_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_frsqrts_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_rsqrts_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_frsqrts_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_rsqrts_simd Rd Rn Rm b__0 b__1) s"
  unfolding decode_frsqrts_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_rsqrts_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_frsqrts_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_rsqrts_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_frsqrts_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_rsqrts_sisd Rd Rn Rm b__0) s"
  unfolding decode_frsqrts_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_rsqrts_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_arithmetic_unary_special_sqrt_fp16[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "int LENGTH('esize) \<in> {16, 32, 64}" and "int LENGTH('datasize) \<in> {64, 128}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_arithmetic_unary_special_sqrt_fp16 d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) n) s"
  unfolding execute_aarch64_instrs_vector_arithmetic_unary_special_sqrt_fp16_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fsqrt_advsimd_aarch64_instrs_vector_arithmetic_unary_special_sqrt[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fsqrt_advsimd_aarch64_instrs_vector_arithmetic_unary_special_sqrt Rd Rn b__0 b__1) s"
  unfolding decode_fsqrt_advsimd_aarch64_instrs_vector_arithmetic_unary_special_sqrt_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fsqrt_advsimd_aarch64_instrs_vector_arithmetic_unary_special_sqrt_fp16[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fsqrt_advsimd_aarch64_instrs_vector_arithmetic_unary_special_sqrt_fp16 Rd Rn b__0) s"
  unfolding decode_fsqrt_advsimd_aarch64_instrs_vector_arithmetic_unary_special_sqrt_fp16_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fsqrt_float_aarch64_instrs_float_arithmetic_unary[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fsqrt_float_aarch64_instrs_float_arithmetic_unary Rd Rn opc b__0) s"
  unfolding decode_fsqrt_float_aarch64_instrs_float_arithmetic_unary_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_arithmetic_binary_uniform_sub_fp16_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "int LENGTH('esize) \<in> {16, 32, 64}" and "int LENGTH('datasize) \<in> {64, 128}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_arithmetic_binary_uniform_sub_fp16_simd abs__arg d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) m n) s"
  unfolding execute_aarch64_instrs_vector_arithmetic_binary_uniform_sub_fp16_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_fp16_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_fp16_simd Rd Rn Rm U b__0) s"
  unfolding decode_fsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_fp16_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_fp_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_fp_simd Rd Rn Rm b__0 U b__1) s"
  unfolding decode_fsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_fp_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_fsub_float_aarch64_instrs_float_arithmetic_add_sub[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_fsub_float_aarch64_instrs_float_arithmetic_add_sub Rd Rn op Rm b__0) s"
  unfolding decode_fsub_float_aarch64_instrs_float_arithmetic_add_sub_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_hint_aarch64_instrs_system_hints[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_hint_aarch64_instrs_system_hints op2 CRm) s"
  unfolding decode_hint_aarch64_instrs_system_hints_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_system_exceptions_debug_halt[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "system_reg_access s"
  shows "traces_enabled (execute_aarch64_instrs_system_exceptions_debug_halt arg0) s"
  unfolding execute_aarch64_instrs_system_exceptions_debug_halt_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_hlt_aarch64_instrs_system_exceptions_debug_halt[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_hlt_aarch64_instrs_system_exceptions_debug_halt imm16) s"
  unfolding decode_hlt_aarch64_instrs_system_exceptions_debug_halt_def bind_assoc
  by (traces_enabledI assms: assms elim: Run_or_not_HaltingAllowed_system_reg_access)

lemma traces_enabled_execute_aarch64_instrs_system_exceptions_runtime_hvc[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_aarch64_instrs_system_exceptions_runtime_hvc imm) s"
  unfolding execute_aarch64_instrs_system_exceptions_runtime_hvc_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_hvc_aarch64_instrs_system_exceptions_runtime_hvc[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_hvc_aarch64_instrs_system_exceptions_runtime_hvc imm16) s"
  unfolding decode_hvc_aarch64_instrs_system_exceptions_runtime_hvc_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_transfer_vector_insert[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "int LENGTH('idxdsize) \<in> {64, 128}" and "int LENGTH('esize) \<in> {8, 16, 32, 64, 128, 256}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_transfer_vector_insert d dst_index (esize :: 'esize::len itself) (idxdsize :: 'idxdsize::len itself) n src_index) s"
  unfolding execute_aarch64_instrs_vector_transfer_vector_insert_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ins_advsimd_elt_aarch64_instrs_vector_transfer_vector_insert[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ins_advsimd_elt_aarch64_instrs_vector_transfer_vector_insert Rd Rn imm4 imm5) s"
  unfolding decode_ins_advsimd_elt_aarch64_instrs_vector_transfer_vector_insert_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_transfer_integer_insert[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "int LENGTH('esize) \<in> {8, 16, 32, 64, 128, 256}" and "datasize = 128" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_transfer_integer_insert d datasize (esize :: 'esize::len itself) index__arg n) s"
  unfolding execute_aarch64_instrs_vector_transfer_integer_insert_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ins_advsimd_gen_aarch64_instrs_vector_transfer_integer_insert[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ins_advsimd_gen_aarch64_instrs_vector_transfer_integer_insert Rd Rn b__0) s"
  unfolding decode_ins_advsimd_gen_aarch64_instrs_vector_transfer_integer_insert_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_memory_vector_multiple_no_wb[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "selem \<in> {1, 2, 3, 4}" and "rpt \<in> {1, 2, 3, 4}" and "0 \<le> n" and "n \<le> 31" and "int LENGTH('esize) \<in> {8, 16, 32, 64}" and "int LENGTH('datasize) \<in> {64, 128}"
  shows "traces_enabled (execute_aarch64_instrs_memory_vector_multiple_no_wb (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) m memop n rpt selem t__arg wback) s"
  unfolding execute_aarch64_instrs_memory_vector_multiple_no_wb_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ld1_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ld1_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb Rt Rn b__0 opcode L b__1) s"
  unfolding decode_ld1_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ld1_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ld1_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc Rt Rn b__0 opcode Rm L b__1) s"
  unfolding decode_ld1_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_memory_vector_single_no_wb[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "selem \<in> {1, 2, 3, 4}" and "0 \<le> n" and "n \<le> 31" and "int LENGTH('esize) \<in> {8, 16, 32, 64}" and "int LENGTH('datasize) \<in> {64, 128}"
  shows "traces_enabled (execute_aarch64_instrs_memory_vector_single_no_wb (datasize :: 'datasize::len itself) (esize :: 'esize::len itself) index__arg m memop n replicate__arg selem t__arg wback) s"
  unfolding execute_aarch64_instrs_memory_vector_single_no_wb_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ld1_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ld1_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb Rt Rn b__0 S b__1 R L b__2) s"
  unfolding decode_ld1_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ld1_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ld1_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc Rt Rn b__0 S b__1 Rm R L b__2) s"
  unfolding decode_ld1_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ld1r_advsimd_aarch64_instrs_memory_vector_single_no_wb[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ld1r_advsimd_aarch64_instrs_memory_vector_single_no_wb Rt Rn b__0 S b__1 R L b__2) s"
  unfolding decode_ld1r_advsimd_aarch64_instrs_memory_vector_single_no_wb_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ld1r_advsimd_aarch64_instrs_memory_vector_single_post_inc[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ld1r_advsimd_aarch64_instrs_memory_vector_single_post_inc Rt Rn b__0 S b__1 Rm R L b__2) s"
  unfolding decode_ld1r_advsimd_aarch64_instrs_memory_vector_single_post_inc_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ld2_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ld2_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb Rt Rn b__0 opcode L b__1) s"
  unfolding decode_ld2_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ld2_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ld2_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc Rt Rn b__0 opcode Rm L b__1) s"
  unfolding decode_ld2_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ld2_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ld2_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb Rt Rn b__0 S b__1 R L b__2) s"
  unfolding decode_ld2_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ld2_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ld2_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc Rt Rn b__0 S b__1 Rm R L b__2) s"
  unfolding decode_ld2_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ld2r_advsimd_aarch64_instrs_memory_vector_single_no_wb[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ld2r_advsimd_aarch64_instrs_memory_vector_single_no_wb Rt Rn b__0 S b__1 R L b__2) s"
  unfolding decode_ld2r_advsimd_aarch64_instrs_memory_vector_single_no_wb_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ld2r_advsimd_aarch64_instrs_memory_vector_single_post_inc[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ld2r_advsimd_aarch64_instrs_memory_vector_single_post_inc Rt Rn b__0 S b__1 Rm R L b__2) s"
  unfolding decode_ld2r_advsimd_aarch64_instrs_memory_vector_single_post_inc_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ld3_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ld3_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb Rt Rn b__0 opcode L b__1) s"
  unfolding decode_ld3_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ld3_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ld3_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc Rt Rn b__0 opcode Rm L b__1) s"
  unfolding decode_ld3_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ld3_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ld3_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb Rt Rn b__0 S b__1 R L b__2) s"
  unfolding decode_ld3_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ld3_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ld3_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc Rt Rn b__0 S b__1 Rm R L b__2) s"
  unfolding decode_ld3_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ld3r_advsimd_aarch64_instrs_memory_vector_single_no_wb[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ld3r_advsimd_aarch64_instrs_memory_vector_single_no_wb Rt Rn b__0 S b__1 R L b__2) s"
  unfolding decode_ld3r_advsimd_aarch64_instrs_memory_vector_single_no_wb_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ld3r_advsimd_aarch64_instrs_memory_vector_single_post_inc[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ld3r_advsimd_aarch64_instrs_memory_vector_single_post_inc Rt Rn b__0 S b__1 Rm R L b__2) s"
  unfolding decode_ld3r_advsimd_aarch64_instrs_memory_vector_single_post_inc_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ld4_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ld4_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb Rt Rn b__0 opcode L b__1) s"
  unfolding decode_ld4_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ld4_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ld4_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc Rt Rn b__0 opcode Rm L b__1) s"
  unfolding decode_ld4_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ld4_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ld4_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb Rt Rn b__0 S b__1 R L b__2) s"
  unfolding decode_ld4_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ld4_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ld4_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc Rt Rn b__0 S b__1 Rm R L b__2) s"
  unfolding decode_ld4_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ld4r_advsimd_aarch64_instrs_memory_vector_single_no_wb[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ld4r_advsimd_aarch64_instrs_memory_vector_single_no_wb Rt Rn b__0 S b__1 R L b__2) s"
  unfolding decode_ld4r_advsimd_aarch64_instrs_memory_vector_single_no_wb_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ld4r_advsimd_aarch64_instrs_memory_vector_single_post_inc[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ld4r_advsimd_aarch64_instrs_memory_vector_single_post_inc Rt Rn b__0 S b__1 Rm R L b__2) s"
  unfolding decode_ld4r_advsimd_aarch64_instrs_memory_vector_single_post_inc_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_memory_atomicops_ld[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "0 \<le> s__arg" and "s__arg \<le> 31" and "int LENGTH('regsize) \<in> {32, 64}" and "0 \<le> n" and "n \<le> 31" and "int LENGTH('datasize) \<in> {8, 16, 32, 64}"
  shows "traces_enabled (execute_aarch64_instrs_memory_atomicops_ld (datasize :: 'datasize::len itself) ldacctype n op (regsize :: 'regsize::len itself) s__arg stacctype t__arg) s"
  unfolding execute_aarch64_instrs_memory_atomicops_ld_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldadd_aarch64_instrs_memory_atomicops_ld[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldadd_aarch64_instrs_memory_atomicops_ld Rt Rn opc Rs R A b__0) s"
  unfolding decode_ldadd_aarch64_instrs_memory_atomicops_ld_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldaddb_aarch64_instrs_memory_atomicops_ld[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldaddb_aarch64_instrs_memory_atomicops_ld Rt Rn opc Rs R A b__0) s"
  unfolding decode_ldaddb_aarch64_instrs_memory_atomicops_ld_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldaddh_aarch64_instrs_memory_atomicops_ld[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldaddh_aarch64_instrs_memory_atomicops_ld Rt Rn opc Rs R A b__0) s"
  unfolding decode_ldaddh_aarch64_instrs_memory_atomicops_ld_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_memory_ordered_rcpc[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "int LENGTH('regsize) \<in> {32, 64}" and "0 \<le> n" and "n \<le> 31" and "int LENGTH('datasize) \<in> {8, 16, 32, 64}"
  shows "traces_enabled (execute_aarch64_instrs_memory_ordered_rcpc acctype (datasize :: 'datasize::len itself) n (regsize :: 'regsize::len itself) t__arg) s"
  unfolding execute_aarch64_instrs_memory_ordered_rcpc_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldapr_aarch64_instrs_memory_ordered_rcpc[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldapr_aarch64_instrs_memory_ordered_rcpc Rt Rn Rs b__0) s"
  unfolding decode_ldapr_aarch64_instrs_memory_ordered_rcpc_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldaprb_aarch64_instrs_memory_ordered_rcpc[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldaprb_aarch64_instrs_memory_ordered_rcpc Rt Rn Rs b__0) s"
  unfolding decode_ldaprb_aarch64_instrs_memory_ordered_rcpc_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldaprh_aarch64_instrs_memory_ordered_rcpc[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldaprh_aarch64_instrs_memory_ordered_rcpc Rt Rn Rs b__0) s"
  unfolding decode_ldaprh_aarch64_instrs_memory_ordered_rcpc_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_memory_ordered[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "int LENGTH('regsize) \<in> {32, 64}" and "0 \<le> n" and "n \<le> 31" and "int LENGTH('datasize) \<in> {8, 16, 32, 64}"
  shows "traces_enabled (execute_aarch64_instrs_memory_ordered acctype (datasize :: 'datasize::len itself) memop n (regsize :: 'regsize::len itself) t__arg) s"
  unfolding execute_aarch64_instrs_memory_ordered_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldar_aarch64_instrs_memory_ordered[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldar_aarch64_instrs_memory_ordered Rt Rn Rt2 o0 Rs L b__0) s"
  unfolding decode_ldar_aarch64_instrs_memory_ordered_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldarb_aarch64_instrs_memory_ordered[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldarb_aarch64_instrs_memory_ordered Rt Rn Rt2 o0 Rs L b__0) s"
  unfolding decode_ldarb_aarch64_instrs_memory_ordered_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldarh_aarch64_instrs_memory_ordered[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldarh_aarch64_instrs_memory_ordered Rt Rn Rt2 o0 Rs L b__0) s"
  unfolding decode_ldarh_aarch64_instrs_memory_ordered_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_memory_exclusive_pair[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t2" and "t2 \<le> 31" and "0 \<le> t__arg" and "t__arg \<le> 31" and "0 \<le> s__arg" and "s__arg \<le> 31" and "int LENGTH('regsize) \<in> {32, 64}" and "0 \<le> n" and "n \<le> 31" and "elsize \<in> {32, 64}" and "l__197 \<in> {32, 64, 128}"
  shows "traces_enabled (execute_aarch64_instrs_memory_exclusive_pair acctype l__197 elsize memop n pair (regsize :: 'regsize::len itself) s__arg t__arg t2) s"
  unfolding execute_aarch64_instrs_memory_exclusive_pair_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldaxp_aarch64_instrs_memory_exclusive_pair[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldaxp_aarch64_instrs_memory_exclusive_pair Rt Rn Rt2 o0 Rs L b__0) s"
  unfolding decode_ldaxp_aarch64_instrs_memory_exclusive_pair_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_memory_exclusive_single[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t2" and "t2 \<le> 31" and "0 \<le> t__arg" and "t__arg \<le> 31" and "0 \<le> s__arg" and "s__arg \<le> 31" and "int LENGTH('regsize) \<in> {32, 64}" and "0 \<le> n" and "n \<le> 31" and "elsize \<in> {8, 16, 32, 64}" and "l__532 \<in> {8, 16, 32, 64, 128}"
  shows "traces_enabled (execute_aarch64_instrs_memory_exclusive_single acctype l__532 elsize memop n pair (regsize :: 'regsize::len itself) s__arg t__arg t2) s"
  unfolding execute_aarch64_instrs_memory_exclusive_single_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldaxr_aarch64_instrs_memory_exclusive_single[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldaxr_aarch64_instrs_memory_exclusive_single Rt Rn Rt2 o0 Rs L b__0) s"
  unfolding decode_ldaxr_aarch64_instrs_memory_exclusive_single_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldaxrb_aarch64_instrs_memory_exclusive_single[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldaxrb_aarch64_instrs_memory_exclusive_single Rt Rn Rt2 o0 Rs L b__0) s"
  unfolding decode_ldaxrb_aarch64_instrs_memory_exclusive_single_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldaxrh_aarch64_instrs_memory_exclusive_single[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldaxrh_aarch64_instrs_memory_exclusive_single Rt Rn Rt2 o0 Rs L b__0) s"
  unfolding decode_ldaxrh_aarch64_instrs_memory_exclusive_single_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldclr_aarch64_instrs_memory_atomicops_ld[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldclr_aarch64_instrs_memory_atomicops_ld Rt Rn opc Rs R A b__0) s"
  unfolding decode_ldclr_aarch64_instrs_memory_atomicops_ld_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldclrb_aarch64_instrs_memory_atomicops_ld[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldclrb_aarch64_instrs_memory_atomicops_ld Rt Rn opc Rs R A b__0) s"
  unfolding decode_ldclrb_aarch64_instrs_memory_atomicops_ld_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldclrh_aarch64_instrs_memory_atomicops_ld[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldclrh_aarch64_instrs_memory_atomicops_ld Rt Rn opc Rs R A b__0) s"
  unfolding decode_ldclrh_aarch64_instrs_memory_atomicops_ld_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldeor_aarch64_instrs_memory_atomicops_ld[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldeor_aarch64_instrs_memory_atomicops_ld Rt Rn opc Rs R A b__0) s"
  unfolding decode_ldeor_aarch64_instrs_memory_atomicops_ld_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldeorb_aarch64_instrs_memory_atomicops_ld[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldeorb_aarch64_instrs_memory_atomicops_ld Rt Rn opc Rs R A b__0) s"
  unfolding decode_ldeorb_aarch64_instrs_memory_atomicops_ld_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldeorh_aarch64_instrs_memory_atomicops_ld[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldeorh_aarch64_instrs_memory_atomicops_ld Rt Rn opc Rs R A b__0) s"
  unfolding decode_ldeorh_aarch64_instrs_memory_atomicops_ld_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldlar_aarch64_instrs_memory_ordered[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldlar_aarch64_instrs_memory_ordered Rt Rn Rt2 o0 Rs L b__0) s"
  unfolding decode_ldlar_aarch64_instrs_memory_ordered_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldlarb_aarch64_instrs_memory_ordered[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldlarb_aarch64_instrs_memory_ordered Rt Rn Rt2 o0 Rs L b__0) s"
  unfolding decode_ldlarb_aarch64_instrs_memory_ordered_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldlarh_aarch64_instrs_memory_ordered[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldlarh_aarch64_instrs_memory_ordered Rt Rn Rt2 o0 Rs L b__0) s"
  unfolding decode_ldlarh_aarch64_instrs_memory_ordered_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_memory_pair_simdfp_no_alloc[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "int LENGTH('datasize) \<in> {32, 64, 128, 256}" and "\<not>postindex" and "\<not>wback"
  shows "traces_enabled (execute_aarch64_instrs_memory_pair_simdfp_no_alloc acctype (datasize :: 'datasize::len itself) memop n offset postindex t__arg t2 wback) s"
  unfolding execute_aarch64_instrs_memory_pair_simdfp_no_alloc_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldnp_fpsimd_aarch64_instrs_memory_pair_simdfp_no_alloc[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldnp_fpsimd_aarch64_instrs_memory_pair_simdfp_no_alloc Rt Rn Rt2 imm7 L b__0) s"
  unfolding decode_ldnp_fpsimd_aarch64_instrs_memory_pair_simdfp_no_alloc_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_memory_pair_general_no_alloc[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "int LENGTH('datasize) \<in> {32, 64}" and "\<not>wback"
  shows "traces_enabled (execute_aarch64_instrs_memory_pair_general_no_alloc acctype (datasize :: 'datasize::len itself) memop n offset postindex t__arg t2 wback) s"
  unfolding execute_aarch64_instrs_memory_pair_general_no_alloc_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldnp_gen_aarch64_instrs_memory_pair_general_no_alloc[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldnp_gen_aarch64_instrs_memory_pair_general_no_alloc Rt Rn Rt2 imm7 L b__0) s"
  unfolding decode_ldnp_gen_aarch64_instrs_memory_pair_general_no_alloc_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_memory_pair_simdfp_post_idx[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "int LENGTH('datasize) \<in> {32, 64, 128, 256}" and "memop \<noteq> MemOp_PREFETCH"
  shows "traces_enabled (execute_aarch64_instrs_memory_pair_simdfp_post_idx acctype (datasize :: 'datasize::len itself) memop n offset postindex t__arg t2 wback) s"
  unfolding execute_aarch64_instrs_memory_pair_simdfp_post_idx_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldp_fpsimd_aarch64_instrs_memory_pair_simdfp_offset[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldp_fpsimd_aarch64_instrs_memory_pair_simdfp_offset Rt Rn Rt2 imm7 L b__0) s"
  unfolding decode_ldp_fpsimd_aarch64_instrs_memory_pair_simdfp_offset_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldp_fpsimd_aarch64_instrs_memory_pair_simdfp_post_idx[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldp_fpsimd_aarch64_instrs_memory_pair_simdfp_post_idx Rt Rn Rt2 imm7 L b__0) s"
  unfolding decode_ldp_fpsimd_aarch64_instrs_memory_pair_simdfp_post_idx_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldp_fpsimd_aarch64_instrs_memory_pair_simdfp_pre_idx[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldp_fpsimd_aarch64_instrs_memory_pair_simdfp_pre_idx Rt Rn Rt2 imm7 L b__0) s"
  unfolding decode_ldp_fpsimd_aarch64_instrs_memory_pair_simdfp_pre_idx_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_memory_pair_general_post_idx[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "int LENGTH('datasize) \<in> {32, 64}" and "memop \<noteq> MemOp_PREFETCH"
  shows "traces_enabled (execute_aarch64_instrs_memory_pair_general_post_idx acctype (datasize :: 'datasize::len itself) memop n offset postindex is_signed t__arg t2 wback__arg) s"
  unfolding execute_aarch64_instrs_memory_pair_general_post_idx_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldp_gen_aarch64_instrs_memory_pair_general_offset[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldp_gen_aarch64_instrs_memory_pair_general_offset Rt Rn Rt2 imm7 L b__0) s"
  unfolding decode_ldp_gen_aarch64_instrs_memory_pair_general_offset_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldp_gen_aarch64_instrs_memory_pair_general_post_idx[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldp_gen_aarch64_instrs_memory_pair_general_post_idx Rt Rn Rt2 imm7 L b__0) s"
  unfolding decode_ldp_gen_aarch64_instrs_memory_pair_general_post_idx_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldp_gen_aarch64_instrs_memory_pair_general_pre_idx[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldp_gen_aarch64_instrs_memory_pair_general_pre_idx Rt Rn Rt2 imm7 L b__0) s"
  unfolding decode_ldp_gen_aarch64_instrs_memory_pair_general_pre_idx_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldpsw_aarch64_instrs_memory_pair_general_offset[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldpsw_aarch64_instrs_memory_pair_general_offset Rt Rn Rt2 imm7 L b__0) s"
  unfolding decode_ldpsw_aarch64_instrs_memory_pair_general_offset_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldpsw_aarch64_instrs_memory_pair_general_post_idx[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldpsw_aarch64_instrs_memory_pair_general_post_idx Rt Rn Rt2 imm7 L b__0) s"
  unfolding decode_ldpsw_aarch64_instrs_memory_pair_general_post_idx_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldpsw_aarch64_instrs_memory_pair_general_pre_idx[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldpsw_aarch64_instrs_memory_pair_general_pre_idx Rt Rn Rt2 imm7 L b__0) s"
  unfolding decode_ldpsw_aarch64_instrs_memory_pair_general_pre_idx_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_memory_single_simdfp_immediate_signed_post_idx[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "int LENGTH('datasize) \<in> {8, 16, 32, 64, 128, 256, 512, 1024}" and "memop \<noteq> MemOp_PREFETCH"
  shows "traces_enabled (execute_aarch64_instrs_memory_single_simdfp_immediate_signed_post_idx acctype (datasize :: 'datasize::len itself) memop n offset postindex t__arg wback) s"
  unfolding execute_aarch64_instrs_memory_single_simdfp_immediate_signed_post_idx_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldr_imm_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_post_idx[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldr_imm_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_post_idx Rt Rn imm9 b__0 b__1) s"
  unfolding decode_ldr_imm_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_post_idx_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldr_imm_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_pre_idx[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldr_imm_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_pre_idx Rt Rn imm9 b__0 b__1) s"
  unfolding decode_ldr_imm_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_pre_idx_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldr_imm_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_unsigned[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldr_imm_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_unsigned Rt Rn imm12 b__0 b__1) s"
  unfolding decode_ldr_imm_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_unsigned_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_memory_single_general_immediate_signed_post_idx[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "int LENGTH('regsize) \<in> {32, 64}" and "int LENGTH('datasize) \<in> {8, 16, 32, 64}" and "memop \<noteq> MemOp_PREFETCH"
  shows "traces_enabled (execute_aarch64_instrs_memory_single_general_immediate_signed_post_idx acctype (datasize :: 'datasize::len itself) memop n offset postindex (regsize :: 'regsize::len itself) is_signed t__arg wback__arg) s"
  unfolding execute_aarch64_instrs_memory_single_general_immediate_signed_post_idx_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldr_imm_gen_aarch64_instrs_memory_single_general_immediate_signed_post_idx[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldr_imm_gen_aarch64_instrs_memory_single_general_immediate_signed_post_idx Rt Rn imm9 b__0 b__1) s"
  unfolding decode_ldr_imm_gen_aarch64_instrs_memory_single_general_immediate_signed_post_idx_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldr_imm_gen_aarch64_instrs_memory_single_general_immediate_signed_pre_idx[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldr_imm_gen_aarch64_instrs_memory_single_general_immediate_signed_pre_idx Rt Rn imm9 b__0 b__1) s"
  unfolding decode_ldr_imm_gen_aarch64_instrs_memory_single_general_immediate_signed_pre_idx_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldr_imm_gen_aarch64_instrs_memory_single_general_immediate_unsigned[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldr_imm_gen_aarch64_instrs_memory_single_general_immediate_unsigned Rt Rn imm12 b__0 b__1) s"
  unfolding decode_ldr_imm_gen_aarch64_instrs_memory_single_general_immediate_unsigned_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_memory_literal_simdfp[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "l__44 \<in> {4, 8, 16}"
  shows "traces_enabled (execute_aarch64_instrs_memory_literal_simdfp offset l__44 t__arg) s"
  unfolding execute_aarch64_instrs_memory_literal_simdfp_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldr_lit_fpsimd_aarch64_instrs_memory_literal_simdfp[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldr_lit_fpsimd_aarch64_instrs_memory_literal_simdfp Rt imm19 opc) s"
  unfolding decode_ldr_lit_fpsimd_aarch64_instrs_memory_literal_simdfp_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_memory_literal_general[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "l__200 \<in> {4, 8}"
  shows "traces_enabled (execute_aarch64_instrs_memory_literal_general memop offset is_signed l__200 t__arg) s"
  unfolding execute_aarch64_instrs_memory_literal_general_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldr_lit_gen_aarch64_instrs_memory_literal_general[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldr_lit_gen_aarch64_instrs_memory_literal_general Rt imm19 opc) s"
  unfolding decode_ldr_lit_gen_aarch64_instrs_memory_literal_general_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_memory_single_simdfp_register[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "shift \<in> {0, 1, 2, 3, 4, 5, 6, 7}" and "int LENGTH('datasize) \<in> {8, 16, 32, 64, 128, 256, 512, 1024}" and "memop \<noteq> MemOp_PREFETCH"
  shows "traces_enabled (execute_aarch64_instrs_memory_single_simdfp_register acctype (datasize :: 'datasize::len itself) extend_type m memop n postindex shift t__arg wback) s"
  unfolding execute_aarch64_instrs_memory_single_simdfp_register_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldr_reg_fpsimd_aarch64_instrs_memory_single_simdfp_register[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldr_reg_fpsimd_aarch64_instrs_memory_single_simdfp_register Rt Rn S option_name Rm b__0 b__1) s"
  unfolding decode_ldr_reg_fpsimd_aarch64_instrs_memory_single_simdfp_register_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_memory_single_general_register[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "shift \<in> {0, 1, 2, 3}" and "int LENGTH('regsize) \<in> {32, 64}" and "int LENGTH('datasize) \<in> {8, 16, 32, 64}" and "\<not>wback__arg"
  shows "traces_enabled (execute_aarch64_instrs_memory_single_general_register acctype (datasize :: 'datasize::len itself) extend_type m memop n postindex (regsize :: 'regsize::len itself) shift is_signed t__arg wback__arg) s"
  unfolding execute_aarch64_instrs_memory_single_general_register_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldr_reg_gen_aarch64_instrs_memory_single_general_register[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldr_reg_gen_aarch64_instrs_memory_single_general_register Rt Rn S option_name Rm b__0 b__1) s"
  unfolding decode_ldr_reg_gen_aarch64_instrs_memory_single_general_register_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldrb_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldrb_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx Rt Rn imm9 b__0 b__1) s"
  unfolding decode_ldrb_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldrb_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldrb_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx Rt Rn imm9 b__0 b__1) s"
  unfolding decode_ldrb_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldrb_imm_aarch64_instrs_memory_single_general_immediate_unsigned[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldrb_imm_aarch64_instrs_memory_single_general_immediate_unsigned Rt Rn imm12 b__0 b__1) s"
  unfolding decode_ldrb_imm_aarch64_instrs_memory_single_general_immediate_unsigned_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldrb_reg_aarch64_instrs_memory_single_general_register[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldrb_reg_aarch64_instrs_memory_single_general_register Rt Rn S option_name Rm b__0 b__1) s"
  unfolding decode_ldrb_reg_aarch64_instrs_memory_single_general_register_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldrh_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldrh_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx Rt Rn imm9 b__0 b__1) s"
  unfolding decode_ldrh_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldrh_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldrh_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx Rt Rn imm9 b__0 b__1) s"
  unfolding decode_ldrh_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldrh_imm_aarch64_instrs_memory_single_general_immediate_unsigned[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldrh_imm_aarch64_instrs_memory_single_general_immediate_unsigned Rt Rn imm12 b__0 b__1) s"
  unfolding decode_ldrh_imm_aarch64_instrs_memory_single_general_immediate_unsigned_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldrh_reg_aarch64_instrs_memory_single_general_register[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldrh_reg_aarch64_instrs_memory_single_general_register Rt Rn S option_name Rm b__0 b__1) s"
  unfolding decode_ldrh_reg_aarch64_instrs_memory_single_general_register_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldrsb_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldrsb_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx Rt Rn imm9 b__0 b__1) s"
  unfolding decode_ldrsb_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldrsb_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldrsb_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx Rt Rn imm9 b__0 b__1) s"
  unfolding decode_ldrsb_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldrsb_imm_aarch64_instrs_memory_single_general_immediate_unsigned[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldrsb_imm_aarch64_instrs_memory_single_general_immediate_unsigned Rt Rn imm12 b__0 b__1) s"
  unfolding decode_ldrsb_imm_aarch64_instrs_memory_single_general_immediate_unsigned_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldrsb_reg_aarch64_instrs_memory_single_general_register[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldrsb_reg_aarch64_instrs_memory_single_general_register Rt Rn S option_name Rm b__0 b__1) s"
  unfolding decode_ldrsb_reg_aarch64_instrs_memory_single_general_register_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldrsh_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldrsh_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx Rt Rn imm9 b__0 b__1) s"
  unfolding decode_ldrsh_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldrsh_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldrsh_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx Rt Rn imm9 b__0 b__1) s"
  unfolding decode_ldrsh_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldrsh_imm_aarch64_instrs_memory_single_general_immediate_unsigned[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldrsh_imm_aarch64_instrs_memory_single_general_immediate_unsigned Rt Rn imm12 b__0 b__1) s"
  unfolding decode_ldrsh_imm_aarch64_instrs_memory_single_general_immediate_unsigned_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldrsh_reg_aarch64_instrs_memory_single_general_register[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldrsh_reg_aarch64_instrs_memory_single_general_register Rt Rn S option_name Rm b__0 b__1) s"
  unfolding decode_ldrsh_reg_aarch64_instrs_memory_single_general_register_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldrsw_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldrsw_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx Rt Rn imm9 b__0 b__1) s"
  unfolding decode_ldrsw_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldrsw_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldrsw_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx Rt Rn imm9 b__0 b__1) s"
  unfolding decode_ldrsw_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldrsw_imm_aarch64_instrs_memory_single_general_immediate_unsigned[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldrsw_imm_aarch64_instrs_memory_single_general_immediate_unsigned Rt Rn imm12 b__0 b__1) s"
  unfolding decode_ldrsw_imm_aarch64_instrs_memory_single_general_immediate_unsigned_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldrsw_lit_aarch64_instrs_memory_literal_general[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldrsw_lit_aarch64_instrs_memory_literal_general Rt imm19 opc) s"
  unfolding decode_ldrsw_lit_aarch64_instrs_memory_literal_general_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldrsw_reg_aarch64_instrs_memory_single_general_register[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldrsw_reg_aarch64_instrs_memory_single_general_register Rt Rn S option_name Rm b__0 b__1) s"
  unfolding decode_ldrsw_reg_aarch64_instrs_memory_single_general_register_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldset_aarch64_instrs_memory_atomicops_ld[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldset_aarch64_instrs_memory_atomicops_ld Rt Rn opc Rs R A b__0) s"
  unfolding decode_ldset_aarch64_instrs_memory_atomicops_ld_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldsetb_aarch64_instrs_memory_atomicops_ld[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldsetb_aarch64_instrs_memory_atomicops_ld Rt Rn opc Rs R A b__0) s"
  unfolding decode_ldsetb_aarch64_instrs_memory_atomicops_ld_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldseth_aarch64_instrs_memory_atomicops_ld[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldseth_aarch64_instrs_memory_atomicops_ld Rt Rn opc Rs R A b__0) s"
  unfolding decode_ldseth_aarch64_instrs_memory_atomicops_ld_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldsmax_aarch64_instrs_memory_atomicops_ld[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldsmax_aarch64_instrs_memory_atomicops_ld Rt Rn opc Rs R A b__0) s"
  unfolding decode_ldsmax_aarch64_instrs_memory_atomicops_ld_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldsmaxb_aarch64_instrs_memory_atomicops_ld[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldsmaxb_aarch64_instrs_memory_atomicops_ld Rt Rn opc Rs R A b__0) s"
  unfolding decode_ldsmaxb_aarch64_instrs_memory_atomicops_ld_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldsmaxh_aarch64_instrs_memory_atomicops_ld[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldsmaxh_aarch64_instrs_memory_atomicops_ld Rt Rn opc Rs R A b__0) s"
  unfolding decode_ldsmaxh_aarch64_instrs_memory_atomicops_ld_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldsmin_aarch64_instrs_memory_atomicops_ld[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldsmin_aarch64_instrs_memory_atomicops_ld Rt Rn opc Rs R A b__0) s"
  unfolding decode_ldsmin_aarch64_instrs_memory_atomicops_ld_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldsminb_aarch64_instrs_memory_atomicops_ld[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldsminb_aarch64_instrs_memory_atomicops_ld Rt Rn opc Rs R A b__0) s"
  unfolding decode_ldsminb_aarch64_instrs_memory_atomicops_ld_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldsminh_aarch64_instrs_memory_atomicops_ld[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldsminh_aarch64_instrs_memory_atomicops_ld Rt Rn opc Rs R A b__0) s"
  unfolding decode_ldsminh_aarch64_instrs_memory_atomicops_ld_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "int LENGTH('regsize) \<in> {32, 64}" and "int LENGTH('datasize) \<in> {8, 16, 32, 64}" and "\<not>wback__arg"
  shows "traces_enabled (execute_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv acctype (datasize :: 'datasize::len itself) memop n offset postindex (regsize :: 'regsize::len itself) is_signed t__arg wback__arg) s"
  unfolding execute_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldtr_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldtr_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv Rt Rn imm9 b__0 b__1) s"
  unfolding decode_ldtr_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldtrb_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldtrb_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv Rt Rn imm9 b__0 b__1) s"
  unfolding decode_ldtrb_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldtrh_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldtrh_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv Rt Rn imm9 b__0 b__1) s"
  unfolding decode_ldtrh_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldtrsb_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldtrsb_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv Rt Rn imm9 b__0 b__1) s"
  unfolding decode_ldtrsb_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldtrsh_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldtrsh_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv Rt Rn imm9 b__0 b__1) s"
  unfolding decode_ldtrsh_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldtrsw_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldtrsw_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv Rt Rn imm9 b__0 b__1) s"
  unfolding decode_ldtrsw_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldumax_aarch64_instrs_memory_atomicops_ld[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldumax_aarch64_instrs_memory_atomicops_ld Rt Rn opc Rs R A b__0) s"
  unfolding decode_ldumax_aarch64_instrs_memory_atomicops_ld_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldumaxb_aarch64_instrs_memory_atomicops_ld[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldumaxb_aarch64_instrs_memory_atomicops_ld Rt Rn opc Rs R A b__0) s"
  unfolding decode_ldumaxb_aarch64_instrs_memory_atomicops_ld_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldumaxh_aarch64_instrs_memory_atomicops_ld[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldumaxh_aarch64_instrs_memory_atomicops_ld Rt Rn opc Rs R A b__0) s"
  unfolding decode_ldumaxh_aarch64_instrs_memory_atomicops_ld_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldumin_aarch64_instrs_memory_atomicops_ld[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldumin_aarch64_instrs_memory_atomicops_ld Rt Rn opc Rs R A b__0) s"
  unfolding decode_ldumin_aarch64_instrs_memory_atomicops_ld_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_lduminb_aarch64_instrs_memory_atomicops_ld[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_lduminb_aarch64_instrs_memory_atomicops_ld Rt Rn opc Rs R A b__0) s"
  unfolding decode_lduminb_aarch64_instrs_memory_atomicops_ld_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_lduminh_aarch64_instrs_memory_atomicops_ld[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_lduminh_aarch64_instrs_memory_atomicops_ld Rt Rn opc Rs R A b__0) s"
  unfolding decode_lduminh_aarch64_instrs_memory_atomicops_ld_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_memory_single_simdfp_immediate_signed_offset_normal[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "int LENGTH('datasize) \<in> {8, 16, 32, 64, 128, 256, 512, 1024}" and "\<not>wback"
  shows "traces_enabled (execute_aarch64_instrs_memory_single_simdfp_immediate_signed_offset_normal acctype (datasize :: 'datasize::len itself) memop n offset postindex t__arg wback) s"
  unfolding execute_aarch64_instrs_memory_single_simdfp_immediate_signed_offset_normal_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldur_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_offset_normal[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldur_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_offset_normal Rt Rn imm9 b__0 b__1) s"
  unfolding decode_ldur_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_offset_normal_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_memory_single_general_immediate_signed_offset_normal[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "int LENGTH('regsize) \<in> {32, 64}" and "int LENGTH('datasize) \<in> {8, 16, 32, 64}" and "\<not>wback__arg"
  shows "traces_enabled (execute_aarch64_instrs_memory_single_general_immediate_signed_offset_normal acctype (datasize :: 'datasize::len itself) memop n offset postindex (regsize :: 'regsize::len itself) is_signed t__arg wback__arg) s"
  unfolding execute_aarch64_instrs_memory_single_general_immediate_signed_offset_normal_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldur_gen_aarch64_instrs_memory_single_general_immediate_signed_offset_normal[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldur_gen_aarch64_instrs_memory_single_general_immediate_signed_offset_normal Rt Rn imm9 b__0 b__1) s"
  unfolding decode_ldur_gen_aarch64_instrs_memory_single_general_immediate_signed_offset_normal_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldurb_aarch64_instrs_memory_single_general_immediate_signed_offset_normal[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldurb_aarch64_instrs_memory_single_general_immediate_signed_offset_normal Rt Rn imm9 b__0 b__1) s"
  unfolding decode_ldurb_aarch64_instrs_memory_single_general_immediate_signed_offset_normal_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldurh_aarch64_instrs_memory_single_general_immediate_signed_offset_normal[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldurh_aarch64_instrs_memory_single_general_immediate_signed_offset_normal Rt Rn imm9 b__0 b__1) s"
  unfolding decode_ldurh_aarch64_instrs_memory_single_general_immediate_signed_offset_normal_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldursb_aarch64_instrs_memory_single_general_immediate_signed_offset_normal[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldursb_aarch64_instrs_memory_single_general_immediate_signed_offset_normal Rt Rn imm9 b__0 b__1) s"
  unfolding decode_ldursb_aarch64_instrs_memory_single_general_immediate_signed_offset_normal_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldursh_aarch64_instrs_memory_single_general_immediate_signed_offset_normal[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldursh_aarch64_instrs_memory_single_general_immediate_signed_offset_normal Rt Rn imm9 b__0 b__1) s"
  unfolding decode_ldursh_aarch64_instrs_memory_single_general_immediate_signed_offset_normal_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldursw_aarch64_instrs_memory_single_general_immediate_signed_offset_normal[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldursw_aarch64_instrs_memory_single_general_immediate_signed_offset_normal Rt Rn imm9 b__0 b__1) s"
  unfolding decode_ldursw_aarch64_instrs_memory_single_general_immediate_signed_offset_normal_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldxp_aarch64_instrs_memory_exclusive_pair[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldxp_aarch64_instrs_memory_exclusive_pair Rt Rn Rt2 o0 Rs L b__0) s"
  unfolding decode_ldxp_aarch64_instrs_memory_exclusive_pair_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldxr_aarch64_instrs_memory_exclusive_single[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldxr_aarch64_instrs_memory_exclusive_single Rt Rn Rt2 o0 Rs L b__0) s"
  unfolding decode_ldxr_aarch64_instrs_memory_exclusive_single_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldxrb_aarch64_instrs_memory_exclusive_single[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldxrb_aarch64_instrs_memory_exclusive_single Rt Rn Rt2 o0 Rs L b__0) s"
  unfolding decode_ldxrb_aarch64_instrs_memory_exclusive_single_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldxrh_aarch64_instrs_memory_exclusive_single[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldxrh_aarch64_instrs_memory_exclusive_single Rt Rn Rt2 o0 Rs L b__0) s"
  unfolding decode_ldxrh_aarch64_instrs_memory_exclusive_single_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_lslv_aarch64_instrs_integer_shift_variable[traces_enabledI]:
  assumes "{''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_lslv_aarch64_instrs_integer_shift_variable Rd Rn op2 Rm b__0) s"
  unfolding decode_lslv_aarch64_instrs_integer_shift_variable_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_lsrv_aarch64_instrs_integer_shift_variable[traces_enabledI]:
  assumes "{''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_lsrv_aarch64_instrs_integer_shift_variable Rd Rn op2 Rm b__0) s"
  unfolding decode_lsrv_aarch64_instrs_integer_shift_variable_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_integer_arithmetic_mul_uniform_add_sub[traces_enabledI]:
  assumes "{''_R29''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "int LENGTH('destsize) \<in> {32, 64}" and "int LENGTH('datasize) \<in> {32, 64}" and "0 \<le> d" and "d \<le> 31" and "0 \<le> a" and "a \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_integer_arithmetic_mul_uniform_add_sub a d (datasize :: 'datasize::len itself) (destsize :: 'destsize::len itself) m n sub_op) s"
  unfolding execute_aarch64_instrs_integer_arithmetic_mul_uniform_add_sub_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_madd_aarch64_instrs_integer_arithmetic_mul_uniform_add_sub[traces_enabledI]:
  assumes "{''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_madd_aarch64_instrs_integer_arithmetic_mul_uniform_add_sub Rd Rn Ra o0 Rm b__0) s"
  unfolding decode_madd_aarch64_instrs_integer_arithmetic_mul_uniform_add_sub_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_int[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "index__arg \<in> {0, 1, 2, 3, 4, 5, 6, 7}" and "int LENGTH('idxdsize) \<in> {64, 128}" and "int LENGTH('esize) \<in> {8, 16, 32, 64}" and "int LENGTH('datasize) \<in> {64, 128}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_int d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) (idxdsize :: 'idxdsize::len itself) index__arg m n sub_op) s"
  unfolding execute_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_int_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_mla_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_int[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_mla_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_int Rd Rn b__0 o2 Rm M L b__1 b__2) s"
  unfolding decode_mla_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_int_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_accum[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "int LENGTH('esize) \<in> {8, 16, 32, 64}" and "int LENGTH('datasize) \<in> {64, 128}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_accum d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) m n sub_op) s"
  unfolding execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_accum_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_mla_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_accum[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_mla_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_accum Rd Rn Rm b__0 U b__1) s"
  unfolding decode_mla_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_accum_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_mls_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_int[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_mls_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_int Rd Rn b__0 o2 Rm M L b__1 b__2) s"
  unfolding decode_mls_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_int_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_mls_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_accum[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_mls_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_accum Rd Rn Rm b__0 U b__1) s"
  unfolding decode_mls_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_accum_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_movi_advsimd_aarch64_instrs_vector_logical[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_movi_advsimd_aarch64_instrs_vector_logical Rd h g f e d cmode c__arg b a op b__0) s"
  unfolding decode_movi_advsimd_aarch64_instrs_vector_logical_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_integer_ins_ext_insert_movewide[traces_enabledI]:
  assumes "{''_R29''} \<subseteq> accessible_regs s" and "0 \<le> pos" and "pos \<le> 63" and "int LENGTH('datasize) \<in> {32, 64}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_integer_ins_ext_insert_movewide d (datasize :: 'datasize::len itself) imm opcode pos) s"
  unfolding execute_aarch64_instrs_integer_ins_ext_insert_movewide_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_movk_aarch64_instrs_integer_ins_ext_insert_movewide[traces_enabledI]:
  assumes "{''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_movk_aarch64_instrs_integer_ins_ext_insert_movewide Rd imm16 hw opc b__0) s"
  unfolding decode_movk_aarch64_instrs_integer_ins_ext_insert_movewide_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_movn_aarch64_instrs_integer_ins_ext_insert_movewide[traces_enabledI]:
  assumes "{''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_movn_aarch64_instrs_integer_ins_ext_insert_movewide Rd imm16 hw opc b__0) s"
  unfolding decode_movn_aarch64_instrs_integer_ins_ext_insert_movewide_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_movz_aarch64_instrs_integer_ins_ext_insert_movewide[traces_enabledI]:
  assumes "{''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_movz_aarch64_instrs_integer_ins_ext_insert_movewide Rd imm16 hw opc b__0) s"
  unfolding decode_movz_aarch64_instrs_integer_ins_ext_insert_movewide_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_system_register_system[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "(\<not>read \<and> sys_op0 = 3 \<and> sys_op1 \<in> {0, 4, 6} \<and> sys_op2 = 2 \<and> sys_crn = 12 \<and> sys_crm = 0) \<longrightarrow> no_system_reg_access"
  shows "traces_enabled (execute_aarch64_instrs_system_register_system read sys_crm sys_crn sys_op0 sys_op1 sys_op2 t) s"
  unfolding execute_aarch64_instrs_system_register_system_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_mrs_aarch64_instrs_system_register_system[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "(L \<noteq> 1 \<and> uint o0 = 1 \<and> uint op1 \<in> {0, 4, 6} \<and> uint op2 = 2 \<and> uint CRn = 12 \<and> uint CRm = 0) \<longrightarrow> no_system_reg_access"
  shows "traces_enabled (decode_mrs_aarch64_instrs_system_register_system Rt op2 CRm CRn op1 o0 L) s"
  unfolding decode_mrs_aarch64_instrs_system_register_system_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_system_register_cpsr[traces_enabledI]:
  "traces_enabled (execute_aarch64_instrs_system_register_cpsr field operand) s"
  by (cases field; simp; traces_enabledI)

lemma traces_enabled_decode_msr_imm_aarch64_instrs_system_register_cpsr[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_msr_imm_aarch64_instrs_system_register_cpsr op2 CRm op1) s"
  unfolding decode_msr_imm_aarch64_instrs_system_register_cpsr_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_msr_reg_aarch64_instrs_system_register_system[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "(L \<noteq> 1 \<and> uint o0 = 1 \<and> uint op1 \<in> {0, 4, 6} \<and> uint op2 = 2 \<and> uint CRn = 12 \<and> uint CRm = 0) \<longrightarrow> no_system_reg_access"
  shows "traces_enabled (decode_msr_reg_aarch64_instrs_system_register_system Rt op2 CRm CRn op1 o0 L) s"
  unfolding decode_msr_reg_aarch64_instrs_system_register_system_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_msub_aarch64_instrs_integer_arithmetic_mul_uniform_add_sub[traces_enabledI]:
  assumes "{''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_msub_aarch64_instrs_integer_arithmetic_mul_uniform_add_sub Rd Rn Ra o0 Rm b__0) s"
  unfolding decode_msub_aarch64_instrs_integer_arithmetic_mul_uniform_add_sub_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_arithmetic_binary_element_mul_int[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "index__arg \<in> {0, 1, 2, 3, 4, 5, 6, 7}" and "int LENGTH('idxdsize) \<in> {64, 128}" and "int LENGTH('esize) \<in> {8, 16, 32, 64}" and "int LENGTH('datasize) \<in> {64, 128}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_int d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) (idxdsize :: 'idxdsize::len itself) index__arg m n) s"
  unfolding execute_aarch64_instrs_vector_arithmetic_binary_element_mul_int_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_mul_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_int[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_mul_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_int Rd Rn b__0 Rm M L b__1 b__2) s"
  unfolding decode_mul_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_int_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_product[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "l__55 \<in> {8, 16, 32, 64}" and "int LENGTH('datasize) \<in> {64, 128}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_product d (datasize :: 'datasize::len itself) elements l__55 m n poly) s"
  unfolding execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_product_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_mul_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_product[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_mul_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_product Rd Rn Rm b__0 U b__1) s"
  unfolding decode_mul_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_product_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_mvni_advsimd_aarch64_instrs_vector_logical[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_mvni_advsimd_aarch64_instrs_vector_logical Rd h g f e d cmode c__arg b a op b__0) s"
  unfolding decode_mvni_advsimd_aarch64_instrs_vector_logical_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_neg_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_int_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_neg_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_int_simd Rd Rn b__0 U b__1) s"
  unfolding decode_neg_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_int_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_neg_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_int_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_neg_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_int_sisd Rd Rn b__0 U) s"
  unfolding decode_neg_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_int_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_nop_aarch64_instrs_system_hints[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_nop_aarch64_instrs_system_hints op2 CRm) s"
  unfolding decode_nop_aarch64_instrs_system_hints_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_arithmetic_unary_not[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "esize = 8" and "elements \<in> {8, 16}" and "int LENGTH('datasize) \<in> {64, 128}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_arithmetic_unary_not d (datasize :: 'datasize::len itself) elements esize n) s"
  unfolding execute_aarch64_instrs_vector_arithmetic_unary_not_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_not_advsimd_aarch64_instrs_vector_arithmetic_unary_not[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_not_advsimd_aarch64_instrs_vector_arithmetic_unary_not Rd Rn b__0) s"
  unfolding decode_not_advsimd_aarch64_instrs_vector_arithmetic_unary_not_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_orn_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_logical_and_orr[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_orn_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_logical_and_orr Rd Rn Rm size__arg b__0) s"
  unfolding decode_orn_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_logical_and_orr_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_orn_log_shift_aarch64_instrs_integer_logical_shiftedreg[traces_enabledI]:
  assumes "{''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_orn_log_shift_aarch64_instrs_integer_logical_shiftedreg Rd Rn imm6 Rm N shift opc b__0) s"
  unfolding decode_orn_log_shift_aarch64_instrs_integer_logical_shiftedreg_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_orr_advsimd_imm_aarch64_instrs_vector_logical[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_orr_advsimd_imm_aarch64_instrs_vector_logical Rd h g f e d cmode c__arg b a op b__0) s"
  unfolding decode_orr_advsimd_imm_aarch64_instrs_vector_logical_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_orr_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_logical_and_orr[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_orr_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_logical_and_orr Rd Rn Rm size__arg b__0) s"
  unfolding decode_orr_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_logical_and_orr_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_orr_log_imm_aarch64_instrs_integer_logical_immediate[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_orr_log_imm_aarch64_instrs_integer_logical_immediate Rd Rn imms immr N opc b__0) s"
  unfolding decode_orr_log_imm_aarch64_instrs_integer_logical_immediate_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_orr_log_shift_aarch64_instrs_integer_logical_shiftedreg[traces_enabledI]:
  assumes "{''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_orr_log_shift_aarch64_instrs_integer_logical_shiftedreg Rd Rn imm6 Rm N shift opc b__0) s"
  unfolding decode_orr_log_shift_aarch64_instrs_integer_logical_shiftedreg_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_pmul_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_product[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_pmul_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_product Rd Rn Rm b__0 U b__1) s"
  unfolding decode_pmul_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_product_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_arithmetic_binary_disparate_mul_poly[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "part \<in> {0, 1}" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "l__379 \<in> {8, 16, 32, 64}" and "datasize = 64" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_arithmetic_binary_disparate_mul_poly d datasize elements l__379 m n part) s"
  unfolding execute_aarch64_instrs_vector_arithmetic_binary_disparate_mul_poly_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_pmull_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_mul_poly[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_pmull_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_mul_poly Rd Rn Rm b__0 Q) s"
  unfolding decode_pmull_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_mul_poly_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_memory_single_general_immediate_unsigned[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "int LENGTH('regsize) \<in> {32, 64}" and "int LENGTH('datasize) \<in> {8, 16, 32, 64}" and "\<not>wback__arg"
  shows "traces_enabled (execute_aarch64_instrs_memory_single_general_immediate_unsigned acctype (datasize :: 'datasize::len itself) memop n offset postindex (regsize :: 'regsize::len itself) is_signed t__arg wback__arg) s"
  unfolding execute_aarch64_instrs_memory_single_general_immediate_unsigned_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_prfm_imm_aarch64_instrs_memory_single_general_immediate_unsigned[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_prfm_imm_aarch64_instrs_memory_single_general_immediate_unsigned Rt Rn imm12 b__0 b__1) s"
  unfolding decode_prfm_imm_aarch64_instrs_memory_single_general_immediate_unsigned_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_prfm_lit_aarch64_instrs_memory_literal_general[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_prfm_lit_aarch64_instrs_memory_literal_general Rt imm19 opc) s"
  unfolding decode_prfm_lit_aarch64_instrs_memory_literal_general_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_prfm_reg_aarch64_instrs_memory_single_general_register[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_prfm_reg_aarch64_instrs_memory_single_general_register Rt Rn S option_name Rm b__0 b__1) s"
  unfolding decode_prfm_reg_aarch64_instrs_memory_single_general_register_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_prfum_aarch64_instrs_memory_single_general_immediate_signed_offset_normal[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_prfum_aarch64_instrs_memory_single_general_immediate_signed_offset_normal Rt Rn imm9 b__0 b__1) s"
  unfolding decode_prfum_aarch64_instrs_memory_single_general_immediate_signed_offset_normal_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_psb_aarch64_instrs_system_hints[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_psb_aarch64_instrs_system_hints op2 CRm) s"
  unfolding decode_psb_aarch64_instrs_system_hints_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_raddhn_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_narrow[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_raddhn_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_narrow Rd Rn o1 Rm b__0 U Q) s"
  unfolding decode_raddhn_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_narrow_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_crypto_sha3_rax1[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_crypto_sha3_rax1 d m n) s"
  unfolding execute_aarch64_instrs_vector_crypto_sha3_rax1_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_rax1_advsimd_aarch64_instrs_vector_crypto_sha3_rax1[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_rax1_advsimd_aarch64_instrs_vector_crypto_sha3_rax1 Rd Rn Rm) s"
  unfolding decode_rax1_advsimd_aarch64_instrs_vector_crypto_sha3_rax1_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_integer_arithmetic_rbit[traces_enabledI]:
  assumes "{''_R29''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "int LENGTH('datasize) \<in> {32, 64}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_integer_arithmetic_rbit d (datasize :: 'datasize::len itself) n) s"
  unfolding execute_aarch64_instrs_integer_arithmetic_rbit_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_rbit_int_aarch64_instrs_integer_arithmetic_rbit[traces_enabledI]:
  assumes "{''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_rbit_int_aarch64_instrs_integer_arithmetic_rbit Rd Rn b__0) s"
  unfolding decode_rbit_int_aarch64_instrs_integer_arithmetic_rbit_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ret_aarch64_instrs_branch_unconditional_register[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ret_aarch64_instrs_branch_unconditional_register Rm Rn M A op Z) s"
  unfolding decode_ret_aarch64_instrs_branch_unconditional_register_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_reta_aarch64_instrs_branch_unconditional_register[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_reta_aarch64_instrs_branch_unconditional_register Rm Rn M A op Z) s"
  unfolding decode_reta_aarch64_instrs_branch_unconditional_register_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_arithmetic_unary_rev[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "int LENGTH('esize) \<in> {8, 16, 32, 64}" and "int LENGTH('datasize) \<in> {64, 128}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_arithmetic_unary_rev containers d (datasize :: 'datasize::len itself) elements_per_container (esize :: 'esize::len itself) n) s"
  unfolding execute_aarch64_instrs_vector_arithmetic_unary_rev_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_rev16_advsimd_aarch64_instrs_vector_arithmetic_unary_rev[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_rev16_advsimd_aarch64_instrs_vector_arithmetic_unary_rev Rd Rn o0 b__0 U b__1) s"
  unfolding decode_rev16_advsimd_aarch64_instrs_vector_arithmetic_unary_rev_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_integer_arithmetic_rev[traces_enabledI]:
  assumes "{''_R29''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "int LENGTH('datasize) \<in> {32, 64}" and "0 \<le> d" and "d \<le> 31" and "container_size \<in> {16, 32, 64}"
  shows "traces_enabled (execute_aarch64_instrs_integer_arithmetic_rev container_size d (datasize :: 'datasize::len itself) n) s"
  unfolding execute_aarch64_instrs_integer_arithmetic_rev_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_rev16_int_aarch64_instrs_integer_arithmetic_rev[traces_enabledI]:
  assumes "{''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_rev16_int_aarch64_instrs_integer_arithmetic_rev Rd Rn opc b__0) s"
  unfolding decode_rev16_int_aarch64_instrs_integer_arithmetic_rev_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_rev32_advsimd_aarch64_instrs_vector_arithmetic_unary_rev[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_rev32_advsimd_aarch64_instrs_vector_arithmetic_unary_rev Rd Rn o0 b__0 U b__1) s"
  unfolding decode_rev32_advsimd_aarch64_instrs_vector_arithmetic_unary_rev_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_rev32_int_aarch64_instrs_integer_arithmetic_rev[traces_enabledI]:
  assumes "{''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_rev32_int_aarch64_instrs_integer_arithmetic_rev Rd Rn opc b__0) s"
  unfolding decode_rev32_int_aarch64_instrs_integer_arithmetic_rev_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_rev64_advsimd_aarch64_instrs_vector_arithmetic_unary_rev[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_rev64_advsimd_aarch64_instrs_vector_arithmetic_unary_rev Rd Rn o0 b__0 U b__1) s"
  unfolding decode_rev64_advsimd_aarch64_instrs_vector_arithmetic_unary_rev_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_rev_aarch64_instrs_integer_arithmetic_rev[traces_enabledI]:
  assumes "{''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_rev_aarch64_instrs_integer_arithmetic_rev Rd Rn opc b__0) s"
  unfolding decode_rev_aarch64_instrs_integer_arithmetic_rev_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_rorv_aarch64_instrs_integer_shift_variable[traces_enabledI]:
  assumes "{''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_rorv_aarch64_instrs_integer_shift_variable Rd Rn op2 Rm b__0) s"
  unfolding decode_rorv_aarch64_instrs_integer_shift_variable_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_shift_right_narrow_logical[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "part \<in> {0, 1}" and "0 \<le> n" and "n \<le> 31" and "l__473 \<in> {4, 8, 16, 32, 64}" and "datasize = 64" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_shift_right_narrow_logical d datasize elements l__473 n part round__arg shift) s"
  unfolding execute_aarch64_instrs_vector_shift_right_narrow_logical_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_rshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_logical[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_rshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_logical Rd Rn op immb b__0 Q) s"
  unfolding decode_rshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_logical_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_rsubhn_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_narrow[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_rsubhn_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_narrow Rd Rn o1 Rm b__0 U Q) s"
  unfolding decode_rsubhn_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_narrow_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_arithmetic_binary_uniform_diff[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "int LENGTH('esize) \<in> {8, 16, 32, 64}" and "int LENGTH('datasize) \<in> {64, 128}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_arithmetic_binary_uniform_diff accumulate d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) m n is_unsigned) s"
  unfolding execute_aarch64_instrs_vector_arithmetic_binary_uniform_diff_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_saba_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_diff[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_saba_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_diff Rd Rn ac Rm b__0 U b__1) s"
  unfolding decode_saba_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_diff_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_arithmetic_binary_disparate_diff[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "part \<in> {0, 1}" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "l__469 \<in> {8, 16, 32, 64}" and "datasize = 64" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_arithmetic_binary_disparate_diff accumulate d datasize elements l__469 m n part is_unsigned) s"
  unfolding execute_aarch64_instrs_vector_arithmetic_binary_disparate_diff_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sabal_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_diff[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sabal_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_diff Rd Rn op Rm b__0 U Q) s"
  unfolding decode_sabal_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_diff_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sabd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_diff[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sabd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_diff Rd Rn ac Rm b__0 U b__1) s"
  unfolding decode_sabd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_diff_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sabdl_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_diff[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sabdl_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_diff Rd Rn op Rm b__0 U Q) s"
  unfolding decode_sabdl_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_diff_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_arithmetic_unary_add_pairwise[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "l__169 \<in> {8, 16, 32, 64}" and "int LENGTH('datasize) \<in> {64, 128}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_arithmetic_unary_add_pairwise acc d (datasize :: 'datasize::len itself) elements l__169 n is_unsigned) s"
  unfolding execute_aarch64_instrs_vector_arithmetic_unary_add_pairwise_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sadalp_advsimd_aarch64_instrs_vector_arithmetic_unary_add_pairwise[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sadalp_advsimd_aarch64_instrs_vector_arithmetic_unary_add_pairwise Rd Rn op b__0 U b__1) s"
  unfolding decode_sadalp_advsimd_aarch64_instrs_vector_arithmetic_unary_add_pairwise_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_long[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "part \<in> {0, 1}" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "l__316 \<in> {8, 16, 32, 64}" and "datasize = 64" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_long d datasize elements l__316 m n part sub_op is_unsigned) s"
  unfolding execute_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_long_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_saddl_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_long[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_saddl_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_long Rd Rn o1 Rm b__0 U Q) s"
  unfolding decode_saddl_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_long_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_saddlp_advsimd_aarch64_instrs_vector_arithmetic_unary_add_pairwise[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_saddlp_advsimd_aarch64_instrs_vector_arithmetic_unary_add_pairwise Rd Rn op b__0 U b__1) s"
  unfolding decode_saddlp_advsimd_aarch64_instrs_vector_arithmetic_unary_add_pairwise_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_reduce_add_long[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "l__159 \<in> {8, 16, 32, 64}" and "int LENGTH('datasize) \<in> {64, 128}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_reduce_add_long d (datasize :: 'datasize::len itself) elements l__159 n is_unsigned) s"
  unfolding execute_aarch64_instrs_vector_reduce_add_long_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_saddlv_advsimd_aarch64_instrs_vector_reduce_add_long[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_saddlv_advsimd_aarch64_instrs_vector_reduce_add_long Rd Rn b__0 U b__1) s"
  unfolding decode_saddlv_advsimd_aarch64_instrs_vector_reduce_add_long_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_wide[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "part \<in> {0, 1}" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "l__478 \<in> {8, 16, 32, 64}" and "datasize = 64" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_wide d datasize elements l__478 m n part sub_op is_unsigned) s"
  unfolding execute_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_wide_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_saddw_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_wide[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_saddw_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_wide Rd Rn o1 Rm b__0 U Q) s"
  unfolding decode_saddw_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_wide_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sbc_aarch64_instrs_integer_arithmetic_add_sub_carry[traces_enabledI]:
  assumes "{''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sbc_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn Rm S op b__0) s"
  unfolding decode_sbc_aarch64_instrs_integer_arithmetic_add_sub_carry_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sbcs_aarch64_instrs_integer_arithmetic_add_sub_carry[traces_enabledI]:
  assumes "{''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sbcs_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn Rm S op b__0) s"
  unfolding decode_sbcs_aarch64_instrs_integer_arithmetic_add_sub_carry_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sbfm_aarch64_instrs_integer_bitfield[traces_enabledI]:
  assumes "{''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sbfm_aarch64_instrs_integer_bitfield Rd Rn imms immr N opc b__0) s"
  unfolding decode_sbfm_aarch64_instrs_integer_bitfield_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_shift_conv_int_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "int LENGTH('esize) \<in> {16, 32, 64}" and "int LENGTH('datasize) \<in> {16, 32, 64, 128}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_shift_conv_int_sisd d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) fracbits n rounding is_unsigned) s"
  unfolding execute_aarch64_instrs_vector_shift_conv_int_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_scvtf_advsimd_fix_aarch64_instrs_vector_shift_conv_int_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_scvtf_advsimd_fix_aarch64_instrs_vector_shift_conv_int_simd Rd Rn immb b__0 U b__1) s"
  unfolding decode_scvtf_advsimd_fix_aarch64_instrs_vector_shift_conv_int_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_scvtf_advsimd_fix_aarch64_instrs_vector_shift_conv_int_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_scvtf_advsimd_fix_aarch64_instrs_vector_shift_conv_int_sisd Rd Rn immb b__0 U) s"
  unfolding decode_scvtf_advsimd_fix_aarch64_instrs_vector_shift_conv_int_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_int_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "int LENGTH('esize) \<in> {16, 32, 64}" and "int LENGTH('datasize) \<in> {16, 32, 64, 128}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_int_sisd d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) n is_unsigned) s"
  unfolding execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_int_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_scvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_int_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_scvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_int_simd Rd Rn b__0 U b__1) s"
  unfolding decode_scvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_int_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_scvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_int_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_scvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_int_sisd Rd Rn b__0 U) s"
  unfolding decode_scvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_int_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_scvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_int_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_scvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_int_simd Rd Rn U b__0) s"
  unfolding decode_scvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_int_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_scvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_int_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_scvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_int_sisd Rd Rn U) s"
  unfolding decode_scvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_int_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_scvtf_float_fix_aarch64_instrs_float_convert_fix[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_scvtf_float_fix_aarch64_instrs_float_convert_fix Rd Rn scale opcode rmode b__0 b__1) s"
  unfolding decode_scvtf_float_fix_aarch64_instrs_float_convert_fix_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_scvtf_float_int_aarch64_instrs_float_convert_int[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_scvtf_float_int_aarch64_instrs_float_convert_int Rd Rn opcode rmode ftype b__0) s"
  unfolding decode_scvtf_float_int_aarch64_instrs_float_convert_int_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_integer_arithmetic_div[traces_enabledI]:
  assumes "{''_R29''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "int LENGTH('datasize) \<in> {32, 64}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_integer_arithmetic_div d (datasize :: 'datasize::len itself) m n is_unsigned) s"
  unfolding execute_aarch64_instrs_integer_arithmetic_div_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sdiv_aarch64_instrs_integer_arithmetic_div[traces_enabledI]:
  assumes "{''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sdiv_aarch64_instrs_integer_arithmetic_div Rd Rn o1 Rm b__0) s"
  unfolding decode_sdiv_aarch64_instrs_integer_arithmetic_div_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_arithmetic_binary_element_dotp[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "index__arg \<in> {0, 1, 2, 3}" and "l__375 \<in> {8, 16, 32, 64}" and "int LENGTH('datasize) \<in> {64, 128}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_arithmetic_binary_element_dotp d (datasize :: 'datasize::len itself) elements l__375 index__arg m n is_signed) s"
  unfolding execute_aarch64_instrs_vector_arithmetic_binary_element_dotp_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sdot_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_dotp[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sdot_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_dotp Rd Rn H Rm M L b__0 U b__1) s"
  unfolding decode_sdot_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_dotp_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_dotp[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "l__165 \<in> {8, 16, 32, 64}" and "int LENGTH('datasize) \<in> {64, 128}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_dotp d (datasize :: 'datasize::len itself) elements l__165 m n is_signed) s"
  unfolding execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_dotp_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sdot_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_dotp[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sdot_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_dotp Rd Rn Rm b__0 U b__1) s"
  unfolding decode_sdot_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_dotp_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sev_aarch64_instrs_system_hints[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sev_aarch64_instrs_system_hints op2 CRm) s"
  unfolding decode_sev_aarch64_instrs_system_hints_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sevl_aarch64_instrs_system_hints[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sevl_aarch64_instrs_system_hints op2 CRm) s"
  unfolding decode_sevl_aarch64_instrs_system_hints_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_crypto_sha3op_sha1_hash_choose[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_crypto_sha3op_sha1_hash_choose d m n) s"
  unfolding execute_aarch64_instrs_vector_crypto_sha3op_sha1_hash_choose_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sha1c_advsimd_aarch64_instrs_vector_crypto_sha3op_sha1_hash_choose[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sha1c_advsimd_aarch64_instrs_vector_crypto_sha3op_sha1_hash_choose Rd Rn Rm) s"
  unfolding decode_sha1c_advsimd_aarch64_instrs_vector_crypto_sha3op_sha1_hash_choose_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_crypto_sha2op_sha1_hash[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_crypto_sha2op_sha1_hash d n) s"
  unfolding execute_aarch64_instrs_vector_crypto_sha2op_sha1_hash_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sha1h_advsimd_aarch64_instrs_vector_crypto_sha2op_sha1_hash[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sha1h_advsimd_aarch64_instrs_vector_crypto_sha2op_sha1_hash Rd Rn) s"
  unfolding decode_sha1h_advsimd_aarch64_instrs_vector_crypto_sha2op_sha1_hash_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_crypto_sha3op_sha1_hash_majority[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_crypto_sha3op_sha1_hash_majority d m n) s"
  unfolding execute_aarch64_instrs_vector_crypto_sha3op_sha1_hash_majority_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sha1m_advsimd_aarch64_instrs_vector_crypto_sha3op_sha1_hash_majority[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sha1m_advsimd_aarch64_instrs_vector_crypto_sha3op_sha1_hash_majority Rd Rn Rm) s"
  unfolding decode_sha1m_advsimd_aarch64_instrs_vector_crypto_sha3op_sha1_hash_majority_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_crypto_sha3op_sha1_hash_parity[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_crypto_sha3op_sha1_hash_parity d m n) s"
  unfolding execute_aarch64_instrs_vector_crypto_sha3op_sha1_hash_parity_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sha1p_advsimd_aarch64_instrs_vector_crypto_sha3op_sha1_hash_parity[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sha1p_advsimd_aarch64_instrs_vector_crypto_sha3op_sha1_hash_parity Rd Rn Rm) s"
  unfolding decode_sha1p_advsimd_aarch64_instrs_vector_crypto_sha3op_sha1_hash_parity_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_crypto_sha3op_sha1_sched0[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_crypto_sha3op_sha1_sched0 d m n) s"
  unfolding execute_aarch64_instrs_vector_crypto_sha3op_sha1_sched0_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sha1su0_advsimd_aarch64_instrs_vector_crypto_sha3op_sha1_sched0[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sha1su0_advsimd_aarch64_instrs_vector_crypto_sha3op_sha1_sched0 Rd Rn Rm) s"
  unfolding decode_sha1su0_advsimd_aarch64_instrs_vector_crypto_sha3op_sha1_sched0_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_crypto_sha2op_sha1_sched1[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_crypto_sha2op_sha1_sched1 d n) s"
  unfolding execute_aarch64_instrs_vector_crypto_sha2op_sha1_sched1_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sha1su1_advsimd_aarch64_instrs_vector_crypto_sha2op_sha1_sched1[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sha1su1_advsimd_aarch64_instrs_vector_crypto_sha2op_sha1_sched1 Rd Rn) s"
  unfolding decode_sha1su1_advsimd_aarch64_instrs_vector_crypto_sha2op_sha1_sched1_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_crypto_sha3op_sha256_hash[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_crypto_sha3op_sha256_hash d m n part1) s"
  unfolding execute_aarch64_instrs_vector_crypto_sha3op_sha256_hash_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sha256h2_advsimd_aarch64_instrs_vector_crypto_sha3op_sha256_hash[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sha256h2_advsimd_aarch64_instrs_vector_crypto_sha3op_sha256_hash Rd Rn P Rm) s"
  unfolding decode_sha256h2_advsimd_aarch64_instrs_vector_crypto_sha3op_sha256_hash_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sha256h_advsimd_aarch64_instrs_vector_crypto_sha3op_sha256_hash[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sha256h_advsimd_aarch64_instrs_vector_crypto_sha3op_sha256_hash Rd Rn P Rm) s"
  unfolding decode_sha256h_advsimd_aarch64_instrs_vector_crypto_sha3op_sha256_hash_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_crypto_sha2op_sha256_sched0[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_crypto_sha2op_sha256_sched0 d n) s"
  unfolding execute_aarch64_instrs_vector_crypto_sha2op_sha256_sched0_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sha256su0_advsimd_aarch64_instrs_vector_crypto_sha2op_sha256_sched0[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sha256su0_advsimd_aarch64_instrs_vector_crypto_sha2op_sha256_sched0 Rd Rn) s"
  unfolding decode_sha256su0_advsimd_aarch64_instrs_vector_crypto_sha2op_sha256_sched0_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_crypto_sha3op_sha256_sched1[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_crypto_sha3op_sha256_sched1 d m n) s"
  unfolding execute_aarch64_instrs_vector_crypto_sha3op_sha256_sched1_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sha256su1_advsimd_aarch64_instrs_vector_crypto_sha3op_sha256_sched1[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sha256su1_advsimd_aarch64_instrs_vector_crypto_sha3op_sha256_sched1 Rd Rn Rm) s"
  unfolding decode_sha256su1_advsimd_aarch64_instrs_vector_crypto_sha3op_sha256_sched1_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_crypto_sha512_sha512h2[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_crypto_sha512_sha512h2 d m n) s"
  unfolding execute_aarch64_instrs_vector_crypto_sha512_sha512h2_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sha512h2_advsimd_aarch64_instrs_vector_crypto_sha512_sha512h2[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sha512h2_advsimd_aarch64_instrs_vector_crypto_sha512_sha512h2 Rd Rn Rm) s"
  unfolding decode_sha512h2_advsimd_aarch64_instrs_vector_crypto_sha512_sha512h2_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_crypto_sha512_sha512h[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_crypto_sha512_sha512h d m n) s"
  unfolding execute_aarch64_instrs_vector_crypto_sha512_sha512h_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sha512h_advsimd_aarch64_instrs_vector_crypto_sha512_sha512h[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sha512h_advsimd_aarch64_instrs_vector_crypto_sha512_sha512h Rd Rn Rm) s"
  unfolding decode_sha512h_advsimd_aarch64_instrs_vector_crypto_sha512_sha512h_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_crypto_sha512_sha512su0[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_crypto_sha512_sha512su0 d n) s"
  unfolding execute_aarch64_instrs_vector_crypto_sha512_sha512su0_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sha512su0_advsimd_aarch64_instrs_vector_crypto_sha512_sha512su0[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sha512su0_advsimd_aarch64_instrs_vector_crypto_sha512_sha512su0 Rd Rn) s"
  unfolding decode_sha512su0_advsimd_aarch64_instrs_vector_crypto_sha512_sha512su0_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_crypto_sha512_sha512su1[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_crypto_sha512_sha512su1 d m n) s"
  unfolding execute_aarch64_instrs_vector_crypto_sha512_sha512su1_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sha512su1_advsimd_aarch64_instrs_vector_crypto_sha512_sha512su1[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sha512su1_advsimd_aarch64_instrs_vector_crypto_sha512_sha512su1 Rd Rn Rm) s"
  unfolding decode_sha512su1_advsimd_aarch64_instrs_vector_crypto_sha512_sha512su1_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_arithmetic_binary_uniform_add_halving_truncating[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "int LENGTH('esize) \<in> {8, 16, 32, 64}" and "int LENGTH('datasize) \<in> {64, 128}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_arithmetic_binary_uniform_add_halving_truncating d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) m n is_unsigned) s"
  unfolding execute_aarch64_instrs_vector_arithmetic_binary_uniform_add_halving_truncating_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_shadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_halving_truncating[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_shadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_halving_truncating Rd Rn Rm b__0 U b__1) s"
  unfolding decode_shadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_halving_truncating_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_shift_left_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_shift_left_sisd d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) n shift) s"
  unfolding execute_aarch64_instrs_vector_shift_left_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_shl_advsimd_aarch64_instrs_vector_shift_left_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_shl_advsimd_aarch64_instrs_vector_shift_left_simd Rd Rn immb b__0 b__1) s"
  unfolding decode_shl_advsimd_aarch64_instrs_vector_shift_left_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_shl_advsimd_aarch64_instrs_vector_shift_left_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_shl_advsimd_aarch64_instrs_vector_shift_left_sisd Rd Rn immb immh) s"
  unfolding decode_shl_advsimd_aarch64_instrs_vector_shift_left_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_arithmetic_unary_shift[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "shift \<in> {8, 16, 32, 64}" and "part \<in> {0, 1}" and "0 \<le> n" and "n \<le> 31" and "l__49 \<in> {8, 16, 32, 64}" and "datasize = 64" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_arithmetic_unary_shift d datasize elements l__49 n part shift is_unsigned) s"
  unfolding execute_aarch64_instrs_vector_arithmetic_unary_shift_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_shll_advsimd_aarch64_instrs_vector_arithmetic_unary_shift[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_shll_advsimd_aarch64_instrs_vector_arithmetic_unary_shift Rd Rn b__0 Q) s"
  unfolding decode_shll_advsimd_aarch64_instrs_vector_arithmetic_unary_shift_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_shrn_advsimd_aarch64_instrs_vector_shift_right_narrow_logical[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_shrn_advsimd_aarch64_instrs_vector_shift_right_narrow_logical Rd Rn op immb b__0 Q) s"
  unfolding decode_shrn_advsimd_aarch64_instrs_vector_shift_right_narrow_logical_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_arithmetic_binary_uniform_sub_int[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "int LENGTH('esize) \<in> {8, 16, 32, 64}" and "int LENGTH('datasize) \<in> {64, 128}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_arithmetic_binary_uniform_sub_int d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) m n is_unsigned) s"
  unfolding execute_aarch64_instrs_vector_arithmetic_binary_uniform_sub_int_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_shsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_int[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_shsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_int Rd Rn Rm b__0 U b__1) s"
  unfolding decode_shsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_int_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_shift_left_insert_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_shift_left_insert_sisd d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) n shift) s"
  unfolding execute_aarch64_instrs_vector_shift_left_insert_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sli_advsimd_aarch64_instrs_vector_shift_left_insert_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sli_advsimd_aarch64_instrs_vector_shift_left_insert_simd Rd Rn immb b__0 b__1) s"
  unfolding decode_sli_advsimd_aarch64_instrs_vector_shift_left_insert_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sli_advsimd_aarch64_instrs_vector_shift_left_insert_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sli_advsimd_aarch64_instrs_vector_shift_left_insert_sisd Rd Rn immb immh) s"
  unfolding decode_sli_advsimd_aarch64_instrs_vector_shift_left_insert_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_crypto_sm3_sm3partw1[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_crypto_sm3_sm3partw1 d m n) s"
  unfolding execute_aarch64_instrs_vector_crypto_sm3_sm3partw1_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sm3partw1_advsimd_aarch64_instrs_vector_crypto_sm3_sm3partw1[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sm3partw1_advsimd_aarch64_instrs_vector_crypto_sm3_sm3partw1 Rd Rn Rm) s"
  unfolding decode_sm3partw1_advsimd_aarch64_instrs_vector_crypto_sm3_sm3partw1_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_crypto_sm3_sm3partw2[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_crypto_sm3_sm3partw2 d m n) s"
  unfolding execute_aarch64_instrs_vector_crypto_sm3_sm3partw2_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sm3partw2_advsimd_aarch64_instrs_vector_crypto_sm3_sm3partw2[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sm3partw2_advsimd_aarch64_instrs_vector_crypto_sm3_sm3partw2 Rd Rn Rm) s"
  unfolding decode_sm3partw2_advsimd_aarch64_instrs_vector_crypto_sm3_sm3partw2_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_crypto_sm3_sm3ss1[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "0 \<le> d" and "d \<le> 31" and "0 \<le> a" and "a \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_crypto_sm3_sm3ss1 a d m n) s"
  unfolding execute_aarch64_instrs_vector_crypto_sm3_sm3ss1_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sm3ss1_advsimd_aarch64_instrs_vector_crypto_sm3_sm3ss1[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sm3ss1_advsimd_aarch64_instrs_vector_crypto_sm3_sm3ss1 Rd Rn Ra Rm) s"
  unfolding decode_sm3ss1_advsimd_aarch64_instrs_vector_crypto_sm3_sm3ss1_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_crypto_sm3_sm3tt1a[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "i \<in> {0, 1, 2, 3}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_crypto_sm3_sm3tt1a d i m n) s"
  unfolding execute_aarch64_instrs_vector_crypto_sm3_sm3tt1a_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sm3tt1a_advsimd_aarch64_instrs_vector_crypto_sm3_sm3tt1a[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sm3tt1a_advsimd_aarch64_instrs_vector_crypto_sm3_sm3tt1a Rd Rn imm2 Rm) s"
  unfolding decode_sm3tt1a_advsimd_aarch64_instrs_vector_crypto_sm3_sm3tt1a_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_crypto_sm3_sm3tt1b[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "i \<in> {0, 1, 2, 3}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_crypto_sm3_sm3tt1b d i m n) s"
  unfolding execute_aarch64_instrs_vector_crypto_sm3_sm3tt1b_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sm3tt1b_advsimd_aarch64_instrs_vector_crypto_sm3_sm3tt1b[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sm3tt1b_advsimd_aarch64_instrs_vector_crypto_sm3_sm3tt1b Rd Rn imm2 Rm) s"
  unfolding decode_sm3tt1b_advsimd_aarch64_instrs_vector_crypto_sm3_sm3tt1b_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_crypto_sm3_sm3tt2a[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "i \<in> {0, 1, 2, 3}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_crypto_sm3_sm3tt2a d i m n) s"
  unfolding execute_aarch64_instrs_vector_crypto_sm3_sm3tt2a_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sm3tt2a_advsimd_aarch64_instrs_vector_crypto_sm3_sm3tt2a[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sm3tt2a_advsimd_aarch64_instrs_vector_crypto_sm3_sm3tt2a Rd Rn imm2 Rm) s"
  unfolding decode_sm3tt2a_advsimd_aarch64_instrs_vector_crypto_sm3_sm3tt2a_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_crypto_sm3_sm3tt2b[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "i \<in> {0, 1, 2, 3}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_crypto_sm3_sm3tt2b d i m n) s"
  unfolding execute_aarch64_instrs_vector_crypto_sm3_sm3tt2b_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sm3tt2b_advsimd_aarch64_instrs_vector_crypto_sm3_sm3tt2b[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sm3tt2b_advsimd_aarch64_instrs_vector_crypto_sm3_sm3tt2b Rd Rn imm2 Rm) s"
  unfolding decode_sm3tt2b_advsimd_aarch64_instrs_vector_crypto_sm3_sm3tt2b_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_crypto_sm4_sm4enc[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_crypto_sm4_sm4enc d n) s"
  unfolding execute_aarch64_instrs_vector_crypto_sm4_sm4enc_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sm4e_advsimd_aarch64_instrs_vector_crypto_sm4_sm4enc[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sm4e_advsimd_aarch64_instrs_vector_crypto_sm4_sm4enc Rd Rn) s"
  unfolding decode_sm4e_advsimd_aarch64_instrs_vector_crypto_sm4_sm4enc_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_crypto_sm4_sm4enckey[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_crypto_sm4_sm4enckey d m n) s"
  unfolding execute_aarch64_instrs_vector_crypto_sm4_sm4enckey_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sm4ekey_advsimd_aarch64_instrs_vector_crypto_sm4_sm4enckey[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sm4ekey_advsimd_aarch64_instrs_vector_crypto_sm4_sm4enckey Rd Rn Rm) s"
  unfolding decode_sm4ekey_advsimd_aarch64_instrs_vector_crypto_sm4_sm4enckey_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_integer_arithmetic_mul_widening_32_64[traces_enabledI]:
  assumes "{''_R29''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "destsize = 64" and "datasize = 32" and "0 \<le> d" and "d \<le> 31" and "0 \<le> a" and "a \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_integer_arithmetic_mul_widening_32_64 a d datasize destsize m n sub_op is_unsigned) s"
  unfolding execute_aarch64_instrs_integer_arithmetic_mul_widening_32_64_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_smaddl_aarch64_instrs_integer_arithmetic_mul_widening_32_64[traces_enabledI]:
  assumes "{''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_smaddl_aarch64_instrs_integer_arithmetic_mul_widening_32_64 Rd Rn Ra o0 Rm U) s"
  unfolding decode_smaddl_aarch64_instrs_integer_arithmetic_mul_widening_32_64_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_single[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "int LENGTH('esize) \<in> {8, 16, 32, 64}" and "int LENGTH('datasize) \<in> {64, 128}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_single d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) m minimum n is_unsigned) s"
  unfolding execute_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_single_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_smax_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_single[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_smax_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_single Rd Rn o1 Rm b__0 U b__1) s"
  unfolding decode_smax_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_single_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_pair[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "int LENGTH('esize) \<in> {8, 16, 32, 64}" and "l__193 \<in> {64, 128}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_pair d l__193 elements (esize :: 'esize::len itself) m minimum n is_unsigned) s"
  unfolding execute_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_pair_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_smaxp_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_pair[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_smaxp_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_pair Rd Rn o1 Rm b__0 U b__1) s"
  unfolding decode_smaxp_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_pair_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_reduce_int_max[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "int LENGTH('esize) \<in> {8, 16, 32, 64}" and "int LENGTH('datasize) \<in> {64, 128}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_reduce_int_max d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) min__arg n is_unsigned) s"
  unfolding execute_aarch64_instrs_vector_reduce_int_max_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_smaxv_advsimd_aarch64_instrs_vector_reduce_int_max[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_smaxv_advsimd_aarch64_instrs_vector_reduce_int_max Rd Rn op b__0 U b__1) s"
  unfolding decode_smaxv_advsimd_aarch64_instrs_vector_reduce_int_max_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_system_exceptions_runtime_smc[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_aarch64_instrs_system_exceptions_runtime_smc imm) s"
  unfolding execute_aarch64_instrs_system_exceptions_runtime_smc_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_smc_aarch64_instrs_system_exceptions_runtime_smc[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_smc_aarch64_instrs_system_exceptions_runtime_smc imm16) s"
  unfolding decode_smc_aarch64_instrs_system_exceptions_runtime_smc_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_smin_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_single[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_smin_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_single Rd Rn o1 Rm b__0 U b__1) s"
  unfolding decode_smin_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_single_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sminp_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_pair[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sminp_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_pair Rd Rn o1 Rm b__0 U b__1) s"
  unfolding decode_sminp_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_pair_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sminv_advsimd_aarch64_instrs_vector_reduce_int_max[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sminv_advsimd_aarch64_instrs_vector_reduce_int_max Rd Rn op b__0 U b__1) s"
  unfolding decode_sminv_advsimd_aarch64_instrs_vector_reduce_int_max_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_long[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "part \<in> {0, 1}" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "index__arg \<in> {0, 1, 2, 3, 4, 5, 6, 7}" and "int LENGTH('idxdsize) \<in> {64, 128}" and "l__185 \<in> {8, 16, 32, 64}" and "datasize = 64" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_long d datasize elements l__185 (idxdsize :: 'idxdsize::len itself) index__arg m n part sub_op is_unsigned) s"
  unfolding execute_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_long_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_smlal_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_long[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_smlal_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_long Rd Rn b__0 o2 Rm M L b__1 U Q) s"
  unfolding decode_smlal_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_long_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_arithmetic_binary_disparate_mul_accum[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "part \<in> {0, 1}" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "l__537 \<in> {8, 16, 32, 64}" and "datasize = 64" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_arithmetic_binary_disparate_mul_accum d datasize elements l__537 m n part sub_op is_unsigned) s"
  unfolding execute_aarch64_instrs_vector_arithmetic_binary_disparate_mul_accum_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_smlal_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_accum[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_smlal_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_accum Rd Rn o1 Rm b__0 U Q) s"
  unfolding decode_smlal_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_accum_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_smlsl_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_long[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_smlsl_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_long Rd Rn b__0 o2 Rm M L b__1 U Q) s"
  unfolding decode_smlsl_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_long_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_smlsl_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_accum[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_smlsl_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_accum Rd Rn o1 Rm b__0 U Q) s"
  unfolding decode_smlsl_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_accum_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_transfer_integer_move_signed[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "int LENGTH('idxdsize) \<in> {64, 128}" and "int LENGTH('esize) \<in> {8, 16, 32}" and "int LENGTH('datasize) \<in> {32, 64}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_transfer_integer_move_signed d (datasize :: 'datasize::len itself) (esize :: 'esize::len itself) (idxdsize :: 'idxdsize::len itself) index__arg n) s"
  unfolding execute_aarch64_instrs_vector_transfer_integer_move_signed_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_smov_advsimd_aarch64_instrs_vector_transfer_integer_move_signed[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_smov_advsimd_aarch64_instrs_vector_transfer_integer_move_signed Rd Rn b__0 b__1) s"
  unfolding decode_smov_advsimd_aarch64_instrs_vector_transfer_integer_move_signed_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_smsubl_aarch64_instrs_integer_arithmetic_mul_widening_32_64[traces_enabledI]:
  assumes "{''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_smsubl_aarch64_instrs_integer_arithmetic_mul_widening_32_64 Rd Rn Ra o0 Rm U) s"
  unfolding decode_smsubl_aarch64_instrs_integer_arithmetic_mul_widening_32_64_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_integer_arithmetic_mul_widening_64_128hi[traces_enabledI]:
  assumes "{''_R29''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "datasize = 64" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_integer_arithmetic_mul_widening_64_128hi d datasize m n is_unsigned) s"
  unfolding execute_aarch64_instrs_integer_arithmetic_mul_widening_64_128hi_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_smulh_aarch64_instrs_integer_arithmetic_mul_widening_64_128hi[traces_enabledI]:
  assumes "{''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_smulh_aarch64_instrs_integer_arithmetic_mul_widening_64_128hi Rd Rn Ra Rm U) s"
  unfolding decode_smulh_aarch64_instrs_integer_arithmetic_mul_widening_64_128hi_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_arithmetic_binary_element_mul_long[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "part \<in> {0, 1}" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "index__arg \<in> {0, 1, 2, 3, 4, 5, 6, 7}" and "int LENGTH('idxdsize) \<in> {64, 128}" and "l__173 \<in> {8, 16, 32, 64}" and "datasize = 64" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_long d datasize elements l__173 (idxdsize :: 'idxdsize::len itself) index__arg m n part is_unsigned) s"
  unfolding execute_aarch64_instrs_vector_arithmetic_binary_element_mul_long_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_smull_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_long[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_smull_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_long Rd Rn b__0 Rm M L b__1 U Q) s"
  unfolding decode_smull_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_long_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_arithmetic_binary_disparate_mul_product[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "part \<in> {0, 1}" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "l__189 \<in> {8, 16, 32, 64}" and "datasize = 64" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_arithmetic_binary_disparate_mul_product d datasize elements l__189 m n part is_unsigned) s"
  unfolding execute_aarch64_instrs_vector_arithmetic_binary_disparate_mul_product_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_smull_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_product[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_smull_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_product Rd Rn Rm b__0 U Q) s"
  unfolding decode_smull_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_product_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_arithmetic_unary_diff_neg_sat_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "int LENGTH('esize) \<in> {8, 16, 32, 64}" and "int LENGTH('datasize) \<in> {8, 16, 32, 64, 128}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_arithmetic_unary_diff_neg_sat_sisd d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) n neg) s"
  unfolding execute_aarch64_instrs_vector_arithmetic_unary_diff_neg_sat_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sqabs_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_sat_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sqabs_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_sat_simd Rd Rn b__0 U b__1) s"
  unfolding decode_sqabs_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_sat_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sqabs_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_sat_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sqabs_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_sat_sisd Rd Rn b__0 U) s"
  unfolding decode_sqabs_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_sat_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_arithmetic_binary_uniform_add_saturating_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "int LENGTH('esize) \<in> {8, 16, 32, 64}" and "int LENGTH('datasize) \<in> {8, 16, 32, 64, 128}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_arithmetic_binary_uniform_add_saturating_sisd d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) m n is_unsigned) s"
  unfolding execute_aarch64_instrs_vector_arithmetic_binary_uniform_add_saturating_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sqadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_saturating_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sqadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_saturating_simd Rd Rn Rm b__0 U b__1) s"
  unfolding decode_sqadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_saturating_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sqadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_saturating_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sqadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_saturating_sisd Rd Rn Rm b__0 U) s"
  unfolding decode_sqadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_saturating_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_double_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "part \<in> {0, 1}" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "index__arg \<in> {0, 1, 2, 3, 4, 5, 6, 7}" and "int LENGTH('idxdsize) \<in> {64, 128}" and "l__404 \<in> {8, 16, 32, 64}" and "l__403 \<in> {8, 16, 32, 64}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_double_sisd d l__403 elements l__404 (idxdsize :: 'idxdsize::len itself) index__arg m n part sub_op) s"
  unfolding execute_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_double_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sqdmlal_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_double_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sqdmlal_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_double_simd Rd Rn b__0 o2 Rm M L b__1 Q) s"
  unfolding decode_sqdmlal_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_double_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sqdmlal_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_double_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sqdmlal_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_double_sisd Rd Rn b__0 o2 Rm M L b__1) s"
  unfolding decode_sqdmlal_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_double_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_arithmetic_binary_disparate_mul_dmacc_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "part \<in> {0, 1}" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "l__438 \<in> {8, 16, 32, 64}" and "l__437 \<in> {8, 16, 32, 64}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_arithmetic_binary_disparate_mul_dmacc_sisd d l__437 elements l__438 m n part sub_op) s"
  unfolding execute_aarch64_instrs_vector_arithmetic_binary_disparate_mul_dmacc_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sqdmlal_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_dmacc_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sqdmlal_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_dmacc_simd Rd Rn o1 Rm b__0 Q) s"
  unfolding decode_sqdmlal_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_dmacc_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sqdmlal_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_dmacc_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sqdmlal_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_dmacc_sisd Rd Rn o1 Rm b__0) s"
  unfolding decode_sqdmlal_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_dmacc_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sqdmlsl_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_double_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sqdmlsl_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_double_simd Rd Rn b__0 o2 Rm M L b__1 Q) s"
  unfolding decode_sqdmlsl_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_double_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sqdmlsl_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_double_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sqdmlsl_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_double_sisd Rd Rn b__0 o2 Rm M L b__1) s"
  unfolding decode_sqdmlsl_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_double_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sqdmlsl_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_dmacc_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sqdmlsl_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_dmacc_simd Rd Rn o1 Rm b__0 Q) s"
  unfolding decode_sqdmlsl_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_dmacc_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sqdmlsl_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_dmacc_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sqdmlsl_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_dmacc_sisd Rd Rn o1 Rm b__0) s"
  unfolding decode_sqdmlsl_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_dmacc_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_arithmetic_binary_element_mul_high_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "index__arg \<in> {0, 1, 2, 3, 4, 5, 6, 7}" and "int LENGTH('idxdsize) \<in> {64, 128}" and "int LENGTH('esize) \<in> {8, 16, 32, 64}" and "int LENGTH('datasize) \<in> {8, 16, 32, 64, 128}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_high_sisd d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) (idxdsize :: 'idxdsize::len itself) index__arg m n round__arg) s"
  unfolding execute_aarch64_instrs_vector_arithmetic_binary_element_mul_high_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sqdmulh_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_high_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sqdmulh_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_high_simd Rd Rn b__0 op Rm M L b__1 b__2) s"
  unfolding decode_sqdmulh_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_high_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sqdmulh_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_high_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sqdmulh_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_high_sisd Rd Rn b__0 op Rm M L b__1) s"
  unfolding decode_sqdmulh_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_high_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "int LENGTH('esize) \<in> {8, 16, 32, 64}" and "int LENGTH('datasize) \<in> {8, 16, 32, 64, 128}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_sisd d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) m n rounding) s"
  unfolding execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sqdmulh_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sqdmulh_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_simd Rd Rn Rm b__0 U b__1) s"
  unfolding decode_sqdmulh_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sqdmulh_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sqdmulh_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_sisd Rd Rn Rm b__0 U) s"
  unfolding decode_sqdmulh_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_arithmetic_binary_element_mul_double_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "part \<in> {0, 1}" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "index__arg \<in> {0, 1, 2, 3, 4, 5, 6, 7}" and "int LENGTH('idxdsize) \<in> {64, 128}" and "l__124 \<in> {8, 16, 32, 64}" and "l__123 \<in> {8, 16, 32, 64}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_double_sisd d l__123 elements l__124 (idxdsize :: 'idxdsize::len itself) index__arg m n part) s"
  unfolding execute_aarch64_instrs_vector_arithmetic_binary_element_mul_double_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sqdmull_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_double_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sqdmull_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_double_simd Rd Rn b__0 Rm M L b__1 Q) s"
  unfolding decode_sqdmull_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_double_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sqdmull_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_double_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sqdmull_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_double_sisd Rd Rn b__0 Rm M L b__1) s"
  unfolding decode_sqdmull_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_double_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_arithmetic_binary_disparate_mul_double_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "part \<in> {0, 1}" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "l__60 \<in> {8, 16, 32, 64}" and "l__59 \<in> {8, 16, 32, 64}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_arithmetic_binary_disparate_mul_double_sisd d l__59 elements l__60 m n part) s"
  unfolding execute_aarch64_instrs_vector_arithmetic_binary_disparate_mul_double_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sqdmull_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_double_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sqdmull_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_double_simd Rd Rn Rm b__0 Q) s"
  unfolding decode_sqdmull_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_double_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sqdmull_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_double_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sqdmull_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_double_sisd Rd Rn Rm b__0) s"
  unfolding decode_sqdmull_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_double_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sqneg_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_sat_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sqneg_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_sat_simd Rd Rn b__0 U b__1) s"
  unfolding decode_sqneg_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_sat_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sqneg_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_sat_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sqneg_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_sat_sisd Rd Rn b__0 U) s"
  unfolding decode_sqneg_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_sat_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_high_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "index__arg \<in> {0, 1, 2, 3, 4, 5, 6, 7}" and "int LENGTH('idxdsize) \<in> {64, 128}" and "int LENGTH('esize) \<in> {8, 16, 32, 64}" and "int LENGTH('datasize) \<in> {8, 16, 32, 64, 128}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_high_sisd d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) (idxdsize :: 'idxdsize::len itself) index__arg m n rounding sub_op) s"
  unfolding execute_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_high_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sqrdmlah_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_high_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sqrdmlah_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_high_simd Rd Rn b__0 S Rm M L b__1 b__2) s"
  unfolding decode_sqrdmlah_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_high_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sqrdmlah_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_high_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sqrdmlah_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_high_sisd Rd Rn b__0 S Rm M L b__1) s"
  unfolding decode_sqrdmlah_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_high_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_accum_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "int LENGTH('esize) \<in> {8, 16, 32, 64}" and "int LENGTH('datasize) \<in> {8, 16, 32, 64, 128}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_accum_sisd d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) m n rounding sub_op) s"
  unfolding execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_accum_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sqrdmlah_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_accum_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sqrdmlah_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_accum_simd Rd Rn S Rm b__0 b__1) s"
  unfolding decode_sqrdmlah_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_accum_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sqrdmlah_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_accum_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sqrdmlah_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_accum_sisd Rd Rn S Rm b__0) s"
  unfolding decode_sqrdmlah_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_accum_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sqrdmlsh_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_high_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sqrdmlsh_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_high_simd Rd Rn b__0 S Rm M L b__1 b__2) s"
  unfolding decode_sqrdmlsh_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_high_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sqrdmlsh_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_high_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sqrdmlsh_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_high_sisd Rd Rn b__0 S Rm M L b__1) s"
  unfolding decode_sqrdmlsh_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_high_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sqrdmlsh_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_accum_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sqrdmlsh_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_accum_simd Rd Rn S Rm b__0 b__1) s"
  unfolding decode_sqrdmlsh_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_accum_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sqrdmlsh_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_accum_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sqrdmlsh_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_accum_sisd Rd Rn S Rm b__0) s"
  unfolding decode_sqrdmlsh_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_accum_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sqrdmulh_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_high_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sqrdmulh_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_high_simd Rd Rn b__0 op Rm M L b__1 b__2) s"
  unfolding decode_sqrdmulh_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_high_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sqrdmulh_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_high_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sqrdmulh_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_high_sisd Rd Rn b__0 op Rm M L b__1) s"
  unfolding decode_sqrdmulh_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_high_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sqrdmulh_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sqrdmulh_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_simd Rd Rn Rm b__0 U b__1) s"
  unfolding decode_sqrdmulh_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sqrdmulh_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sqrdmulh_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_sisd Rd Rn Rm b__0 U) s"
  unfolding decode_sqrdmulh_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "int LENGTH('esize) \<in> {8, 16, 32, 64}" and "int LENGTH('datasize) \<in> {8, 16, 32, 64, 128}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) m n rounding saturating is_unsigned) s"
  unfolding execute_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sqrshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sqrshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd Rd Rn S R Rm b__0 U b__1) s"
  unfolding decode_sqrshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sqrshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sqrshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd Rd Rn S R Rm b__0 U) s"
  unfolding decode_sqrshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_shift_right_narrow_uniform_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "part \<in> {0, 1}" and "0 \<le> n" and "n \<le> 31" and "l__326 \<in> {4, 8, 16, 32, 64}" and "l__325 \<in> {4, 8, 16, 32, 64}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_shift_right_narrow_uniform_sisd d l__325 elements l__326 n part round__arg shift is_unsigned) s"
  unfolding execute_aarch64_instrs_vector_shift_right_narrow_uniform_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sqrshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sqrshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_simd Rd Rn op immb b__0 U Q) s"
  unfolding decode_sqrshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sqrshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sqrshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_sisd Rd Rn op immb b__0 U) s"
  unfolding decode_sqrshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_shift_right_narrow_nonuniform_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "part \<in> {0, 1}" and "0 \<le> n" and "n \<le> 31" and "l__483 \<in> {4, 8, 16, 32, 64}" and "l__482 \<in> {4, 8, 16, 32, 64}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_shift_right_narrow_nonuniform_sisd d l__482 elements l__483 n part round__arg shift) s"
  unfolding execute_aarch64_instrs_vector_shift_right_narrow_nonuniform_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sqrshrun_advsimd_aarch64_instrs_vector_shift_right_narrow_nonuniform_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sqrshrun_advsimd_aarch64_instrs_vector_shift_right_narrow_nonuniform_simd Rd Rn op immb b__0 Q) s"
  unfolding decode_sqrshrun_advsimd_aarch64_instrs_vector_shift_right_narrow_nonuniform_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sqrshrun_advsimd_aarch64_instrs_vector_shift_right_narrow_nonuniform_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sqrshrun_advsimd_aarch64_instrs_vector_shift_right_narrow_nonuniform_sisd Rd Rn op immb b__0) s"
  unfolding decode_sqrshrun_advsimd_aarch64_instrs_vector_shift_right_narrow_nonuniform_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_shift_left_sat_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "int LENGTH('esize) \<in> {4, 8, 16, 32, 64}" and "int LENGTH('datasize) \<in> {4, 8, 16, 32, 64, 128}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_shift_left_sat_sisd d (datasize :: 'datasize::len itself) dst_unsigned elements (esize :: 'esize::len itself) n shift src_unsigned) s"
  unfolding execute_aarch64_instrs_vector_shift_left_sat_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sqshl_advsimd_imm_aarch64_instrs_vector_shift_left_sat_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sqshl_advsimd_imm_aarch64_instrs_vector_shift_left_sat_simd Rd Rn op immb b__0 U b__1) s"
  unfolding decode_sqshl_advsimd_imm_aarch64_instrs_vector_shift_left_sat_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sqshl_advsimd_imm_aarch64_instrs_vector_shift_left_sat_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sqshl_advsimd_imm_aarch64_instrs_vector_shift_left_sat_sisd Rd Rn op immb b__0 U) s"
  unfolding decode_sqshl_advsimd_imm_aarch64_instrs_vector_shift_left_sat_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sqshl_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sqshl_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd Rd Rn S R Rm b__0 U b__1) s"
  unfolding decode_sqshl_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sqshl_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sqshl_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd Rd Rn S R Rm b__0 U) s"
  unfolding decode_sqshl_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sqshlu_advsimd_aarch64_instrs_vector_shift_left_sat_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sqshlu_advsimd_aarch64_instrs_vector_shift_left_sat_simd Rd Rn op immb b__0 U b__1) s"
  unfolding decode_sqshlu_advsimd_aarch64_instrs_vector_shift_left_sat_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sqshlu_advsimd_aarch64_instrs_vector_shift_left_sat_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sqshlu_advsimd_aarch64_instrs_vector_shift_left_sat_sisd Rd Rn op immb b__0 U) s"
  unfolding decode_sqshlu_advsimd_aarch64_instrs_vector_shift_left_sat_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sqshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sqshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_simd Rd Rn op immb b__0 U Q) s"
  unfolding decode_sqshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sqshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sqshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_sisd Rd Rn op immb b__0 U) s"
  unfolding decode_sqshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sqshrun_advsimd_aarch64_instrs_vector_shift_right_narrow_nonuniform_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sqshrun_advsimd_aarch64_instrs_vector_shift_right_narrow_nonuniform_simd Rd Rn op immb b__0 Q) s"
  unfolding decode_sqshrun_advsimd_aarch64_instrs_vector_shift_right_narrow_nonuniform_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sqshrun_advsimd_aarch64_instrs_vector_shift_right_narrow_nonuniform_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sqshrun_advsimd_aarch64_instrs_vector_shift_right_narrow_nonuniform_sisd Rd Rn op immb b__0) s"
  unfolding decode_sqshrun_advsimd_aarch64_instrs_vector_shift_right_narrow_nonuniform_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_arithmetic_binary_uniform_sub_saturating_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "int LENGTH('esize) \<in> {8, 16, 32, 64}" and "int LENGTH('datasize) \<in> {8, 16, 32, 64, 128}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_arithmetic_binary_uniform_sub_saturating_sisd d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) m n is_unsigned) s"
  unfolding execute_aarch64_instrs_vector_arithmetic_binary_uniform_sub_saturating_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sqsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_saturating_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sqsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_saturating_simd Rd Rn Rm b__0 U b__1) s"
  unfolding decode_sqsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_saturating_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sqsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_saturating_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sqsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_saturating_sisd Rd Rn Rm b__0 U) s"
  unfolding decode_sqsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_saturating_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_arithmetic_unary_extract_sat_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "part \<in> {0, 1}" and "0 \<le> n" and "n \<le> 31" and "l__92 \<in> {8, 16, 32, 64}" and "l__91 \<in> {8, 16, 32, 64}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_arithmetic_unary_extract_sat_sisd d l__91 elements l__92 n part is_unsigned) s"
  unfolding execute_aarch64_instrs_vector_arithmetic_unary_extract_sat_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sqxtn_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_sat_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sqxtn_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_sat_simd Rd Rn b__0 U Q) s"
  unfolding decode_sqxtn_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_sat_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sqxtn_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_sat_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sqxtn_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_sat_sisd Rd Rn b__0 U) s"
  unfolding decode_sqxtn_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_sat_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_arithmetic_unary_extract_sqxtun_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "part \<in> {0, 1}" and "0 \<le> n" and "n \<le> 31" and "l__5 \<in> {8, 16, 32, 64}" and "l__4 \<in> {8, 16, 32, 64}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_arithmetic_unary_extract_sqxtun_sisd d l__4 elements l__5 n part) s"
  unfolding execute_aarch64_instrs_vector_arithmetic_unary_extract_sqxtun_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sqxtun_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_sqxtun_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sqxtun_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_sqxtun_simd Rd Rn b__0 Q) s"
  unfolding decode_sqxtun_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_sqxtun_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sqxtun_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_sqxtun_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sqxtun_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_sqxtun_sisd Rd Rn b__0) s"
  unfolding decode_sqxtun_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_sqxtun_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_arithmetic_binary_uniform_add_halving_rounding[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "int LENGTH('esize) \<in> {8, 16, 32, 64}" and "int LENGTH('datasize) \<in> {64, 128}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_arithmetic_binary_uniform_add_halving_rounding d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) m n is_unsigned) s"
  unfolding execute_aarch64_instrs_vector_arithmetic_binary_uniform_add_halving_rounding_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_srhadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_halving_rounding[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_srhadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_halving_rounding Rd Rn Rm b__0 U b__1) s"
  unfolding decode_srhadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_halving_rounding_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_shift_right_insert_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_shift_right_insert_sisd d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) n shift) s"
  unfolding execute_aarch64_instrs_vector_shift_right_insert_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sri_advsimd_aarch64_instrs_vector_shift_right_insert_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sri_advsimd_aarch64_instrs_vector_shift_right_insert_simd Rd Rn immb b__0 b__1) s"
  unfolding decode_sri_advsimd_aarch64_instrs_vector_shift_right_insert_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sri_advsimd_aarch64_instrs_vector_shift_right_insert_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sri_advsimd_aarch64_instrs_vector_shift_right_insert_sisd Rd Rn immb immh) s"
  unfolding decode_sri_advsimd_aarch64_instrs_vector_shift_right_insert_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_srshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_srshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd Rd Rn S R Rm b__0 U b__1) s"
  unfolding decode_srshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_srshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_srshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd Rd Rn S R Rm b__0 U) s"
  unfolding decode_srshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_shift_right_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_shift_right_sisd accumulate d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) n round__arg shift is_unsigned) s"
  unfolding execute_aarch64_instrs_vector_shift_right_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_srshr_advsimd_aarch64_instrs_vector_shift_right_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_srshr_advsimd_aarch64_instrs_vector_shift_right_simd Rd Rn o0 o1 immb b__0 U b__1) s"
  unfolding decode_srshr_advsimd_aarch64_instrs_vector_shift_right_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_srshr_advsimd_aarch64_instrs_vector_shift_right_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_srshr_advsimd_aarch64_instrs_vector_shift_right_sisd Rd Rn o0 o1 immb immh U) s"
  unfolding decode_srshr_advsimd_aarch64_instrs_vector_shift_right_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_srsra_advsimd_aarch64_instrs_vector_shift_right_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_srsra_advsimd_aarch64_instrs_vector_shift_right_simd Rd Rn o0 o1 immb b__0 U b__1) s"
  unfolding decode_srsra_advsimd_aarch64_instrs_vector_shift_right_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_srsra_advsimd_aarch64_instrs_vector_shift_right_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_srsra_advsimd_aarch64_instrs_vector_shift_right_sisd Rd Rn o0 o1 immb immh U) s"
  unfolding decode_srsra_advsimd_aarch64_instrs_vector_shift_right_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd Rd Rn S R Rm b__0 U b__1) s"
  unfolding decode_sshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd Rd Rn S R Rm b__0 U) s"
  unfolding decode_sshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_shift_left_long[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "part \<in> {0, 1}" and "0 \<le> n" and "n \<le> 31" and "l__320 \<in> {4, 8, 16, 32, 64}" and "datasize = 64" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_shift_left_long d datasize elements l__320 n part shift is_unsigned) s"
  unfolding execute_aarch64_instrs_vector_shift_left_long_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sshll_advsimd_aarch64_instrs_vector_shift_left_long[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sshll_advsimd_aarch64_instrs_vector_shift_left_long Rd Rn immb b__0 U Q) s"
  unfolding decode_sshll_advsimd_aarch64_instrs_vector_shift_left_long_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sshr_advsimd_aarch64_instrs_vector_shift_right_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sshr_advsimd_aarch64_instrs_vector_shift_right_simd Rd Rn o0 o1 immb b__0 U b__1) s"
  unfolding decode_sshr_advsimd_aarch64_instrs_vector_shift_right_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sshr_advsimd_aarch64_instrs_vector_shift_right_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sshr_advsimd_aarch64_instrs_vector_shift_right_sisd Rd Rn o0 o1 immb immh U) s"
  unfolding decode_sshr_advsimd_aarch64_instrs_vector_shift_right_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ssra_advsimd_aarch64_instrs_vector_shift_right_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ssra_advsimd_aarch64_instrs_vector_shift_right_simd Rd Rn o0 o1 immb b__0 U b__1) s"
  unfolding decode_ssra_advsimd_aarch64_instrs_vector_shift_right_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ssra_advsimd_aarch64_instrs_vector_shift_right_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ssra_advsimd_aarch64_instrs_vector_shift_right_sisd Rd Rn o0 o1 immb immh U) s"
  unfolding decode_ssra_advsimd_aarch64_instrs_vector_shift_right_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ssubl_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_long[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ssubl_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_long Rd Rn o1 Rm b__0 U Q) s"
  unfolding decode_ssubl_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_long_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ssubw_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_wide[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ssubw_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_wide Rd Rn o1 Rm b__0 U Q) s"
  unfolding decode_ssubw_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_wide_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_st1_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_st1_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb Rt Rn b__0 opcode L b__1) s"
  unfolding decode_st1_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_st1_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_st1_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc Rt Rn b__0 opcode Rm L b__1) s"
  unfolding decode_st1_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_st1_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_st1_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb Rt Rn b__0 S b__1 R L b__2) s"
  unfolding decode_st1_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_st1_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_st1_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc Rt Rn b__0 S b__1 Rm R L b__2) s"
  unfolding decode_st1_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_st2_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_st2_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb Rt Rn b__0 opcode L b__1) s"
  unfolding decode_st2_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_st2_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_st2_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc Rt Rn b__0 opcode Rm L b__1) s"
  unfolding decode_st2_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_st2_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_st2_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb Rt Rn b__0 S b__1 R L b__2) s"
  unfolding decode_st2_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_st2_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_st2_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc Rt Rn b__0 S b__1 Rm R L b__2) s"
  unfolding decode_st2_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_st3_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_st3_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb Rt Rn b__0 opcode L b__1) s"
  unfolding decode_st3_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_st3_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_st3_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc Rt Rn b__0 opcode Rm L b__1) s"
  unfolding decode_st3_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_st3_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_st3_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb Rt Rn b__0 S b__1 R L b__2) s"
  unfolding decode_st3_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_st3_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_st3_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc Rt Rn b__0 S b__1 Rm R L b__2) s"
  unfolding decode_st3_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_st4_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_st4_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb Rt Rn b__0 opcode L b__1) s"
  unfolding decode_st4_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_st4_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_st4_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc Rt Rn b__0 opcode Rm L b__1) s"
  unfolding decode_st4_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_st4_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_st4_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb Rt Rn b__0 S b__1 R L b__2) s"
  unfolding decode_st4_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_st4_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_st4_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc Rt Rn b__0 S b__1 Rm R L b__2) s"
  unfolding decode_st4_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_memory_atomicops_st[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> s__arg" and "s__arg \<le> 31" and "0 \<le> n" and "n \<le> 31" and "int LENGTH('datasize) \<in> {8, 16, 32, 64}"
  shows "traces_enabled (execute_aarch64_instrs_memory_atomicops_st (datasize :: 'datasize::len itself) ldacctype n op s__arg stacctype) s"
  unfolding execute_aarch64_instrs_memory_atomicops_st_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_stadd_aarch64_instrs_memory_atomicops_st[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_stadd_aarch64_instrs_memory_atomicops_st Rn opc o3 Rs R A V b__0) s"
  unfolding decode_stadd_aarch64_instrs_memory_atomicops_st_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_staddb_aarch64_instrs_memory_atomicops_st[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_staddb_aarch64_instrs_memory_atomicops_st Rn opc o3 Rs R A V b__0) s"
  unfolding decode_staddb_aarch64_instrs_memory_atomicops_st_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_staddh_aarch64_instrs_memory_atomicops_st[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_staddh_aarch64_instrs_memory_atomicops_st Rn opc o3 Rs R A V b__0) s"
  unfolding decode_staddh_aarch64_instrs_memory_atomicops_st_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_stclr_aarch64_instrs_memory_atomicops_st[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_stclr_aarch64_instrs_memory_atomicops_st Rn opc o3 Rs R A V b__0) s"
  unfolding decode_stclr_aarch64_instrs_memory_atomicops_st_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_stclrb_aarch64_instrs_memory_atomicops_st[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_stclrb_aarch64_instrs_memory_atomicops_st Rn opc o3 Rs R A V b__0) s"
  unfolding decode_stclrb_aarch64_instrs_memory_atomicops_st_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_stclrh_aarch64_instrs_memory_atomicops_st[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_stclrh_aarch64_instrs_memory_atomicops_st Rn opc o3 Rs R A V b__0) s"
  unfolding decode_stclrh_aarch64_instrs_memory_atomicops_st_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_steor_aarch64_instrs_memory_atomicops_st[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_steor_aarch64_instrs_memory_atomicops_st Rn opc o3 Rs R A V b__0) s"
  unfolding decode_steor_aarch64_instrs_memory_atomicops_st_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_steorb_aarch64_instrs_memory_atomicops_st[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_steorb_aarch64_instrs_memory_atomicops_st Rn opc o3 Rs R A V b__0) s"
  unfolding decode_steorb_aarch64_instrs_memory_atomicops_st_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_steorh_aarch64_instrs_memory_atomicops_st[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_steorh_aarch64_instrs_memory_atomicops_st Rn opc o3 Rs R A V b__0) s"
  unfolding decode_steorh_aarch64_instrs_memory_atomicops_st_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_stllr_aarch64_instrs_memory_ordered[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_stllr_aarch64_instrs_memory_ordered Rt Rn Rt2 o0 Rs L b__0) s"
  unfolding decode_stllr_aarch64_instrs_memory_ordered_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_stllrb_aarch64_instrs_memory_ordered[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_stllrb_aarch64_instrs_memory_ordered Rt Rn Rt2 o0 Rs L b__0) s"
  unfolding decode_stllrb_aarch64_instrs_memory_ordered_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_stllrh_aarch64_instrs_memory_ordered[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_stllrh_aarch64_instrs_memory_ordered Rt Rn Rt2 o0 Rs L b__0) s"
  unfolding decode_stllrh_aarch64_instrs_memory_ordered_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_stlr_aarch64_instrs_memory_ordered[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_stlr_aarch64_instrs_memory_ordered Rt Rn Rt2 o0 Rs L b__0) s"
  unfolding decode_stlr_aarch64_instrs_memory_ordered_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_stlrb_aarch64_instrs_memory_ordered[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_stlrb_aarch64_instrs_memory_ordered Rt Rn Rt2 o0 Rs L b__0) s"
  unfolding decode_stlrb_aarch64_instrs_memory_ordered_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_stlrh_aarch64_instrs_memory_ordered[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_stlrh_aarch64_instrs_memory_ordered Rt Rn Rt2 o0 Rs L b__0) s"
  unfolding decode_stlrh_aarch64_instrs_memory_ordered_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_stlxp_aarch64_instrs_memory_exclusive_pair[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_stlxp_aarch64_instrs_memory_exclusive_pair Rt Rn Rt2 o0 Rs L b__0) s"
  unfolding decode_stlxp_aarch64_instrs_memory_exclusive_pair_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_stlxr_aarch64_instrs_memory_exclusive_single[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_stlxr_aarch64_instrs_memory_exclusive_single Rt Rn Rt2 o0 Rs L b__0) s"
  unfolding decode_stlxr_aarch64_instrs_memory_exclusive_single_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_stlxrb_aarch64_instrs_memory_exclusive_single[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_stlxrb_aarch64_instrs_memory_exclusive_single Rt Rn Rt2 o0 Rs L b__0) s"
  unfolding decode_stlxrb_aarch64_instrs_memory_exclusive_single_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_stlxrh_aarch64_instrs_memory_exclusive_single[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_stlxrh_aarch64_instrs_memory_exclusive_single Rt Rn Rt2 o0 Rs L b__0) s"
  unfolding decode_stlxrh_aarch64_instrs_memory_exclusive_single_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_stnp_fpsimd_aarch64_instrs_memory_pair_simdfp_no_alloc[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_stnp_fpsimd_aarch64_instrs_memory_pair_simdfp_no_alloc Rt Rn Rt2 imm7 L b__0) s"
  unfolding decode_stnp_fpsimd_aarch64_instrs_memory_pair_simdfp_no_alloc_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_stnp_gen_aarch64_instrs_memory_pair_general_no_alloc[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_stnp_gen_aarch64_instrs_memory_pair_general_no_alloc Rt Rn Rt2 imm7 L b__0) s"
  unfolding decode_stnp_gen_aarch64_instrs_memory_pair_general_no_alloc_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_stp_fpsimd_aarch64_instrs_memory_pair_simdfp_offset[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_stp_fpsimd_aarch64_instrs_memory_pair_simdfp_offset Rt Rn Rt2 imm7 L b__0) s"
  unfolding decode_stp_fpsimd_aarch64_instrs_memory_pair_simdfp_offset_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_stp_fpsimd_aarch64_instrs_memory_pair_simdfp_post_idx[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_stp_fpsimd_aarch64_instrs_memory_pair_simdfp_post_idx Rt Rn Rt2 imm7 L b__0) s"
  unfolding decode_stp_fpsimd_aarch64_instrs_memory_pair_simdfp_post_idx_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_stp_fpsimd_aarch64_instrs_memory_pair_simdfp_pre_idx[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_stp_fpsimd_aarch64_instrs_memory_pair_simdfp_pre_idx Rt Rn Rt2 imm7 L b__0) s"
  unfolding decode_stp_fpsimd_aarch64_instrs_memory_pair_simdfp_pre_idx_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_stp_gen_aarch64_instrs_memory_pair_general_offset[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_stp_gen_aarch64_instrs_memory_pair_general_offset Rt Rn Rt2 imm7 L b__0) s"
  unfolding decode_stp_gen_aarch64_instrs_memory_pair_general_offset_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_stp_gen_aarch64_instrs_memory_pair_general_post_idx[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_stp_gen_aarch64_instrs_memory_pair_general_post_idx Rt Rn Rt2 imm7 L b__0) s"
  unfolding decode_stp_gen_aarch64_instrs_memory_pair_general_post_idx_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_stp_gen_aarch64_instrs_memory_pair_general_pre_idx[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_stp_gen_aarch64_instrs_memory_pair_general_pre_idx Rt Rn Rt2 imm7 L b__0) s"
  unfolding decode_stp_gen_aarch64_instrs_memory_pair_general_pre_idx_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_str_imm_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_post_idx[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_str_imm_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_post_idx Rt Rn imm9 b__0 b__1) s"
  unfolding decode_str_imm_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_post_idx_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_str_imm_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_pre_idx[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_str_imm_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_pre_idx Rt Rn imm9 b__0 b__1) s"
  unfolding decode_str_imm_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_pre_idx_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_str_imm_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_unsigned[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_str_imm_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_unsigned Rt Rn imm12 b__0 b__1) s"
  unfolding decode_str_imm_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_unsigned_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_str_imm_gen_aarch64_instrs_memory_single_general_immediate_signed_post_idx[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_str_imm_gen_aarch64_instrs_memory_single_general_immediate_signed_post_idx Rt Rn imm9 b__0 b__1) s"
  unfolding decode_str_imm_gen_aarch64_instrs_memory_single_general_immediate_signed_post_idx_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_str_imm_gen_aarch64_instrs_memory_single_general_immediate_signed_pre_idx[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_str_imm_gen_aarch64_instrs_memory_single_general_immediate_signed_pre_idx Rt Rn imm9 b__0 b__1) s"
  unfolding decode_str_imm_gen_aarch64_instrs_memory_single_general_immediate_signed_pre_idx_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_str_imm_gen_aarch64_instrs_memory_single_general_immediate_unsigned[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_str_imm_gen_aarch64_instrs_memory_single_general_immediate_unsigned Rt Rn imm12 b__0 b__1) s"
  unfolding decode_str_imm_gen_aarch64_instrs_memory_single_general_immediate_unsigned_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_str_reg_fpsimd_aarch64_instrs_memory_single_simdfp_register[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_str_reg_fpsimd_aarch64_instrs_memory_single_simdfp_register Rt Rn S option_name Rm b__0 b__1) s"
  unfolding decode_str_reg_fpsimd_aarch64_instrs_memory_single_simdfp_register_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_str_reg_gen_aarch64_instrs_memory_single_general_register[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_str_reg_gen_aarch64_instrs_memory_single_general_register Rt Rn S option_name Rm b__0 b__1) s"
  unfolding decode_str_reg_gen_aarch64_instrs_memory_single_general_register_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_strb_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_strb_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx Rt Rn imm9 b__0 b__1) s"
  unfolding decode_strb_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_strb_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_strb_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx Rt Rn imm9 b__0 b__1) s"
  unfolding decode_strb_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_strb_imm_aarch64_instrs_memory_single_general_immediate_unsigned[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_strb_imm_aarch64_instrs_memory_single_general_immediate_unsigned Rt Rn imm12 b__0 b__1) s"
  unfolding decode_strb_imm_aarch64_instrs_memory_single_general_immediate_unsigned_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_strb_reg_aarch64_instrs_memory_single_general_register[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_strb_reg_aarch64_instrs_memory_single_general_register Rt Rn S option_name Rm b__0 b__1) s"
  unfolding decode_strb_reg_aarch64_instrs_memory_single_general_register_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_strh_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_strh_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx Rt Rn imm9 b__0 b__1) s"
  unfolding decode_strh_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_strh_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_strh_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx Rt Rn imm9 b__0 b__1) s"
  unfolding decode_strh_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_strh_imm_aarch64_instrs_memory_single_general_immediate_unsigned[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_strh_imm_aarch64_instrs_memory_single_general_immediate_unsigned Rt Rn imm12 b__0 b__1) s"
  unfolding decode_strh_imm_aarch64_instrs_memory_single_general_immediate_unsigned_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_strh_reg_aarch64_instrs_memory_single_general_register[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_strh_reg_aarch64_instrs_memory_single_general_register Rt Rn S option_name Rm b__0 b__1) s"
  unfolding decode_strh_reg_aarch64_instrs_memory_single_general_register_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_stset_aarch64_instrs_memory_atomicops_st[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_stset_aarch64_instrs_memory_atomicops_st Rn opc o3 Rs R A V b__0) s"
  unfolding decode_stset_aarch64_instrs_memory_atomicops_st_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_stsetb_aarch64_instrs_memory_atomicops_st[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_stsetb_aarch64_instrs_memory_atomicops_st Rn opc o3 Rs R A V b__0) s"
  unfolding decode_stsetb_aarch64_instrs_memory_atomicops_st_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_stseth_aarch64_instrs_memory_atomicops_st[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_stseth_aarch64_instrs_memory_atomicops_st Rn opc o3 Rs R A V b__0) s"
  unfolding decode_stseth_aarch64_instrs_memory_atomicops_st_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_stsmax_aarch64_instrs_memory_atomicops_st[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_stsmax_aarch64_instrs_memory_atomicops_st Rn opc o3 Rs R A V b__0) s"
  unfolding decode_stsmax_aarch64_instrs_memory_atomicops_st_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_stsmaxb_aarch64_instrs_memory_atomicops_st[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_stsmaxb_aarch64_instrs_memory_atomicops_st Rn opc o3 Rs R A V b__0) s"
  unfolding decode_stsmaxb_aarch64_instrs_memory_atomicops_st_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_stsmaxh_aarch64_instrs_memory_atomicops_st[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_stsmaxh_aarch64_instrs_memory_atomicops_st Rn opc o3 Rs R A V b__0) s"
  unfolding decode_stsmaxh_aarch64_instrs_memory_atomicops_st_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_stsmin_aarch64_instrs_memory_atomicops_st[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_stsmin_aarch64_instrs_memory_atomicops_st Rn opc o3 Rs R A V b__0) s"
  unfolding decode_stsmin_aarch64_instrs_memory_atomicops_st_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_stsminb_aarch64_instrs_memory_atomicops_st[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_stsminb_aarch64_instrs_memory_atomicops_st Rn opc o3 Rs R A V b__0) s"
  unfolding decode_stsminb_aarch64_instrs_memory_atomicops_st_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_stsminh_aarch64_instrs_memory_atomicops_st[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_stsminh_aarch64_instrs_memory_atomicops_st Rn opc o3 Rs R A V b__0) s"
  unfolding decode_stsminh_aarch64_instrs_memory_atomicops_st_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sttr_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sttr_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv Rt Rn imm9 b__0 b__1) s"
  unfolding decode_sttr_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sttrb_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sttrb_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv Rt Rn imm9 b__0 b__1) s"
  unfolding decode_sttrb_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sttrh_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sttrh_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv Rt Rn imm9 b__0 b__1) s"
  unfolding decode_sttrh_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_stumax_aarch64_instrs_memory_atomicops_st[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_stumax_aarch64_instrs_memory_atomicops_st Rn opc o3 Rs R A V b__0) s"
  unfolding decode_stumax_aarch64_instrs_memory_atomicops_st_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_stumaxb_aarch64_instrs_memory_atomicops_st[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_stumaxb_aarch64_instrs_memory_atomicops_st Rn opc o3 Rs R A V b__0) s"
  unfolding decode_stumaxb_aarch64_instrs_memory_atomicops_st_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_stumaxh_aarch64_instrs_memory_atomicops_st[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_stumaxh_aarch64_instrs_memory_atomicops_st Rn opc o3 Rs R A V b__0) s"
  unfolding decode_stumaxh_aarch64_instrs_memory_atomicops_st_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_stumin_aarch64_instrs_memory_atomicops_st[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_stumin_aarch64_instrs_memory_atomicops_st Rn opc o3 Rs R A V b__0) s"
  unfolding decode_stumin_aarch64_instrs_memory_atomicops_st_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_stuminb_aarch64_instrs_memory_atomicops_st[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_stuminb_aarch64_instrs_memory_atomicops_st Rn opc o3 Rs R A V b__0) s"
  unfolding decode_stuminb_aarch64_instrs_memory_atomicops_st_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_stuminh_aarch64_instrs_memory_atomicops_st[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_stuminh_aarch64_instrs_memory_atomicops_st Rn opc o3 Rs R A V b__0) s"
  unfolding decode_stuminh_aarch64_instrs_memory_atomicops_st_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_stur_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_offset_normal[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_stur_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_offset_normal Rt Rn imm9 b__0 b__1) s"
  unfolding decode_stur_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_offset_normal_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_stur_gen_aarch64_instrs_memory_single_general_immediate_signed_offset_normal[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_stur_gen_aarch64_instrs_memory_single_general_immediate_signed_offset_normal Rt Rn imm9 b__0 b__1) s"
  unfolding decode_stur_gen_aarch64_instrs_memory_single_general_immediate_signed_offset_normal_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sturb_aarch64_instrs_memory_single_general_immediate_signed_offset_normal[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sturb_aarch64_instrs_memory_single_general_immediate_signed_offset_normal Rt Rn imm9 b__0 b__1) s"
  unfolding decode_sturb_aarch64_instrs_memory_single_general_immediate_signed_offset_normal_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sturh_aarch64_instrs_memory_single_general_immediate_signed_offset_normal[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sturh_aarch64_instrs_memory_single_general_immediate_signed_offset_normal Rt Rn imm9 b__0 b__1) s"
  unfolding decode_sturh_aarch64_instrs_memory_single_general_immediate_signed_offset_normal_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_stxp_aarch64_instrs_memory_exclusive_pair[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_stxp_aarch64_instrs_memory_exclusive_pair Rt Rn Rt2 o0 Rs L b__0) s"
  unfolding decode_stxp_aarch64_instrs_memory_exclusive_pair_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_stxr_aarch64_instrs_memory_exclusive_single[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_stxr_aarch64_instrs_memory_exclusive_single Rt Rn Rt2 o0 Rs L b__0) s"
  unfolding decode_stxr_aarch64_instrs_memory_exclusive_single_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_stxrb_aarch64_instrs_memory_exclusive_single[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_stxrb_aarch64_instrs_memory_exclusive_single Rt Rn Rt2 o0 Rs L b__0) s"
  unfolding decode_stxrb_aarch64_instrs_memory_exclusive_single_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_stxrh_aarch64_instrs_memory_exclusive_single[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_stxrh_aarch64_instrs_memory_exclusive_single Rt Rn Rt2 o0 Rs L b__0) s"
  unfolding decode_stxrh_aarch64_instrs_memory_exclusive_single_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sub_addsub_ext_aarch64_instrs_integer_arithmetic_add_sub_extendedreg[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sub_addsub_ext_aarch64_instrs_integer_arithmetic_add_sub_extendedreg Rd Rn imm3 option_name Rm S op b__0) s"
  unfolding decode_sub_addsub_ext_aarch64_instrs_integer_arithmetic_add_sub_extendedreg_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sub_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sub_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate Rd Rn imm12 sh S op b__0) s"
  unfolding decode_sub_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sub_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg[traces_enabledI]:
  assumes "{''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sub_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg Rd Rn imm6 Rm shift S op b__0) s"
  unfolding decode_sub_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_wrapping_single_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_wrapping_single_simd Rd Rn Rm b__0 U b__1) s"
  unfolding decode_sub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_wrapping_single_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_wrapping_single_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_wrapping_single_sisd Rd Rn Rm b__0 U) s"
  unfolding decode_sub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_wrapping_single_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_subhn_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_narrow[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_subhn_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_narrow Rd Rn o1 Rm b__0 U Q) s"
  unfolding decode_subhn_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_narrow_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_subs_addsub_ext_aarch64_instrs_integer_arithmetic_add_sub_extendedreg[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_subs_addsub_ext_aarch64_instrs_integer_arithmetic_add_sub_extendedreg Rd Rn imm3 option_name Rm S op b__0) s"
  unfolding decode_subs_addsub_ext_aarch64_instrs_integer_arithmetic_add_sub_extendedreg_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_subs_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_subs_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate Rd Rn imm12 sh S op b__0) s"
  unfolding decode_subs_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_subs_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg[traces_enabledI]:
  assumes "{''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_subs_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg Rd Rn imm6 Rm shift S op b__0) s"
  unfolding decode_subs_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_arithmetic_unary_add_saturating_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "int LENGTH('esize) \<in> {8, 16, 32, 64}" and "int LENGTH('datasize) \<in> {8, 16, 32, 64, 128}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_arithmetic_unary_add_saturating_sisd d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) n is_unsigned) s"
  unfolding execute_aarch64_instrs_vector_arithmetic_unary_add_saturating_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_suqadd_advsimd_aarch64_instrs_vector_arithmetic_unary_add_saturating_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_suqadd_advsimd_aarch64_instrs_vector_arithmetic_unary_add_saturating_simd Rd Rn b__0 U b__1) s"
  unfolding decode_suqadd_advsimd_aarch64_instrs_vector_arithmetic_unary_add_saturating_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_suqadd_advsimd_aarch64_instrs_vector_arithmetic_unary_add_saturating_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_suqadd_advsimd_aarch64_instrs_vector_arithmetic_unary_add_saturating_sisd Rd Rn b__0 U) s"
  unfolding decode_suqadd_advsimd_aarch64_instrs_vector_arithmetic_unary_add_saturating_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_system_exceptions_runtime_svc[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_aarch64_instrs_system_exceptions_runtime_svc imm) s"
  unfolding execute_aarch64_instrs_system_exceptions_runtime_svc_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_svc_aarch64_instrs_system_exceptions_runtime_svc[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_svc_aarch64_instrs_system_exceptions_runtime_svc imm16) s"
  unfolding decode_svc_aarch64_instrs_system_exceptions_runtime_svc_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_memory_atomicops_swp[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "0 \<le> s__arg" and "s__arg \<le> 31" and "int LENGTH('regsize) \<in> {32, 64}" and "0 \<le> n" and "n \<le> 31" and "int LENGTH('datasize) \<in> {8, 16, 32, 64}"
  shows "traces_enabled (execute_aarch64_instrs_memory_atomicops_swp (datasize :: 'datasize::len itself) ldacctype n (regsize :: 'regsize::len itself) s__arg stacctype t__arg) s"
  unfolding execute_aarch64_instrs_memory_atomicops_swp_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_swp_aarch64_instrs_memory_atomicops_swp[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_swp_aarch64_instrs_memory_atomicops_swp Rt Rn Rs R A b__0) s"
  unfolding decode_swp_aarch64_instrs_memory_atomicops_swp_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_swpb_aarch64_instrs_memory_atomicops_swp[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_swpb_aarch64_instrs_memory_atomicops_swp Rt Rn Rs R A b__0) s"
  unfolding decode_swpb_aarch64_instrs_memory_atomicops_swp_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_swph_aarch64_instrs_memory_atomicops_swp[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_swph_aarch64_instrs_memory_atomicops_swp Rt Rn Rs R A b__0) s"
  unfolding decode_swph_aarch64_instrs_memory_atomicops_swp_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_system_sysops[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "sys_op2 \<in> {0, 1, 2, 3, 4, 5, 6, 7}" and "sys_op1 \<in> {0, 1, 2, 3, 4, 5, 6, 7}" and "sys_op0 = 1" and "0 \<le> sys_crn" and "sys_crn \<le> 15" and "0 \<le> sys_crm" and "sys_crm \<le> 15"
  shows "traces_enabled (execute_aarch64_instrs_system_sysops has_result sys_crm sys_crn sys_op0 sys_op1 sys_op2 t__arg) s"
  unfolding execute_aarch64_instrs_system_sysops_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sys_aarch64_instrs_system_sysops[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sys_aarch64_instrs_system_sysops Rt op2 CRm CRn op1 L) s"
  unfolding decode_sys_aarch64_instrs_system_sysops_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_sysl_aarch64_instrs_system_sysops[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_sysl_aarch64_instrs_system_sysops Rt op2 CRm CRn op1 L) s"
  unfolding decode_sysl_aarch64_instrs_system_sysops_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_transfer_vector_table[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "l__181 \<in> {1, 2, 3, 4}" and "0 \<le> n__arg" and "n__arg \<le> 31" and "0 \<le> m" and "m \<le> 31" and "elements \<in> {8, 16}" and "int LENGTH('datasize) \<in> {64, 128}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_transfer_vector_table d (datasize :: 'datasize::len itself) elements is_tbl m n__arg l__181) s"
  unfolding execute_aarch64_instrs_vector_transfer_vector_table_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_tbl_advsimd_aarch64_instrs_vector_transfer_vector_table[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_tbl_advsimd_aarch64_instrs_vector_transfer_vector_table Rd Rn op len Rm b__0) s"
  unfolding decode_tbl_advsimd_aarch64_instrs_vector_transfer_vector_table_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_branch_conditional_test[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "int LENGTH('datasize) \<in> {32, 64}" and "0 \<le> bit_pos" and "bit_pos \<le> 63"
  shows "traces_enabled (execute_aarch64_instrs_branch_conditional_test bit_pos bit_val (datasize :: 'datasize::len itself) offset t__arg) s"
  unfolding execute_aarch64_instrs_branch_conditional_test_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_tbnz_aarch64_instrs_branch_conditional_test[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_tbnz_aarch64_instrs_branch_conditional_test Rt imm14 b40 op b__0) s"
  unfolding decode_tbnz_aarch64_instrs_branch_conditional_test_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_tbx_advsimd_aarch64_instrs_vector_transfer_vector_table[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_tbx_advsimd_aarch64_instrs_vector_transfer_vector_table Rd Rn op len Rm b__0) s"
  unfolding decode_tbx_advsimd_aarch64_instrs_vector_transfer_vector_table_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_tbz_aarch64_instrs_branch_conditional_test[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_tbz_aarch64_instrs_branch_conditional_test Rt imm14 b40 op b__0) s"
  unfolding decode_tbz_aarch64_instrs_branch_conditional_test_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_transfer_vector_permute_transpose[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "part \<in> {0, 1}" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "int LENGTH('esize) \<in> {8, 16, 32, 64}" and "int LENGTH('datasize) \<in> {64, 128}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_transfer_vector_permute_transpose d (datasize :: 'datasize::len itself) (esize :: 'esize::len itself) m n pairs part) s"
  unfolding execute_aarch64_instrs_vector_transfer_vector_permute_transpose_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_trn1_advsimd_aarch64_instrs_vector_transfer_vector_permute_transpose[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_trn1_advsimd_aarch64_instrs_vector_transfer_vector_permute_transpose Rd Rn op Rm b__0 b__1) s"
  unfolding decode_trn1_advsimd_aarch64_instrs_vector_transfer_vector_permute_transpose_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_trn2_advsimd_aarch64_instrs_vector_transfer_vector_permute_transpose[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_trn2_advsimd_aarch64_instrs_vector_transfer_vector_permute_transpose Rd Rn op Rm b__0 b__1) s"
  unfolding decode_trn2_advsimd_aarch64_instrs_vector_transfer_vector_permute_transpose_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_uaba_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_diff[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_uaba_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_diff Rd Rn ac Rm b__0 U b__1) s"
  unfolding decode_uaba_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_diff_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_uabal_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_diff[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_uabal_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_diff Rd Rn op Rm b__0 U Q) s"
  unfolding decode_uabal_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_diff_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_uabd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_diff[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_uabd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_diff Rd Rn ac Rm b__0 U b__1) s"
  unfolding decode_uabd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_diff_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_uabdl_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_diff[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_uabdl_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_diff Rd Rn op Rm b__0 U Q) s"
  unfolding decode_uabdl_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_diff_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_uadalp_advsimd_aarch64_instrs_vector_arithmetic_unary_add_pairwise[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_uadalp_advsimd_aarch64_instrs_vector_arithmetic_unary_add_pairwise Rd Rn op b__0 U b__1) s"
  unfolding decode_uadalp_advsimd_aarch64_instrs_vector_arithmetic_unary_add_pairwise_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_uaddl_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_long[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_uaddl_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_long Rd Rn o1 Rm b__0 U Q) s"
  unfolding decode_uaddl_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_long_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_uaddlp_advsimd_aarch64_instrs_vector_arithmetic_unary_add_pairwise[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_uaddlp_advsimd_aarch64_instrs_vector_arithmetic_unary_add_pairwise Rd Rn op b__0 U b__1) s"
  unfolding decode_uaddlp_advsimd_aarch64_instrs_vector_arithmetic_unary_add_pairwise_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_uaddlv_advsimd_aarch64_instrs_vector_reduce_add_long[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_uaddlv_advsimd_aarch64_instrs_vector_reduce_add_long Rd Rn b__0 U b__1) s"
  unfolding decode_uaddlv_advsimd_aarch64_instrs_vector_reduce_add_long_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_uaddw_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_wide[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_uaddw_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_wide Rd Rn o1 Rm b__0 U Q) s"
  unfolding decode_uaddw_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_wide_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ubfm_aarch64_instrs_integer_bitfield[traces_enabledI]:
  assumes "{''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ubfm_aarch64_instrs_integer_bitfield Rd Rn imms immr N opc b__0) s"
  unfolding decode_ubfm_aarch64_instrs_integer_bitfield_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ucvtf_advsimd_fix_aarch64_instrs_vector_shift_conv_int_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ucvtf_advsimd_fix_aarch64_instrs_vector_shift_conv_int_simd Rd Rn immb b__0 U b__1) s"
  unfolding decode_ucvtf_advsimd_fix_aarch64_instrs_vector_shift_conv_int_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ucvtf_advsimd_fix_aarch64_instrs_vector_shift_conv_int_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ucvtf_advsimd_fix_aarch64_instrs_vector_shift_conv_int_sisd Rd Rn immb b__0 U) s"
  unfolding decode_ucvtf_advsimd_fix_aarch64_instrs_vector_shift_conv_int_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ucvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_int_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ucvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_int_simd Rd Rn b__0 U b__1) s"
  unfolding decode_ucvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_int_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ucvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_int_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ucvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_int_sisd Rd Rn b__0 U) s"
  unfolding decode_ucvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_int_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ucvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_int_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ucvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_int_simd Rd Rn U b__0) s"
  unfolding decode_ucvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_int_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ucvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_int_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ucvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_int_sisd Rd Rn U) s"
  unfolding decode_ucvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_int_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ucvtf_float_fix_aarch64_instrs_float_convert_fix[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ucvtf_float_fix_aarch64_instrs_float_convert_fix Rd Rn scale opcode rmode b__0 b__1) s"
  unfolding decode_ucvtf_float_fix_aarch64_instrs_float_convert_fix_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ucvtf_float_int_aarch64_instrs_float_convert_int[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ucvtf_float_int_aarch64_instrs_float_convert_int Rd Rn opcode rmode ftype b__0) s"
  unfolding decode_ucvtf_float_int_aarch64_instrs_float_convert_int_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_udiv_aarch64_instrs_integer_arithmetic_div[traces_enabledI]:
  assumes "{''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_udiv_aarch64_instrs_integer_arithmetic_div Rd Rn o1 Rm b__0) s"
  unfolding decode_udiv_aarch64_instrs_integer_arithmetic_div_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_udot_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_dotp[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_udot_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_dotp Rd Rn H Rm M L b__0 U b__1) s"
  unfolding decode_udot_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_dotp_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_udot_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_dotp[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_udot_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_dotp Rd Rn Rm b__0 U b__1) s"
  unfolding decode_udot_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_dotp_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_uhadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_halving_truncating[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_uhadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_halving_truncating Rd Rn Rm b__0 U b__1) s"
  unfolding decode_uhadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_halving_truncating_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_uhsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_int[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_uhsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_int Rd Rn Rm b__0 U b__1) s"
  unfolding decode_uhsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_int_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_umaddl_aarch64_instrs_integer_arithmetic_mul_widening_32_64[traces_enabledI]:
  assumes "{''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_umaddl_aarch64_instrs_integer_arithmetic_mul_widening_32_64 Rd Rn Ra o0 Rm U) s"
  unfolding decode_umaddl_aarch64_instrs_integer_arithmetic_mul_widening_32_64_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_umax_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_single[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_umax_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_single Rd Rn o1 Rm b__0 U b__1) s"
  unfolding decode_umax_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_single_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_umaxp_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_pair[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_umaxp_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_pair Rd Rn o1 Rm b__0 U b__1) s"
  unfolding decode_umaxp_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_pair_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_umaxv_advsimd_aarch64_instrs_vector_reduce_int_max[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_umaxv_advsimd_aarch64_instrs_vector_reduce_int_max Rd Rn op b__0 U b__1) s"
  unfolding decode_umaxv_advsimd_aarch64_instrs_vector_reduce_int_max_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_umin_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_single[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_umin_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_single Rd Rn o1 Rm b__0 U b__1) s"
  unfolding decode_umin_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_single_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_uminp_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_pair[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_uminp_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_pair Rd Rn o1 Rm b__0 U b__1) s"
  unfolding decode_uminp_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_pair_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_uminv_advsimd_aarch64_instrs_vector_reduce_int_max[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_uminv_advsimd_aarch64_instrs_vector_reduce_int_max Rd Rn op b__0 U b__1) s"
  unfolding decode_uminv_advsimd_aarch64_instrs_vector_reduce_int_max_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_umlal_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_long[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_umlal_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_long Rd Rn b__0 o2 Rm M L b__1 U Q) s"
  unfolding decode_umlal_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_long_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_umlal_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_accum[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_umlal_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_accum Rd Rn o1 Rm b__0 U Q) s"
  unfolding decode_umlal_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_accum_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_umlsl_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_long[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_umlsl_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_long Rd Rn b__0 o2 Rm M L b__1 U Q) s"
  unfolding decode_umlsl_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_long_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_umlsl_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_accum[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_umlsl_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_accum Rd Rn o1 Rm b__0 U Q) s"
  unfolding decode_umlsl_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_accum_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_transfer_integer_move_unsigned[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "int LENGTH('idxdsize) \<in> {64, 128}" and "int LENGTH('esize) \<in> {8, 16, 32, 64}" and "int LENGTH('datasize) \<in> {32, 64}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_transfer_integer_move_unsigned d (datasize :: 'datasize::len itself) (esize :: 'esize::len itself) (idxdsize :: 'idxdsize::len itself) index__arg n) s"
  unfolding execute_aarch64_instrs_vector_transfer_integer_move_unsigned_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_umov_advsimd_aarch64_instrs_vector_transfer_integer_move_unsigned[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_umov_advsimd_aarch64_instrs_vector_transfer_integer_move_unsigned Rd Rn b__0 b__1) s"
  unfolding decode_umov_advsimd_aarch64_instrs_vector_transfer_integer_move_unsigned_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_umsubl_aarch64_instrs_integer_arithmetic_mul_widening_32_64[traces_enabledI]:
  assumes "{''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_umsubl_aarch64_instrs_integer_arithmetic_mul_widening_32_64 Rd Rn Ra o0 Rm U) s"
  unfolding decode_umsubl_aarch64_instrs_integer_arithmetic_mul_widening_32_64_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_umulh_aarch64_instrs_integer_arithmetic_mul_widening_64_128hi[traces_enabledI]:
  assumes "{''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_umulh_aarch64_instrs_integer_arithmetic_mul_widening_64_128hi Rd Rn Ra Rm U) s"
  unfolding decode_umulh_aarch64_instrs_integer_arithmetic_mul_widening_64_128hi_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_umull_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_long[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_umull_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_long Rd Rn b__0 Rm M L b__1 U Q) s"
  unfolding decode_umull_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_long_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_umull_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_product[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_umull_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_product Rd Rn Rm b__0 U Q) s"
  unfolding decode_umull_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_product_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_uqadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_saturating_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_uqadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_saturating_simd Rd Rn Rm b__0 U b__1) s"
  unfolding decode_uqadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_saturating_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_uqadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_saturating_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_uqadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_saturating_sisd Rd Rn Rm b__0 U) s"
  unfolding decode_uqadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_saturating_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_uqrshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_uqrshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd Rd Rn S R Rm b__0 U b__1) s"
  unfolding decode_uqrshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_uqrshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_uqrshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd Rd Rn S R Rm b__0 U) s"
  unfolding decode_uqrshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_uqrshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_uqrshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_simd Rd Rn op immb b__0 U Q) s"
  unfolding decode_uqrshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_uqrshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_uqrshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_sisd Rd Rn op immb b__0 U) s"
  unfolding decode_uqrshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_uqshl_advsimd_imm_aarch64_instrs_vector_shift_left_sat_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_uqshl_advsimd_imm_aarch64_instrs_vector_shift_left_sat_simd Rd Rn op immb b__0 U b__1) s"
  unfolding decode_uqshl_advsimd_imm_aarch64_instrs_vector_shift_left_sat_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_uqshl_advsimd_imm_aarch64_instrs_vector_shift_left_sat_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_uqshl_advsimd_imm_aarch64_instrs_vector_shift_left_sat_sisd Rd Rn op immb b__0 U) s"
  unfolding decode_uqshl_advsimd_imm_aarch64_instrs_vector_shift_left_sat_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_uqshl_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_uqshl_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd Rd Rn S R Rm b__0 U b__1) s"
  unfolding decode_uqshl_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_uqshl_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_uqshl_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd Rd Rn S R Rm b__0 U) s"
  unfolding decode_uqshl_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_uqshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_uqshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_simd Rd Rn op immb b__0 U Q) s"
  unfolding decode_uqshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_uqshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_uqshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_sisd Rd Rn op immb b__0 U) s"
  unfolding decode_uqshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_uqsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_saturating_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_uqsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_saturating_simd Rd Rn Rm b__0 U b__1) s"
  unfolding decode_uqsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_saturating_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_uqsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_saturating_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_uqsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_saturating_sisd Rd Rn Rm b__0 U) s"
  unfolding decode_uqsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_saturating_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_uqxtn_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_sat_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_uqxtn_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_sat_simd Rd Rn b__0 U Q) s"
  unfolding decode_uqxtn_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_sat_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_uqxtn_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_sat_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_uqxtn_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_sat_sisd Rd Rn b__0 U) s"
  unfolding decode_uqxtn_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_sat_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_arithmetic_unary_special_recip_int[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "int LENGTH('datasize) \<in> {64, 128}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_arithmetic_unary_special_recip_int d (datasize :: 'datasize::len itself) elements n) s"
  unfolding execute_aarch64_instrs_vector_arithmetic_unary_special_recip_int_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_urecpe_advsimd_aarch64_instrs_vector_arithmetic_unary_special_recip_int[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_urecpe_advsimd_aarch64_instrs_vector_arithmetic_unary_special_recip_int Rd Rn sz b__0) s"
  unfolding decode_urecpe_advsimd_aarch64_instrs_vector_arithmetic_unary_special_recip_int_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_urhadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_halving_rounding[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_urhadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_halving_rounding Rd Rn Rm b__0 U b__1) s"
  unfolding decode_urhadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_halving_rounding_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_urshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_urshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd Rd Rn S R Rm b__0 U b__1) s"
  unfolding decode_urshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_urshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_urshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd Rd Rn S R Rm b__0 U) s"
  unfolding decode_urshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_urshr_advsimd_aarch64_instrs_vector_shift_right_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_urshr_advsimd_aarch64_instrs_vector_shift_right_simd Rd Rn o0 o1 immb b__0 U b__1) s"
  unfolding decode_urshr_advsimd_aarch64_instrs_vector_shift_right_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_urshr_advsimd_aarch64_instrs_vector_shift_right_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_urshr_advsimd_aarch64_instrs_vector_shift_right_sisd Rd Rn o0 o1 immb immh U) s"
  unfolding decode_urshr_advsimd_aarch64_instrs_vector_shift_right_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_arithmetic_unary_special_sqrt_est_int[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "int LENGTH('datasize) \<in> {64, 128}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_arithmetic_unary_special_sqrt_est_int d (datasize :: 'datasize::len itself) elements n) s"
  unfolding execute_aarch64_instrs_vector_arithmetic_unary_special_sqrt_est_int_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ursqrte_advsimd_aarch64_instrs_vector_arithmetic_unary_special_sqrt_est_int[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ursqrte_advsimd_aarch64_instrs_vector_arithmetic_unary_special_sqrt_est_int Rd Rn sz b__0) s"
  unfolding decode_ursqrte_advsimd_aarch64_instrs_vector_arithmetic_unary_special_sqrt_est_int_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ursra_advsimd_aarch64_instrs_vector_shift_right_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ursra_advsimd_aarch64_instrs_vector_shift_right_simd Rd Rn o0 o1 immb b__0 U b__1) s"
  unfolding decode_ursra_advsimd_aarch64_instrs_vector_shift_right_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ursra_advsimd_aarch64_instrs_vector_shift_right_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ursra_advsimd_aarch64_instrs_vector_shift_right_sisd Rd Rn o0 o1 immb immh U) s"
  unfolding decode_ursra_advsimd_aarch64_instrs_vector_shift_right_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ushl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ushl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd Rd Rn S R Rm b__0 U b__1) s"
  unfolding decode_ushl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ushl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ushl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd Rd Rn S R Rm b__0 U) s"
  unfolding decode_ushl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ushll_advsimd_aarch64_instrs_vector_shift_left_long[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ushll_advsimd_aarch64_instrs_vector_shift_left_long Rd Rn immb b__0 U Q) s"
  unfolding decode_ushll_advsimd_aarch64_instrs_vector_shift_left_long_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ushr_advsimd_aarch64_instrs_vector_shift_right_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ushr_advsimd_aarch64_instrs_vector_shift_right_simd Rd Rn o0 o1 immb b__0 U b__1) s"
  unfolding decode_ushr_advsimd_aarch64_instrs_vector_shift_right_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ushr_advsimd_aarch64_instrs_vector_shift_right_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ushr_advsimd_aarch64_instrs_vector_shift_right_sisd Rd Rn o0 o1 immb immh U) s"
  unfolding decode_ushr_advsimd_aarch64_instrs_vector_shift_right_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_usqadd_advsimd_aarch64_instrs_vector_arithmetic_unary_add_saturating_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_usqadd_advsimd_aarch64_instrs_vector_arithmetic_unary_add_saturating_simd Rd Rn b__0 U b__1) s"
  unfolding decode_usqadd_advsimd_aarch64_instrs_vector_arithmetic_unary_add_saturating_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_usqadd_advsimd_aarch64_instrs_vector_arithmetic_unary_add_saturating_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_usqadd_advsimd_aarch64_instrs_vector_arithmetic_unary_add_saturating_sisd Rd Rn b__0 U) s"
  unfolding decode_usqadd_advsimd_aarch64_instrs_vector_arithmetic_unary_add_saturating_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_usra_advsimd_aarch64_instrs_vector_shift_right_simd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_usra_advsimd_aarch64_instrs_vector_shift_right_simd Rd Rn o0 o1 immb b__0 U b__1) s"
  unfolding decode_usra_advsimd_aarch64_instrs_vector_shift_right_simd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_usra_advsimd_aarch64_instrs_vector_shift_right_sisd[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_usra_advsimd_aarch64_instrs_vector_shift_right_sisd Rd Rn o0 o1 immb immh U) s"
  unfolding decode_usra_advsimd_aarch64_instrs_vector_shift_right_sisd_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_usubl_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_long[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_usubl_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_long Rd Rn o1 Rm b__0 U Q) s"
  unfolding decode_usubl_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_long_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_usubw_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_wide[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_usubw_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_wide Rd Rn o1 Rm b__0 U Q) s"
  unfolding decode_usubw_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_wide_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_transfer_vector_permute_unzip[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "part \<in> {0, 1}" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "int LENGTH('esize) \<in> {8, 16, 32, 64}" and "l__195 \<in> {64, 128}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_transfer_vector_permute_unzip d l__195 elements (esize :: 'esize::len itself) m n part) s"
  unfolding execute_aarch64_instrs_vector_transfer_vector_permute_unzip_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_uzp1_advsimd_aarch64_instrs_vector_transfer_vector_permute_unzip[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_uzp1_advsimd_aarch64_instrs_vector_transfer_vector_permute_unzip Rd Rn op Rm b__0 b__1) s"
  unfolding decode_uzp1_advsimd_aarch64_instrs_vector_transfer_vector_permute_unzip_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_uzp2_advsimd_aarch64_instrs_vector_transfer_vector_permute_unzip[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_uzp2_advsimd_aarch64_instrs_vector_transfer_vector_permute_unzip Rd Rn op Rm b__0 b__1) s"
  unfolding decode_uzp2_advsimd_aarch64_instrs_vector_transfer_vector_permute_unzip_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_wfe_aarch64_instrs_system_hints[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_wfe_aarch64_instrs_system_hints op2 CRm) s"
  unfolding decode_wfe_aarch64_instrs_system_hints_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_wfi_aarch64_instrs_system_hints[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_wfi_aarch64_instrs_system_hints op2 CRm) s"
  unfolding decode_wfi_aarch64_instrs_system_hints_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_crypto_sha3_xar[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_crypto_sha3_xar d imm6 m n) s"
  unfolding execute_aarch64_instrs_vector_crypto_sha3_xar_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_xar_advsimd_aarch64_instrs_vector_crypto_sha3_xar[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_xar_advsimd_aarch64_instrs_vector_crypto_sha3_xar Rd Rn imm6 Rm) s"
  unfolding decode_xar_advsimd_aarch64_instrs_vector_crypto_sha3_xar_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_arithmetic_unary_extract_nosat[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "part \<in> {0, 1}" and "0 \<le> n" and "n \<le> 31" and "l__0 \<in> {8, 16, 32, 64}" and "datasize = 64" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_arithmetic_unary_extract_nosat d datasize elements l__0 n part) s"
  unfolding execute_aarch64_instrs_vector_arithmetic_unary_extract_nosat_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_xtn_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_nosat[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_xtn_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_nosat Rd Rn b__0 Q) s"
  unfolding decode_xtn_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_nosat_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_yield_aarch64_instrs_system_hints[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_yield_aarch64_instrs_system_hints op2 CRm) s"
  unfolding decode_yield_aarch64_instrs_system_hints_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_vector_transfer_vector_permute_zip[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "part \<in> {0, 1}" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "int LENGTH('esize) \<in> {8, 16, 32, 64}" and "int LENGTH('datasize) \<in> {64, 128}" and "0 \<le> d" and "d \<le> 31"
  shows "traces_enabled (execute_aarch64_instrs_vector_transfer_vector_permute_zip d (datasize :: 'datasize::len itself) (esize :: 'esize::len itself) m n pairs part) s"
  unfolding execute_aarch64_instrs_vector_transfer_vector_permute_zip_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_zip1_advsimd_aarch64_instrs_vector_transfer_vector_permute_zip[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_zip1_advsimd_aarch64_instrs_vector_transfer_vector_permute_zip Rd Rn op Rm b__0 b__1) s"
  unfolding decode_zip1_advsimd_aarch64_instrs_vector_transfer_vector_permute_zip_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_zip2_advsimd_aarch64_instrs_vector_transfer_vector_permute_zip[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_zip2_advsimd_aarch64_instrs_vector_transfer_vector_permute_zip Rd Rn op Rm b__0 b__1) s"
  unfolding decode_zip2_advsimd_aarch64_instrs_vector_transfer_vector_permute_zip_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_DecodeA64[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "instr_exp_assms (DecodeA64 pc opcode)" and "no_system_reg_access"
  shows "traces_enabled (DecodeA64 pc opcode) s"
  using assms(2)
  by (unfold DecodeA64_def, elim instr_exp_assms_traces_enabled_ifE instr_exp_assms_traces_enabled_letE) (solves \<open>traces_enabledI assms: assms(1) intro: assms(3) simp: instr_exp_assms_def invocation_instr_exp_assms_write_ThisInstrAbstract_iff load_instr_exp_assms_write_ThisInstrAbstract_iff\<close>)+

end

end
