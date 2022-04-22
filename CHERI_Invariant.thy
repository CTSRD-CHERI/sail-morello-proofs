section \<open>Invariant preservation\<close>

theory CHERI_Invariant
imports CHERI_Lemmas
begin

lemma non_inv_reg_writes_preserve_invariant:
  "\<And>v. runs_preserve_invariant (liftS (write_reg ThisInstrAbstract_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg EventRegister_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg saved_exception_level_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg SP_EL3_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg V_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg PMSWINC_EL0_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg OSLAR_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ICC_SGI1R_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ICC_SGI0R_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ICV_EOIR1_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ICC_EOIR1_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ICV_EOIR0_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ICC_EOIR0_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ICV_DIR_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ICC_DIR_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ICC_ASGI1R_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg DBGDTRTX_EL0_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg RDDC_EL0_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg DDC_EL3_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg DDC_EL2_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg DDC_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg DDC_EL0_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg VTTBR_EL2_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg VTCR_EL2_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg VSESR_EL2_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg TTBR1_EL2_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg TTBR1_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg TTBR0_EL3_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg TTBR0_EL2_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg TTBR0_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg TPIDR_EL3_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg TPIDR_EL2_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg TPIDR_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg TPIDR_EL0_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg TPIDRRO_EL0_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg SP_EL2_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg SP_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg SP_EL0_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg SPSR_und_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg SPSR_irq_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg SPSR_fiq_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg SPSR_abt_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg SDER32_EL3_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg SCXTNUM_EL3_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg SCXTNUM_EL2_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg SCXTNUM_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg CID_EL0_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg S3_op1_Cn_Cm_op2_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg RVBAR_EL3_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg RVBAR_EL2_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg RVBAR_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg RTPIDR_EL0_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg RSP_EL0_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg RMR_EL3_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg RMR_EL2_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg RMR_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg REVIDR_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg PMXEVTYPER_EL0_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg PMXEVCNTR_EL0_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg PMSLATFR_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg PMSIRR_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg PMSIDR_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg PMSICR_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg PMSFCR_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg PMSEVFR_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg PMSELR_EL0_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg PMSCR_EL2_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg PMSCR_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg PMOVSSET_EL0_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg PMOVSCLR_EL0_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg PMINTENSET_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg PMINTENCLR_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg PMEVTYPER_EL0_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg PMEVCNTR_EL0_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg PMCR_EL0_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg PMCNTENSET_EL0_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg PMCNTENCLR_EL0_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg PMCEID1_EL0_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg PMCEID0_EL0_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg PMCCNTR_EL0_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg PMUSERENR_EL0_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg PMCCFILTR_EL0_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg PMBSR_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg PMBPTR_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg PMBLIMITR_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg PMBIDR_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg PAR_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg OSECCR_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg OSDTRTX_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg OSDTRRX_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg MVFR2_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg MVFR1_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg MVFR0_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg VMPIDR_EL2_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg MPIDR_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg MPAMVPMV_EL2_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg MPAMVPM7_EL2_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg MPAMVPM6_EL2_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg MPAMVPM5_EL2_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg MPAMVPM4_EL2_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg MPAMVPM3_EL2_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg MPAMVPM2_EL2_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg MPAMVPM1_EL2_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg MPAMVPM0_EL2_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg MPAMIDR_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg MPAMHCR_EL2_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg MPAM1_EL1_0_62_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg MPAM2_EL2_0_62_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg MPAM3_EL3_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg MPAM0_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg VPIDR_EL2_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg MIDR_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg MDRAR_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg MDCCSR_EL0_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg MDCCINT_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg MAIR_EL3_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg MAIR_EL2_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg MAIR_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg LORSA_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg LORN_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg LORID_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg LOREA_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg LORC_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ISR_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg IFSR32_EL2_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ID_PFR2_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ID_PFR1_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ID_PFR0_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ID_MMFR5_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ID_MMFR4_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ID_MMFR3_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ID_MMFR2_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ID_MMFR1_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ID_MMFR0_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ID_ISAR6_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ID_ISAR5_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ID_ISAR4_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ID_ISAR3_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ID_ISAR2_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ID_ISAR1_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ID_ISAR0_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ID_DFR0_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ID_AFR0_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ID_AA64ZFR0_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ID_AA64PFR1_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ID_AA64PFR0_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ID_AA64MMFR2_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ID_AA64MMFR1_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ID_AA64MMFR0_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ID_AA64ISAR1_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ID_AA64ISAR0_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ID_AA64DFR1_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ID_AA64DFR0_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ID_AA64AFR1_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ID_AA64AFR0_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ICH_VTR_EL2_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ICH_VMCR_EL2_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ICH_MISR_EL2_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ICH_LR_EL2_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ICH_ELRSR_EL2_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ICH_EISR_EL2_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ICH_AP1R_EL2_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ICH_AP0R_EL2_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ICV_RPR_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ICC_RPR_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ICV_PMR_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ICC_PMR_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ICC_IGRPEN1_EL3_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ICV_IGRPEN1_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ICC_IGRPEN1_EL1_S_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ICC_IGRPEN1_EL1_NS_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ICV_IGRPEN0_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ICC_IGRPEN0_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ICV_IAR1_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ICC_IAR1_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ICV_IAR0_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ICC_IAR0_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ICV_HPPIR1_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ICC_HPPIR1_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ICV_HPPIR0_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ICC_HPPIR0_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ICC_CTLR_EL3_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ICV_CTLR_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ICC_CTLR_EL1_S_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ICC_CTLR_EL1_NS_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ICV_BPR1_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ICC_BPR1_EL1_S_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ICC_BPR1_EL1_NS_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ICV_BPR0_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ICC_BPR0_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ICV_AP1R_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ICC_AP1R_EL1_S_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ICC_AP1R_EL1_NS_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ICC_AP1R_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ICV_AP0R_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ICH_HCR_EL2_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ICC_SRE_EL3_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ICC_SRE_EL2_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ICC_SRE_EL1_S_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ICC_SRE_EL1_NS_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ICC_AP0R_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg HSTR_EL2_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg HACR_EL2_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg FPSR_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg FPEXC32_EL2_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg FPCR_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ERXSTATUS_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ERXMISC1_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ERXMISC0_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ERXFR_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ERXCTLR_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ERXADDR_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ERRSELR_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ERRIDR_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg VDISR_EL2_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg DISR_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg DBGWVR_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg DBGWCR_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg DBGVCR32_EL2_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg CDBGDTR_EL0_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg MDSCR_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg DBGDTRRX_EL0_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg DBGCLAIMSET_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg DBGCLAIMCLR_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg DBGBVR_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg OSLSR_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg OSDLR_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg DBGPRCR_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg SPIDEN_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg DSPSR_EL0_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg CDLR_EL0_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg DBGBCR_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg MDCR_EL3_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg MDCR_EL2_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg DBGAUTHSTATUS_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg DACR32_EL2_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg CTR_EL0_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg CSSELR_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg CSCR_EL3_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg CONTEXTIDR_EL2_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg CONTEXTIDR_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg CNTV_TVAL_EL0_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg CNTV_CVAL_EL0_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg CNTV_CTL_EL0_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg CNTVOFF_EL2_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg CNTVCT_EL0_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg CNTP_TVAL_EL0_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg CNTP_CVAL_EL0_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg CNTP_CTL_EL0_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg CNTPS_TVAL_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg CNTPS_CVAL_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg CNTPS_CTL_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg CNTPCT_EL0_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg CNTHV_TVAL_EL2_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg CNTHV_CVAL_EL2_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg CNTHV_CTL_EL2_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg CNTHP_TVAL_EL2_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg CNTHP_CVAL_EL2_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg CNTHP_CTL_EL2_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg CNTKCTL_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg CNTHCTL_EL2_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg CNTFRQ_EL0_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg CLIDR_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg CHCR_EL2_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg CCSIDR_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg AMAIR_EL3_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg AMAIR_EL2_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg AMAIR_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg AIDR_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg AFSR1_EL3_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg AFSR1_EL2_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg AFSR1_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg AFSR0_EL3_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg AFSR0_EL2_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg AFSR0_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ACTLR_EL3_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ACTLR_EL2_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ACTLR_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg SPSR_EL3_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg SPSR_EL2_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg SPSR_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg SCTLR_EL3_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg SCTLR_EL2_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg SCTLR_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg CPTR_EL3_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg CPTR_EL2_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg CPACR_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg VBAR_EL3_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg VBAR_EL2_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg VBAR_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ELR_EL3_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ELR_EL2_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ELR_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg CCTLR_EL3_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg CCTLR_EL2_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg CCTLR_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg CCTLR_EL0_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg BranchTaken_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg PC_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg TCR_EL3_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg TCR_EL2_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg TCR_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg HPFAR_EL2_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg FAR_EL3_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg FAR_EL2_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg FAR_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ESR_EL3_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ESR_EL2_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ESR_EL1_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg R30_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg R29_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg R28_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg R27_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg R26_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg R25_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg R24_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg R23_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg R22_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg R21_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg R20_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg R19_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg R18_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg R17_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg R16_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg R15_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg R14_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg R13_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg R12_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg R11_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg R10_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg R09_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg R08_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg R07_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg R06_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg R05_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg R04_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg R03_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg R02_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg R01_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg R00_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg ThisInstr_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg PSTATE_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg HCR_EL2_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg SCR_EL3_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg CNTHVS_TVAL_EL2_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg CNTHVS_CVAL_EL2_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg CNTHVS_CTL_EL2_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg CNTHPS_TVAL_EL2_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg CNTHPS_CVAL_EL2_ref v)) cheri_invariant"
  "\<And>v. runs_preserve_invariant (liftS (write_reg CNTHPS_CTL_EL2_ref v)) cheri_invariant"
  by (non_inv_reg_writes_preserve_cheri_invariant)+


lemmas non_inv_reg_writesS_preserve_invariant[runs_preserve_invariantI] =
  non_inv_reg_writes_preserve_invariant[unfolded liftState_simp]

lemma BranchTo_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (BranchTo target branch_type)) cheri_invariant"
  by (unfold BranchTo_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma BranchToCapability_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (BranchToCapability target branch_type)) cheri_invariant"
  by (unfold BranchToCapability_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma DBGBCR_EL1_SysRegRead_2d021994672d40d3_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (DBGBCR_EL1_SysRegRead_2d021994672d40d3 el op0 op1 CRn op2 CRm)) cheri_invariant"
  by (unfold DBGBCR_EL1_SysRegRead_2d021994672d40d3_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma DBGBVR_EL1_SysRegRead_dc4a8f61b400622f_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (DBGBVR_EL1_SysRegRead_dc4a8f61b400622f el op0 op1 CRn op2 CRm)) cheri_invariant"
  by (unfold DBGBVR_EL1_SysRegRead_dc4a8f61b400622f_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma DBGWCR_EL1_SysRegRead_03139d052b544b2f_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (DBGWCR_EL1_SysRegRead_03139d052b544b2f el op0 op1 CRn op2 CRm)) cheri_invariant"
  by (unfold DBGWCR_EL1_SysRegRead_03139d052b544b2f_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma DBGWVR_EL1_SysRegRead_029de1005ef34888_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (DBGWVR_EL1_SysRegRead_029de1005ef34888 el op0 op1 CRn op2 CRm)) cheri_invariant"
  by (unfold DBGWVR_EL1_SysRegRead_029de1005ef34888_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma AArch64_AutoGen_SysRegRead_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (AArch64_AutoGen_SysRegRead el op0 op1 CRn op2 CRm)) cheri_invariant"
  by (unfold AArch64_AutoGen_SysRegRead_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma AArch64_SysRegRead_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (AArch64_SysRegRead op0 op1 crn crm op2)) cheri_invariant"
  by (unfold AArch64_SysRegRead_def catch_early_return_bind_liftR liftState_bind liftState_read_reg comp_def, preserves_invariantI)

lemma DBGBCR_EL1_SysRegWrite_6730f3e3839510c5_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (DBGBCR_EL1_SysRegWrite_6730f3e3839510c5 el op0 op1 CRn op2 CRm val_name)) cheri_invariant"
  by (unfold DBGBCR_EL1_SysRegWrite_6730f3e3839510c5_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma DBGBVR_EL1_SysRegWrite_915752bfd6a41a2b_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (DBGBVR_EL1_SysRegWrite_915752bfd6a41a2b el op0 op1 CRn op2 CRm val_name)) cheri_invariant"
  by (unfold DBGBVR_EL1_SysRegWrite_915752bfd6a41a2b_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma DBGWCR_EL1_SysRegWrite_6bda3acb5910d354_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (DBGWCR_EL1_SysRegWrite_6bda3acb5910d354 el op0 op1 CRn op2 CRm val_name)) cheri_invariant"
  by (unfold DBGWCR_EL1_SysRegWrite_6bda3acb5910d354_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma DBGWVR_EL1_SysRegWrite_745b296ee53305ea_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (DBGWVR_EL1_SysRegWrite_745b296ee53305ea el op0 op1 CRn op2 CRm val_name)) cheri_invariant"
  by (unfold DBGWVR_EL1_SysRegWrite_745b296ee53305ea_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma AArch64_AutoGen_SysRegWrite_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (AArch64_AutoGen_SysRegWrite el op0 op1 CRn op2 CRm val_name)) cheri_invariant"
  by (unfold AArch64_AutoGen_SysRegWrite_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma AArch64_IMPDEFResets_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (AArch64_IMPDEFResets arg0)) cheri_invariant"
  by (unfold AArch64_IMPDEFResets_def bind_assoc liftState_simp comp_def, preserves_invariantI intro: modify_DCZID_preserves_invariant simp: set_slice_def ucast_update_subrange_vec_dec_simps)

lemma AArch64_TakeReset_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (AArch64_TakeReset cold_reset)) cheri_invariant"
  by (unfold AArch64_TakeReset_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma TakeReset_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (TakeReset cold)) cheri_invariant"
  by (unfold TakeReset_def bind_assoc liftState_simp comp_def, preserves_invariantI intro: modify_EDSCR_preserves_invariant simp: set_slice_def ucast_update_subrange_vec_dec_simps)

lemma AArch64_SysRegWrite_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (AArch64_SysRegWrite op0 op1 crn crm op2 val_name)) cheri_invariant"
  by (unfold AArch64_SysRegWrite_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma AArch64_CheckBreakpoint_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (AArch64_CheckBreakpoint vaddress size__arg)) cheri_invariant"
  by (unfold AArch64_CheckBreakpoint_def bind_assoc liftState_simp comp_def, preserves_invariantI elim: Value_and_boolS_elim HaltOnBreakpointOrWatchpoint_False)

lemma AArch64_CheckWatchpoint_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (AArch64_CheckWatchpoint vaddress acctype iswrite size__arg)) cheri_invariant"
  by (unfold AArch64_CheckWatchpoint_def bind_assoc liftState_simp comp_def, preserves_invariantI elim: Value_and_boolS_elim HaltOnBreakpointOrWatchpoint_False)

lemma AArch64_CheckDebug_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (AArch64_CheckDebug vaddress acctype iswrite size__arg)) cheri_invariant"
  by (unfold AArch64_CheckDebug_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma AArch64_TranslateAddressWithTag_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (AArch64_TranslateAddressWithTag vaddress acctype iswrite wasaligned size__arg iswritevalidcap)) cheri_invariant"
  by (unfold AArch64_TranslateAddressWithTag_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma AArch64_TranslateAddress_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (AArch64_TranslateAddress vaddress acctype iswrite wasaligned size__arg)) cheri_invariant"
  by (unfold AArch64_TranslateAddress_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma DC_CIVAC_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (DC_CIVAC val_name)) cheri_invariant"
  by (unfold DC_CIVAC_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma DC_CIVAC0_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (DC_CIVAC0 val_name__arg)) cheri_invariant"
  by (unfold DC_CIVAC0_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma CIVAC_SysOpsWrite_47ad60ecb930d217_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (CIVAC_SysOpsWrite_47ad60ecb930d217 el op0 op1 CRn op2 CRm val_name)) cheri_invariant"
  by (unfold CIVAC_SysOpsWrite_47ad60ecb930d217_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma DC_CVAC_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (DC_CVAC val_name)) cheri_invariant"
  by (unfold DC_CVAC_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma DC_CVAC0_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (DC_CVAC0 val_name__arg)) cheri_invariant"
  by (unfold DC_CVAC0_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma CVAC_SysOpsWrite_c7d2e911c691cc6b_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (CVAC_SysOpsWrite_c7d2e911c691cc6b el op0 op1 CRn op2 CRm val_name)) cheri_invariant"
  by (unfold CVAC_SysOpsWrite_c7d2e911c691cc6b_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma DC_CVAP_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (DC_CVAP val_name)) cheri_invariant"
  by (unfold DC_CVAP_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma DC_CVADP_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (DC_CVADP val_name)) cheri_invariant"
  by (unfold DC_CVADP_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma CVADP_SysOpsWrite_9953ef108c01d34a_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (CVADP_SysOpsWrite_9953ef108c01d34a el op0 op1 CRn op2 CRm val_name)) cheri_invariant"
  by (unfold CVADP_SysOpsWrite_9953ef108c01d34a_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma CVAP_SysOpsWrite_a43f75867888e74a_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (CVAP_SysOpsWrite_a43f75867888e74a el op0 op1 CRn op2 CRm val_name)) cheri_invariant"
  by (unfold CVAP_SysOpsWrite_a43f75867888e74a_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma DC_CVAU_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (DC_CVAU val_name)) cheri_invariant"
  by (unfold DC_CVAU_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma DC_CVAU0_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (DC_CVAU0 val_name__arg)) cheri_invariant"
  by (unfold DC_CVAU0_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma CVAU_SysOpsWrite_4a72bbc98a17973c_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (CVAU_SysOpsWrite_4a72bbc98a17973c el op0 op1 CRn op2 CRm val_name)) cheri_invariant"
  by (unfold CVAU_SysOpsWrite_4a72bbc98a17973c_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma DC_IVAC_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (DC_IVAC val_name)) cheri_invariant"
  by (unfold DC_IVAC_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma DC_IVAC0_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (DC_IVAC0 val_name__arg)) cheri_invariant"
  by (unfold DC_IVAC0_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma IVAC_SysOpsWrite_41b93e0e56e4f107_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (IVAC_SysOpsWrite_41b93e0e56e4f107 el op0 op1 CRn op2 CRm val_name)) cheri_invariant"
  by (unfold IVAC_SysOpsWrite_41b93e0e56e4f107_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma IC_IVAU_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (IC_IVAU val_name)) cheri_invariant"
  by (unfold IC_IVAU_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma IVAU_SysOpsWrite_2dfe97b748dd324e_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (IVAU_SysOpsWrite_2dfe97b748dd324e el op0 op1 CRn op2 CRm val_name)) cheri_invariant"
  by (unfold IVAU_SysOpsWrite_2dfe97b748dd324e_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma AArch64_AutoGen_SysOpsWrite_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (AArch64_AutoGen_SysOpsWrite el op0 op1 CRn op2 CRm val_name)) cheri_invariant"
  by (unfold AArch64_AutoGen_SysOpsWrite_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma AArch64_SysInstr_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (AArch64_SysInstr op0 op1 crn crm op2 val_name)) cheri_invariant"
  by (unfold AArch64_SysInstr_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma BranchXToCapability_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (BranchXToCapability target__arg branch_type)) cheri_invariant"
  by (unfold BranchXToCapability_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma BranchToOffset_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (BranchToOffset offset branch_type)) cheri_invariant"
  by (unfold BranchToOffset_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma AArch64_MemSingle_read_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (AArch64_MemSingle_read address size__arg acctype wasaligned)) cheri_invariant"
  by (unfold AArch64_MemSingle_read_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma AArch64_MemSingle_set_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (AArch64_MemSingle_set address size__arg acctype wasaligned value_name)) cheri_invariant"
  by (unfold AArch64_MemSingle_set_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma AArch64_TaggedMemSingle_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (AArch64_TaggedMemSingle address size__arg acctype wasaligned)) cheri_invariant"
  by (unfold AArch64_TaggedMemSingle_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma AArch64_TaggedMemSingle__1_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (AArch64_TaggedMemSingle__1 address size__arg acctype wasaligned tags value_name)) cheri_invariant"
  by (unfold AArch64_TaggedMemSingle__1_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma AArch64_CapabilityTag_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (AArch64_CapabilityTag address acctype)) cheri_invariant"
  by (unfold AArch64_CapabilityTag_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma AArch64_CapabilityTag_set_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (AArch64_CapabilityTag_set address acctype tag)) cheri_invariant"
  by (unfold AArch64_CapabilityTag_set_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma Mem_read0_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (Mem_read0 address size__arg acctype)) cheri_invariant"
  by (unfold Mem_read0_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma Mem_set0_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (Mem_set0 address size__arg acctype value_name__arg)) cheri_invariant"
  by (unfold Mem_set0_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma MemC_read_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (MemC_read address acctype)) cheri_invariant"
  by (unfold MemC_read_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma MemC_set_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (MemC_set address acctype value_name)) cheri_invariant"
  by (unfold MemC_set_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma MemCP__1_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (MemCP__1 address acctype value1_name value2_name)) cheri_invariant"
  by (unfold MemCP__1_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma AArch64_TranslateAddressForAtomicAccess_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (AArch64_TranslateAddressForAtomicAccess address sizeinbits)) cheri_invariant"
  by (unfold AArch64_TranslateAddressForAtomicAccess_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma MemAtomicCompareAndSwap_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (MemAtomicCompareAndSwap base expectedvalue newvalue__arg ldacctype stacctype)) cheri_invariant"
  by (unfold MemAtomicCompareAndSwap_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma MemAtomic_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (MemAtomic base op value_name ldacctype stacctype)) cheri_invariant"
  by (unfold MemAtomic_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma MemAtomicCompareAndSwapC_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (MemAtomicCompareAndSwapC vaddr address expectedcap newcap ldacctype stacctype)) cheri_invariant"
  by (unfold MemAtomicCompareAndSwapC_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma MemAtomicC_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (MemAtomicC address op value_name ldacctype stacctype)) cheri_invariant"
  by (unfold MemAtomicC_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma AArch64_SetExclusiveMonitors_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (AArch64_SetExclusiveMonitors address size__arg)) cheri_invariant"
  by (unfold AArch64_SetExclusiveMonitors_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma AArch64_ExclusiveMonitorsPass_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (AArch64_ExclusiveMonitorsPass address size__arg)) cheri_invariant"
  by (unfold AArch64_ExclusiveMonitorsPass_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma AArch64_ExceptionReturnToCapability_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (AArch64_ExceptionReturnToCapability new_pcc__arg spsr)) cheri_invariant"
  by (unfold AArch64_ExceptionReturnToCapability_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma CAP_DC_CIVAC_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (CAP_DC_CIVAC cval)) cheri_invariant"
  by (unfold CAP_DC_CIVAC_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma CAP_DC_CVAC_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (CAP_DC_CVAC cval)) cheri_invariant"
  by (unfold CAP_DC_CVAC_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma CAP_DC_CVADP_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (CAP_DC_CVADP cval)) cheri_invariant"
  by (unfold CAP_DC_CVADP_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma CAP_DC_CVAP_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (CAP_DC_CVAP cval)) cheri_invariant"
  by (unfold CAP_DC_CVAP_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma CAP_DC_CVAU_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (CAP_DC_CVAU cval)) cheri_invariant"
  by (unfold CAP_DC_CVAU_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma CAP_DC_IVAC_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (CAP_DC_IVAC cval)) cheri_invariant"
  by (unfold CAP_DC_IVAC_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma CAP_IC_IVAU_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (CAP_IC_IVAU cval)) cheri_invariant"
  by (unfold CAP_IC_IVAU_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma AArch64_SysInstrWithCapability_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (AArch64_SysInstrWithCapability op0 op1 crn crm op2 val_name)) cheri_invariant"
  by (unfold AArch64_SysInstrWithCapability_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma FetchNextInstr_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (FetchNextInstr arg0)) cheri_invariant"
  by (unfold FetchNextInstr_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma Step_PC_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (Step_PC arg0)) cheri_invariant"
  by (unfold Step_PC_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_ALDARB_R_R_B_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_ALDARB_R_R_B acctype datasize n regsize t__arg)) cheri_invariant"
  by (unfold execute_ALDARB_R_R_B_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ALDARB_R_R_B_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ALDARB_R_R_B L Rn Rt)) cheri_invariant"
  by (unfold decode_ALDARB_R_R_B_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_ALDAR_C_R_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_ALDAR_C_R_C acctype n t__arg)) cheri_invariant"
  by (unfold execute_ALDAR_C_R_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ALDAR_C_R_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ALDAR_C_R_C L Rn Ct)) cheri_invariant"
  by (unfold decode_ALDAR_C_R_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_ALDAR_R_R_32_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_ALDAR_R_R_32 acctype datasize n regsize t__arg)) cheri_invariant"
  by (unfold execute_ALDAR_R_R_32_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ALDAR_R_R_32_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ALDAR_R_R_32 L Rn Rt)) cheri_invariant"
  by (unfold decode_ALDAR_R_R_32_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_ALDRB_R_RRB_B_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_ALDRB_R_RRB_B extend_type m n regsize l__550 shift t__arg)) cheri_invariant"
  by (unfold execute_ALDRB_R_RRB_B_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ALDRB_R_RRB_B_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ALDRB_R_RRB_B L Rm sign sz S opc Rn Rt)) cheri_invariant"
  by (unfold decode_ALDRB_R_RRB_B_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_ALDRB_R_RUI_B_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_ALDRB_R_RUI_B datasize n offset regsize t__arg)) cheri_invariant"
  by (unfold execute_ALDRB_R_RUI_B_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ALDRB_R_RUI_B_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ALDRB_R_RUI_B L imm9 op Rn Rt)) cheri_invariant"
  by (unfold decode_ALDRB_R_RUI_B_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_ALDRH_R_RRB_32_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_ALDRH_R_RRB_32 extend_type m n regsize l__549 shift t__arg)) cheri_invariant"
  by (unfold execute_ALDRH_R_RRB_32_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ALDRH_R_RRB_32_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ALDRH_R_RRB_32 L Rm sign sz S opc Rn Rt)) cheri_invariant"
  by (unfold decode_ALDRH_R_RRB_32_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_ALDRSB_R_RRB_32_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_ALDRSB_R_RRB_32 extend_type m n regsize l__545 shift t__arg)) cheri_invariant"
  by (unfold execute_ALDRSB_R_RRB_32_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ALDRSB_R_RRB_32_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ALDRSB_R_RRB_32 L Rm sign sz S opc Rn Rt)) cheri_invariant"
  by (unfold decode_ALDRSB_R_RRB_32_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_ALDRSB_R_RRB_64_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_ALDRSB_R_RRB_64 extend_type m n regsize l__546 shift t__arg)) cheri_invariant"
  by (unfold execute_ALDRSB_R_RRB_64_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ALDRSB_R_RRB_64_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ALDRSB_R_RRB_64 L Rm sign sz S opc Rn Rt)) cheri_invariant"
  by (unfold decode_ALDRSB_R_RRB_64_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_ALDRSH_R_RRB_32_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_ALDRSH_R_RRB_32 extend_type m n regsize l__543 shift t__arg)) cheri_invariant"
  by (unfold execute_ALDRSH_R_RRB_32_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ALDRSH_R_RRB_32_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ALDRSH_R_RRB_32 L Rm sign sz S opc Rn Rt)) cheri_invariant"
  by (unfold decode_ALDRSH_R_RRB_32_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_ALDRSH_R_RRB_64_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_ALDRSH_R_RRB_64 extend_type m n regsize l__544 shift t__arg)) cheri_invariant"
  by (unfold execute_ALDRSH_R_RRB_64_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ALDRSH_R_RRB_64_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ALDRSH_R_RRB_64 L Rm sign sz S opc Rn Rt)) cheri_invariant"
  by (unfold decode_ALDRSH_R_RRB_64_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_ALDR_C_RRB_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_ALDR_C_RRB_C extend_type m n shift t__arg)) cheri_invariant"
  by (unfold execute_ALDR_C_RRB_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ALDR_C_RRB_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ALDR_C_RRB_C Rm sign sz S L Rn Ct)) cheri_invariant"
  by (unfold decode_ALDR_C_RRB_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_ALDR_C_RUI_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_ALDR_C_RUI_C n offset t__arg)) cheri_invariant"
  by (unfold execute_ALDR_C_RUI_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ALDR_C_RUI_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ALDR_C_RUI_C L imm9 op Rn Ct)) cheri_invariant"
  by (unfold decode_ALDR_C_RUI_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_ALDR_R_RRB_32_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_ALDR_R_RRB_32 extend_type m n regsize l__548 shift t__arg)) cheri_invariant"
  by (unfold execute_ALDR_R_RRB_32_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ALDR_R_RRB_32_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ALDR_R_RRB_32 L Rm sign sz S opc Rn Rt)) cheri_invariant"
  by (unfold decode_ALDR_R_RRB_32_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_ALDR_R_RRB_64_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_ALDR_R_RRB_64 extend_type m n regsize l__547 shift t__arg)) cheri_invariant"
  by (unfold execute_ALDR_R_RRB_64_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ALDR_R_RRB_64_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ALDR_R_RRB_64 L Rm sign sz S opc Rn Rt)) cheri_invariant"
  by (unfold decode_ALDR_R_RRB_64_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_ALDR_R_RUI_32_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_ALDR_R_RUI_32 datasize n offset regsize t__arg)) cheri_invariant"
  by (unfold execute_ALDR_R_RUI_32_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ALDR_R_RUI_32_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ALDR_R_RUI_32 L imm9 op Rn Rt)) cheri_invariant"
  by (unfold decode_ALDR_R_RUI_32_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_ALDR_R_RUI_64_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_ALDR_R_RUI_64 datasize n offset regsize t__arg)) cheri_invariant"
  by (unfold execute_ALDR_R_RUI_64_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ALDR_R_RUI_64_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ALDR_R_RUI_64 L imm9 op Rn Rt)) cheri_invariant"
  by (unfold decode_ALDR_R_RUI_64_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_ALDR_V_RRB_D_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_ALDR_V_RRB_D extend_type m n l__542 shift t__arg)) cheri_invariant"
  by (unfold execute_ALDR_V_RRB_D_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ALDR_V_RRB_D_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ALDR_V_RRB_D L Rm sign sz S opc Rn Rt)) cheri_invariant"
  by (unfold decode_ALDR_V_RRB_D_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_ALDR_V_RRB_S_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_ALDR_V_RRB_S extend_type m n l__541 shift t__arg)) cheri_invariant"
  by (unfold execute_ALDR_V_RRB_S_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ALDR_V_RRB_S_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ALDR_V_RRB_S L Rm sign sz S opc Rn Rt)) cheri_invariant"
  by (unfold decode_ALDR_V_RRB_S_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_ALDURB_R_RI_32_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_ALDURB_R_RI_32 datasize n offset regsize t__arg)) cheri_invariant"
  by (unfold execute_ALDURB_R_RI_32_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ALDURB_R_RI_32_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ALDURB_R_RI_32 op1 V imm9 op2 Rn Rt)) cheri_invariant"
  by (unfold decode_ALDURB_R_RI_32_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_ALDURH_R_RI_32_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_ALDURH_R_RI_32 datasize n offset regsize t__arg)) cheri_invariant"
  by (unfold execute_ALDURH_R_RI_32_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ALDURH_R_RI_32_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ALDURH_R_RI_32 op1 V imm9 op2 Rn Rt)) cheri_invariant"
  by (unfold decode_ALDURH_R_RI_32_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_ALDURSB_R_RI_32_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_ALDURSB_R_RI_32 datasize n offset regsize t__arg)) cheri_invariant"
  by (unfold execute_ALDURSB_R_RI_32_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ALDURSB_R_RI_32_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ALDURSB_R_RI_32 op1 V imm9 op2 Rn Rt)) cheri_invariant"
  by (unfold decode_ALDURSB_R_RI_32_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_ALDURSB_R_RI_64_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_ALDURSB_R_RI_64 datasize n offset regsize t__arg)) cheri_invariant"
  by (unfold execute_ALDURSB_R_RI_64_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ALDURSB_R_RI_64_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ALDURSB_R_RI_64 op1 V imm9 op2 Rn Rt)) cheri_invariant"
  by (unfold decode_ALDURSB_R_RI_64_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_ALDURSH_R_RI_32_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_ALDURSH_R_RI_32 datasize n offset regsize t__arg)) cheri_invariant"
  by (unfold execute_ALDURSH_R_RI_32_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ALDURSH_R_RI_32_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ALDURSH_R_RI_32 op1 V imm9 op2 Rn Rt)) cheri_invariant"
  by (unfold decode_ALDURSH_R_RI_32_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_ALDURSH_R_RI_64_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_ALDURSH_R_RI_64 datasize n offset regsize t__arg)) cheri_invariant"
  by (unfold execute_ALDURSH_R_RI_64_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ALDURSH_R_RI_64_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ALDURSH_R_RI_64 op1 V imm9 op2 Rn Rt)) cheri_invariant"
  by (unfold decode_ALDURSH_R_RI_64_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_ALDURSW_R_RI_64_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_ALDURSW_R_RI_64 datasize n offset regsize t__arg)) cheri_invariant"
  by (unfold execute_ALDURSW_R_RI_64_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ALDURSW_R_RI_64_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ALDURSW_R_RI_64 op1 V imm9 op2 Rn Rt)) cheri_invariant"
  by (unfold decode_ALDURSW_R_RI_64_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_ALDUR_C_RI_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_ALDUR_C_RI_C n offset t__arg)) cheri_invariant"
  by (unfold execute_ALDUR_C_RI_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ALDUR_C_RI_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ALDUR_C_RI_C op1 V imm9 op2 Rn Ct)) cheri_invariant"
  by (unfold decode_ALDUR_C_RI_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_ALDUR_R_RI_32_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_ALDUR_R_RI_32 datasize n offset regsize t__arg)) cheri_invariant"
  by (unfold execute_ALDUR_R_RI_32_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ALDUR_R_RI_32_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ALDUR_R_RI_32 op1 V imm9 op2 Rn Rt)) cheri_invariant"
  by (unfold decode_ALDUR_R_RI_32_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_ALDUR_R_RI_64_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_ALDUR_R_RI_64 datasize n offset regsize t__arg)) cheri_invariant"
  by (unfold execute_ALDUR_R_RI_64_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ALDUR_R_RI_64_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ALDUR_R_RI_64 op1 V imm9 op2 Rn Rt)) cheri_invariant"
  by (unfold decode_ALDUR_R_RI_64_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_ALDUR_V_RI_B_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_ALDUR_V_RI_B datasize n offset t__arg)) cheri_invariant"
  by (unfold execute_ALDUR_V_RI_B_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ALDUR_V_RI_B_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ALDUR_V_RI_B op1 V imm9 op2 Rn Rt)) cheri_invariant"
  by (unfold decode_ALDUR_V_RI_B_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_ALDUR_V_RI_D_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_ALDUR_V_RI_D datasize n offset t__arg)) cheri_invariant"
  by (unfold execute_ALDUR_V_RI_D_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ALDUR_V_RI_D_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ALDUR_V_RI_D op1 V imm9 op2 Rn Rt)) cheri_invariant"
  by (unfold decode_ALDUR_V_RI_D_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_ALDUR_V_RI_H_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_ALDUR_V_RI_H datasize n offset t__arg)) cheri_invariant"
  by (unfold execute_ALDUR_V_RI_H_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ALDUR_V_RI_H_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ALDUR_V_RI_H op1 V imm9 op2 Rn Rt)) cheri_invariant"
  by (unfold decode_ALDUR_V_RI_H_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_ALDUR_V_RI_Q_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_ALDUR_V_RI_Q datasize n offset t__arg)) cheri_invariant"
  by (unfold execute_ALDUR_V_RI_Q_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ALDUR_V_RI_Q_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ALDUR_V_RI_Q op1 V imm9 op2 Rn Rt)) cheri_invariant"
  by (unfold decode_ALDUR_V_RI_Q_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_ALDUR_V_RI_S_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_ALDUR_V_RI_S datasize n offset t__arg)) cheri_invariant"
  by (unfold execute_ALDUR_V_RI_S_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ALDUR_V_RI_S_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ALDUR_V_RI_S op1 V imm9 op2 Rn Rt)) cheri_invariant"
  by (unfold decode_ALDUR_V_RI_S_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_ASTLRB_R_R_B_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_ASTLRB_R_R_B acctype datasize n t__arg)) cheri_invariant"
  by (unfold execute_ASTLRB_R_R_B_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ASTLRB_R_R_B_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ASTLRB_R_R_B L Rn Rt)) cheri_invariant"
  by (unfold decode_ASTLRB_R_R_B_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_ASTLR_C_R_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_ASTLR_C_R_C acctype n t__arg)) cheri_invariant"
  by (unfold execute_ASTLR_C_R_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ASTLR_C_R_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ASTLR_C_R_C L Rn Ct)) cheri_invariant"
  by (unfold decode_ASTLR_C_R_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_ASTLR_R_R_32_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_ASTLR_R_R_32 acctype datasize n t__arg)) cheri_invariant"
  by (unfold execute_ASTLR_R_R_32_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ASTLR_R_R_32_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ASTLR_R_R_32 L Rn Rt)) cheri_invariant"
  by (unfold decode_ASTLR_R_R_32_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_ASTRB_R_RRB_B_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_ASTRB_R_RRB_B extend_type m n l__556 shift t__arg)) cheri_invariant"
  by (unfold execute_ASTRB_R_RRB_B_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ASTRB_R_RRB_B_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ASTRB_R_RRB_B L Rm sign sz S opc Rn Rt)) cheri_invariant"
  by (unfold decode_ASTRB_R_RRB_B_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_ASTRB_R_RUI_B_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_ASTRB_R_RUI_B datasize n offset t__arg)) cheri_invariant"
  by (unfold execute_ASTRB_R_RUI_B_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ASTRB_R_RUI_B_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ASTRB_R_RUI_B L imm9 op Rn Rt)) cheri_invariant"
  by (unfold decode_ASTRB_R_RUI_B_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_ASTRH_R_RRB_32_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_ASTRH_R_RRB_32 extend_type m n l__555 shift t__arg)) cheri_invariant"
  by (unfold execute_ASTRH_R_RRB_32_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ASTRH_R_RRB_32_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ASTRH_R_RRB_32 L Rm sign sz S opc Rn Rt)) cheri_invariant"
  by (unfold decode_ASTRH_R_RRB_32_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_ASTR_C_RRB_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_ASTR_C_RRB_C extend_type m n shift t__arg)) cheri_invariant"
  by (unfold execute_ASTR_C_RRB_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ASTR_C_RRB_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ASTR_C_RRB_C Rm sign sz S L Rn Ct)) cheri_invariant"
  by (unfold decode_ASTR_C_RRB_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_ASTR_C_RUI_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_ASTR_C_RUI_C n offset t__arg)) cheri_invariant"
  by (unfold execute_ASTR_C_RUI_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ASTR_C_RUI_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ASTR_C_RUI_C L imm9 op Rn Ct)) cheri_invariant"
  by (unfold decode_ASTR_C_RUI_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_ASTR_R_RRB_32_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_ASTR_R_RRB_32 extend_type m n l__554 shift t__arg)) cheri_invariant"
  by (unfold execute_ASTR_R_RRB_32_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ASTR_R_RRB_32_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ASTR_R_RRB_32 L Rm sign sz S opc Rn Rt)) cheri_invariant"
  by (unfold decode_ASTR_R_RRB_32_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_ASTR_R_RRB_64_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_ASTR_R_RRB_64 extend_type m n l__553 shift t__arg)) cheri_invariant"
  by (unfold execute_ASTR_R_RRB_64_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ASTR_R_RRB_64_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ASTR_R_RRB_64 L Rm sign sz S opc Rn Rt)) cheri_invariant"
  by (unfold decode_ASTR_R_RRB_64_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_ASTR_R_RUI_32_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_ASTR_R_RUI_32 datasize n offset t__arg)) cheri_invariant"
  by (unfold execute_ASTR_R_RUI_32_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ASTR_R_RUI_32_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ASTR_R_RUI_32 L imm9 op Rn Rt)) cheri_invariant"
  by (unfold decode_ASTR_R_RUI_32_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_ASTR_R_RUI_64_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_ASTR_R_RUI_64 datasize n offset t__arg)) cheri_invariant"
  by (unfold execute_ASTR_R_RUI_64_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ASTR_R_RUI_64_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ASTR_R_RUI_64 L imm9 op Rn Rt)) cheri_invariant"
  by (unfold decode_ASTR_R_RUI_64_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_ASTR_V_RRB_D_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_ASTR_V_RRB_D extend_type m n l__552 shift t__arg)) cheri_invariant"
  by (unfold execute_ASTR_V_RRB_D_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ASTR_V_RRB_D_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ASTR_V_RRB_D L Rm sign sz S opc Rn Rt)) cheri_invariant"
  by (unfold decode_ASTR_V_RRB_D_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_ASTR_V_RRB_S_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_ASTR_V_RRB_S extend_type m n l__551 shift t__arg)) cheri_invariant"
  by (unfold execute_ASTR_V_RRB_S_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ASTR_V_RRB_S_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ASTR_V_RRB_S L Rm sign sz S opc Rn Rt)) cheri_invariant"
  by (unfold decode_ASTR_V_RRB_S_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_ASTURB_R_RI_32_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_ASTURB_R_RI_32 datasize n offset t__arg)) cheri_invariant"
  by (unfold execute_ASTURB_R_RI_32_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ASTURB_R_RI_32_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ASTURB_R_RI_32 op1 V imm9 op2 Rn Rt)) cheri_invariant"
  by (unfold decode_ASTURB_R_RI_32_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_ASTURH_R_RI_32_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_ASTURH_R_RI_32 datasize n offset t__arg)) cheri_invariant"
  by (unfold execute_ASTURH_R_RI_32_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ASTURH_R_RI_32_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ASTURH_R_RI_32 op1 V imm9 op2 Rn Rt)) cheri_invariant"
  by (unfold decode_ASTURH_R_RI_32_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_ASTUR_C_RI_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_ASTUR_C_RI_C n offset t__arg)) cheri_invariant"
  by (unfold execute_ASTUR_C_RI_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ASTUR_C_RI_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ASTUR_C_RI_C op1 V imm9 op2 Rn Ct)) cheri_invariant"
  by (unfold decode_ASTUR_C_RI_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_ASTUR_R_RI_32_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_ASTUR_R_RI_32 datasize n offset t__arg)) cheri_invariant"
  by (unfold execute_ASTUR_R_RI_32_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ASTUR_R_RI_32_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ASTUR_R_RI_32 op1 V imm9 op2 Rn Rt)) cheri_invariant"
  by (unfold decode_ASTUR_R_RI_32_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_ASTUR_R_RI_64_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_ASTUR_R_RI_64 datasize n offset t__arg)) cheri_invariant"
  by (unfold execute_ASTUR_R_RI_64_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ASTUR_R_RI_64_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ASTUR_R_RI_64 op1 V imm9 op2 Rn Rt)) cheri_invariant"
  by (unfold decode_ASTUR_R_RI_64_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_ASTUR_V_RI_B_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_ASTUR_V_RI_B datasize n offset t__arg)) cheri_invariant"
  by (unfold execute_ASTUR_V_RI_B_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ASTUR_V_RI_B_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ASTUR_V_RI_B op1 V imm9 op2 Rn Rt)) cheri_invariant"
  by (unfold decode_ASTUR_V_RI_B_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_ASTUR_V_RI_D_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_ASTUR_V_RI_D datasize n offset t__arg)) cheri_invariant"
  by (unfold execute_ASTUR_V_RI_D_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ASTUR_V_RI_D_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ASTUR_V_RI_D op1 V imm9 op2 Rn Rt)) cheri_invariant"
  by (unfold decode_ASTUR_V_RI_D_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_ASTUR_V_RI_H_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_ASTUR_V_RI_H datasize n offset t__arg)) cheri_invariant"
  by (unfold execute_ASTUR_V_RI_H_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ASTUR_V_RI_H_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ASTUR_V_RI_H op1 V imm9 op2 Rn Rt)) cheri_invariant"
  by (unfold decode_ASTUR_V_RI_H_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_ASTUR_V_RI_Q_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_ASTUR_V_RI_Q datasize n offset t__arg)) cheri_invariant"
  by (unfold execute_ASTUR_V_RI_Q_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ASTUR_V_RI_Q_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ASTUR_V_RI_Q op1 V imm9 op2 Rn Rt)) cheri_invariant"
  by (unfold decode_ASTUR_V_RI_Q_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_ASTUR_V_RI_S_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_ASTUR_V_RI_S datasize n offset t__arg)) cheri_invariant"
  by (unfold execute_ASTUR_V_RI_S_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ASTUR_V_RI_S_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ASTUR_V_RI_S op1 V imm9 op2 Rn Rt)) cheri_invariant"
  by (unfold decode_ASTUR_V_RI_S_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_BLRR_C_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_BLRR_C_C branch_type n)) cheri_invariant"
  by (unfold execute_BLRR_C_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_BLRR_C_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_BLRR_C_C opc Cn)) cheri_invariant"
  by (unfold decode_BLRR_C_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_BLRS_C_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_BLRS_C_C branch_type n)) cheri_invariant"
  by (unfold execute_BLRS_C_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_BLRS_C_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_BLRS_C_C opc Cn)) cheri_invariant"
  by (unfold decode_BLRS_C_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_BLRS_C_C_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_BLRS_C_C_C branch_type m n)) cheri_invariant"
  by (unfold execute_BLRS_C_C_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_BLRS_C_C_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_BLRS_C_C_C Cm opc Cn)) cheri_invariant"
  by (unfold decode_BLRS_C_C_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_BLR_CI_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_BLR_CI_C branch_type n offset)) cheri_invariant"
  by (unfold execute_BLR_CI_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_BLR_CI_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_BLR_CI_C imm7 Cn)) cheri_invariant"
  by (unfold decode_BLR_CI_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_BLR_C_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_BLR_C_C branch_type n)) cheri_invariant"
  by (unfold execute_BLR_C_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_BLR_C_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_BLR_C_C opc Cn)) cheri_invariant"
  by (unfold decode_BLR_C_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_BRR_C_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_BRR_C_C branch_type n)) cheri_invariant"
  by (unfold execute_BRR_C_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_BRR_C_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_BRR_C_C opc Cn)) cheri_invariant"
  by (unfold decode_BRR_C_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_BRS_C_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_BRS_C_C branch_type n)) cheri_invariant"
  by (unfold execute_BRS_C_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_BRS_C_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_BRS_C_C opc Cn)) cheri_invariant"
  by (unfold decode_BRS_C_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_BRS_C_C_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_BRS_C_C_C branch_type m n)) cheri_invariant"
  by (unfold execute_BRS_C_C_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_BRS_C_C_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_BRS_C_C_C Cm opc Cn)) cheri_invariant"
  by (unfold decode_BRS_C_C_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_BR_CI_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_BR_CI_C branch_type n offset)) cheri_invariant"
  by (unfold execute_BR_CI_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_BR_CI_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_BR_CI_C imm7 Cn)) cheri_invariant"
  by (unfold decode_BR_CI_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_BR_C_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_BR_C_C branch_type n)) cheri_invariant"
  by (unfold execute_BR_C_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_BR_C_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_BR_C_C opc Cn)) cheri_invariant"
  by (unfold decode_BR_C_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_BX___C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_BX___C branch_type)) cheri_invariant"
  by (unfold execute_BX___C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_BX___C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_BX___C opc)) cheri_invariant"
  by (unfold decode_BX___C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_CASAL_C_R_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_CASAL_C_R_C ldacctype n s__arg stacctype t__arg)) cheri_invariant"
  by (unfold execute_CASAL_C_R_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_CASAL_C_R_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_CASAL_C_R_C L Cs R Rn Ct)) cheri_invariant"
  by (unfold decode_CASAL_C_R_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_CASA_C_R_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_CASA_C_R_C ldacctype n s__arg stacctype t__arg)) cheri_invariant"
  by (unfold execute_CASA_C_R_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_CASA_C_R_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_CASA_C_R_C L Cs R Rn Ct)) cheri_invariant"
  by (unfold decode_CASA_C_R_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_CASL_C_R_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_CASL_C_R_C ldacctype n s__arg stacctype t__arg)) cheri_invariant"
  by (unfold execute_CASL_C_R_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_CASL_C_R_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_CASL_C_R_C L Cs R Rn Ct)) cheri_invariant"
  by (unfold decode_CASL_C_R_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_CAS_C_R_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_CAS_C_R_C ldacctype n s__arg stacctype t__arg)) cheri_invariant"
  by (unfold execute_CAS_C_R_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_CAS_C_R_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_CAS_C_R_C L Cs R Rn Ct)) cheri_invariant"
  by (unfold decode_CAS_C_R_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_LDAPR_C_R_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_LDAPR_C_R_C acctype n t__arg)) cheri_invariant"
  by (unfold execute_LDAPR_C_R_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_LDAPR_C_R_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_LDAPR_C_R_C Rn Ct)) cheri_invariant"
  by (unfold decode_LDAPR_C_R_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_LDAR_C_R_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_LDAR_C_R_C acctype n t__arg)) cheri_invariant"
  by (unfold execute_LDAR_C_R_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_LDAR_C_R_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_LDAR_C_R_C L Rn Ct)) cheri_invariant"
  by (unfold decode_LDAR_C_R_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_LDAXP_C_R_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_LDAXP_C_R_C acctype n t__arg t2)) cheri_invariant"
  by (unfold execute_LDAXP_C_R_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_LDAXP_C_R_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_LDAXP_C_R_C L Ct2 Rn Ct)) cheri_invariant"
  by (unfold decode_LDAXP_C_R_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_LDAXR_C_R_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_LDAXR_C_R_C acctype n t__arg)) cheri_invariant"
  by (unfold execute_LDAXR_C_R_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_LDAXR_C_R_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_LDAXR_C_R_C L Rn Ct)) cheri_invariant"
  by (unfold decode_LDAXR_C_R_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_LDCT_R_R_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_LDCT_R_R n t__arg)) cheri_invariant"
  by (unfold execute_LDCT_R_R_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_LDCT_R_R_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_LDCT_R_R opc Rn Rt)) cheri_invariant"
  by (unfold decode_LDCT_R_R_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_LDNP_C_RIB_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_LDNP_C_RIB_C acctype n offset t__arg t2)) cheri_invariant"
  by (unfold execute_LDNP_C_RIB_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_LDNP_C_RIB_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_LDNP_C_RIB_C L imm7 Ct2 Rn Ct)) cheri_invariant"
  by (unfold decode_LDNP_C_RIB_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_LDPBLR_C_C_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_LDPBLR_C_C_C branch_type n t__arg)) cheri_invariant"
  by (unfold execute_LDPBLR_C_C_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_LDPBLR_C_C_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_LDPBLR_C_C_C opc Cn Ct)) cheri_invariant"
  by (unfold decode_LDPBLR_C_C_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_LDPBR_C_C_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_LDPBR_C_C_C branch_type n t__arg)) cheri_invariant"
  by (unfold execute_LDPBR_C_C_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_LDPBR_C_C_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_LDPBR_C_C_C opc Cn Ct)) cheri_invariant"
  by (unfold decode_LDPBR_C_C_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_LDP_CC_RIAW_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_LDP_CC_RIAW_C acctype n offset t__arg t2)) cheri_invariant"
  by (unfold execute_LDP_CC_RIAW_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_LDP_CC_RIAW_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_LDP_CC_RIAW_C L imm7 Ct2 Rn Ct)) cheri_invariant"
  by (unfold decode_LDP_CC_RIAW_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_LDP_C_RIBW_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_LDP_C_RIBW_C acctype n offset t__arg t2)) cheri_invariant"
  by (unfold execute_LDP_C_RIBW_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_LDP_C_RIBW_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_LDP_C_RIBW_C L imm7 Ct2 Rn Ct)) cheri_invariant"
  by (unfold decode_LDP_C_RIBW_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_LDP_C_RIB_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_LDP_C_RIB_C acctype n offset t__arg t2)) cheri_invariant"
  by (unfold execute_LDP_C_RIB_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_LDP_C_RIB_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_LDP_C_RIB_C L imm7 Ct2 Rn Ct)) cheri_invariant"
  by (unfold decode_LDP_C_RIB_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_LDR_C_I_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_LDR_C_I_C offset t__arg)) cheri_invariant"
  by (unfold execute_LDR_C_I_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_LDR_C_I_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_LDR_C_I_C imm17 Ct)) cheri_invariant"
  by (unfold decode_LDR_C_I_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_LDR_C_RIAW_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_LDR_C_RIAW_C n offset t__arg)) cheri_invariant"
  by (unfold execute_LDR_C_RIAW_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_LDR_C_RIAW_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_LDR_C_RIAW_C opc imm9 Rn Ct)) cheri_invariant"
  by (unfold decode_LDR_C_RIAW_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_LDR_C_RIBW_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_LDR_C_RIBW_C n offset t__arg)) cheri_invariant"
  by (unfold execute_LDR_C_RIBW_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_LDR_C_RIBW_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_LDR_C_RIBW_C opc imm9 Rn Ct)) cheri_invariant"
  by (unfold decode_LDR_C_RIBW_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_LDR_C_RRB_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_LDR_C_RRB_C extend_type m n shift t__arg)) cheri_invariant"
  by (unfold execute_LDR_C_RRB_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_LDR_C_RRB_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_LDR_C_RRB_C opc Rm sign sz S Rn Ct)) cheri_invariant"
  by (unfold decode_LDR_C_RRB_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_LDR_C_RUIB_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_LDR_C_RUIB_C n offset t__arg)) cheri_invariant"
  by (unfold execute_LDR_C_RUIB_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_LDR_C_RUIB_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_LDR_C_RUIB_C L imm12 Rn Ct)) cheri_invariant"
  by (unfold decode_LDR_C_RUIB_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_LDTR_C_RIB_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_LDTR_C_RIB_C n offset t__arg)) cheri_invariant"
  by (unfold execute_LDTR_C_RIB_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_LDTR_C_RIB_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_LDTR_C_RIB_C opc imm9 Rn Ct)) cheri_invariant"
  by (unfold decode_LDTR_C_RIB_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_LDUR_C_RI_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_LDUR_C_RI_C n offset t__arg)) cheri_invariant"
  by (unfold execute_LDUR_C_RI_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_LDUR_C_RI_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_LDUR_C_RI_C opc imm9 Rn Ct)) cheri_invariant"
  by (unfold decode_LDUR_C_RI_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_LDXP_C_R_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_LDXP_C_R_C acctype n t__arg t2)) cheri_invariant"
  by (unfold execute_LDXP_C_R_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_LDXP_C_R_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_LDXP_C_R_C L Ct2 Rn Ct)) cheri_invariant"
  by (unfold decode_LDXP_C_R_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_LDXR_C_R_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_LDXR_C_R_C acctype n t__arg)) cheri_invariant"
  by (unfold execute_LDXR_C_R_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_LDXR_C_R_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_LDXR_C_R_C L Rn Ct)) cheri_invariant"
  by (unfold decode_LDXR_C_R_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_RETR_C_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_RETR_C_C branch_type n)) cheri_invariant"
  by (unfold execute_RETR_C_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_RETR_C_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_RETR_C_C opc Cn)) cheri_invariant"
  by (unfold decode_RETR_C_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_RETS_C_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_RETS_C_C branch_type n)) cheri_invariant"
  by (unfold execute_RETS_C_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_RETS_C_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_RETS_C_C opc Cn)) cheri_invariant"
  by (unfold decode_RETS_C_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_RETS_C_C_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_RETS_C_C_C branch_type m n)) cheri_invariant"
  by (unfold execute_RETS_C_C_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_RETS_C_C_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_RETS_C_C_C Cm opc Cn)) cheri_invariant"
  by (unfold decode_RETS_C_C_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_RET_C_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_RET_C_C branch_type n)) cheri_invariant"
  by (unfold execute_RET_C_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_RET_C_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_RET_C_C opc Cn)) cheri_invariant"
  by (unfold decode_RET_C_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_STCT_R_R_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_STCT_R_R n t__arg)) cheri_invariant"
  by (unfold execute_STCT_R_R_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_STCT_R_R_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_STCT_R_R opc Rn Rt)) cheri_invariant"
  by (unfold decode_STCT_R_R_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_STLR_C_R_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_STLR_C_R_C acctype n t__arg)) cheri_invariant"
  by (unfold execute_STLR_C_R_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_STLR_C_R_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_STLR_C_R_C L Rn Ct)) cheri_invariant"
  by (unfold decode_STLR_C_R_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_STLXP_R_CR_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_STLXP_R_CR_C acctype n s__arg t__arg t2)) cheri_invariant"
  by (unfold execute_STLXP_R_CR_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_STLXP_R_CR_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_STLXP_R_CR_C L Rs Ct2 Rn Ct)) cheri_invariant"
  by (unfold decode_STLXP_R_CR_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_STLXR_R_CR_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_STLXR_R_CR_C acctype n s__arg t__arg)) cheri_invariant"
  by (unfold execute_STLXR_R_CR_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_STLXR_R_CR_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_STLXR_R_CR_C L Rs Rn Ct)) cheri_invariant"
  by (unfold decode_STLXR_R_CR_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_STNP_C_RIB_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_STNP_C_RIB_C acctype n offset t__arg t2)) cheri_invariant"
  by (unfold execute_STNP_C_RIB_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_STNP_C_RIB_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_STNP_C_RIB_C L imm7 Ct2 Rn Ct)) cheri_invariant"
  by (unfold decode_STNP_C_RIB_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_STP_CC_RIAW_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_STP_CC_RIAW_C acctype n offset t__arg t2)) cheri_invariant"
  by (unfold execute_STP_CC_RIAW_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_STP_CC_RIAW_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_STP_CC_RIAW_C L imm7 Ct2 Rn Ct)) cheri_invariant"
  by (unfold decode_STP_CC_RIAW_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_STP_C_RIBW_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_STP_C_RIBW_C acctype n offset t__arg t2)) cheri_invariant"
  by (unfold execute_STP_C_RIBW_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_STP_C_RIBW_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_STP_C_RIBW_C L imm7 Ct2 Rn Ct)) cheri_invariant"
  by (unfold decode_STP_C_RIBW_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_STP_C_RIB_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_STP_C_RIB_C acctype n offset t__arg t2)) cheri_invariant"
  by (unfold execute_STP_C_RIB_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_STP_C_RIB_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_STP_C_RIB_C L imm7 Ct2 Rn Ct)) cheri_invariant"
  by (unfold decode_STP_C_RIB_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_STR_C_RIAW_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_STR_C_RIAW_C n offset t__arg)) cheri_invariant"
  by (unfold execute_STR_C_RIAW_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_STR_C_RIAW_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_STR_C_RIAW_C opc imm9 Rn Ct)) cheri_invariant"
  by (unfold decode_STR_C_RIAW_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_STR_C_RIBW_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_STR_C_RIBW_C n offset t__arg)) cheri_invariant"
  by (unfold execute_STR_C_RIBW_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_STR_C_RIBW_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_STR_C_RIBW_C opc imm9 Rn Ct)) cheri_invariant"
  by (unfold decode_STR_C_RIBW_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_STR_C_RRB_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_STR_C_RRB_C extend_type m n shift t__arg)) cheri_invariant"
  by (unfold execute_STR_C_RRB_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_STR_C_RRB_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_STR_C_RRB_C opc Rm sign sz S Rn Ct)) cheri_invariant"
  by (unfold decode_STR_C_RRB_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_STR_C_RUIB_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_STR_C_RUIB_C n offset t__arg)) cheri_invariant"
  by (unfold execute_STR_C_RUIB_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_STR_C_RUIB_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_STR_C_RUIB_C L imm12 Rn Ct)) cheri_invariant"
  by (unfold decode_STR_C_RUIB_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_STTR_C_RIB_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_STTR_C_RIB_C n offset t__arg)) cheri_invariant"
  by (unfold execute_STTR_C_RIB_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_STTR_C_RIB_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_STTR_C_RIB_C opc imm9 Rn Ct)) cheri_invariant"
  by (unfold decode_STTR_C_RIB_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_STUR_C_RI_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_STUR_C_RI_C n offset t__arg)) cheri_invariant"
  by (unfold execute_STUR_C_RI_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_STUR_C_RI_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_STUR_C_RI_C opc imm9 Rn Ct)) cheri_invariant"
  by (unfold decode_STUR_C_RI_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_STXP_R_CR_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_STXP_R_CR_C acctype n s__arg t__arg t2)) cheri_invariant"
  by (unfold execute_STXP_R_CR_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_STXP_R_CR_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_STXP_R_CR_C L Rs Ct2 Rn Ct)) cheri_invariant"
  by (unfold decode_STXP_R_CR_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_STXR_R_CR_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_STXR_R_CR_C acctype n s__arg t__arg)) cheri_invariant"
  by (unfold execute_STXR_R_CR_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_STXR_R_CR_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_STXR_R_CR_C L Rs Rn Ct)) cheri_invariant"
  by (unfold decode_STXR_R_CR_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_SWPAL_CC_R_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_SWPAL_CC_R_C ldacctype n s__arg stacctype t__arg)) cheri_invariant"
  by (unfold execute_SWPAL_CC_R_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_SWPAL_CC_R_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_SWPAL_CC_R_C A R Cs Rn Ct)) cheri_invariant"
  by (unfold decode_SWPAL_CC_R_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_SWPA_CC_R_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_SWPA_CC_R_C ldacctype n s__arg stacctype t__arg)) cheri_invariant"
  by (unfold execute_SWPA_CC_R_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_SWPA_CC_R_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_SWPA_CC_R_C A R Cs Rn Ct)) cheri_invariant"
  by (unfold decode_SWPA_CC_R_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_SWPL_CC_R_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_SWPL_CC_R_C ldacctype n s__arg stacctype t__arg)) cheri_invariant"
  by (unfold execute_SWPL_CC_R_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_SWPL_CC_R_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_SWPL_CC_R_C A R Cs Rn Ct)) cheri_invariant"
  by (unfold decode_SWPL_CC_R_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_SWP_CC_R_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_SWP_CC_R_C ldacctype n s__arg stacctype t__arg)) cheri_invariant"
  by (unfold execute_SWP_CC_R_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_SWP_CC_R_C_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_SWP_CC_R_C A R Cs Rn Ct)) cheri_invariant"
  by (unfold decode_SWP_CC_R_C_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_aarch64_instrs_branch_conditional_cond_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_aarch64_instrs_branch_conditional_cond condition offset)) cheri_invariant"
  by (unfold execute_aarch64_instrs_branch_conditional_cond_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_b_cond_aarch64_instrs_branch_conditional_cond_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_b_cond_aarch64_instrs_branch_conditional_cond cond imm19)) cheri_invariant"
  by (unfold decode_b_cond_aarch64_instrs_branch_conditional_cond_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_aarch64_instrs_branch_unconditional_immediate_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_aarch64_instrs_branch_unconditional_immediate branch_type offset)) cheri_invariant"
  by (unfold execute_aarch64_instrs_branch_unconditional_immediate_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_b_uncond_aarch64_instrs_branch_unconditional_immediate_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_b_uncond_aarch64_instrs_branch_unconditional_immediate imm26 op)) cheri_invariant"
  by (unfold decode_b_uncond_aarch64_instrs_branch_unconditional_immediate_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_bl_aarch64_instrs_branch_unconditional_immediate_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_bl_aarch64_instrs_branch_unconditional_immediate imm26 op)) cheri_invariant"
  by (unfold decode_bl_aarch64_instrs_branch_unconditional_immediate_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_aarch64_instrs_branch_unconditional_register_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_aarch64_instrs_branch_unconditional_register branch_type n)) cheri_invariant"
  by (unfold execute_aarch64_instrs_branch_unconditional_register_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_blr_aarch64_instrs_branch_unconditional_register_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_blr_aarch64_instrs_branch_unconditional_register Rm Rn M A op Z)) cheri_invariant"
  by (unfold decode_blr_aarch64_instrs_branch_unconditional_register_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_blra_aarch64_instrs_branch_unconditional_register_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_blra_aarch64_instrs_branch_unconditional_register Rm Rn M A op Z)) cheri_invariant"
  by (unfold decode_blra_aarch64_instrs_branch_unconditional_register_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_br_aarch64_instrs_branch_unconditional_register_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_br_aarch64_instrs_branch_unconditional_register Rm Rn M A op Z)) cheri_invariant"
  by (unfold decode_br_aarch64_instrs_branch_unconditional_register_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_bra_aarch64_instrs_branch_unconditional_register_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_bra_aarch64_instrs_branch_unconditional_register Rm Rn M A op Z)) cheri_invariant"
  by (unfold decode_bra_aarch64_instrs_branch_unconditional_register_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_aarch64_instrs_memory_atomicops_cas_single_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_aarch64_instrs_memory_atomicops_cas_single (datasize :: 'datasize::len itself) ldacctype n (regsize :: 'regsize::len itself) s__arg stacctype t__arg)) cheri_invariant"
  by (unfold execute_aarch64_instrs_memory_atomicops_cas_single_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_cas_aarch64_instrs_memory_atomicops_cas_single_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_cas_aarch64_instrs_memory_atomicops_cas_single Rt Rn o0 Rs L b__0)) cheri_invariant"
  by (unfold decode_cas_aarch64_instrs_memory_atomicops_cas_single_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_casb_aarch64_instrs_memory_atomicops_cas_single_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_casb_aarch64_instrs_memory_atomicops_cas_single Rt Rn o0 Rs L b__0)) cheri_invariant"
  by (unfold decode_casb_aarch64_instrs_memory_atomicops_cas_single_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_cash_aarch64_instrs_memory_atomicops_cas_single_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_cash_aarch64_instrs_memory_atomicops_cas_single Rt Rn o0 Rs L b__0)) cheri_invariant"
  by (unfold decode_cash_aarch64_instrs_memory_atomicops_cas_single_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_aarch64_instrs_memory_atomicops_cas_pair_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_aarch64_instrs_memory_atomicops_cas_pair l__38 ldacctype n (regsize :: 'regsize::len itself) s__arg stacctype t__arg)) cheri_invariant"
  by (unfold execute_aarch64_instrs_memory_atomicops_cas_pair_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_casp_aarch64_instrs_memory_atomicops_cas_pair_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_casp_aarch64_instrs_memory_atomicops_cas_pair Rt Rn Rt2 o0 Rs L b__0)) cheri_invariant"
  by (unfold decode_casp_aarch64_instrs_memory_atomicops_cas_pair_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_aarch64_instrs_branch_conditional_compare_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_aarch64_instrs_branch_conditional_compare (datasize :: 'datasize::len itself) iszero__arg offset t__arg)) cheri_invariant"
  by (unfold execute_aarch64_instrs_branch_conditional_compare_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_cbnz_aarch64_instrs_branch_conditional_compare_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_cbnz_aarch64_instrs_branch_conditional_compare Rt imm19 op b__0)) cheri_invariant"
  by (unfold decode_cbnz_aarch64_instrs_branch_conditional_compare_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_cbz_aarch64_instrs_branch_conditional_compare_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_cbz_aarch64_instrs_branch_conditional_compare Rt imm19 op b__0)) cheri_invariant"
  by (unfold decode_cbz_aarch64_instrs_branch_conditional_compare_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_dcps1_aarch64_instrs_system_exceptions_debug_exception_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_dcps1_aarch64_instrs_system_exceptions_debug_exception LL imm16)) cheri_invariant"
  by (unfold decode_dcps1_aarch64_instrs_system_exceptions_debug_exception_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_dcps2_aarch64_instrs_system_exceptions_debug_exception_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_dcps2_aarch64_instrs_system_exceptions_debug_exception LL imm16)) cheri_invariant"
  by (unfold decode_dcps2_aarch64_instrs_system_exceptions_debug_exception_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_dcps3_aarch64_instrs_system_exceptions_debug_exception_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_dcps3_aarch64_instrs_system_exceptions_debug_exception LL imm16)) cheri_invariant"
  by (unfold decode_dcps3_aarch64_instrs_system_exceptions_debug_exception_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_drps_aarch64_instrs_branch_unconditional_dret_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_drps_aarch64_instrs_branch_unconditional_dret arg0)) cheri_invariant"
  by (unfold decode_drps_aarch64_instrs_branch_unconditional_dret_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_aarch64_instrs_branch_unconditional_eret_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_aarch64_instrs_branch_unconditional_eret arg0)) cheri_invariant"
  by (unfold execute_aarch64_instrs_branch_unconditional_eret_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_eret_aarch64_instrs_branch_unconditional_eret_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_eret_aarch64_instrs_branch_unconditional_eret op4 Rn M A)) cheri_invariant"
  by (unfold decode_eret_aarch64_instrs_branch_unconditional_eret_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ereta_aarch64_instrs_branch_unconditional_eret_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ereta_aarch64_instrs_branch_unconditional_eret op4 Rn M A)) cheri_invariant"
  by (unfold decode_ereta_aarch64_instrs_branch_unconditional_eret_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_hlt_aarch64_instrs_system_exceptions_debug_halt_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_hlt_aarch64_instrs_system_exceptions_debug_halt imm16)) cheri_invariant"
  by (unfold decode_hlt_aarch64_instrs_system_exceptions_debug_halt_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_aarch64_instrs_memory_vector_multiple_no_wb_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_aarch64_instrs_memory_vector_multiple_no_wb (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) m memop n rpt selem t__arg wback)) cheri_invariant"
  by (unfold execute_aarch64_instrs_memory_vector_multiple_no_wb_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ld1_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ld1_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb Rt Rn b__0 opcode L b__1)) cheri_invariant"
  by (unfold decode_ld1_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ld1_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ld1_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc Rt Rn b__0 opcode Rm L b__1)) cheri_invariant"
  by (unfold decode_ld1_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_aarch64_instrs_memory_vector_single_no_wb_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_aarch64_instrs_memory_vector_single_no_wb (datasize :: 'datasize::len itself) (esize :: 'esize::len itself) index__arg m memop n replicate__arg selem t__arg wback)) cheri_invariant"
  by (unfold execute_aarch64_instrs_memory_vector_single_no_wb_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ld1_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ld1_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb Rt Rn b__0 S b__1 R L b__2)) cheri_invariant"
  by (unfold decode_ld1_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ld1_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ld1_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc Rt Rn b__0 S b__1 Rm R L b__2)) cheri_invariant"
  by (unfold decode_ld1_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ld1r_advsimd_aarch64_instrs_memory_vector_single_no_wb_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ld1r_advsimd_aarch64_instrs_memory_vector_single_no_wb Rt Rn b__0 S b__1 R L b__2)) cheri_invariant"
  by (unfold decode_ld1r_advsimd_aarch64_instrs_memory_vector_single_no_wb_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ld1r_advsimd_aarch64_instrs_memory_vector_single_post_inc_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ld1r_advsimd_aarch64_instrs_memory_vector_single_post_inc Rt Rn b__0 S b__1 Rm R L b__2)) cheri_invariant"
  by (unfold decode_ld1r_advsimd_aarch64_instrs_memory_vector_single_post_inc_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ld2_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ld2_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb Rt Rn b__0 opcode L b__1)) cheri_invariant"
  by (unfold decode_ld2_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ld2_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ld2_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc Rt Rn b__0 opcode Rm L b__1)) cheri_invariant"
  by (unfold decode_ld2_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ld2_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ld2_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb Rt Rn b__0 S b__1 R L b__2)) cheri_invariant"
  by (unfold decode_ld2_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ld2_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ld2_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc Rt Rn b__0 S b__1 Rm R L b__2)) cheri_invariant"
  by (unfold decode_ld2_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ld2r_advsimd_aarch64_instrs_memory_vector_single_no_wb_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ld2r_advsimd_aarch64_instrs_memory_vector_single_no_wb Rt Rn b__0 S b__1 R L b__2)) cheri_invariant"
  by (unfold decode_ld2r_advsimd_aarch64_instrs_memory_vector_single_no_wb_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ld2r_advsimd_aarch64_instrs_memory_vector_single_post_inc_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ld2r_advsimd_aarch64_instrs_memory_vector_single_post_inc Rt Rn b__0 S b__1 Rm R L b__2)) cheri_invariant"
  by (unfold decode_ld2r_advsimd_aarch64_instrs_memory_vector_single_post_inc_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ld3_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ld3_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb Rt Rn b__0 opcode L b__1)) cheri_invariant"
  by (unfold decode_ld3_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ld3_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ld3_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc Rt Rn b__0 opcode Rm L b__1)) cheri_invariant"
  by (unfold decode_ld3_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ld3_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ld3_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb Rt Rn b__0 S b__1 R L b__2)) cheri_invariant"
  by (unfold decode_ld3_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ld3_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ld3_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc Rt Rn b__0 S b__1 Rm R L b__2)) cheri_invariant"
  by (unfold decode_ld3_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ld3r_advsimd_aarch64_instrs_memory_vector_single_no_wb_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ld3r_advsimd_aarch64_instrs_memory_vector_single_no_wb Rt Rn b__0 S b__1 R L b__2)) cheri_invariant"
  by (unfold decode_ld3r_advsimd_aarch64_instrs_memory_vector_single_no_wb_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ld3r_advsimd_aarch64_instrs_memory_vector_single_post_inc_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ld3r_advsimd_aarch64_instrs_memory_vector_single_post_inc Rt Rn b__0 S b__1 Rm R L b__2)) cheri_invariant"
  by (unfold decode_ld3r_advsimd_aarch64_instrs_memory_vector_single_post_inc_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ld4_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ld4_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb Rt Rn b__0 opcode L b__1)) cheri_invariant"
  by (unfold decode_ld4_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ld4_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ld4_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc Rt Rn b__0 opcode Rm L b__1)) cheri_invariant"
  by (unfold decode_ld4_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ld4_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ld4_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb Rt Rn b__0 S b__1 R L b__2)) cheri_invariant"
  by (unfold decode_ld4_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ld4_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ld4_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc Rt Rn b__0 S b__1 Rm R L b__2)) cheri_invariant"
  by (unfold decode_ld4_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ld4r_advsimd_aarch64_instrs_memory_vector_single_no_wb_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ld4r_advsimd_aarch64_instrs_memory_vector_single_no_wb Rt Rn b__0 S b__1 R L b__2)) cheri_invariant"
  by (unfold decode_ld4r_advsimd_aarch64_instrs_memory_vector_single_no_wb_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ld4r_advsimd_aarch64_instrs_memory_vector_single_post_inc_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ld4r_advsimd_aarch64_instrs_memory_vector_single_post_inc Rt Rn b__0 S b__1 Rm R L b__2)) cheri_invariant"
  by (unfold decode_ld4r_advsimd_aarch64_instrs_memory_vector_single_post_inc_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_aarch64_instrs_memory_atomicops_ld_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_aarch64_instrs_memory_atomicops_ld (datasize :: 'datasize::len itself) ldacctype n op (regsize :: 'regsize::len itself) s__arg stacctype t__arg)) cheri_invariant"
  by (unfold execute_aarch64_instrs_memory_atomicops_ld_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ldadd_aarch64_instrs_memory_atomicops_ld_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ldadd_aarch64_instrs_memory_atomicops_ld Rt Rn opc Rs R A b__0)) cheri_invariant"
  by (unfold decode_ldadd_aarch64_instrs_memory_atomicops_ld_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ldaddb_aarch64_instrs_memory_atomicops_ld_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ldaddb_aarch64_instrs_memory_atomicops_ld Rt Rn opc Rs R A b__0)) cheri_invariant"
  by (unfold decode_ldaddb_aarch64_instrs_memory_atomicops_ld_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ldaddh_aarch64_instrs_memory_atomicops_ld_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ldaddh_aarch64_instrs_memory_atomicops_ld Rt Rn opc Rs R A b__0)) cheri_invariant"
  by (unfold decode_ldaddh_aarch64_instrs_memory_atomicops_ld_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_aarch64_instrs_memory_ordered_rcpc_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_aarch64_instrs_memory_ordered_rcpc acctype (datasize :: 'datasize::len itself) n (regsize :: 'regsize::len itself) t__arg)) cheri_invariant"
  by (unfold execute_aarch64_instrs_memory_ordered_rcpc_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ldapr_aarch64_instrs_memory_ordered_rcpc_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ldapr_aarch64_instrs_memory_ordered_rcpc Rt Rn Rs b__0)) cheri_invariant"
  by (unfold decode_ldapr_aarch64_instrs_memory_ordered_rcpc_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ldaprb_aarch64_instrs_memory_ordered_rcpc_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ldaprb_aarch64_instrs_memory_ordered_rcpc Rt Rn Rs b__0)) cheri_invariant"
  by (unfold decode_ldaprb_aarch64_instrs_memory_ordered_rcpc_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ldaprh_aarch64_instrs_memory_ordered_rcpc_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ldaprh_aarch64_instrs_memory_ordered_rcpc Rt Rn Rs b__0)) cheri_invariant"
  by (unfold decode_ldaprh_aarch64_instrs_memory_ordered_rcpc_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_aarch64_instrs_memory_ordered_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_aarch64_instrs_memory_ordered acctype (datasize :: 'datasize::len itself) memop n (regsize :: 'regsize::len itself) t__arg)) cheri_invariant"
  by (unfold execute_aarch64_instrs_memory_ordered_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ldar_aarch64_instrs_memory_ordered_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ldar_aarch64_instrs_memory_ordered Rt Rn Rt2 o0 Rs L b__0)) cheri_invariant"
  by (unfold decode_ldar_aarch64_instrs_memory_ordered_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ldarb_aarch64_instrs_memory_ordered_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ldarb_aarch64_instrs_memory_ordered Rt Rn Rt2 o0 Rs L b__0)) cheri_invariant"
  by (unfold decode_ldarb_aarch64_instrs_memory_ordered_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ldarh_aarch64_instrs_memory_ordered_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ldarh_aarch64_instrs_memory_ordered Rt Rn Rt2 o0 Rs L b__0)) cheri_invariant"
  by (unfold decode_ldarh_aarch64_instrs_memory_ordered_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_aarch64_instrs_memory_exclusive_pair_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_aarch64_instrs_memory_exclusive_pair acctype l__197 elsize memop n pair (regsize :: 'regsize::len itself) s__arg t__arg t2)) cheri_invariant"
  by (unfold execute_aarch64_instrs_memory_exclusive_pair_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ldaxp_aarch64_instrs_memory_exclusive_pair_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ldaxp_aarch64_instrs_memory_exclusive_pair Rt Rn Rt2 o0 Rs L b__0)) cheri_invariant"
  by (unfold decode_ldaxp_aarch64_instrs_memory_exclusive_pair_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_aarch64_instrs_memory_exclusive_single_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_aarch64_instrs_memory_exclusive_single acctype l__532 elsize memop n pair (regsize :: 'regsize::len itself) s__arg t__arg t2)) cheri_invariant"
  by (unfold execute_aarch64_instrs_memory_exclusive_single_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ldaxr_aarch64_instrs_memory_exclusive_single_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ldaxr_aarch64_instrs_memory_exclusive_single Rt Rn Rt2 o0 Rs L b__0)) cheri_invariant"
  by (unfold decode_ldaxr_aarch64_instrs_memory_exclusive_single_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ldaxrb_aarch64_instrs_memory_exclusive_single_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ldaxrb_aarch64_instrs_memory_exclusive_single Rt Rn Rt2 o0 Rs L b__0)) cheri_invariant"
  by (unfold decode_ldaxrb_aarch64_instrs_memory_exclusive_single_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ldaxrh_aarch64_instrs_memory_exclusive_single_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ldaxrh_aarch64_instrs_memory_exclusive_single Rt Rn Rt2 o0 Rs L b__0)) cheri_invariant"
  by (unfold decode_ldaxrh_aarch64_instrs_memory_exclusive_single_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ldclr_aarch64_instrs_memory_atomicops_ld_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ldclr_aarch64_instrs_memory_atomicops_ld Rt Rn opc Rs R A b__0)) cheri_invariant"
  by (unfold decode_ldclr_aarch64_instrs_memory_atomicops_ld_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ldclrb_aarch64_instrs_memory_atomicops_ld_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ldclrb_aarch64_instrs_memory_atomicops_ld Rt Rn opc Rs R A b__0)) cheri_invariant"
  by (unfold decode_ldclrb_aarch64_instrs_memory_atomicops_ld_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ldclrh_aarch64_instrs_memory_atomicops_ld_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ldclrh_aarch64_instrs_memory_atomicops_ld Rt Rn opc Rs R A b__0)) cheri_invariant"
  by (unfold decode_ldclrh_aarch64_instrs_memory_atomicops_ld_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ldeor_aarch64_instrs_memory_atomicops_ld_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ldeor_aarch64_instrs_memory_atomicops_ld Rt Rn opc Rs R A b__0)) cheri_invariant"
  by (unfold decode_ldeor_aarch64_instrs_memory_atomicops_ld_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ldeorb_aarch64_instrs_memory_atomicops_ld_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ldeorb_aarch64_instrs_memory_atomicops_ld Rt Rn opc Rs R A b__0)) cheri_invariant"
  by (unfold decode_ldeorb_aarch64_instrs_memory_atomicops_ld_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ldeorh_aarch64_instrs_memory_atomicops_ld_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ldeorh_aarch64_instrs_memory_atomicops_ld Rt Rn opc Rs R A b__0)) cheri_invariant"
  by (unfold decode_ldeorh_aarch64_instrs_memory_atomicops_ld_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ldlar_aarch64_instrs_memory_ordered_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ldlar_aarch64_instrs_memory_ordered Rt Rn Rt2 o0 Rs L b__0)) cheri_invariant"
  by (unfold decode_ldlar_aarch64_instrs_memory_ordered_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ldlarb_aarch64_instrs_memory_ordered_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ldlarb_aarch64_instrs_memory_ordered Rt Rn Rt2 o0 Rs L b__0)) cheri_invariant"
  by (unfold decode_ldlarb_aarch64_instrs_memory_ordered_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ldlarh_aarch64_instrs_memory_ordered_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ldlarh_aarch64_instrs_memory_ordered Rt Rn Rt2 o0 Rs L b__0)) cheri_invariant"
  by (unfold decode_ldlarh_aarch64_instrs_memory_ordered_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_aarch64_instrs_memory_pair_simdfp_no_alloc_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_aarch64_instrs_memory_pair_simdfp_no_alloc acctype (datasize :: 'datasize::len itself) memop n offset postindex t__arg t2 wback)) cheri_invariant"
  by (unfold execute_aarch64_instrs_memory_pair_simdfp_no_alloc_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ldnp_fpsimd_aarch64_instrs_memory_pair_simdfp_no_alloc_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ldnp_fpsimd_aarch64_instrs_memory_pair_simdfp_no_alloc Rt Rn Rt2 imm7 L b__0)) cheri_invariant"
  by (unfold decode_ldnp_fpsimd_aarch64_instrs_memory_pair_simdfp_no_alloc_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_aarch64_instrs_memory_pair_general_no_alloc_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_aarch64_instrs_memory_pair_general_no_alloc acctype (datasize :: 'datasize::len itself) memop n offset postindex t__arg t2 wback)) cheri_invariant"
  by (unfold execute_aarch64_instrs_memory_pair_general_no_alloc_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ldnp_gen_aarch64_instrs_memory_pair_general_no_alloc_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ldnp_gen_aarch64_instrs_memory_pair_general_no_alloc Rt Rn Rt2 imm7 L b__0)) cheri_invariant"
  by (unfold decode_ldnp_gen_aarch64_instrs_memory_pair_general_no_alloc_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_aarch64_instrs_memory_pair_simdfp_post_idx_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_aarch64_instrs_memory_pair_simdfp_post_idx acctype (datasize :: 'datasize::len itself) memop n offset postindex t__arg t2 wback)) cheri_invariant"
  by (unfold execute_aarch64_instrs_memory_pair_simdfp_post_idx_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ldp_fpsimd_aarch64_instrs_memory_pair_simdfp_offset_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ldp_fpsimd_aarch64_instrs_memory_pair_simdfp_offset Rt Rn Rt2 imm7 L b__0)) cheri_invariant"
  by (unfold decode_ldp_fpsimd_aarch64_instrs_memory_pair_simdfp_offset_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ldp_fpsimd_aarch64_instrs_memory_pair_simdfp_post_idx_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ldp_fpsimd_aarch64_instrs_memory_pair_simdfp_post_idx Rt Rn Rt2 imm7 L b__0)) cheri_invariant"
  by (unfold decode_ldp_fpsimd_aarch64_instrs_memory_pair_simdfp_post_idx_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ldp_fpsimd_aarch64_instrs_memory_pair_simdfp_pre_idx_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ldp_fpsimd_aarch64_instrs_memory_pair_simdfp_pre_idx Rt Rn Rt2 imm7 L b__0)) cheri_invariant"
  by (unfold decode_ldp_fpsimd_aarch64_instrs_memory_pair_simdfp_pre_idx_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_aarch64_instrs_memory_pair_general_post_idx_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_aarch64_instrs_memory_pair_general_post_idx acctype (datasize :: 'datasize::len itself) memop n offset postindex is_signed t__arg t2 wback__arg)) cheri_invariant"
  by (unfold execute_aarch64_instrs_memory_pair_general_post_idx_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ldp_gen_aarch64_instrs_memory_pair_general_offset_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ldp_gen_aarch64_instrs_memory_pair_general_offset Rt Rn Rt2 imm7 L b__0)) cheri_invariant"
  by (unfold decode_ldp_gen_aarch64_instrs_memory_pair_general_offset_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ldp_gen_aarch64_instrs_memory_pair_general_post_idx_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ldp_gen_aarch64_instrs_memory_pair_general_post_idx Rt Rn Rt2 imm7 L b__0)) cheri_invariant"
  by (unfold decode_ldp_gen_aarch64_instrs_memory_pair_general_post_idx_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ldp_gen_aarch64_instrs_memory_pair_general_pre_idx_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ldp_gen_aarch64_instrs_memory_pair_general_pre_idx Rt Rn Rt2 imm7 L b__0)) cheri_invariant"
  by (unfold decode_ldp_gen_aarch64_instrs_memory_pair_general_pre_idx_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ldpsw_aarch64_instrs_memory_pair_general_offset_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ldpsw_aarch64_instrs_memory_pair_general_offset Rt Rn Rt2 imm7 L b__0)) cheri_invariant"
  by (unfold decode_ldpsw_aarch64_instrs_memory_pair_general_offset_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ldpsw_aarch64_instrs_memory_pair_general_post_idx_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ldpsw_aarch64_instrs_memory_pair_general_post_idx Rt Rn Rt2 imm7 L b__0)) cheri_invariant"
  by (unfold decode_ldpsw_aarch64_instrs_memory_pair_general_post_idx_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ldpsw_aarch64_instrs_memory_pair_general_pre_idx_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ldpsw_aarch64_instrs_memory_pair_general_pre_idx Rt Rn Rt2 imm7 L b__0)) cheri_invariant"
  by (unfold decode_ldpsw_aarch64_instrs_memory_pair_general_pre_idx_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_aarch64_instrs_memory_single_simdfp_immediate_signed_post_idx_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_aarch64_instrs_memory_single_simdfp_immediate_signed_post_idx acctype (datasize :: 'datasize::len itself) memop n offset postindex t__arg wback)) cheri_invariant"
  by (unfold execute_aarch64_instrs_memory_single_simdfp_immediate_signed_post_idx_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ldr_imm_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_post_idx_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ldr_imm_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_post_idx Rt Rn imm9 b__0 b__1)) cheri_invariant"
  by (unfold decode_ldr_imm_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_post_idx_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ldr_imm_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_pre_idx_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ldr_imm_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_pre_idx Rt Rn imm9 b__0 b__1)) cheri_invariant"
  by (unfold decode_ldr_imm_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_pre_idx_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ldr_imm_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_unsigned_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ldr_imm_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_unsigned Rt Rn imm12 b__0 b__1)) cheri_invariant"
  by (unfold decode_ldr_imm_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_unsigned_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_aarch64_instrs_memory_single_general_immediate_signed_post_idx_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_aarch64_instrs_memory_single_general_immediate_signed_post_idx acctype (datasize :: 'datasize::len itself) memop n offset postindex (regsize :: 'regsize::len itself) is_signed t__arg wback__arg)) cheri_invariant"
  by (unfold execute_aarch64_instrs_memory_single_general_immediate_signed_post_idx_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ldr_imm_gen_aarch64_instrs_memory_single_general_immediate_signed_post_idx_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ldr_imm_gen_aarch64_instrs_memory_single_general_immediate_signed_post_idx Rt Rn imm9 b__0 b__1)) cheri_invariant"
  by (unfold decode_ldr_imm_gen_aarch64_instrs_memory_single_general_immediate_signed_post_idx_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ldr_imm_gen_aarch64_instrs_memory_single_general_immediate_signed_pre_idx_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ldr_imm_gen_aarch64_instrs_memory_single_general_immediate_signed_pre_idx Rt Rn imm9 b__0 b__1)) cheri_invariant"
  by (unfold decode_ldr_imm_gen_aarch64_instrs_memory_single_general_immediate_signed_pre_idx_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ldr_imm_gen_aarch64_instrs_memory_single_general_immediate_unsigned_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ldr_imm_gen_aarch64_instrs_memory_single_general_immediate_unsigned Rt Rn imm12 b__0 b__1)) cheri_invariant"
  by (unfold decode_ldr_imm_gen_aarch64_instrs_memory_single_general_immediate_unsigned_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_aarch64_instrs_memory_literal_simdfp_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_aarch64_instrs_memory_literal_simdfp offset l__44 t__arg)) cheri_invariant"
  by (unfold execute_aarch64_instrs_memory_literal_simdfp_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ldr_lit_fpsimd_aarch64_instrs_memory_literal_simdfp_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ldr_lit_fpsimd_aarch64_instrs_memory_literal_simdfp Rt imm19 opc)) cheri_invariant"
  by (unfold decode_ldr_lit_fpsimd_aarch64_instrs_memory_literal_simdfp_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_aarch64_instrs_memory_literal_general_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_aarch64_instrs_memory_literal_general memop offset is_signed l__200 t__arg)) cheri_invariant"
  by (unfold execute_aarch64_instrs_memory_literal_general_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ldr_lit_gen_aarch64_instrs_memory_literal_general_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ldr_lit_gen_aarch64_instrs_memory_literal_general Rt imm19 opc)) cheri_invariant"
  by (unfold decode_ldr_lit_gen_aarch64_instrs_memory_literal_general_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_aarch64_instrs_memory_single_simdfp_register_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_aarch64_instrs_memory_single_simdfp_register acctype (datasize :: 'datasize::len itself) extend_type m memop n postindex shift t__arg wback)) cheri_invariant"
  by (unfold execute_aarch64_instrs_memory_single_simdfp_register_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ldr_reg_fpsimd_aarch64_instrs_memory_single_simdfp_register_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ldr_reg_fpsimd_aarch64_instrs_memory_single_simdfp_register Rt Rn S option_name Rm b__0 b__1)) cheri_invariant"
  by (unfold decode_ldr_reg_fpsimd_aarch64_instrs_memory_single_simdfp_register_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_aarch64_instrs_memory_single_general_register_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_aarch64_instrs_memory_single_general_register acctype (datasize :: 'datasize::len itself) extend_type m memop n postindex (regsize :: 'regsize::len itself) shift is_signed t__arg wback__arg)) cheri_invariant"
  by (unfold execute_aarch64_instrs_memory_single_general_register_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ldr_reg_gen_aarch64_instrs_memory_single_general_register_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ldr_reg_gen_aarch64_instrs_memory_single_general_register Rt Rn S option_name Rm b__0 b__1)) cheri_invariant"
  by (unfold decode_ldr_reg_gen_aarch64_instrs_memory_single_general_register_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ldrb_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ldrb_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx Rt Rn imm9 b__0 b__1)) cheri_invariant"
  by (unfold decode_ldrb_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ldrb_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ldrb_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx Rt Rn imm9 b__0 b__1)) cheri_invariant"
  by (unfold decode_ldrb_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ldrb_imm_aarch64_instrs_memory_single_general_immediate_unsigned_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ldrb_imm_aarch64_instrs_memory_single_general_immediate_unsigned Rt Rn imm12 b__0 b__1)) cheri_invariant"
  by (unfold decode_ldrb_imm_aarch64_instrs_memory_single_general_immediate_unsigned_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ldrb_reg_aarch64_instrs_memory_single_general_register_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ldrb_reg_aarch64_instrs_memory_single_general_register Rt Rn S option_name Rm b__0 b__1)) cheri_invariant"
  by (unfold decode_ldrb_reg_aarch64_instrs_memory_single_general_register_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ldrh_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ldrh_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx Rt Rn imm9 b__0 b__1)) cheri_invariant"
  by (unfold decode_ldrh_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ldrh_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ldrh_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx Rt Rn imm9 b__0 b__1)) cheri_invariant"
  by (unfold decode_ldrh_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ldrh_imm_aarch64_instrs_memory_single_general_immediate_unsigned_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ldrh_imm_aarch64_instrs_memory_single_general_immediate_unsigned Rt Rn imm12 b__0 b__1)) cheri_invariant"
  by (unfold decode_ldrh_imm_aarch64_instrs_memory_single_general_immediate_unsigned_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ldrh_reg_aarch64_instrs_memory_single_general_register_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ldrh_reg_aarch64_instrs_memory_single_general_register Rt Rn S option_name Rm b__0 b__1)) cheri_invariant"
  by (unfold decode_ldrh_reg_aarch64_instrs_memory_single_general_register_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ldrsb_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ldrsb_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx Rt Rn imm9 b__0 b__1)) cheri_invariant"
  by (unfold decode_ldrsb_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ldrsb_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ldrsb_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx Rt Rn imm9 b__0 b__1)) cheri_invariant"
  by (unfold decode_ldrsb_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ldrsb_imm_aarch64_instrs_memory_single_general_immediate_unsigned_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ldrsb_imm_aarch64_instrs_memory_single_general_immediate_unsigned Rt Rn imm12 b__0 b__1)) cheri_invariant"
  by (unfold decode_ldrsb_imm_aarch64_instrs_memory_single_general_immediate_unsigned_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ldrsb_reg_aarch64_instrs_memory_single_general_register_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ldrsb_reg_aarch64_instrs_memory_single_general_register Rt Rn S option_name Rm b__0 b__1)) cheri_invariant"
  by (unfold decode_ldrsb_reg_aarch64_instrs_memory_single_general_register_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ldrsh_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ldrsh_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx Rt Rn imm9 b__0 b__1)) cheri_invariant"
  by (unfold decode_ldrsh_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ldrsh_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ldrsh_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx Rt Rn imm9 b__0 b__1)) cheri_invariant"
  by (unfold decode_ldrsh_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ldrsh_imm_aarch64_instrs_memory_single_general_immediate_unsigned_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ldrsh_imm_aarch64_instrs_memory_single_general_immediate_unsigned Rt Rn imm12 b__0 b__1)) cheri_invariant"
  by (unfold decode_ldrsh_imm_aarch64_instrs_memory_single_general_immediate_unsigned_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ldrsh_reg_aarch64_instrs_memory_single_general_register_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ldrsh_reg_aarch64_instrs_memory_single_general_register Rt Rn S option_name Rm b__0 b__1)) cheri_invariant"
  by (unfold decode_ldrsh_reg_aarch64_instrs_memory_single_general_register_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ldrsw_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ldrsw_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx Rt Rn imm9 b__0 b__1)) cheri_invariant"
  by (unfold decode_ldrsw_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ldrsw_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ldrsw_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx Rt Rn imm9 b__0 b__1)) cheri_invariant"
  by (unfold decode_ldrsw_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ldrsw_imm_aarch64_instrs_memory_single_general_immediate_unsigned_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ldrsw_imm_aarch64_instrs_memory_single_general_immediate_unsigned Rt Rn imm12 b__0 b__1)) cheri_invariant"
  by (unfold decode_ldrsw_imm_aarch64_instrs_memory_single_general_immediate_unsigned_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ldrsw_lit_aarch64_instrs_memory_literal_general_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ldrsw_lit_aarch64_instrs_memory_literal_general Rt imm19 opc)) cheri_invariant"
  by (unfold decode_ldrsw_lit_aarch64_instrs_memory_literal_general_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ldrsw_reg_aarch64_instrs_memory_single_general_register_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ldrsw_reg_aarch64_instrs_memory_single_general_register Rt Rn S option_name Rm b__0 b__1)) cheri_invariant"
  by (unfold decode_ldrsw_reg_aarch64_instrs_memory_single_general_register_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ldset_aarch64_instrs_memory_atomicops_ld_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ldset_aarch64_instrs_memory_atomicops_ld Rt Rn opc Rs R A b__0)) cheri_invariant"
  by (unfold decode_ldset_aarch64_instrs_memory_atomicops_ld_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ldsetb_aarch64_instrs_memory_atomicops_ld_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ldsetb_aarch64_instrs_memory_atomicops_ld Rt Rn opc Rs R A b__0)) cheri_invariant"
  by (unfold decode_ldsetb_aarch64_instrs_memory_atomicops_ld_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ldseth_aarch64_instrs_memory_atomicops_ld_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ldseth_aarch64_instrs_memory_atomicops_ld Rt Rn opc Rs R A b__0)) cheri_invariant"
  by (unfold decode_ldseth_aarch64_instrs_memory_atomicops_ld_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ldsmax_aarch64_instrs_memory_atomicops_ld_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ldsmax_aarch64_instrs_memory_atomicops_ld Rt Rn opc Rs R A b__0)) cheri_invariant"
  by (unfold decode_ldsmax_aarch64_instrs_memory_atomicops_ld_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ldsmaxb_aarch64_instrs_memory_atomicops_ld_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ldsmaxb_aarch64_instrs_memory_atomicops_ld Rt Rn opc Rs R A b__0)) cheri_invariant"
  by (unfold decode_ldsmaxb_aarch64_instrs_memory_atomicops_ld_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ldsmaxh_aarch64_instrs_memory_atomicops_ld_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ldsmaxh_aarch64_instrs_memory_atomicops_ld Rt Rn opc Rs R A b__0)) cheri_invariant"
  by (unfold decode_ldsmaxh_aarch64_instrs_memory_atomicops_ld_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ldsmin_aarch64_instrs_memory_atomicops_ld_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ldsmin_aarch64_instrs_memory_atomicops_ld Rt Rn opc Rs R A b__0)) cheri_invariant"
  by (unfold decode_ldsmin_aarch64_instrs_memory_atomicops_ld_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ldsminb_aarch64_instrs_memory_atomicops_ld_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ldsminb_aarch64_instrs_memory_atomicops_ld Rt Rn opc Rs R A b__0)) cheri_invariant"
  by (unfold decode_ldsminb_aarch64_instrs_memory_atomicops_ld_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ldsminh_aarch64_instrs_memory_atomicops_ld_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ldsminh_aarch64_instrs_memory_atomicops_ld Rt Rn opc Rs R A b__0)) cheri_invariant"
  by (unfold decode_ldsminh_aarch64_instrs_memory_atomicops_ld_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv acctype (datasize :: 'datasize::len itself) memop n offset postindex (regsize :: 'regsize::len itself) is_signed t__arg wback__arg)) cheri_invariant"
  by (unfold execute_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ldtr_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ldtr_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv Rt Rn imm9 b__0 b__1)) cheri_invariant"
  by (unfold decode_ldtr_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ldtrb_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ldtrb_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv Rt Rn imm9 b__0 b__1)) cheri_invariant"
  by (unfold decode_ldtrb_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ldtrh_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ldtrh_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv Rt Rn imm9 b__0 b__1)) cheri_invariant"
  by (unfold decode_ldtrh_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ldtrsb_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ldtrsb_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv Rt Rn imm9 b__0 b__1)) cheri_invariant"
  by (unfold decode_ldtrsb_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ldtrsh_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ldtrsh_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv Rt Rn imm9 b__0 b__1)) cheri_invariant"
  by (unfold decode_ldtrsh_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ldtrsw_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ldtrsw_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv Rt Rn imm9 b__0 b__1)) cheri_invariant"
  by (unfold decode_ldtrsw_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ldumax_aarch64_instrs_memory_atomicops_ld_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ldumax_aarch64_instrs_memory_atomicops_ld Rt Rn opc Rs R A b__0)) cheri_invariant"
  by (unfold decode_ldumax_aarch64_instrs_memory_atomicops_ld_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ldumaxb_aarch64_instrs_memory_atomicops_ld_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ldumaxb_aarch64_instrs_memory_atomicops_ld Rt Rn opc Rs R A b__0)) cheri_invariant"
  by (unfold decode_ldumaxb_aarch64_instrs_memory_atomicops_ld_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ldumaxh_aarch64_instrs_memory_atomicops_ld_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ldumaxh_aarch64_instrs_memory_atomicops_ld Rt Rn opc Rs R A b__0)) cheri_invariant"
  by (unfold decode_ldumaxh_aarch64_instrs_memory_atomicops_ld_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ldumin_aarch64_instrs_memory_atomicops_ld_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ldumin_aarch64_instrs_memory_atomicops_ld Rt Rn opc Rs R A b__0)) cheri_invariant"
  by (unfold decode_ldumin_aarch64_instrs_memory_atomicops_ld_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_lduminb_aarch64_instrs_memory_atomicops_ld_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_lduminb_aarch64_instrs_memory_atomicops_ld Rt Rn opc Rs R A b__0)) cheri_invariant"
  by (unfold decode_lduminb_aarch64_instrs_memory_atomicops_ld_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_lduminh_aarch64_instrs_memory_atomicops_ld_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_lduminh_aarch64_instrs_memory_atomicops_ld Rt Rn opc Rs R A b__0)) cheri_invariant"
  by (unfold decode_lduminh_aarch64_instrs_memory_atomicops_ld_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_aarch64_instrs_memory_single_simdfp_immediate_signed_offset_normal_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_aarch64_instrs_memory_single_simdfp_immediate_signed_offset_normal acctype (datasize :: 'datasize::len itself) memop n offset postindex t__arg wback)) cheri_invariant"
  by (unfold execute_aarch64_instrs_memory_single_simdfp_immediate_signed_offset_normal_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ldur_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_offset_normal_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ldur_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_offset_normal Rt Rn imm9 b__0 b__1)) cheri_invariant"
  by (unfold decode_ldur_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_offset_normal_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_aarch64_instrs_memory_single_general_immediate_signed_offset_normal_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_aarch64_instrs_memory_single_general_immediate_signed_offset_normal acctype (datasize :: 'datasize::len itself) memop n offset postindex (regsize :: 'regsize::len itself) is_signed t__arg wback__arg)) cheri_invariant"
  by (unfold execute_aarch64_instrs_memory_single_general_immediate_signed_offset_normal_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ldur_gen_aarch64_instrs_memory_single_general_immediate_signed_offset_normal_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ldur_gen_aarch64_instrs_memory_single_general_immediate_signed_offset_normal Rt Rn imm9 b__0 b__1)) cheri_invariant"
  by (unfold decode_ldur_gen_aarch64_instrs_memory_single_general_immediate_signed_offset_normal_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ldurb_aarch64_instrs_memory_single_general_immediate_signed_offset_normal_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ldurb_aarch64_instrs_memory_single_general_immediate_signed_offset_normal Rt Rn imm9 b__0 b__1)) cheri_invariant"
  by (unfold decode_ldurb_aarch64_instrs_memory_single_general_immediate_signed_offset_normal_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ldurh_aarch64_instrs_memory_single_general_immediate_signed_offset_normal_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ldurh_aarch64_instrs_memory_single_general_immediate_signed_offset_normal Rt Rn imm9 b__0 b__1)) cheri_invariant"
  by (unfold decode_ldurh_aarch64_instrs_memory_single_general_immediate_signed_offset_normal_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ldursb_aarch64_instrs_memory_single_general_immediate_signed_offset_normal_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ldursb_aarch64_instrs_memory_single_general_immediate_signed_offset_normal Rt Rn imm9 b__0 b__1)) cheri_invariant"
  by (unfold decode_ldursb_aarch64_instrs_memory_single_general_immediate_signed_offset_normal_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ldursh_aarch64_instrs_memory_single_general_immediate_signed_offset_normal_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ldursh_aarch64_instrs_memory_single_general_immediate_signed_offset_normal Rt Rn imm9 b__0 b__1)) cheri_invariant"
  by (unfold decode_ldursh_aarch64_instrs_memory_single_general_immediate_signed_offset_normal_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ldursw_aarch64_instrs_memory_single_general_immediate_signed_offset_normal_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ldursw_aarch64_instrs_memory_single_general_immediate_signed_offset_normal Rt Rn imm9 b__0 b__1)) cheri_invariant"
  by (unfold decode_ldursw_aarch64_instrs_memory_single_general_immediate_signed_offset_normal_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ldxp_aarch64_instrs_memory_exclusive_pair_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ldxp_aarch64_instrs_memory_exclusive_pair Rt Rn Rt2 o0 Rs L b__0)) cheri_invariant"
  by (unfold decode_ldxp_aarch64_instrs_memory_exclusive_pair_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ldxr_aarch64_instrs_memory_exclusive_single_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ldxr_aarch64_instrs_memory_exclusive_single Rt Rn Rt2 o0 Rs L b__0)) cheri_invariant"
  by (unfold decode_ldxr_aarch64_instrs_memory_exclusive_single_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ldxrb_aarch64_instrs_memory_exclusive_single_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ldxrb_aarch64_instrs_memory_exclusive_single Rt Rn Rt2 o0 Rs L b__0)) cheri_invariant"
  by (unfold decode_ldxrb_aarch64_instrs_memory_exclusive_single_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ldxrh_aarch64_instrs_memory_exclusive_single_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ldxrh_aarch64_instrs_memory_exclusive_single Rt Rn Rt2 o0 Rs L b__0)) cheri_invariant"
  by (unfold decode_ldxrh_aarch64_instrs_memory_exclusive_single_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_aarch64_instrs_system_register_system_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_aarch64_instrs_system_register_system read sys_crm sys_crn sys_op0 sys_op1 sys_op2 t__arg)) cheri_invariant"
  by (unfold execute_aarch64_instrs_system_register_system_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_mrs_aarch64_instrs_system_register_system_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_mrs_aarch64_instrs_system_register_system Rt op2 CRm CRn op1 o0 L)) cheri_invariant"
  by (unfold decode_mrs_aarch64_instrs_system_register_system_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_msr_reg_aarch64_instrs_system_register_system_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_msr_reg_aarch64_instrs_system_register_system Rt op2 CRm CRn op1 o0 L)) cheri_invariant"
  by (unfold decode_msr_reg_aarch64_instrs_system_register_system_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_aarch64_instrs_memory_single_general_immediate_unsigned_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_aarch64_instrs_memory_single_general_immediate_unsigned acctype (datasize :: 'datasize::len itself) memop n offset postindex (regsize :: 'regsize::len itself) is_signed t__arg wback__arg)) cheri_invariant"
  by (unfold execute_aarch64_instrs_memory_single_general_immediate_unsigned_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_prfm_imm_aarch64_instrs_memory_single_general_immediate_unsigned_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_prfm_imm_aarch64_instrs_memory_single_general_immediate_unsigned Rt Rn imm12 b__0 b__1)) cheri_invariant"
  by (unfold decode_prfm_imm_aarch64_instrs_memory_single_general_immediate_unsigned_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_prfm_lit_aarch64_instrs_memory_literal_general_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_prfm_lit_aarch64_instrs_memory_literal_general Rt imm19 opc)) cheri_invariant"
  by (unfold decode_prfm_lit_aarch64_instrs_memory_literal_general_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_prfm_reg_aarch64_instrs_memory_single_general_register_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_prfm_reg_aarch64_instrs_memory_single_general_register Rt Rn S option_name Rm b__0 b__1)) cheri_invariant"
  by (unfold decode_prfm_reg_aarch64_instrs_memory_single_general_register_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_prfum_aarch64_instrs_memory_single_general_immediate_signed_offset_normal_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_prfum_aarch64_instrs_memory_single_general_immediate_signed_offset_normal Rt Rn imm9 b__0 b__1)) cheri_invariant"
  by (unfold decode_prfum_aarch64_instrs_memory_single_general_immediate_signed_offset_normal_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_ret_aarch64_instrs_branch_unconditional_register_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_ret_aarch64_instrs_branch_unconditional_register Rm Rn M A op Z)) cheri_invariant"
  by (unfold decode_ret_aarch64_instrs_branch_unconditional_register_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_reta_aarch64_instrs_branch_unconditional_register_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_reta_aarch64_instrs_branch_unconditional_register Rm Rn M A op Z)) cheri_invariant"
  by (unfold decode_reta_aarch64_instrs_branch_unconditional_register_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_st1_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_st1_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb Rt Rn b__0 opcode L b__1)) cheri_invariant"
  by (unfold decode_st1_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_st1_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_st1_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc Rt Rn b__0 opcode Rm L b__1)) cheri_invariant"
  by (unfold decode_st1_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_st1_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_st1_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb Rt Rn b__0 S b__1 R L b__2)) cheri_invariant"
  by (unfold decode_st1_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_st1_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_st1_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc Rt Rn b__0 S b__1 Rm R L b__2)) cheri_invariant"
  by (unfold decode_st1_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_st2_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_st2_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb Rt Rn b__0 opcode L b__1)) cheri_invariant"
  by (unfold decode_st2_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_st2_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_st2_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc Rt Rn b__0 opcode Rm L b__1)) cheri_invariant"
  by (unfold decode_st2_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_st2_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_st2_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb Rt Rn b__0 S b__1 R L b__2)) cheri_invariant"
  by (unfold decode_st2_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_st2_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_st2_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc Rt Rn b__0 S b__1 Rm R L b__2)) cheri_invariant"
  by (unfold decode_st2_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_st3_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_st3_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb Rt Rn b__0 opcode L b__1)) cheri_invariant"
  by (unfold decode_st3_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_st3_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_st3_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc Rt Rn b__0 opcode Rm L b__1)) cheri_invariant"
  by (unfold decode_st3_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_st3_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_st3_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb Rt Rn b__0 S b__1 R L b__2)) cheri_invariant"
  by (unfold decode_st3_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_st3_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_st3_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc Rt Rn b__0 S b__1 Rm R L b__2)) cheri_invariant"
  by (unfold decode_st3_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_st4_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_st4_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb Rt Rn b__0 opcode L b__1)) cheri_invariant"
  by (unfold decode_st4_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_st4_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_st4_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc Rt Rn b__0 opcode Rm L b__1)) cheri_invariant"
  by (unfold decode_st4_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_st4_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_st4_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb Rt Rn b__0 S b__1 R L b__2)) cheri_invariant"
  by (unfold decode_st4_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_st4_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_st4_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc Rt Rn b__0 S b__1 Rm R L b__2)) cheri_invariant"
  by (unfold decode_st4_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_aarch64_instrs_memory_atomicops_st_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_aarch64_instrs_memory_atomicops_st (datasize :: 'datasize::len itself) ldacctype n op s__arg stacctype)) cheri_invariant"
  by (unfold execute_aarch64_instrs_memory_atomicops_st_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_stadd_aarch64_instrs_memory_atomicops_st_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_stadd_aarch64_instrs_memory_atomicops_st Rn opc o3 Rs R A V b__0)) cheri_invariant"
  by (unfold decode_stadd_aarch64_instrs_memory_atomicops_st_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_staddb_aarch64_instrs_memory_atomicops_st_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_staddb_aarch64_instrs_memory_atomicops_st Rn opc o3 Rs R A V b__0)) cheri_invariant"
  by (unfold decode_staddb_aarch64_instrs_memory_atomicops_st_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_staddh_aarch64_instrs_memory_atomicops_st_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_staddh_aarch64_instrs_memory_atomicops_st Rn opc o3 Rs R A V b__0)) cheri_invariant"
  by (unfold decode_staddh_aarch64_instrs_memory_atomicops_st_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_stclr_aarch64_instrs_memory_atomicops_st_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_stclr_aarch64_instrs_memory_atomicops_st Rn opc o3 Rs R A V b__0)) cheri_invariant"
  by (unfold decode_stclr_aarch64_instrs_memory_atomicops_st_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_stclrb_aarch64_instrs_memory_atomicops_st_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_stclrb_aarch64_instrs_memory_atomicops_st Rn opc o3 Rs R A V b__0)) cheri_invariant"
  by (unfold decode_stclrb_aarch64_instrs_memory_atomicops_st_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_stclrh_aarch64_instrs_memory_atomicops_st_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_stclrh_aarch64_instrs_memory_atomicops_st Rn opc o3 Rs R A V b__0)) cheri_invariant"
  by (unfold decode_stclrh_aarch64_instrs_memory_atomicops_st_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_steor_aarch64_instrs_memory_atomicops_st_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_steor_aarch64_instrs_memory_atomicops_st Rn opc o3 Rs R A V b__0)) cheri_invariant"
  by (unfold decode_steor_aarch64_instrs_memory_atomicops_st_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_steorb_aarch64_instrs_memory_atomicops_st_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_steorb_aarch64_instrs_memory_atomicops_st Rn opc o3 Rs R A V b__0)) cheri_invariant"
  by (unfold decode_steorb_aarch64_instrs_memory_atomicops_st_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_steorh_aarch64_instrs_memory_atomicops_st_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_steorh_aarch64_instrs_memory_atomicops_st Rn opc o3 Rs R A V b__0)) cheri_invariant"
  by (unfold decode_steorh_aarch64_instrs_memory_atomicops_st_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_stllr_aarch64_instrs_memory_ordered_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_stllr_aarch64_instrs_memory_ordered Rt Rn Rt2 o0 Rs L b__0)) cheri_invariant"
  by (unfold decode_stllr_aarch64_instrs_memory_ordered_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_stllrb_aarch64_instrs_memory_ordered_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_stllrb_aarch64_instrs_memory_ordered Rt Rn Rt2 o0 Rs L b__0)) cheri_invariant"
  by (unfold decode_stllrb_aarch64_instrs_memory_ordered_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_stllrh_aarch64_instrs_memory_ordered_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_stllrh_aarch64_instrs_memory_ordered Rt Rn Rt2 o0 Rs L b__0)) cheri_invariant"
  by (unfold decode_stllrh_aarch64_instrs_memory_ordered_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_stlr_aarch64_instrs_memory_ordered_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_stlr_aarch64_instrs_memory_ordered Rt Rn Rt2 o0 Rs L b__0)) cheri_invariant"
  by (unfold decode_stlr_aarch64_instrs_memory_ordered_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_stlrb_aarch64_instrs_memory_ordered_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_stlrb_aarch64_instrs_memory_ordered Rt Rn Rt2 o0 Rs L b__0)) cheri_invariant"
  by (unfold decode_stlrb_aarch64_instrs_memory_ordered_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_stlrh_aarch64_instrs_memory_ordered_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_stlrh_aarch64_instrs_memory_ordered Rt Rn Rt2 o0 Rs L b__0)) cheri_invariant"
  by (unfold decode_stlrh_aarch64_instrs_memory_ordered_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_stlxp_aarch64_instrs_memory_exclusive_pair_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_stlxp_aarch64_instrs_memory_exclusive_pair Rt Rn Rt2 o0 Rs L b__0)) cheri_invariant"
  by (unfold decode_stlxp_aarch64_instrs_memory_exclusive_pair_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_stlxr_aarch64_instrs_memory_exclusive_single_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_stlxr_aarch64_instrs_memory_exclusive_single Rt Rn Rt2 o0 Rs L b__0)) cheri_invariant"
  by (unfold decode_stlxr_aarch64_instrs_memory_exclusive_single_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_stlxrb_aarch64_instrs_memory_exclusive_single_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_stlxrb_aarch64_instrs_memory_exclusive_single Rt Rn Rt2 o0 Rs L b__0)) cheri_invariant"
  by (unfold decode_stlxrb_aarch64_instrs_memory_exclusive_single_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_stlxrh_aarch64_instrs_memory_exclusive_single_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_stlxrh_aarch64_instrs_memory_exclusive_single Rt Rn Rt2 o0 Rs L b__0)) cheri_invariant"
  by (unfold decode_stlxrh_aarch64_instrs_memory_exclusive_single_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_stnp_fpsimd_aarch64_instrs_memory_pair_simdfp_no_alloc_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_stnp_fpsimd_aarch64_instrs_memory_pair_simdfp_no_alloc Rt Rn Rt2 imm7 L b__0)) cheri_invariant"
  by (unfold decode_stnp_fpsimd_aarch64_instrs_memory_pair_simdfp_no_alloc_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_stnp_gen_aarch64_instrs_memory_pair_general_no_alloc_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_stnp_gen_aarch64_instrs_memory_pair_general_no_alloc Rt Rn Rt2 imm7 L b__0)) cheri_invariant"
  by (unfold decode_stnp_gen_aarch64_instrs_memory_pair_general_no_alloc_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_stp_fpsimd_aarch64_instrs_memory_pair_simdfp_offset_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_stp_fpsimd_aarch64_instrs_memory_pair_simdfp_offset Rt Rn Rt2 imm7 L b__0)) cheri_invariant"
  by (unfold decode_stp_fpsimd_aarch64_instrs_memory_pair_simdfp_offset_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_stp_fpsimd_aarch64_instrs_memory_pair_simdfp_post_idx_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_stp_fpsimd_aarch64_instrs_memory_pair_simdfp_post_idx Rt Rn Rt2 imm7 L b__0)) cheri_invariant"
  by (unfold decode_stp_fpsimd_aarch64_instrs_memory_pair_simdfp_post_idx_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_stp_fpsimd_aarch64_instrs_memory_pair_simdfp_pre_idx_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_stp_fpsimd_aarch64_instrs_memory_pair_simdfp_pre_idx Rt Rn Rt2 imm7 L b__0)) cheri_invariant"
  by (unfold decode_stp_fpsimd_aarch64_instrs_memory_pair_simdfp_pre_idx_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_stp_gen_aarch64_instrs_memory_pair_general_offset_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_stp_gen_aarch64_instrs_memory_pair_general_offset Rt Rn Rt2 imm7 L b__0)) cheri_invariant"
  by (unfold decode_stp_gen_aarch64_instrs_memory_pair_general_offset_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_stp_gen_aarch64_instrs_memory_pair_general_post_idx_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_stp_gen_aarch64_instrs_memory_pair_general_post_idx Rt Rn Rt2 imm7 L b__0)) cheri_invariant"
  by (unfold decode_stp_gen_aarch64_instrs_memory_pair_general_post_idx_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_stp_gen_aarch64_instrs_memory_pair_general_pre_idx_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_stp_gen_aarch64_instrs_memory_pair_general_pre_idx Rt Rn Rt2 imm7 L b__0)) cheri_invariant"
  by (unfold decode_stp_gen_aarch64_instrs_memory_pair_general_pre_idx_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_str_imm_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_post_idx_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_str_imm_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_post_idx Rt Rn imm9 b__0 b__1)) cheri_invariant"
  by (unfold decode_str_imm_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_post_idx_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_str_imm_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_pre_idx_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_str_imm_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_pre_idx Rt Rn imm9 b__0 b__1)) cheri_invariant"
  by (unfold decode_str_imm_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_pre_idx_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_str_imm_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_unsigned_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_str_imm_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_unsigned Rt Rn imm12 b__0 b__1)) cheri_invariant"
  by (unfold decode_str_imm_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_unsigned_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_str_imm_gen_aarch64_instrs_memory_single_general_immediate_signed_post_idx_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_str_imm_gen_aarch64_instrs_memory_single_general_immediate_signed_post_idx Rt Rn imm9 b__0 b__1)) cheri_invariant"
  by (unfold decode_str_imm_gen_aarch64_instrs_memory_single_general_immediate_signed_post_idx_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_str_imm_gen_aarch64_instrs_memory_single_general_immediate_signed_pre_idx_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_str_imm_gen_aarch64_instrs_memory_single_general_immediate_signed_pre_idx Rt Rn imm9 b__0 b__1)) cheri_invariant"
  by (unfold decode_str_imm_gen_aarch64_instrs_memory_single_general_immediate_signed_pre_idx_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_str_imm_gen_aarch64_instrs_memory_single_general_immediate_unsigned_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_str_imm_gen_aarch64_instrs_memory_single_general_immediate_unsigned Rt Rn imm12 b__0 b__1)) cheri_invariant"
  by (unfold decode_str_imm_gen_aarch64_instrs_memory_single_general_immediate_unsigned_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_str_reg_fpsimd_aarch64_instrs_memory_single_simdfp_register_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_str_reg_fpsimd_aarch64_instrs_memory_single_simdfp_register Rt Rn S option_name Rm b__0 b__1)) cheri_invariant"
  by (unfold decode_str_reg_fpsimd_aarch64_instrs_memory_single_simdfp_register_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_str_reg_gen_aarch64_instrs_memory_single_general_register_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_str_reg_gen_aarch64_instrs_memory_single_general_register Rt Rn S option_name Rm b__0 b__1)) cheri_invariant"
  by (unfold decode_str_reg_gen_aarch64_instrs_memory_single_general_register_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_strb_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_strb_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx Rt Rn imm9 b__0 b__1)) cheri_invariant"
  by (unfold decode_strb_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_strb_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_strb_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx Rt Rn imm9 b__0 b__1)) cheri_invariant"
  by (unfold decode_strb_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_strb_imm_aarch64_instrs_memory_single_general_immediate_unsigned_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_strb_imm_aarch64_instrs_memory_single_general_immediate_unsigned Rt Rn imm12 b__0 b__1)) cheri_invariant"
  by (unfold decode_strb_imm_aarch64_instrs_memory_single_general_immediate_unsigned_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_strb_reg_aarch64_instrs_memory_single_general_register_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_strb_reg_aarch64_instrs_memory_single_general_register Rt Rn S option_name Rm b__0 b__1)) cheri_invariant"
  by (unfold decode_strb_reg_aarch64_instrs_memory_single_general_register_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_strh_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_strh_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx Rt Rn imm9 b__0 b__1)) cheri_invariant"
  by (unfold decode_strh_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_strh_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_strh_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx Rt Rn imm9 b__0 b__1)) cheri_invariant"
  by (unfold decode_strh_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_strh_imm_aarch64_instrs_memory_single_general_immediate_unsigned_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_strh_imm_aarch64_instrs_memory_single_general_immediate_unsigned Rt Rn imm12 b__0 b__1)) cheri_invariant"
  by (unfold decode_strh_imm_aarch64_instrs_memory_single_general_immediate_unsigned_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_strh_reg_aarch64_instrs_memory_single_general_register_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_strh_reg_aarch64_instrs_memory_single_general_register Rt Rn S option_name Rm b__0 b__1)) cheri_invariant"
  by (unfold decode_strh_reg_aarch64_instrs_memory_single_general_register_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_stset_aarch64_instrs_memory_atomicops_st_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_stset_aarch64_instrs_memory_atomicops_st Rn opc o3 Rs R A V b__0)) cheri_invariant"
  by (unfold decode_stset_aarch64_instrs_memory_atomicops_st_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_stsetb_aarch64_instrs_memory_atomicops_st_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_stsetb_aarch64_instrs_memory_atomicops_st Rn opc o3 Rs R A V b__0)) cheri_invariant"
  by (unfold decode_stsetb_aarch64_instrs_memory_atomicops_st_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_stseth_aarch64_instrs_memory_atomicops_st_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_stseth_aarch64_instrs_memory_atomicops_st Rn opc o3 Rs R A V b__0)) cheri_invariant"
  by (unfold decode_stseth_aarch64_instrs_memory_atomicops_st_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_stsmax_aarch64_instrs_memory_atomicops_st_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_stsmax_aarch64_instrs_memory_atomicops_st Rn opc o3 Rs R A V b__0)) cheri_invariant"
  by (unfold decode_stsmax_aarch64_instrs_memory_atomicops_st_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_stsmaxb_aarch64_instrs_memory_atomicops_st_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_stsmaxb_aarch64_instrs_memory_atomicops_st Rn opc o3 Rs R A V b__0)) cheri_invariant"
  by (unfold decode_stsmaxb_aarch64_instrs_memory_atomicops_st_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_stsmaxh_aarch64_instrs_memory_atomicops_st_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_stsmaxh_aarch64_instrs_memory_atomicops_st Rn opc o3 Rs R A V b__0)) cheri_invariant"
  by (unfold decode_stsmaxh_aarch64_instrs_memory_atomicops_st_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_stsmin_aarch64_instrs_memory_atomicops_st_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_stsmin_aarch64_instrs_memory_atomicops_st Rn opc o3 Rs R A V b__0)) cheri_invariant"
  by (unfold decode_stsmin_aarch64_instrs_memory_atomicops_st_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_stsminb_aarch64_instrs_memory_atomicops_st_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_stsminb_aarch64_instrs_memory_atomicops_st Rn opc o3 Rs R A V b__0)) cheri_invariant"
  by (unfold decode_stsminb_aarch64_instrs_memory_atomicops_st_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_stsminh_aarch64_instrs_memory_atomicops_st_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_stsminh_aarch64_instrs_memory_atomicops_st Rn opc o3 Rs R A V b__0)) cheri_invariant"
  by (unfold decode_stsminh_aarch64_instrs_memory_atomicops_st_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_sttr_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_sttr_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv Rt Rn imm9 b__0 b__1)) cheri_invariant"
  by (unfold decode_sttr_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_sttrb_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_sttrb_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv Rt Rn imm9 b__0 b__1)) cheri_invariant"
  by (unfold decode_sttrb_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_sttrh_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_sttrh_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv Rt Rn imm9 b__0 b__1)) cheri_invariant"
  by (unfold decode_sttrh_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_stumax_aarch64_instrs_memory_atomicops_st_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_stumax_aarch64_instrs_memory_atomicops_st Rn opc o3 Rs R A V b__0)) cheri_invariant"
  by (unfold decode_stumax_aarch64_instrs_memory_atomicops_st_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_stumaxb_aarch64_instrs_memory_atomicops_st_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_stumaxb_aarch64_instrs_memory_atomicops_st Rn opc o3 Rs R A V b__0)) cheri_invariant"
  by (unfold decode_stumaxb_aarch64_instrs_memory_atomicops_st_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_stumaxh_aarch64_instrs_memory_atomicops_st_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_stumaxh_aarch64_instrs_memory_atomicops_st Rn opc o3 Rs R A V b__0)) cheri_invariant"
  by (unfold decode_stumaxh_aarch64_instrs_memory_atomicops_st_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_stumin_aarch64_instrs_memory_atomicops_st_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_stumin_aarch64_instrs_memory_atomicops_st Rn opc o3 Rs R A V b__0)) cheri_invariant"
  by (unfold decode_stumin_aarch64_instrs_memory_atomicops_st_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_stuminb_aarch64_instrs_memory_atomicops_st_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_stuminb_aarch64_instrs_memory_atomicops_st Rn opc o3 Rs R A V b__0)) cheri_invariant"
  by (unfold decode_stuminb_aarch64_instrs_memory_atomicops_st_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_stuminh_aarch64_instrs_memory_atomicops_st_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_stuminh_aarch64_instrs_memory_atomicops_st Rn opc o3 Rs R A V b__0)) cheri_invariant"
  by (unfold decode_stuminh_aarch64_instrs_memory_atomicops_st_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_stur_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_offset_normal_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_stur_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_offset_normal Rt Rn imm9 b__0 b__1)) cheri_invariant"
  by (unfold decode_stur_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_offset_normal_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_stur_gen_aarch64_instrs_memory_single_general_immediate_signed_offset_normal_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_stur_gen_aarch64_instrs_memory_single_general_immediate_signed_offset_normal Rt Rn imm9 b__0 b__1)) cheri_invariant"
  by (unfold decode_stur_gen_aarch64_instrs_memory_single_general_immediate_signed_offset_normal_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_sturb_aarch64_instrs_memory_single_general_immediate_signed_offset_normal_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_sturb_aarch64_instrs_memory_single_general_immediate_signed_offset_normal Rt Rn imm9 b__0 b__1)) cheri_invariant"
  by (unfold decode_sturb_aarch64_instrs_memory_single_general_immediate_signed_offset_normal_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_sturh_aarch64_instrs_memory_single_general_immediate_signed_offset_normal_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_sturh_aarch64_instrs_memory_single_general_immediate_signed_offset_normal Rt Rn imm9 b__0 b__1)) cheri_invariant"
  by (unfold decode_sturh_aarch64_instrs_memory_single_general_immediate_signed_offset_normal_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_stxp_aarch64_instrs_memory_exclusive_pair_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_stxp_aarch64_instrs_memory_exclusive_pair Rt Rn Rt2 o0 Rs L b__0)) cheri_invariant"
  by (unfold decode_stxp_aarch64_instrs_memory_exclusive_pair_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_stxr_aarch64_instrs_memory_exclusive_single_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_stxr_aarch64_instrs_memory_exclusive_single Rt Rn Rt2 o0 Rs L b__0)) cheri_invariant"
  by (unfold decode_stxr_aarch64_instrs_memory_exclusive_single_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_stxrb_aarch64_instrs_memory_exclusive_single_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_stxrb_aarch64_instrs_memory_exclusive_single Rt Rn Rt2 o0 Rs L b__0)) cheri_invariant"
  by (unfold decode_stxrb_aarch64_instrs_memory_exclusive_single_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_stxrh_aarch64_instrs_memory_exclusive_single_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_stxrh_aarch64_instrs_memory_exclusive_single Rt Rn Rt2 o0 Rs L b__0)) cheri_invariant"
  by (unfold decode_stxrh_aarch64_instrs_memory_exclusive_single_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_aarch64_instrs_memory_atomicops_swp_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_aarch64_instrs_memory_atomicops_swp (datasize :: 'datasize::len itself) ldacctype n (regsize :: 'regsize::len itself) s__arg stacctype t__arg)) cheri_invariant"
  by (unfold execute_aarch64_instrs_memory_atomicops_swp_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_swp_aarch64_instrs_memory_atomicops_swp_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_swp_aarch64_instrs_memory_atomicops_swp Rt Rn Rs R A b__0)) cheri_invariant"
  by (unfold decode_swp_aarch64_instrs_memory_atomicops_swp_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_swpb_aarch64_instrs_memory_atomicops_swp_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_swpb_aarch64_instrs_memory_atomicops_swp Rt Rn Rs R A b__0)) cheri_invariant"
  by (unfold decode_swpb_aarch64_instrs_memory_atomicops_swp_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_swph_aarch64_instrs_memory_atomicops_swp_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_swph_aarch64_instrs_memory_atomicops_swp Rt Rn Rs R A b__0)) cheri_invariant"
  by (unfold decode_swph_aarch64_instrs_memory_atomicops_swp_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_aarch64_instrs_system_sysops_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_aarch64_instrs_system_sysops has_result sys_crm sys_crn sys_op0 sys_op1 sys_op2 t__arg)) cheri_invariant"
  by (unfold execute_aarch64_instrs_system_sysops_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_sys_aarch64_instrs_system_sysops_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_sys_aarch64_instrs_system_sysops Rt op2 CRm CRn op1 L)) cheri_invariant"
  by (unfold decode_sys_aarch64_instrs_system_sysops_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_sysl_aarch64_instrs_system_sysops_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_sysl_aarch64_instrs_system_sysops Rt op2 CRm CRn op1 L)) cheri_invariant"
  by (unfold decode_sysl_aarch64_instrs_system_sysops_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma execute_aarch64_instrs_branch_conditional_test_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (execute_aarch64_instrs_branch_conditional_test bit_pos bit_val (datasize :: 'datasize::len itself) offset t__arg)) cheri_invariant"
  by (unfold execute_aarch64_instrs_branch_conditional_test_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_tbnz_aarch64_instrs_branch_conditional_test_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_tbnz_aarch64_instrs_branch_conditional_test Rt imm14 b40 op b__0)) cheri_invariant"
  by (unfold decode_tbnz_aarch64_instrs_branch_conditional_test_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma decode_tbz_aarch64_instrs_branch_conditional_test_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (decode_tbz_aarch64_instrs_branch_conditional_test Rt imm14 b40 op b__0)) cheri_invariant"
  by (unfold decode_tbz_aarch64_instrs_branch_conditional_test_def bind_assoc liftState_simp comp_def, preserves_invariantI)

lemma DecodeA64_preserves_invariant[runs_preserve_invariantI]:
  "runs_preserve_invariant (liftS (DecodeA64 pc opcode)) cheri_invariant"
  by (unfold DecodeA64_def bind_assoc liftState_simp comp_def, preserves_invariantI)


end
