section \<open>Generated instruction memory check proofs\<close>

theory CHERI_Mem_Properties
imports CHERI_Lemmas
begin

context Morello_Axiom_Automaton
begin

lemma non_mem_exp_R_read[non_mem_expI]:
  "non_mem_exp (R_read idx)"
  by (unfold R_read_def, non_mem_expI)

lemma non_mem_exp_R_set[non_mem_expI]:
  "non_mem_exp (R_set idx c__arg)"
  by (unfold R_set_def, non_mem_expI)

lemma non_mem_exp_BranchTo[non_mem_expI]:
  "non_mem_exp (BranchTo target branch_type)"
  by (unfold BranchTo_def, non_mem_expI)

lemma non_mem_exp_BranchToCapability[non_mem_expI]:
  "non_mem_exp (BranchToCapability target branch_type)"
  by (unfold BranchToCapability_def, non_mem_expI)

lemma non_mem_exp_CELR_set[non_mem_expI]:
  "non_mem_exp (CELR_set el value_name)"
  by (unfold CELR_set_def, non_mem_expI)

lemma non_mem_exp_CELR_set__1[non_mem_expI]:
  "non_mem_exp (CELR_set__1 value_name)"
  by (unfold CELR_set__1_def, non_mem_expI)

lemma non_mem_exp_CVBAR_read[non_mem_expI]:
  "non_mem_exp (CVBAR_read regime)"
  by (unfold CVBAR_read_def, non_mem_expI)

lemma non_mem_exp_CVBAR_read__1[non_mem_expI]:
  "non_mem_exp (CVBAR_read__1 arg0)"
  by (unfold CVBAR_read__1_def, non_mem_expI)

lemma non_mem_exp_ELR_set[non_mem_expI]:
  "non_mem_exp (ELR_set el value_name)"
  by (unfold ELR_set_def, non_mem_expI)

lemma non_mem_exp_ELR_set__1[non_mem_expI]:
  "non_mem_exp (ELR_set__1 value_name)"
  by (unfold ELR_set__1_def, non_mem_expI)

lemma non_mem_exp_PCC_read[non_mem_expI]:
  "non_mem_exp (PCC_read arg0)"
  by (unfold PCC_read_def, non_mem_expI)

lemma non_mem_exp_IsInRestricted[non_mem_expI]:
  "non_mem_exp (IsInRestricted arg0)"
  by (unfold IsInRestricted_def, non_mem_expI)

lemma non_mem_exp_VBAR_read[non_mem_expI]:
  "non_mem_exp (VBAR_read regime)"
  by (unfold VBAR_read_def, non_mem_expI)

lemma non_mem_exp_VBAR_read__1[non_mem_expI]:
  "non_mem_exp (VBAR_read__1 arg0)"
  by (unfold VBAR_read__1_def, non_mem_expI)

lemma non_mem_exp_AArch64_TakeException[non_mem_expI]:
  "non_mem_exp (AArch64_TakeException target_el exception preferred_exception_return vect_offset__arg)"
  by (unfold AArch64_TakeException_def, non_mem_expI)

lemma non_mem_exp_AArch64_SystemAccessTrap[non_mem_expI]:
  "non_mem_exp (AArch64_SystemAccessTrap target_el ec)"
  by (unfold AArch64_SystemAccessTrap_def, non_mem_expI)

lemma non_mem_exp_CapIsSystemAccessEnabled[non_mem_expI]:
  "non_mem_exp (CapIsSystemAccessEnabled arg0)"
  by (unfold CapIsSystemAccessEnabled_def, non_mem_expI)

lemma non_mem_exp_ACTLR_EL1_SysRegRead_56bd4d0367c16236[non_mem_expI]:
  "non_mem_exp (ACTLR_EL1_SysRegRead_56bd4d0367c16236 el op0 op1 CRn op2 CRm)"
  by (unfold ACTLR_EL1_SysRegRead_56bd4d0367c16236_def, non_mem_expI)

lemma non_mem_exp_ACTLR_EL2_SysRegRead_ff23cef1b670b9c7[non_mem_expI]:
  "non_mem_exp (ACTLR_EL2_SysRegRead_ff23cef1b670b9c7 el op0 op1 CRn op2 CRm)"
  by (unfold ACTLR_EL2_SysRegRead_ff23cef1b670b9c7_def, non_mem_expI)

lemma non_mem_exp_ACTLR_EL3_SysRegRead_397e6c0342e2936b[non_mem_expI]:
  "non_mem_exp (ACTLR_EL3_SysRegRead_397e6c0342e2936b el op0 op1 CRn op2 CRm)"
  by (unfold ACTLR_EL3_SysRegRead_397e6c0342e2936b_def, non_mem_expI)

lemma non_mem_exp_AFSR0_EL12_SysRegRead_2488de32a3f38621[non_mem_expI]:
  "non_mem_exp (AFSR0_EL12_SysRegRead_2488de32a3f38621 el op0 op1 CRn op2 CRm)"
  by (unfold AFSR0_EL12_SysRegRead_2488de32a3f38621_def, non_mem_expI)

lemma non_mem_exp_AFSR0_EL1_SysRegRead_80a4a0472e0b9142[non_mem_expI]:
  "non_mem_exp (AFSR0_EL1_SysRegRead_80a4a0472e0b9142 el op0 op1 CRn op2 CRm)"
  by (unfold AFSR0_EL1_SysRegRead_80a4a0472e0b9142_def, non_mem_expI)

lemma non_mem_exp_AFSR0_EL2_SysRegRead_07613e9c4b98061a[non_mem_expI]:
  "non_mem_exp (AFSR0_EL2_SysRegRead_07613e9c4b98061a el op0 op1 CRn op2 CRm)"
  by (unfold AFSR0_EL2_SysRegRead_07613e9c4b98061a_def, non_mem_expI)

lemma non_mem_exp_AFSR0_EL3_SysRegRead_d2e69d7912ca200c[non_mem_expI]:
  "non_mem_exp (AFSR0_EL3_SysRegRead_d2e69d7912ca200c el op0 op1 CRn op2 CRm)"
  by (unfold AFSR0_EL3_SysRegRead_d2e69d7912ca200c_def, non_mem_expI)

lemma non_mem_exp_AFSR1_EL12_SysRegRead_39bb62021df07ecc[non_mem_expI]:
  "non_mem_exp (AFSR1_EL12_SysRegRead_39bb62021df07ecc el op0 op1 CRn op2 CRm)"
  by (unfold AFSR1_EL12_SysRegRead_39bb62021df07ecc_def, non_mem_expI)

lemma non_mem_exp_AFSR1_EL1_SysRegRead_495927b72173c55f[non_mem_expI]:
  "non_mem_exp (AFSR1_EL1_SysRegRead_495927b72173c55f el op0 op1 CRn op2 CRm)"
  by (unfold AFSR1_EL1_SysRegRead_495927b72173c55f_def, non_mem_expI)

lemma non_mem_exp_AFSR1_EL2_SysRegRead_f7cb9a59387f268f[non_mem_expI]:
  "non_mem_exp (AFSR1_EL2_SysRegRead_f7cb9a59387f268f el op0 op1 CRn op2 CRm)"
  by (unfold AFSR1_EL2_SysRegRead_f7cb9a59387f268f_def, non_mem_expI)

lemma non_mem_exp_AFSR1_EL3_SysRegRead_a2ad736ad599f2b2[non_mem_expI]:
  "non_mem_exp (AFSR1_EL3_SysRegRead_a2ad736ad599f2b2 el op0 op1 CRn op2 CRm)"
  by (unfold AFSR1_EL3_SysRegRead_a2ad736ad599f2b2_def, non_mem_expI)

lemma non_mem_exp_AIDR_EL1_SysRegRead_74ea31b1dc6f5c6f[non_mem_expI]:
  "non_mem_exp (AIDR_EL1_SysRegRead_74ea31b1dc6f5c6f el op0 op1 CRn op2 CRm)"
  by (unfold AIDR_EL1_SysRegRead_74ea31b1dc6f5c6f_def, non_mem_expI)

lemma non_mem_exp_AMAIR_EL12_SysRegRead_87964a33cc1ad0ef[non_mem_expI]:
  "non_mem_exp (AMAIR_EL12_SysRegRead_87964a33cc1ad0ef el op0 op1 CRn op2 CRm)"
  by (unfold AMAIR_EL12_SysRegRead_87964a33cc1ad0ef_def, non_mem_expI)

lemma non_mem_exp_AMAIR_EL1_SysRegRead_82d01d3808e04ca3[non_mem_expI]:
  "non_mem_exp (AMAIR_EL1_SysRegRead_82d01d3808e04ca3 el op0 op1 CRn op2 CRm)"
  by (unfold AMAIR_EL1_SysRegRead_82d01d3808e04ca3_def, non_mem_expI)

lemma non_mem_exp_AMAIR_EL2_SysRegRead_3c316bb11b239640[non_mem_expI]:
  "non_mem_exp (AMAIR_EL2_SysRegRead_3c316bb11b239640 el op0 op1 CRn op2 CRm)"
  by (unfold AMAIR_EL2_SysRegRead_3c316bb11b239640_def, non_mem_expI)

lemma non_mem_exp_AMAIR_EL3_SysRegRead_b1547f511477c529[non_mem_expI]:
  "non_mem_exp (AMAIR_EL3_SysRegRead_b1547f511477c529 el op0 op1 CRn op2 CRm)"
  by (unfold AMAIR_EL3_SysRegRead_b1547f511477c529_def, non_mem_expI)

lemma non_mem_exp_CCSIDR_EL1_SysRegRead_210f94b423761d0b[non_mem_expI]:
  "non_mem_exp (CCSIDR_EL1_SysRegRead_210f94b423761d0b el op0 op1 CRn op2 CRm)"
  by (unfold CCSIDR_EL1_SysRegRead_210f94b423761d0b_def, non_mem_expI)

lemma non_mem_exp_CCTLR_EL0_SysRegRead_3baa7e22d96a4ce4[non_mem_expI]:
  "non_mem_exp (CCTLR_EL0_SysRegRead_3baa7e22d96a4ce4 el op0 op1 CRn op2 CRm)"
  by (unfold CCTLR_EL0_SysRegRead_3baa7e22d96a4ce4_def, non_mem_expI)

lemma non_mem_exp_CCTLR_EL12_SysRegRead_e8b17aabd47dc7a1[non_mem_expI]:
  "non_mem_exp (CCTLR_EL12_SysRegRead_e8b17aabd47dc7a1 el op0 op1 CRn op2 CRm)"
  by (unfold CCTLR_EL12_SysRegRead_e8b17aabd47dc7a1_def, non_mem_expI)

lemma non_mem_exp_CCTLR_EL1_SysRegRead_de402a061eecb9b9[non_mem_expI]:
  "non_mem_exp (CCTLR_EL1_SysRegRead_de402a061eecb9b9 el op0 op1 CRn op2 CRm)"
  by (unfold CCTLR_EL1_SysRegRead_de402a061eecb9b9_def, non_mem_expI)

lemma non_mem_exp_CCTLR_EL2_SysRegRead_fca4364f27bb9f9b[non_mem_expI]:
  "non_mem_exp (CCTLR_EL2_SysRegRead_fca4364f27bb9f9b el op0 op1 CRn op2 CRm)"
  by (unfold CCTLR_EL2_SysRegRead_fca4364f27bb9f9b_def, non_mem_expI)

lemma non_mem_exp_CCTLR_EL3_SysRegRead_9121a22ebc361586[non_mem_expI]:
  "non_mem_exp (CCTLR_EL3_SysRegRead_9121a22ebc361586 el op0 op1 CRn op2 CRm)"
  by (unfold CCTLR_EL3_SysRegRead_9121a22ebc361586_def, non_mem_expI)

lemma non_mem_exp_CHCR_EL2_SysRegRead_7d3c39a46321f1a2[non_mem_expI]:
  "non_mem_exp (CHCR_EL2_SysRegRead_7d3c39a46321f1a2 el op0 op1 CRn op2 CRm)"
  by (unfold CHCR_EL2_SysRegRead_7d3c39a46321f1a2_def, non_mem_expI)

lemma non_mem_exp_CLIDR_EL1_SysRegRead_b403ddc99e97c3a8[non_mem_expI]:
  "non_mem_exp (CLIDR_EL1_SysRegRead_b403ddc99e97c3a8 el op0 op1 CRn op2 CRm)"
  by (unfold CLIDR_EL1_SysRegRead_b403ddc99e97c3a8_def, non_mem_expI)

lemma non_mem_exp_CNTFRQ_EL0_SysRegRead_891ca00adf0c3783[non_mem_expI]:
  "non_mem_exp (CNTFRQ_EL0_SysRegRead_891ca00adf0c3783 el op0 op1 CRn op2 CRm)"
  by (unfold CNTFRQ_EL0_SysRegRead_891ca00adf0c3783_def, non_mem_expI)

lemma non_mem_exp_CNTHCTL_EL2_SysRegRead_5f510d633361c720[non_mem_expI]:
  "non_mem_exp (CNTHCTL_EL2_SysRegRead_5f510d633361c720 el op0 op1 CRn op2 CRm)"
  by (unfold CNTHCTL_EL2_SysRegRead_5f510d633361c720_def, non_mem_expI)

lemma non_mem_exp_CNTHP_CTL_EL2_SysRegRead_7103e47839f2c66b[non_mem_expI]:
  "non_mem_exp (CNTHP_CTL_EL2_SysRegRead_7103e47839f2c66b el op0 op1 CRn op2 CRm)"
  by (unfold CNTHP_CTL_EL2_SysRegRead_7103e47839f2c66b_def, non_mem_expI)

lemma non_mem_exp_CNTHP_CVAL_EL2_SysRegRead_e25a0257128c640b[non_mem_expI]:
  "non_mem_exp (CNTHP_CVAL_EL2_SysRegRead_e25a0257128c640b el op0 op1 CRn op2 CRm)"
  by (unfold CNTHP_CVAL_EL2_SysRegRead_e25a0257128c640b_def, non_mem_expI)

lemma non_mem_exp_CNTHP_TVAL_EL2_SysRegRead_d110a1f1616c9f8f[non_mem_expI]:
  "non_mem_exp (CNTHP_TVAL_EL2_SysRegRead_d110a1f1616c9f8f el op0 op1 CRn op2 CRm)"
  by (unfold CNTHP_TVAL_EL2_SysRegRead_d110a1f1616c9f8f_def, non_mem_expI)

lemma non_mem_exp_CNTHV_CTL_EL2_SysRegRead_bc429f3d6b52b800[non_mem_expI]:
  "non_mem_exp (CNTHV_CTL_EL2_SysRegRead_bc429f3d6b52b800 el op0 op1 CRn op2 CRm)"
  by (unfold CNTHV_CTL_EL2_SysRegRead_bc429f3d6b52b800_def, non_mem_expI)

lemma non_mem_exp_CNTHV_CVAL_EL2_SysRegRead_2c78392b89702ca9[non_mem_expI]:
  "non_mem_exp (CNTHV_CVAL_EL2_SysRegRead_2c78392b89702ca9 el op0 op1 CRn op2 CRm)"
  by (unfold CNTHV_CVAL_EL2_SysRegRead_2c78392b89702ca9_def, non_mem_expI)

lemma non_mem_exp_CNTHV_TVAL_EL2_SysRegRead_2464c0e91db55a22[non_mem_expI]:
  "non_mem_exp (CNTHV_TVAL_EL2_SysRegRead_2464c0e91db55a22 el op0 op1 CRn op2 CRm)"
  by (unfold CNTHV_TVAL_EL2_SysRegRead_2464c0e91db55a22_def, non_mem_expI)

lemma non_mem_exp_CNTKCTL_EL12_SysRegRead_c23def3111264258[non_mem_expI]:
  "non_mem_exp (CNTKCTL_EL12_SysRegRead_c23def3111264258 el op0 op1 CRn op2 CRm)"
  by (unfold CNTKCTL_EL12_SysRegRead_c23def3111264258_def, non_mem_expI)

lemma non_mem_exp_CNTKCTL_EL1_SysRegRead_6a6cc900bc3c37df[non_mem_expI]:
  "non_mem_exp (CNTKCTL_EL1_SysRegRead_6a6cc900bc3c37df el op0 op1 CRn op2 CRm)"
  by (unfold CNTKCTL_EL1_SysRegRead_6a6cc900bc3c37df_def, non_mem_expI)

lemma non_mem_exp_CNTPCT_EL0_SysRegRead_579be4c9ef4e6824[non_mem_expI]:
  "non_mem_exp (CNTPCT_EL0_SysRegRead_579be4c9ef4e6824 el op0 op1 CRn op2 CRm)"
  by (unfold CNTPCT_EL0_SysRegRead_579be4c9ef4e6824_def, non_mem_expI)

lemma non_mem_exp_CNTPS_CTL_EL1_SysRegRead_e3bc6e5891147388[non_mem_expI]:
  "non_mem_exp (CNTPS_CTL_EL1_SysRegRead_e3bc6e5891147388 el op0 op1 CRn op2 CRm)"
  by (unfold CNTPS_CTL_EL1_SysRegRead_e3bc6e5891147388_def, non_mem_expI)

lemma non_mem_exp_CNTPS_CVAL_EL1_SysRegRead_3e364bd573c45cae[non_mem_expI]:
  "non_mem_exp (CNTPS_CVAL_EL1_SysRegRead_3e364bd573c45cae el op0 op1 CRn op2 CRm)"
  by (unfold CNTPS_CVAL_EL1_SysRegRead_3e364bd573c45cae_def, non_mem_expI)

lemma non_mem_exp_CNTPS_TVAL_EL1_SysRegRead_0784a7de0899eff0[non_mem_expI]:
  "non_mem_exp (CNTPS_TVAL_EL1_SysRegRead_0784a7de0899eff0 el op0 op1 CRn op2 CRm)"
  by (unfold CNTPS_TVAL_EL1_SysRegRead_0784a7de0899eff0_def, non_mem_expI)

lemma non_mem_exp_CNTP_CTL_EL02_SysRegRead_9d9930274ff7fc36[non_mem_expI]:
  "non_mem_exp (CNTP_CTL_EL02_SysRegRead_9d9930274ff7fc36 el op0 op1 CRn op2 CRm)"
  by (unfold CNTP_CTL_EL02_SysRegRead_9d9930274ff7fc36_def, non_mem_expI)

lemma non_mem_exp_CNTP_CTL_EL0_SysRegRead_47237e002d686ac6[non_mem_expI]:
  "non_mem_exp (CNTP_CTL_EL0_SysRegRead_47237e002d686ac6 el op0 op1 CRn op2 CRm)"
  by (unfold CNTP_CTL_EL0_SysRegRead_47237e002d686ac6_def, non_mem_expI)

lemma non_mem_exp_CNTP_CVAL_EL02_SysRegRead_8377305437cbebb4[non_mem_expI]:
  "non_mem_exp (CNTP_CVAL_EL02_SysRegRead_8377305437cbebb4 el op0 op1 CRn op2 CRm)"
  by (unfold CNTP_CVAL_EL02_SysRegRead_8377305437cbebb4_def, non_mem_expI)

lemma non_mem_exp_CNTP_CVAL_EL0_SysRegRead_4db28ae745612584[non_mem_expI]:
  "non_mem_exp (CNTP_CVAL_EL0_SysRegRead_4db28ae745612584 el op0 op1 CRn op2 CRm)"
  by (unfold CNTP_CVAL_EL0_SysRegRead_4db28ae745612584_def, non_mem_expI)

lemma non_mem_exp_CNTP_TVAL_EL02_SysRegRead_6539005e4eb68283[non_mem_expI]:
  "non_mem_exp (CNTP_TVAL_EL02_SysRegRead_6539005e4eb68283 el op0 op1 CRn op2 CRm)"
  by (unfold CNTP_TVAL_EL02_SysRegRead_6539005e4eb68283_def, non_mem_expI)

lemma non_mem_exp_CNTP_TVAL_EL0_SysRegRead_54cebb7fbc71b9db[non_mem_expI]:
  "non_mem_exp (CNTP_TVAL_EL0_SysRegRead_54cebb7fbc71b9db el op0 op1 CRn op2 CRm)"
  by (unfold CNTP_TVAL_EL0_SysRegRead_54cebb7fbc71b9db_def, non_mem_expI)

lemma non_mem_exp_CNTVCT_EL0_SysRegRead_cd7c8aebed2715e6[non_mem_expI]:
  "non_mem_exp (CNTVCT_EL0_SysRegRead_cd7c8aebed2715e6 el op0 op1 CRn op2 CRm)"
  by (unfold CNTVCT_EL0_SysRegRead_cd7c8aebed2715e6_def, non_mem_expI)

lemma non_mem_exp_CNTVOFF_EL2_SysRegRead_5ca7336b54f14c06[non_mem_expI]:
  "non_mem_exp (CNTVOFF_EL2_SysRegRead_5ca7336b54f14c06 el op0 op1 CRn op2 CRm)"
  by (unfold CNTVOFF_EL2_SysRegRead_5ca7336b54f14c06_def, non_mem_expI)

lemma non_mem_exp_CNTV_CTL_EL02_SysRegRead_4188a8e2bc5c07aa[non_mem_expI]:
  "non_mem_exp (CNTV_CTL_EL02_SysRegRead_4188a8e2bc5c07aa el op0 op1 CRn op2 CRm)"
  by (unfold CNTV_CTL_EL02_SysRegRead_4188a8e2bc5c07aa_def, non_mem_expI)

lemma non_mem_exp_CNTV_CTL_EL0_SysRegRead_bcb2d1b80bdb9c23[non_mem_expI]:
  "non_mem_exp (CNTV_CTL_EL0_SysRegRead_bcb2d1b80bdb9c23 el op0 op1 CRn op2 CRm)"
  by (unfold CNTV_CTL_EL0_SysRegRead_bcb2d1b80bdb9c23_def, non_mem_expI)

lemma non_mem_exp_CNTV_CVAL_EL02_SysRegRead_abd2b9f314cb85b2[non_mem_expI]:
  "non_mem_exp (CNTV_CVAL_EL02_SysRegRead_abd2b9f314cb85b2 el op0 op1 CRn op2 CRm)"
  by (unfold CNTV_CVAL_EL02_SysRegRead_abd2b9f314cb85b2_def, non_mem_expI)

lemma non_mem_exp_CNTV_CVAL_EL0_SysRegRead_54d5eb0bec99456f[non_mem_expI]:
  "non_mem_exp (CNTV_CVAL_EL0_SysRegRead_54d5eb0bec99456f el op0 op1 CRn op2 CRm)"
  by (unfold CNTV_CVAL_EL0_SysRegRead_54d5eb0bec99456f_def, non_mem_expI)

lemma non_mem_exp_CNTV_TVAL_EL02_SysRegRead_f904ccdf39aea128[non_mem_expI]:
  "non_mem_exp (CNTV_TVAL_EL02_SysRegRead_f904ccdf39aea128 el op0 op1 CRn op2 CRm)"
  by (unfold CNTV_TVAL_EL02_SysRegRead_f904ccdf39aea128_def, non_mem_expI)

lemma non_mem_exp_CNTV_TVAL_EL0_SysRegRead_919e73a694090e48[non_mem_expI]:
  "non_mem_exp (CNTV_TVAL_EL0_SysRegRead_919e73a694090e48 el op0 op1 CRn op2 CRm)"
  by (unfold CNTV_TVAL_EL0_SysRegRead_919e73a694090e48_def, non_mem_expI)

lemma non_mem_exp_CONTEXTIDR_EL12_SysRegRead_2aa676fc0cfd631b[non_mem_expI]:
  "non_mem_exp (CONTEXTIDR_EL12_SysRegRead_2aa676fc0cfd631b el op0 op1 CRn op2 CRm)"
  by (unfold CONTEXTIDR_EL12_SysRegRead_2aa676fc0cfd631b_def, non_mem_expI)

lemma non_mem_exp_CONTEXTIDR_EL1_SysRegRead_fa54232c55ea14e3[non_mem_expI]:
  "non_mem_exp (CONTEXTIDR_EL1_SysRegRead_fa54232c55ea14e3 el op0 op1 CRn op2 CRm)"
  by (unfold CONTEXTIDR_EL1_SysRegRead_fa54232c55ea14e3_def, non_mem_expI)

lemma non_mem_exp_CONTEXTIDR_EL2_SysRegRead_f7bf9114ce3113a6[non_mem_expI]:
  "non_mem_exp (CONTEXTIDR_EL2_SysRegRead_f7bf9114ce3113a6 el op0 op1 CRn op2 CRm)"
  by (unfold CONTEXTIDR_EL2_SysRegRead_f7bf9114ce3113a6_def, non_mem_expI)

lemma non_mem_exp_CPACR_EL12_SysRegRead_0f7867518c4e8e99[non_mem_expI]:
  "non_mem_exp (CPACR_EL12_SysRegRead_0f7867518c4e8e99 el op0 op1 CRn op2 CRm)"
  by (unfold CPACR_EL12_SysRegRead_0f7867518c4e8e99_def, non_mem_expI)

lemma non_mem_exp_CPACR_EL1_SysRegRead_63b8f196f3ebba22[non_mem_expI]:
  "non_mem_exp (CPACR_EL1_SysRegRead_63b8f196f3ebba22 el op0 op1 CRn op2 CRm)"
  by (unfold CPACR_EL1_SysRegRead_63b8f196f3ebba22_def, non_mem_expI)

lemma non_mem_exp_CPTR_EL2_SysRegRead_d80843789adc6a43[non_mem_expI]:
  "non_mem_exp (CPTR_EL2_SysRegRead_d80843789adc6a43 el op0 op1 CRn op2 CRm)"
  by (unfold CPTR_EL2_SysRegRead_d80843789adc6a43_def, non_mem_expI)

lemma non_mem_exp_CPTR_EL3_SysRegRead_33cb1e5ec3c99661[non_mem_expI]:
  "non_mem_exp (CPTR_EL3_SysRegRead_33cb1e5ec3c99661 el op0 op1 CRn op2 CRm)"
  by (unfold CPTR_EL3_SysRegRead_33cb1e5ec3c99661_def, non_mem_expI)

lemma non_mem_exp_CSCR_EL3_SysRegRead_3c6b19768f9cd209[non_mem_expI]:
  "non_mem_exp (CSCR_EL3_SysRegRead_3c6b19768f9cd209 el op0 op1 CRn op2 CRm)"
  by (unfold CSCR_EL3_SysRegRead_3c6b19768f9cd209_def, non_mem_expI)

lemma non_mem_exp_CSSELR_EL1_SysRegRead_102b4cddc07c9121[non_mem_expI]:
  "non_mem_exp (CSSELR_EL1_SysRegRead_102b4cddc07c9121 el op0 op1 CRn op2 CRm)"
  by (unfold CSSELR_EL1_SysRegRead_102b4cddc07c9121_def, non_mem_expI)

lemma non_mem_exp_CTR_EL0_SysRegRead_54ef8c769c3c6bba[non_mem_expI]:
  "non_mem_exp (CTR_EL0_SysRegRead_54ef8c769c3c6bba el op0 op1 CRn op2 CRm)"
  by (unfold CTR_EL0_SysRegRead_54ef8c769c3c6bba_def, non_mem_expI)

lemma non_mem_exp_DACR32_EL2_SysRegRead_9571e2946627a596[non_mem_expI]:
  "non_mem_exp (DACR32_EL2_SysRegRead_9571e2946627a596 el op0 op1 CRn op2 CRm)"
  by (unfold DACR32_EL2_SysRegRead_9571e2946627a596_def, non_mem_expI)

lemma non_mem_exp_DAIF_SysRegRead_198f3b46fcf6c8f0[non_mem_expI]:
  "non_mem_exp (DAIF_SysRegRead_198f3b46fcf6c8f0 el op0 op1 CRn op2 CRm)"
  by (unfold DAIF_SysRegRead_198f3b46fcf6c8f0_def, non_mem_expI)

lemma non_mem_exp_DBGAUTHSTATUS_EL1_SysRegRead_6ade6e7a5265bcb7[non_mem_expI]:
  "non_mem_exp (DBGAUTHSTATUS_EL1_SysRegRead_6ade6e7a5265bcb7 el op0 op1 CRn op2 CRm)"
  by (unfold DBGAUTHSTATUS_EL1_SysRegRead_6ade6e7a5265bcb7_def, non_mem_expI)

lemma non_mem_exp_Halt[non_mem_expI]:
  "non_mem_exp (Halt reason)"
  by (unfold Halt_def, non_mem_expI)

lemma non_mem_exp_DBGBCR_EL1_SysRegRead_2d021994672d40d3[non_mem_expI]:
  "non_mem_exp (DBGBCR_EL1_SysRegRead_2d021994672d40d3 el op0 op1 CRn op2 CRm)"
  by (unfold DBGBCR_EL1_SysRegRead_2d021994672d40d3_def, non_mem_expI)

lemma non_mem_exp_DBGBVR_EL1_SysRegRead_dc4a8f61b400622f[non_mem_expI]:
  "non_mem_exp (DBGBVR_EL1_SysRegRead_dc4a8f61b400622f el op0 op1 CRn op2 CRm)"
  by (unfold DBGBVR_EL1_SysRegRead_dc4a8f61b400622f_def, non_mem_expI)

lemma non_mem_exp_DBGCLAIMCLR_EL1_SysRegRead_72ae03c1d5f667da[non_mem_expI]:
  "non_mem_exp (DBGCLAIMCLR_EL1_SysRegRead_72ae03c1d5f667da el op0 op1 CRn op2 CRm)"
  by (unfold DBGCLAIMCLR_EL1_SysRegRead_72ae03c1d5f667da_def, non_mem_expI)

lemma non_mem_exp_DBGCLAIMSET_EL1_SysRegRead_8557cf3b6272a9e8[non_mem_expI]:
  "non_mem_exp (DBGCLAIMSET_EL1_SysRegRead_8557cf3b6272a9e8 el op0 op1 CRn op2 CRm)"
  by (unfold DBGCLAIMSET_EL1_SysRegRead_8557cf3b6272a9e8_def, non_mem_expI)

lemma non_mem_exp_DBGDTRRX_EL0_SysRegRead_e7b48d8296f3b86b[non_mem_expI]:
  "non_mem_exp (DBGDTRRX_EL0_SysRegRead_e7b48d8296f3b86b el op0 op1 CRn op2 CRm)"
  by (unfold DBGDTRRX_EL0_SysRegRead_e7b48d8296f3b86b_def, non_mem_expI)

lemma non_mem_exp_DBGDTR_EL0_read__1[non_mem_expI]:
  "non_mem_exp (DBGDTR_EL0_read__1 arg0)"
  by (unfold DBGDTR_EL0_read__1_def, non_mem_expI)

lemma non_mem_exp_DBGDTR_EL0_SysRegRead_537a006eb82c59aa[non_mem_expI]:
  "non_mem_exp (DBGDTR_EL0_SysRegRead_537a006eb82c59aa el op0 op1 CRn op2 CRm)"
  by (unfold DBGDTR_EL0_SysRegRead_537a006eb82c59aa_def, non_mem_expI)

lemma non_mem_exp_DBGPRCR_EL1_SysRegRead_6b19d62af9619a21[non_mem_expI]:
  "non_mem_exp (DBGPRCR_EL1_SysRegRead_6b19d62af9619a21 el op0 op1 CRn op2 CRm)"
  by (unfold DBGPRCR_EL1_SysRegRead_6b19d62af9619a21_def, non_mem_expI)

lemma non_mem_exp_DBGVCR32_EL2_SysRegRead_7986b2bdf8df010d[non_mem_expI]:
  "non_mem_exp (DBGVCR32_EL2_SysRegRead_7986b2bdf8df010d el op0 op1 CRn op2 CRm)"
  by (unfold DBGVCR32_EL2_SysRegRead_7986b2bdf8df010d_def, non_mem_expI)

lemma non_mem_exp_DBGWCR_EL1_SysRegRead_03139d052b544b2f[non_mem_expI]:
  "non_mem_exp (DBGWCR_EL1_SysRegRead_03139d052b544b2f el op0 op1 CRn op2 CRm)"
  by (unfold DBGWCR_EL1_SysRegRead_03139d052b544b2f_def, non_mem_expI)

lemma non_mem_exp_DBGWVR_EL1_SysRegRead_029de1005ef34888[non_mem_expI]:
  "non_mem_exp (DBGWVR_EL1_SysRegRead_029de1005ef34888 el op0 op1 CRn op2 CRm)"
  by (unfold DBGWVR_EL1_SysRegRead_029de1005ef34888_def, non_mem_expI)

lemma non_mem_exp_DISR_EL1_SysRegRead_d06ce25101dac895[non_mem_expI]:
  "non_mem_exp (DISR_EL1_SysRegRead_d06ce25101dac895 el op0 op1 CRn op2 CRm)"
  by (unfold DISR_EL1_SysRegRead_d06ce25101dac895_def, non_mem_expI)

lemma non_mem_exp_DLR_EL0_read[non_mem_expI]:
  "non_mem_exp (DLR_EL0_read arg0)"
  by (unfold DLR_EL0_read_def, non_mem_expI)

lemma non_mem_exp_DLR_EL0_SysRegRead_75b9821e3e84ec13[non_mem_expI]:
  "non_mem_exp (DLR_EL0_SysRegRead_75b9821e3e84ec13 el op0 op1 CRn op2 CRm)"
  by (unfold DLR_EL0_SysRegRead_75b9821e3e84ec13_def, non_mem_expI)

lemma non_mem_exp_ELR_EL12_SysRegRead_e8215c0ae79859bb[non_mem_expI]:
  "non_mem_exp (ELR_EL12_SysRegRead_e8215c0ae79859bb el op0 op1 CRn op2 CRm)"
  by (unfold ELR_EL12_SysRegRead_e8215c0ae79859bb_def, non_mem_expI)

lemma non_mem_exp_ELR_EL1_SysRegRead_0d3f1ad1483e96c2[non_mem_expI]:
  "non_mem_exp (ELR_EL1_SysRegRead_0d3f1ad1483e96c2 el op0 op1 CRn op2 CRm)"
  by (unfold ELR_EL1_SysRegRead_0d3f1ad1483e96c2_def, non_mem_expI)

lemma non_mem_exp_ELR_EL2_SysRegRead_00b4dd4251404d91[non_mem_expI]:
  "non_mem_exp (ELR_EL2_SysRegRead_00b4dd4251404d91 el op0 op1 CRn op2 CRm)"
  by (unfold ELR_EL2_SysRegRead_00b4dd4251404d91_def, non_mem_expI)

lemma non_mem_exp_ELR_EL3_SysRegRead_a7a7cd4e7e805396[non_mem_expI]:
  "non_mem_exp (ELR_EL3_SysRegRead_a7a7cd4e7e805396 el op0 op1 CRn op2 CRm)"
  by (unfold ELR_EL3_SysRegRead_a7a7cd4e7e805396_def, non_mem_expI)

lemma non_mem_exp_ERRIDR_EL1_SysRegRead_41b56b8d34e51109[non_mem_expI]:
  "non_mem_exp (ERRIDR_EL1_SysRegRead_41b56b8d34e51109 el op0 op1 CRn op2 CRm)"
  by (unfold ERRIDR_EL1_SysRegRead_41b56b8d34e51109_def, non_mem_expI)

lemma non_mem_exp_ERRSELR_EL1_SysRegRead_1bcf942400e8d57f[non_mem_expI]:
  "non_mem_exp (ERRSELR_EL1_SysRegRead_1bcf942400e8d57f el op0 op1 CRn op2 CRm)"
  by (unfold ERRSELR_EL1_SysRegRead_1bcf942400e8d57f_def, non_mem_expI)

lemma non_mem_exp_ERXADDR_EL1_SysRegRead_7dea05bca757fc1d[non_mem_expI]:
  "non_mem_exp (ERXADDR_EL1_SysRegRead_7dea05bca757fc1d el op0 op1 CRn op2 CRm)"
  by (unfold ERXADDR_EL1_SysRegRead_7dea05bca757fc1d_def, non_mem_expI)

lemma non_mem_exp_ERXCTLR_EL1_SysRegRead_e46ed88d092db048[non_mem_expI]:
  "non_mem_exp (ERXCTLR_EL1_SysRegRead_e46ed88d092db048 el op0 op1 CRn op2 CRm)"
  by (unfold ERXCTLR_EL1_SysRegRead_e46ed88d092db048_def, non_mem_expI)

lemma non_mem_exp_ERXFR_EL1_SysRegRead_ed2a3c237ae67a43[non_mem_expI]:
  "non_mem_exp (ERXFR_EL1_SysRegRead_ed2a3c237ae67a43 el op0 op1 CRn op2 CRm)"
  by (unfold ERXFR_EL1_SysRegRead_ed2a3c237ae67a43_def, non_mem_expI)

lemma non_mem_exp_ERXMISC0_EL1_SysRegRead_a71a4de5f2444f19[non_mem_expI]:
  "non_mem_exp (ERXMISC0_EL1_SysRegRead_a71a4de5f2444f19 el op0 op1 CRn op2 CRm)"
  by (unfold ERXMISC0_EL1_SysRegRead_a71a4de5f2444f19_def, non_mem_expI)

lemma non_mem_exp_ERXMISC1_EL1_SysRegRead_bda613f8058b1fd8[non_mem_expI]:
  "non_mem_exp (ERXMISC1_EL1_SysRegRead_bda613f8058b1fd8 el op0 op1 CRn op2 CRm)"
  by (unfold ERXMISC1_EL1_SysRegRead_bda613f8058b1fd8_def, non_mem_expI)

lemma non_mem_exp_ERXSTATUS_EL1_SysRegRead_0ab2cfe6937b8b64[non_mem_expI]:
  "non_mem_exp (ERXSTATUS_EL1_SysRegRead_0ab2cfe6937b8b64 el op0 op1 CRn op2 CRm)"
  by (unfold ERXSTATUS_EL1_SysRegRead_0ab2cfe6937b8b64_def, non_mem_expI)

lemma non_mem_exp_ESR_EL12_SysRegRead_207d3805d256851a[non_mem_expI]:
  "non_mem_exp (ESR_EL12_SysRegRead_207d3805d256851a el op0 op1 CRn op2 CRm)"
  by (unfold ESR_EL12_SysRegRead_207d3805d256851a_def, non_mem_expI)

lemma non_mem_exp_ESR_EL1_SysRegRead_4894753806397624[non_mem_expI]:
  "non_mem_exp (ESR_EL1_SysRegRead_4894753806397624 el op0 op1 CRn op2 CRm)"
  by (unfold ESR_EL1_SysRegRead_4894753806397624_def, non_mem_expI)

lemma non_mem_exp_ESR_EL2_SysRegRead_e0558cb255261414[non_mem_expI]:
  "non_mem_exp (ESR_EL2_SysRegRead_e0558cb255261414 el op0 op1 CRn op2 CRm)"
  by (unfold ESR_EL2_SysRegRead_e0558cb255261414_def, non_mem_expI)

lemma non_mem_exp_ESR_EL3_SysRegRead_e0eabec0b099e366[non_mem_expI]:
  "non_mem_exp (ESR_EL3_SysRegRead_e0eabec0b099e366 el op0 op1 CRn op2 CRm)"
  by (unfold ESR_EL3_SysRegRead_e0eabec0b099e366_def, non_mem_expI)

lemma non_mem_exp_FAR_EL12_SysRegRead_061fecffb03f9fc5[non_mem_expI]:
  "non_mem_exp (FAR_EL12_SysRegRead_061fecffb03f9fc5 el op0 op1 CRn op2 CRm)"
  by (unfold FAR_EL12_SysRegRead_061fecffb03f9fc5_def, non_mem_expI)

lemma non_mem_exp_FAR_EL1_SysRegRead_136ac0cc65bd5f9d[non_mem_expI]:
  "non_mem_exp (FAR_EL1_SysRegRead_136ac0cc65bd5f9d el op0 op1 CRn op2 CRm)"
  by (unfold FAR_EL1_SysRegRead_136ac0cc65bd5f9d_def, non_mem_expI)

lemma non_mem_exp_FAR_EL2_SysRegRead_d686d0a5577f0aae[non_mem_expI]:
  "non_mem_exp (FAR_EL2_SysRegRead_d686d0a5577f0aae el op0 op1 CRn op2 CRm)"
  by (unfold FAR_EL2_SysRegRead_d686d0a5577f0aae_def, non_mem_expI)

lemma non_mem_exp_FAR_EL3_SysRegRead_d63ec2764f8ffe40[non_mem_expI]:
  "non_mem_exp (FAR_EL3_SysRegRead_d63ec2764f8ffe40 el op0 op1 CRn op2 CRm)"
  by (unfold FAR_EL3_SysRegRead_d63ec2764f8ffe40_def, non_mem_expI)

lemma non_mem_exp_FPCR_SysRegRead_4176e216195c5686[non_mem_expI]:
  "non_mem_exp (FPCR_SysRegRead_4176e216195c5686 el op0 op1 CRn op2 CRm)"
  by (unfold FPCR_SysRegRead_4176e216195c5686_def, non_mem_expI)

lemma non_mem_exp_FPEXC32_EL2_SysRegRead_7ee503337da57806[non_mem_expI]:
  "non_mem_exp (FPEXC32_EL2_SysRegRead_7ee503337da57806 el op0 op1 CRn op2 CRm)"
  by (unfold FPEXC32_EL2_SysRegRead_7ee503337da57806_def, non_mem_expI)

lemma non_mem_exp_FPSR_SysRegRead_c1fde5c387acaca1[non_mem_expI]:
  "non_mem_exp (FPSR_SysRegRead_c1fde5c387acaca1 el op0 op1 CRn op2 CRm)"
  by (unfold FPSR_SysRegRead_c1fde5c387acaca1_def, non_mem_expI)

lemma non_mem_exp_HACR_EL2_SysRegRead_07bc3864e8ed8264[non_mem_expI]:
  "non_mem_exp (HACR_EL2_SysRegRead_07bc3864e8ed8264 el op0 op1 CRn op2 CRm)"
  by (unfold HACR_EL2_SysRegRead_07bc3864e8ed8264_def, non_mem_expI)

lemma non_mem_exp_HCR_EL2_SysRegRead_f76ecfdc85c5ff7c[non_mem_expI]:
  "non_mem_exp (HCR_EL2_SysRegRead_f76ecfdc85c5ff7c el op0 op1 CRn op2 CRm)"
  by (unfold HCR_EL2_SysRegRead_f76ecfdc85c5ff7c_def, non_mem_expI)

lemma non_mem_exp_HPFAR_EL2_SysRegRead_4c322cee424dff18[non_mem_expI]:
  "non_mem_exp (HPFAR_EL2_SysRegRead_4c322cee424dff18 el op0 op1 CRn op2 CRm)"
  by (unfold HPFAR_EL2_SysRegRead_4c322cee424dff18_def, non_mem_expI)

lemma non_mem_exp_HSTR_EL2_SysRegRead_680380b9028cf399[non_mem_expI]:
  "non_mem_exp (HSTR_EL2_SysRegRead_680380b9028cf399 el op0 op1 CRn op2 CRm)"
  by (unfold HSTR_EL2_SysRegRead_680380b9028cf399_def, non_mem_expI)

lemma non_mem_exp_ICC_AP0R_EL1_SysRegRead_cac9b22dc3786a15[non_mem_expI]:
  "non_mem_exp (ICC_AP0R_EL1_SysRegRead_cac9b22dc3786a15 el op0 op1 CRn op2 CRm)"
  by (unfold ICC_AP0R_EL1_SysRegRead_cac9b22dc3786a15_def, non_mem_expI)

lemma non_mem_exp_ICC_AP1R_EL1_SysRegRead_4127418c67790ba3[non_mem_expI]:
  "non_mem_exp (ICC_AP1R_EL1_SysRegRead_4127418c67790ba3 el op0 op1 CRn op2 CRm)"
  by (unfold ICC_AP1R_EL1_SysRegRead_4127418c67790ba3_def, non_mem_expI)

lemma non_mem_exp_ICC_BPR0_EL1_SysRegRead_6ada10a9051248c2[non_mem_expI]:
  "non_mem_exp (ICC_BPR0_EL1_SysRegRead_6ada10a9051248c2 el op0 op1 CRn op2 CRm)"
  by (unfold ICC_BPR0_EL1_SysRegRead_6ada10a9051248c2_def, non_mem_expI)

lemma non_mem_exp_ICC_BPR1_EL1_SysRegRead_c56bf88f1b4aee37[non_mem_expI]:
  "non_mem_exp (ICC_BPR1_EL1_SysRegRead_c56bf88f1b4aee37 el op0 op1 CRn op2 CRm)"
  by (unfold ICC_BPR1_EL1_SysRegRead_c56bf88f1b4aee37_def, non_mem_expI)

lemma non_mem_exp_ICC_CTLR_EL1_SysRegRead_5754830bf787a1e2[non_mem_expI]:
  "non_mem_exp (ICC_CTLR_EL1_SysRegRead_5754830bf787a1e2 el op0 op1 CRn op2 CRm)"
  by (unfold ICC_CTLR_EL1_SysRegRead_5754830bf787a1e2_def, non_mem_expI)

lemma non_mem_exp_ICC_CTLR_EL3_SysRegRead_aba1771445e9d51b[non_mem_expI]:
  "non_mem_exp (ICC_CTLR_EL3_SysRegRead_aba1771445e9d51b el op0 op1 CRn op2 CRm)"
  by (unfold ICC_CTLR_EL3_SysRegRead_aba1771445e9d51b_def, non_mem_expI)

lemma non_mem_exp_ICC_HPPIR0_EL1_SysRegRead_221f9a6f32464de4[non_mem_expI]:
  "non_mem_exp (ICC_HPPIR0_EL1_SysRegRead_221f9a6f32464de4 el op0 op1 CRn op2 CRm)"
  by (unfold ICC_HPPIR0_EL1_SysRegRead_221f9a6f32464de4_def, non_mem_expI)

lemma non_mem_exp_ICC_HPPIR1_EL1_SysRegRead_88ed0889f7d5a37a[non_mem_expI]:
  "non_mem_exp (ICC_HPPIR1_EL1_SysRegRead_88ed0889f7d5a37a el op0 op1 CRn op2 CRm)"
  by (unfold ICC_HPPIR1_EL1_SysRegRead_88ed0889f7d5a37a_def, non_mem_expI)

lemma non_mem_exp_ICC_IAR0_EL1_SysRegRead_dcfaf70befc09037[non_mem_expI]:
  "non_mem_exp (ICC_IAR0_EL1_SysRegRead_dcfaf70befc09037 el op0 op1 CRn op2 CRm)"
  by (unfold ICC_IAR0_EL1_SysRegRead_dcfaf70befc09037_def, non_mem_expI)

lemma non_mem_exp_ICC_IAR1_EL1_SysRegRead_9f370ba68fd3e44f[non_mem_expI]:
  "non_mem_exp (ICC_IAR1_EL1_SysRegRead_9f370ba68fd3e44f el op0 op1 CRn op2 CRm)"
  by (unfold ICC_IAR1_EL1_SysRegRead_9f370ba68fd3e44f_def, non_mem_expI)

lemma non_mem_exp_ICC_IGRPEN0_EL1_SysRegRead_e575448f3c7e7a94[non_mem_expI]:
  "non_mem_exp (ICC_IGRPEN0_EL1_SysRegRead_e575448f3c7e7a94 el op0 op1 CRn op2 CRm)"
  by (unfold ICC_IGRPEN0_EL1_SysRegRead_e575448f3c7e7a94_def, non_mem_expI)

lemma non_mem_exp_ICC_IGRPEN1_EL1_SysRegRead_3cfd0733ef9b6efa[non_mem_expI]:
  "non_mem_exp (ICC_IGRPEN1_EL1_SysRegRead_3cfd0733ef9b6efa el op0 op1 CRn op2 CRm)"
  by (unfold ICC_IGRPEN1_EL1_SysRegRead_3cfd0733ef9b6efa_def, non_mem_expI)

lemma non_mem_exp_ICC_IGRPEN1_EL3_SysRegRead_d192d252016b4c8d[non_mem_expI]:
  "non_mem_exp (ICC_IGRPEN1_EL3_SysRegRead_d192d252016b4c8d el op0 op1 CRn op2 CRm)"
  by (unfold ICC_IGRPEN1_EL3_SysRegRead_d192d252016b4c8d_def, non_mem_expI)

lemma non_mem_exp_ICC_PMR_EL1_SysRegRead_4ab2c9427488fbf4[non_mem_expI]:
  "non_mem_exp (ICC_PMR_EL1_SysRegRead_4ab2c9427488fbf4 el op0 op1 CRn op2 CRm)"
  by (unfold ICC_PMR_EL1_SysRegRead_4ab2c9427488fbf4_def, non_mem_expI)

lemma non_mem_exp_ICC_RPR_EL1_SysRegRead_bea9edc41b26aab0[non_mem_expI]:
  "non_mem_exp (ICC_RPR_EL1_SysRegRead_bea9edc41b26aab0 el op0 op1 CRn op2 CRm)"
  by (unfold ICC_RPR_EL1_SysRegRead_bea9edc41b26aab0_def, non_mem_expI)

lemma non_mem_exp_ICC_SRE_EL1_SysRegRead_7cf0aa9fc619dea4[non_mem_expI]:
  "non_mem_exp (ICC_SRE_EL1_SysRegRead_7cf0aa9fc619dea4 el op0 op1 CRn op2 CRm)"
  by (unfold ICC_SRE_EL1_SysRegRead_7cf0aa9fc619dea4_def, non_mem_expI)

lemma non_mem_exp_ICC_SRE_EL2_SysRegRead_35c9349812c986fe[non_mem_expI]:
  "non_mem_exp (ICC_SRE_EL2_SysRegRead_35c9349812c986fe el op0 op1 CRn op2 CRm)"
  by (unfold ICC_SRE_EL2_SysRegRead_35c9349812c986fe_def, non_mem_expI)

lemma non_mem_exp_ICC_SRE_EL3_SysRegRead_c7d421022a5f589d[non_mem_expI]:
  "non_mem_exp (ICC_SRE_EL3_SysRegRead_c7d421022a5f589d el op0 op1 CRn op2 CRm)"
  by (unfold ICC_SRE_EL3_SysRegRead_c7d421022a5f589d_def, non_mem_expI)

lemma non_mem_exp_ICH_AP0R_EL2_SysRegRead_a38114229330a389[non_mem_expI]:
  "non_mem_exp (ICH_AP0R_EL2_SysRegRead_a38114229330a389 el op0 op1 CRn op2 CRm)"
  by (unfold ICH_AP0R_EL2_SysRegRead_a38114229330a389_def, non_mem_expI)

lemma non_mem_exp_ICH_AP1R_EL2_SysRegRead_3ef1256520a6f18e[non_mem_expI]:
  "non_mem_exp (ICH_AP1R_EL2_SysRegRead_3ef1256520a6f18e el op0 op1 CRn op2 CRm)"
  by (unfold ICH_AP1R_EL2_SysRegRead_3ef1256520a6f18e_def, non_mem_expI)

lemma non_mem_exp_ICH_EISR_EL2_SysRegRead_a45d99ec0ef64804[non_mem_expI]:
  "non_mem_exp (ICH_EISR_EL2_SysRegRead_a45d99ec0ef64804 el op0 op1 CRn op2 CRm)"
  by (unfold ICH_EISR_EL2_SysRegRead_a45d99ec0ef64804_def, non_mem_expI)

lemma non_mem_exp_ICH_ELRSR_EL2_SysRegRead_93859a236e9efe6d[non_mem_expI]:
  "non_mem_exp (ICH_ELRSR_EL2_SysRegRead_93859a236e9efe6d el op0 op1 CRn op2 CRm)"
  by (unfold ICH_ELRSR_EL2_SysRegRead_93859a236e9efe6d_def, non_mem_expI)

lemma non_mem_exp_ICH_HCR_EL2_SysRegRead_bd436f3e91661e3b[non_mem_expI]:
  "non_mem_exp (ICH_HCR_EL2_SysRegRead_bd436f3e91661e3b el op0 op1 CRn op2 CRm)"
  by (unfold ICH_HCR_EL2_SysRegRead_bd436f3e91661e3b_def, non_mem_expI)

lemma non_mem_exp_ICH_LR_EL2_SysRegRead_f9d8d38c7064e389[non_mem_expI]:
  "non_mem_exp (ICH_LR_EL2_SysRegRead_f9d8d38c7064e389 el op0 op1 CRn op2 CRm)"
  by (unfold ICH_LR_EL2_SysRegRead_f9d8d38c7064e389_def, non_mem_expI)

lemma non_mem_exp_ICH_MISR_EL2_SysRegRead_4e46f86d49bd21cd[non_mem_expI]:
  "non_mem_exp (ICH_MISR_EL2_SysRegRead_4e46f86d49bd21cd el op0 op1 CRn op2 CRm)"
  by (unfold ICH_MISR_EL2_SysRegRead_4e46f86d49bd21cd_def, non_mem_expI)

lemma non_mem_exp_ICH_VMCR_EL2_SysRegRead_3c019711ec735507[non_mem_expI]:
  "non_mem_exp (ICH_VMCR_EL2_SysRegRead_3c019711ec735507 el op0 op1 CRn op2 CRm)"
  by (unfold ICH_VMCR_EL2_SysRegRead_3c019711ec735507_def, non_mem_expI)

lemma non_mem_exp_ICH_VTR_EL2_SysRegRead_2ed82d00af03b344[non_mem_expI]:
  "non_mem_exp (ICH_VTR_EL2_SysRegRead_2ed82d00af03b344 el op0 op1 CRn op2 CRm)"
  by (unfold ICH_VTR_EL2_SysRegRead_2ed82d00af03b344_def, non_mem_expI)

lemma non_mem_exp_ID_AA64AFR0_EL1_SysRegRead_325547f3ac10431a[non_mem_expI]:
  "non_mem_exp (ID_AA64AFR0_EL1_SysRegRead_325547f3ac10431a el op0 op1 CRn op2 CRm)"
  by (unfold ID_AA64AFR0_EL1_SysRegRead_325547f3ac10431a_def, non_mem_expI)

lemma non_mem_exp_ID_AA64AFR1_EL1_SysRegRead_99b67b76121ee706[non_mem_expI]:
  "non_mem_exp (ID_AA64AFR1_EL1_SysRegRead_99b67b76121ee706 el op0 op1 CRn op2 CRm)"
  by (unfold ID_AA64AFR1_EL1_SysRegRead_99b67b76121ee706_def, non_mem_expI)

lemma non_mem_exp_ID_AA64DFR0_EL1_SysRegRead_c3e6b049dd70bbab[non_mem_expI]:
  "non_mem_exp (ID_AA64DFR0_EL1_SysRegRead_c3e6b049dd70bbab el op0 op1 CRn op2 CRm)"
  by (unfold ID_AA64DFR0_EL1_SysRegRead_c3e6b049dd70bbab_def, non_mem_expI)

lemma non_mem_exp_ID_AA64DFR1_EL1_SysRegRead_2f066031859d7035[non_mem_expI]:
  "non_mem_exp (ID_AA64DFR1_EL1_SysRegRead_2f066031859d7035 el op0 op1 CRn op2 CRm)"
  by (unfold ID_AA64DFR1_EL1_SysRegRead_2f066031859d7035_def, non_mem_expI)

lemma non_mem_exp_ID_AA64ISAR0_EL1_SysRegRead_d35f255c04eaab0f[non_mem_expI]:
  "non_mem_exp (ID_AA64ISAR0_EL1_SysRegRead_d35f255c04eaab0f el op0 op1 CRn op2 CRm)"
  by (unfold ID_AA64ISAR0_EL1_SysRegRead_d35f255c04eaab0f_def, non_mem_expI)

lemma non_mem_exp_ID_AA64ISAR1_EL1_SysRegRead_1132f371c4707f61[non_mem_expI]:
  "non_mem_exp (ID_AA64ISAR1_EL1_SysRegRead_1132f371c4707f61 el op0 op1 CRn op2 CRm)"
  by (unfold ID_AA64ISAR1_EL1_SysRegRead_1132f371c4707f61_def, non_mem_expI)

lemma non_mem_exp_ID_AA64MMFR0_EL1_SysRegRead_836c46ff67ac3f3d[non_mem_expI]:
  "non_mem_exp (ID_AA64MMFR0_EL1_SysRegRead_836c46ff67ac3f3d el op0 op1 CRn op2 CRm)"
  by (unfold ID_AA64MMFR0_EL1_SysRegRead_836c46ff67ac3f3d_def, non_mem_expI)

lemma non_mem_exp_ID_AA64MMFR1_EL1_SysRegRead_3abbf4d2af8dd3be[non_mem_expI]:
  "non_mem_exp (ID_AA64MMFR1_EL1_SysRegRead_3abbf4d2af8dd3be el op0 op1 CRn op2 CRm)"
  by (unfold ID_AA64MMFR1_EL1_SysRegRead_3abbf4d2af8dd3be_def, non_mem_expI)

lemma non_mem_exp_ID_AA64MMFR2_EL1_SysRegRead_1443648da3ca79dd[non_mem_expI]:
  "non_mem_exp (ID_AA64MMFR2_EL1_SysRegRead_1443648da3ca79dd el op0 op1 CRn op2 CRm)"
  by (unfold ID_AA64MMFR2_EL1_SysRegRead_1443648da3ca79dd_def, non_mem_expI)

lemma non_mem_exp_ID_AA64PFR0_EL1_SysRegRead_fe78f914579c8717[non_mem_expI]:
  "non_mem_exp (ID_AA64PFR0_EL1_SysRegRead_fe78f914579c8717 el op0 op1 CRn op2 CRm)"
  by (unfold ID_AA64PFR0_EL1_SysRegRead_fe78f914579c8717_def, non_mem_expI)

lemma non_mem_exp_ID_AA64PFR1_EL1_SysRegRead_3be470f3d1bff138[non_mem_expI]:
  "non_mem_exp (ID_AA64PFR1_EL1_SysRegRead_3be470f3d1bff138 el op0 op1 CRn op2 CRm)"
  by (unfold ID_AA64PFR1_EL1_SysRegRead_3be470f3d1bff138_def, non_mem_expI)

lemma non_mem_exp_ID_AA64ZFR0_EL1_SysRegRead_70425f5143f66c9f[non_mem_expI]:
  "non_mem_exp (ID_AA64ZFR0_EL1_SysRegRead_70425f5143f66c9f el op0 op1 CRn op2 CRm)"
  by (unfold ID_AA64ZFR0_EL1_SysRegRead_70425f5143f66c9f_def, non_mem_expI)

lemma non_mem_exp_ID_AFR0_EL1_SysRegRead_019e5ec822653217[non_mem_expI]:
  "non_mem_exp (ID_AFR0_EL1_SysRegRead_019e5ec822653217 el op0 op1 CRn op2 CRm)"
  by (unfold ID_AFR0_EL1_SysRegRead_019e5ec822653217_def, non_mem_expI)

lemma non_mem_exp_ID_DFR0_EL1_SysRegRead_12146217191b4fee[non_mem_expI]:
  "non_mem_exp (ID_DFR0_EL1_SysRegRead_12146217191b4fee el op0 op1 CRn op2 CRm)"
  by (unfold ID_DFR0_EL1_SysRegRead_12146217191b4fee_def, non_mem_expI)

lemma non_mem_exp_ID_ISAR0_EL1_SysRegRead_4e2f04c3a26dddb3[non_mem_expI]:
  "non_mem_exp (ID_ISAR0_EL1_SysRegRead_4e2f04c3a26dddb3 el op0 op1 CRn op2 CRm)"
  by (unfold ID_ISAR0_EL1_SysRegRead_4e2f04c3a26dddb3_def, non_mem_expI)

lemma non_mem_exp_ID_ISAR1_EL1_SysRegRead_2f4500748023e22b[non_mem_expI]:
  "non_mem_exp (ID_ISAR1_EL1_SysRegRead_2f4500748023e22b el op0 op1 CRn op2 CRm)"
  by (unfold ID_ISAR1_EL1_SysRegRead_2f4500748023e22b_def, non_mem_expI)

lemma non_mem_exp_ID_ISAR2_EL1_SysRegRead_1e8edaee6a0e9ef9[non_mem_expI]:
  "non_mem_exp (ID_ISAR2_EL1_SysRegRead_1e8edaee6a0e9ef9 el op0 op1 CRn op2 CRm)"
  by (unfold ID_ISAR2_EL1_SysRegRead_1e8edaee6a0e9ef9_def, non_mem_expI)

lemma non_mem_exp_ID_ISAR3_EL1_SysRegRead_cf9a1aae39d73bdd[non_mem_expI]:
  "non_mem_exp (ID_ISAR3_EL1_SysRegRead_cf9a1aae39d73bdd el op0 op1 CRn op2 CRm)"
  by (unfold ID_ISAR3_EL1_SysRegRead_cf9a1aae39d73bdd_def, non_mem_expI)

lemma non_mem_exp_ID_ISAR4_EL1_SysRegRead_9bffd9dcf4dd4ef4[non_mem_expI]:
  "non_mem_exp (ID_ISAR4_EL1_SysRegRead_9bffd9dcf4dd4ef4 el op0 op1 CRn op2 CRm)"
  by (unfold ID_ISAR4_EL1_SysRegRead_9bffd9dcf4dd4ef4_def, non_mem_expI)

lemma non_mem_exp_ID_ISAR5_EL1_SysRegRead_f70928ed2f55c1f0[non_mem_expI]:
  "non_mem_exp (ID_ISAR5_EL1_SysRegRead_f70928ed2f55c1f0 el op0 op1 CRn op2 CRm)"
  by (unfold ID_ISAR5_EL1_SysRegRead_f70928ed2f55c1f0_def, non_mem_expI)

lemma non_mem_exp_ID_ISAR6_EL1_SysRegRead_6ce3605912a2db6d[non_mem_expI]:
  "non_mem_exp (ID_ISAR6_EL1_SysRegRead_6ce3605912a2db6d el op0 op1 CRn op2 CRm)"
  by (unfold ID_ISAR6_EL1_SysRegRead_6ce3605912a2db6d_def, non_mem_expI)

lemma non_mem_exp_ID_MMFR0_EL1_SysRegRead_b31c5faa39841084[non_mem_expI]:
  "non_mem_exp (ID_MMFR0_EL1_SysRegRead_b31c5faa39841084 el op0 op1 CRn op2 CRm)"
  by (unfold ID_MMFR0_EL1_SysRegRead_b31c5faa39841084_def, non_mem_expI)

lemma non_mem_exp_ID_MMFR1_EL1_SysRegRead_b0f4bc0d71c9af14[non_mem_expI]:
  "non_mem_exp (ID_MMFR1_EL1_SysRegRead_b0f4bc0d71c9af14 el op0 op1 CRn op2 CRm)"
  by (unfold ID_MMFR1_EL1_SysRegRead_b0f4bc0d71c9af14_def, non_mem_expI)

lemma non_mem_exp_ID_MMFR2_EL1_SysRegRead_b60501193094f759[non_mem_expI]:
  "non_mem_exp (ID_MMFR2_EL1_SysRegRead_b60501193094f759 el op0 op1 CRn op2 CRm)"
  by (unfold ID_MMFR2_EL1_SysRegRead_b60501193094f759_def, non_mem_expI)

lemma non_mem_exp_ID_MMFR3_EL1_SysRegRead_dc45af19c356c392[non_mem_expI]:
  "non_mem_exp (ID_MMFR3_EL1_SysRegRead_dc45af19c356c392 el op0 op1 CRn op2 CRm)"
  by (unfold ID_MMFR3_EL1_SysRegRead_dc45af19c356c392_def, non_mem_expI)

lemma non_mem_exp_ID_MMFR4_EL1_SysRegRead_237ae4b6fb487f3e[non_mem_expI]:
  "non_mem_exp (ID_MMFR4_EL1_SysRegRead_237ae4b6fb487f3e el op0 op1 CRn op2 CRm)"
  by (unfold ID_MMFR4_EL1_SysRegRead_237ae4b6fb487f3e_def, non_mem_expI)

lemma non_mem_exp_ID_MMFR5_EL1_SysRegRead_00dc6140c3593f6a[non_mem_expI]:
  "non_mem_exp (ID_MMFR5_EL1_SysRegRead_00dc6140c3593f6a el op0 op1 CRn op2 CRm)"
  by (unfold ID_MMFR5_EL1_SysRegRead_00dc6140c3593f6a_def, non_mem_expI)

lemma non_mem_exp_ID_PFR0_EL1_SysRegRead_ab73eb91d66cfece[non_mem_expI]:
  "non_mem_exp (ID_PFR0_EL1_SysRegRead_ab73eb91d66cfece el op0 op1 CRn op2 CRm)"
  by (unfold ID_PFR0_EL1_SysRegRead_ab73eb91d66cfece_def, non_mem_expI)

lemma non_mem_exp_ID_PFR1_EL1_SysRegRead_264075958e26856b[non_mem_expI]:
  "non_mem_exp (ID_PFR1_EL1_SysRegRead_264075958e26856b el op0 op1 CRn op2 CRm)"
  by (unfold ID_PFR1_EL1_SysRegRead_264075958e26856b_def, non_mem_expI)

lemma non_mem_exp_ID_PFR2_EL1_SysRegRead_8561b575e8dfcee0[non_mem_expI]:
  "non_mem_exp (ID_PFR2_EL1_SysRegRead_8561b575e8dfcee0 el op0 op1 CRn op2 CRm)"
  by (unfold ID_PFR2_EL1_SysRegRead_8561b575e8dfcee0_def, non_mem_expI)

lemma non_mem_exp_IFSR32_EL2_SysRegRead_3b41290786c143ba[non_mem_expI]:
  "non_mem_exp (IFSR32_EL2_SysRegRead_3b41290786c143ba el op0 op1 CRn op2 CRm)"
  by (unfold IFSR32_EL2_SysRegRead_3b41290786c143ba_def, non_mem_expI)

lemma non_mem_exp_ISR_EL1_SysRegRead_41b7dbf26b89e726[non_mem_expI]:
  "non_mem_exp (ISR_EL1_SysRegRead_41b7dbf26b89e726 el op0 op1 CRn op2 CRm)"
  by (unfold ISR_EL1_SysRegRead_41b7dbf26b89e726_def, non_mem_expI)

lemma non_mem_exp_LORC_EL1_SysRegRead_0067e90ee116c26f[non_mem_expI]:
  "non_mem_exp (LORC_EL1_SysRegRead_0067e90ee116c26f el op0 op1 CRn op2 CRm)"
  by (unfold LORC_EL1_SysRegRead_0067e90ee116c26f_def, non_mem_expI)

lemma non_mem_exp_LOREA_EL1_SysRegRead_ec495c3c15ed4dbe[non_mem_expI]:
  "non_mem_exp (LOREA_EL1_SysRegRead_ec495c3c15ed4dbe el op0 op1 CRn op2 CRm)"
  by (unfold LOREA_EL1_SysRegRead_ec495c3c15ed4dbe_def, non_mem_expI)

lemma non_mem_exp_LORID_EL1_SysRegRead_a063108cc96d4baa[non_mem_expI]:
  "non_mem_exp (LORID_EL1_SysRegRead_a063108cc96d4baa el op0 op1 CRn op2 CRm)"
  by (unfold LORID_EL1_SysRegRead_a063108cc96d4baa_def, non_mem_expI)

lemma non_mem_exp_LORN_EL1_SysRegRead_da981b495b21c400[non_mem_expI]:
  "non_mem_exp (LORN_EL1_SysRegRead_da981b495b21c400 el op0 op1 CRn op2 CRm)"
  by (unfold LORN_EL1_SysRegRead_da981b495b21c400_def, non_mem_expI)

lemma non_mem_exp_LORSA_EL1_SysRegRead_cdc08dda4115abc7[non_mem_expI]:
  "non_mem_exp (LORSA_EL1_SysRegRead_cdc08dda4115abc7 el op0 op1 CRn op2 CRm)"
  by (unfold LORSA_EL1_SysRegRead_cdc08dda4115abc7_def, non_mem_expI)

lemma non_mem_exp_MAIR_EL12_SysRegRead_ac3327848e47dda6[non_mem_expI]:
  "non_mem_exp (MAIR_EL12_SysRegRead_ac3327848e47dda6 el op0 op1 CRn op2 CRm)"
  by (unfold MAIR_EL12_SysRegRead_ac3327848e47dda6_def, non_mem_expI)

lemma non_mem_exp_MAIR_EL1_SysRegRead_ee00b1441fc4a50d[non_mem_expI]:
  "non_mem_exp (MAIR_EL1_SysRegRead_ee00b1441fc4a50d el op0 op1 CRn op2 CRm)"
  by (unfold MAIR_EL1_SysRegRead_ee00b1441fc4a50d_def, non_mem_expI)

lemma non_mem_exp_MAIR_EL2_SysRegRead_66c03f7cb594c1bd[non_mem_expI]:
  "non_mem_exp (MAIR_EL2_SysRegRead_66c03f7cb594c1bd el op0 op1 CRn op2 CRm)"
  by (unfold MAIR_EL2_SysRegRead_66c03f7cb594c1bd_def, non_mem_expI)

lemma non_mem_exp_MAIR_EL3_SysRegRead_0eb4af28a4f9b45a[non_mem_expI]:
  "non_mem_exp (MAIR_EL3_SysRegRead_0eb4af28a4f9b45a el op0 op1 CRn op2 CRm)"
  by (unfold MAIR_EL3_SysRegRead_0eb4af28a4f9b45a_def, non_mem_expI)

lemma non_mem_exp_MDCCINT_EL1_SysRegRead_12f1a0397d5a3729[non_mem_expI]:
  "non_mem_exp (MDCCINT_EL1_SysRegRead_12f1a0397d5a3729 el op0 op1 CRn op2 CRm)"
  by (unfold MDCCINT_EL1_SysRegRead_12f1a0397d5a3729_def, non_mem_expI)

lemma non_mem_exp_MDCCSR_EL0_SysRegRead_1ca0d9105cd616c5[non_mem_expI]:
  "non_mem_exp (MDCCSR_EL0_SysRegRead_1ca0d9105cd616c5 el op0 op1 CRn op2 CRm)"
  by (unfold MDCCSR_EL0_SysRegRead_1ca0d9105cd616c5_def, non_mem_expI)

lemma non_mem_exp_MDCR_EL2_SysRegRead_f2181c815a998208[non_mem_expI]:
  "non_mem_exp (MDCR_EL2_SysRegRead_f2181c815a998208 el op0 op1 CRn op2 CRm)"
  by (unfold MDCR_EL2_SysRegRead_f2181c815a998208_def, non_mem_expI)

lemma non_mem_exp_MDCR_EL3_SysRegRead_229d5ee95c6e9850[non_mem_expI]:
  "non_mem_exp (MDCR_EL3_SysRegRead_229d5ee95c6e9850 el op0 op1 CRn op2 CRm)"
  by (unfold MDCR_EL3_SysRegRead_229d5ee95c6e9850_def, non_mem_expI)

lemma non_mem_exp_MDRAR_EL1_SysRegRead_4c6f0d270d3fe56e[non_mem_expI]:
  "non_mem_exp (MDRAR_EL1_SysRegRead_4c6f0d270d3fe56e el op0 op1 CRn op2 CRm)"
  by (unfold MDRAR_EL1_SysRegRead_4c6f0d270d3fe56e_def, non_mem_expI)

lemma non_mem_exp_MDSCR_EL1_SysRegRead_5184636ced539526[non_mem_expI]:
  "non_mem_exp (MDSCR_EL1_SysRegRead_5184636ced539526 el op0 op1 CRn op2 CRm)"
  by (unfold MDSCR_EL1_SysRegRead_5184636ced539526_def, non_mem_expI)

lemma non_mem_exp_MIDR_EL1_SysRegRead_d49cc5f604ad167e[non_mem_expI]:
  "non_mem_exp (MIDR_EL1_SysRegRead_d49cc5f604ad167e el op0 op1 CRn op2 CRm)"
  by (unfold MIDR_EL1_SysRegRead_d49cc5f604ad167e_def, non_mem_expI)

lemma non_mem_exp_MPAM0_EL1_SysRegRead_87af318fd5c9f9f7[non_mem_expI]:
  "non_mem_exp (MPAM0_EL1_SysRegRead_87af318fd5c9f9f7 el op0 op1 CRn op2 CRm)"
  by (unfold MPAM0_EL1_SysRegRead_87af318fd5c9f9f7_def, non_mem_expI)

lemma non_mem_exp_MPAM1_EL12_SysRegRead_229a253b730e26d9[non_mem_expI]:
  "non_mem_exp (MPAM1_EL12_SysRegRead_229a253b730e26d9 el op0 op1 CRn op2 CRm)"
  by (unfold MPAM1_EL12_SysRegRead_229a253b730e26d9_def, non_mem_expI)

lemma non_mem_exp_MPAM1_EL1_SysRegRead_770ea23b87b18d99[non_mem_expI]:
  "non_mem_exp (MPAM1_EL1_SysRegRead_770ea23b87b18d99 el op0 op1 CRn op2 CRm)"
  by (unfold MPAM1_EL1_SysRegRead_770ea23b87b18d99_def, non_mem_expI)

lemma non_mem_exp_MPAM2_EL2_SysRegRead_10b60646fb381bea[non_mem_expI]:
  "non_mem_exp (MPAM2_EL2_SysRegRead_10b60646fb381bea el op0 op1 CRn op2 CRm)"
  by (unfold MPAM2_EL2_SysRegRead_10b60646fb381bea_def, non_mem_expI)

lemma non_mem_exp_MPAM3_EL3_SysRegRead_989f38b07d8b4265[non_mem_expI]:
  "non_mem_exp (MPAM3_EL3_SysRegRead_989f38b07d8b4265 el op0 op1 CRn op2 CRm)"
  by (unfold MPAM3_EL3_SysRegRead_989f38b07d8b4265_def, non_mem_expI)

lemma non_mem_exp_MPAMHCR_EL2_SysRegRead_6ee5f61be808e32e[non_mem_expI]:
  "non_mem_exp (MPAMHCR_EL2_SysRegRead_6ee5f61be808e32e el op0 op1 CRn op2 CRm)"
  by (unfold MPAMHCR_EL2_SysRegRead_6ee5f61be808e32e_def, non_mem_expI)

lemma non_mem_exp_MPAMIDR_EL1_SysRegRead_df4c57d831354b3c[non_mem_expI]:
  "non_mem_exp (MPAMIDR_EL1_SysRegRead_df4c57d831354b3c el op0 op1 CRn op2 CRm)"
  by (unfold MPAMIDR_EL1_SysRegRead_df4c57d831354b3c_def, non_mem_expI)

lemma non_mem_exp_MPAMVPM0_EL2_SysRegRead_d878a15f2ea1751d[non_mem_expI]:
  "non_mem_exp (MPAMVPM0_EL2_SysRegRead_d878a15f2ea1751d el op0 op1 CRn op2 CRm)"
  by (unfold MPAMVPM0_EL2_SysRegRead_d878a15f2ea1751d_def, non_mem_expI)

lemma non_mem_exp_MPAMVPM1_EL2_SysRegRead_78ba55a3ef5fc5ba[non_mem_expI]:
  "non_mem_exp (MPAMVPM1_EL2_SysRegRead_78ba55a3ef5fc5ba el op0 op1 CRn op2 CRm)"
  by (unfold MPAMVPM1_EL2_SysRegRead_78ba55a3ef5fc5ba_def, non_mem_expI)

lemma non_mem_exp_MPAMVPM2_EL2_SysRegRead_590d1577b5eb780d[non_mem_expI]:
  "non_mem_exp (MPAMVPM2_EL2_SysRegRead_590d1577b5eb780d el op0 op1 CRn op2 CRm)"
  by (unfold MPAMVPM2_EL2_SysRegRead_590d1577b5eb780d_def, non_mem_expI)

lemma non_mem_exp_MPAMVPM3_EL2_SysRegRead_3d93a30deb34ea81[non_mem_expI]:
  "non_mem_exp (MPAMVPM3_EL2_SysRegRead_3d93a30deb34ea81 el op0 op1 CRn op2 CRm)"
  by (unfold MPAMVPM3_EL2_SysRegRead_3d93a30deb34ea81_def, non_mem_expI)

lemma non_mem_exp_MPAMVPM4_EL2_SysRegRead_c4fa65dba541d8f3[non_mem_expI]:
  "non_mem_exp (MPAMVPM4_EL2_SysRegRead_c4fa65dba541d8f3 el op0 op1 CRn op2 CRm)"
  by (unfold MPAMVPM4_EL2_SysRegRead_c4fa65dba541d8f3_def, non_mem_expI)

lemma non_mem_exp_MPAMVPM5_EL2_SysRegRead_0f596cf6a35cf124[non_mem_expI]:
  "non_mem_exp (MPAMVPM5_EL2_SysRegRead_0f596cf6a35cf124 el op0 op1 CRn op2 CRm)"
  by (unfold MPAMVPM5_EL2_SysRegRead_0f596cf6a35cf124_def, non_mem_expI)

lemma non_mem_exp_MPAMVPM6_EL2_SysRegRead_c93ffeb6ea409c71[non_mem_expI]:
  "non_mem_exp (MPAMVPM6_EL2_SysRegRead_c93ffeb6ea409c71 el op0 op1 CRn op2 CRm)"
  by (unfold MPAMVPM6_EL2_SysRegRead_c93ffeb6ea409c71_def, non_mem_expI)

lemma non_mem_exp_MPAMVPM7_EL2_SysRegRead_ef19c89f1fa31f3e[non_mem_expI]:
  "non_mem_exp (MPAMVPM7_EL2_SysRegRead_ef19c89f1fa31f3e el op0 op1 CRn op2 CRm)"
  by (unfold MPAMVPM7_EL2_SysRegRead_ef19c89f1fa31f3e_def, non_mem_expI)

lemma non_mem_exp_MPAMVPMV_EL2_SysRegRead_6de5731367257b91[non_mem_expI]:
  "non_mem_exp (MPAMVPMV_EL2_SysRegRead_6de5731367257b91 el op0 op1 CRn op2 CRm)"
  by (unfold MPAMVPMV_EL2_SysRegRead_6de5731367257b91_def, non_mem_expI)

lemma non_mem_exp_MPIDR_EL1_SysRegRead_1a44c237fc7e90a0[non_mem_expI]:
  "non_mem_exp (MPIDR_EL1_SysRegRead_1a44c237fc7e90a0 el op0 op1 CRn op2 CRm)"
  by (unfold MPIDR_EL1_SysRegRead_1a44c237fc7e90a0_def, non_mem_expI)

lemma non_mem_exp_MVFR0_EL1_SysRegRead_982614cb681cfbbf[non_mem_expI]:
  "non_mem_exp (MVFR0_EL1_SysRegRead_982614cb681cfbbf el op0 op1 CRn op2 CRm)"
  by (unfold MVFR0_EL1_SysRegRead_982614cb681cfbbf_def, non_mem_expI)

lemma non_mem_exp_MVFR1_EL1_SysRegRead_1964a95566ab0fcd[non_mem_expI]:
  "non_mem_exp (MVFR1_EL1_SysRegRead_1964a95566ab0fcd el op0 op1 CRn op2 CRm)"
  by (unfold MVFR1_EL1_SysRegRead_1964a95566ab0fcd_def, non_mem_expI)

lemma non_mem_exp_MVFR2_EL1_SysRegRead_f6245ffc535897f2[non_mem_expI]:
  "non_mem_exp (MVFR2_EL1_SysRegRead_f6245ffc535897f2 el op0 op1 CRn op2 CRm)"
  by (unfold MVFR2_EL1_SysRegRead_f6245ffc535897f2_def, non_mem_expI)

lemma non_mem_exp_OSDLR_EL1_SysRegRead_4cb80c508c4cced4[non_mem_expI]:
  "non_mem_exp (OSDLR_EL1_SysRegRead_4cb80c508c4cced4 el op0 op1 CRn op2 CRm)"
  by (unfold OSDLR_EL1_SysRegRead_4cb80c508c4cced4_def, non_mem_expI)

lemma non_mem_exp_OSDTRRX_EL1_SysRegRead_d4eb07360bc69d28[non_mem_expI]:
  "non_mem_exp (OSDTRRX_EL1_SysRegRead_d4eb07360bc69d28 el op0 op1 CRn op2 CRm)"
  by (unfold OSDTRRX_EL1_SysRegRead_d4eb07360bc69d28_def, non_mem_expI)

lemma non_mem_exp_OSDTRTX_EL1_SysRegRead_008c22058272684f[non_mem_expI]:
  "non_mem_exp (OSDTRTX_EL1_SysRegRead_008c22058272684f el op0 op1 CRn op2 CRm)"
  by (unfold OSDTRTX_EL1_SysRegRead_008c22058272684f_def, non_mem_expI)

lemma non_mem_exp_OSECCR_EL1_SysRegRead_264ab12a32fecc30[non_mem_expI]:
  "non_mem_exp (OSECCR_EL1_SysRegRead_264ab12a32fecc30 el op0 op1 CRn op2 CRm)"
  by (unfold OSECCR_EL1_SysRegRead_264ab12a32fecc30_def, non_mem_expI)

lemma non_mem_exp_OSLSR_EL1_SysRegRead_d99062033a35ccbf[non_mem_expI]:
  "non_mem_exp (OSLSR_EL1_SysRegRead_d99062033a35ccbf el op0 op1 CRn op2 CRm)"
  by (unfold OSLSR_EL1_SysRegRead_d99062033a35ccbf_def, non_mem_expI)

lemma non_mem_exp_PAR_EL1_SysRegRead_888e7c84935ebac7[non_mem_expI]:
  "non_mem_exp (PAR_EL1_SysRegRead_888e7c84935ebac7 el op0 op1 CRn op2 CRm)"
  by (unfold PAR_EL1_SysRegRead_888e7c84935ebac7_def, non_mem_expI)

lemma non_mem_exp_PMBIDR_EL1_SysRegRead_306c3f68e41521a3[non_mem_expI]:
  "non_mem_exp (PMBIDR_EL1_SysRegRead_306c3f68e41521a3 el op0 op1 CRn op2 CRm)"
  by (unfold PMBIDR_EL1_SysRegRead_306c3f68e41521a3_def, non_mem_expI)

lemma non_mem_exp_PMBLIMITR_EL1_SysRegRead_b7c18938ab0566dc[non_mem_expI]:
  "non_mem_exp (PMBLIMITR_EL1_SysRegRead_b7c18938ab0566dc el op0 op1 CRn op2 CRm)"
  by (unfold PMBLIMITR_EL1_SysRegRead_b7c18938ab0566dc_def, non_mem_expI)

lemma non_mem_exp_PMBPTR_EL1_SysRegRead_fb82e1b6e480bd0a[non_mem_expI]:
  "non_mem_exp (PMBPTR_EL1_SysRegRead_fb82e1b6e480bd0a el op0 op1 CRn op2 CRm)"
  by (unfold PMBPTR_EL1_SysRegRead_fb82e1b6e480bd0a_def, non_mem_expI)

lemma non_mem_exp_PMBSR_EL1_SysRegRead_87628bec330b9f53[non_mem_expI]:
  "non_mem_exp (PMBSR_EL1_SysRegRead_87628bec330b9f53 el op0 op1 CRn op2 CRm)"
  by (unfold PMBSR_EL1_SysRegRead_87628bec330b9f53_def, non_mem_expI)

lemma non_mem_exp_PMCCFILTR_EL0_SysRegRead_349918c2333bfc1e[non_mem_expI]:
  "non_mem_exp (PMCCFILTR_EL0_SysRegRead_349918c2333bfc1e el op0 op1 CRn op2 CRm)"
  by (unfold PMCCFILTR_EL0_SysRegRead_349918c2333bfc1e_def, non_mem_expI)

lemma non_mem_exp_PMCCNTR_EL0_SysRegRead_45fc425eff298404[non_mem_expI]:
  "non_mem_exp (PMCCNTR_EL0_SysRegRead_45fc425eff298404 el op0 op1 CRn op2 CRm)"
  by (unfold PMCCNTR_EL0_SysRegRead_45fc425eff298404_def, non_mem_expI)

lemma non_mem_exp_PMCEID0_EL0_SysRegRead_1364a10a0c913d82[non_mem_expI]:
  "non_mem_exp (PMCEID0_EL0_SysRegRead_1364a10a0c913d82 el op0 op1 CRn op2 CRm)"
  by (unfold PMCEID0_EL0_SysRegRead_1364a10a0c913d82_def, non_mem_expI)

lemma non_mem_exp_PMCEID1_EL0_SysRegRead_2db7a3b96735d30a[non_mem_expI]:
  "non_mem_exp (PMCEID1_EL0_SysRegRead_2db7a3b96735d30a el op0 op1 CRn op2 CRm)"
  by (unfold PMCEID1_EL0_SysRegRead_2db7a3b96735d30a_def, non_mem_expI)

lemma non_mem_exp_PMCNTENCLR_EL0_SysRegRead_5ac431b885c9c5e4[non_mem_expI]:
  "non_mem_exp (PMCNTENCLR_EL0_SysRegRead_5ac431b885c9c5e4 el op0 op1 CRn op2 CRm)"
  by (unfold PMCNTENCLR_EL0_SysRegRead_5ac431b885c9c5e4_def, non_mem_expI)

lemma non_mem_exp_PMCNTENSET_EL0_SysRegRead_848c3aa603193fb7[non_mem_expI]:
  "non_mem_exp (PMCNTENSET_EL0_SysRegRead_848c3aa603193fb7 el op0 op1 CRn op2 CRm)"
  by (unfold PMCNTENSET_EL0_SysRegRead_848c3aa603193fb7_def, non_mem_expI)

lemma non_mem_exp_PMCR_EL0_SysRegRead_9a03e454327a1718[non_mem_expI]:
  "non_mem_exp (PMCR_EL0_SysRegRead_9a03e454327a1718 el op0 op1 CRn op2 CRm)"
  by (unfold PMCR_EL0_SysRegRead_9a03e454327a1718_def, non_mem_expI)

lemma non_mem_exp_PMEVCNTR_EL0_SysRegRead_e0380ad70bc25a0c[non_mem_expI]:
  "non_mem_exp (PMEVCNTR_EL0_SysRegRead_e0380ad70bc25a0c el op0 op1 CRn op2 CRm)"
  by (unfold PMEVCNTR_EL0_SysRegRead_e0380ad70bc25a0c_def, non_mem_expI)

lemma non_mem_exp_PMEVTYPER_EL0_SysRegRead_b05172ff9d10dad4[non_mem_expI]:
  "non_mem_exp (PMEVTYPER_EL0_SysRegRead_b05172ff9d10dad4 el op0 op1 CRn op2 CRm)"
  by (unfold PMEVTYPER_EL0_SysRegRead_b05172ff9d10dad4_def, non_mem_expI)

lemma non_mem_exp_PMINTENCLR_EL1_SysRegRead_43b8f4d9b40b2620[non_mem_expI]:
  "non_mem_exp (PMINTENCLR_EL1_SysRegRead_43b8f4d9b40b2620 el op0 op1 CRn op2 CRm)"
  by (unfold PMINTENCLR_EL1_SysRegRead_43b8f4d9b40b2620_def, non_mem_expI)

lemma non_mem_exp_PMINTENSET_EL1_SysRegRead_a3d4464c2051ff23[non_mem_expI]:
  "non_mem_exp (PMINTENSET_EL1_SysRegRead_a3d4464c2051ff23 el op0 op1 CRn op2 CRm)"
  by (unfold PMINTENSET_EL1_SysRegRead_a3d4464c2051ff23_def, non_mem_expI)

lemma non_mem_exp_PMOVSCLR_EL0_SysRegRead_300e5dfb491e58fa[non_mem_expI]:
  "non_mem_exp (PMOVSCLR_EL0_SysRegRead_300e5dfb491e58fa el op0 op1 CRn op2 CRm)"
  by (unfold PMOVSCLR_EL0_SysRegRead_300e5dfb491e58fa_def, non_mem_expI)

lemma non_mem_exp_PMOVSSET_EL0_SysRegRead_e3c0657a6c8b11c8[non_mem_expI]:
  "non_mem_exp (PMOVSSET_EL0_SysRegRead_e3c0657a6c8b11c8 el op0 op1 CRn op2 CRm)"
  by (unfold PMOVSSET_EL0_SysRegRead_e3c0657a6c8b11c8_def, non_mem_expI)

lemma non_mem_exp_PMSCR_EL12_SysRegRead_624c386ea3cce853[non_mem_expI]:
  "non_mem_exp (PMSCR_EL12_SysRegRead_624c386ea3cce853 el op0 op1 CRn op2 CRm)"
  by (unfold PMSCR_EL12_SysRegRead_624c386ea3cce853_def, non_mem_expI)

lemma non_mem_exp_PMSCR_EL1_SysRegRead_39ffc554ca37b155[non_mem_expI]:
  "non_mem_exp (PMSCR_EL1_SysRegRead_39ffc554ca37b155 el op0 op1 CRn op2 CRm)"
  by (unfold PMSCR_EL1_SysRegRead_39ffc554ca37b155_def, non_mem_expI)

lemma non_mem_exp_PMSCR_EL2_SysRegRead_11330bd80566814a[non_mem_expI]:
  "non_mem_exp (PMSCR_EL2_SysRegRead_11330bd80566814a el op0 op1 CRn op2 CRm)"
  by (unfold PMSCR_EL2_SysRegRead_11330bd80566814a_def, non_mem_expI)

lemma non_mem_exp_PMSELR_EL0_SysRegRead_540b592cb875b32f[non_mem_expI]:
  "non_mem_exp (PMSELR_EL0_SysRegRead_540b592cb875b32f el op0 op1 CRn op2 CRm)"
  by (unfold PMSELR_EL0_SysRegRead_540b592cb875b32f_def, non_mem_expI)

lemma non_mem_exp_PMSEVFR_EL1_SysRegRead_9e9a58f73d629d59[non_mem_expI]:
  "non_mem_exp (PMSEVFR_EL1_SysRegRead_9e9a58f73d629d59 el op0 op1 CRn op2 CRm)"
  by (unfold PMSEVFR_EL1_SysRegRead_9e9a58f73d629d59_def, non_mem_expI)

lemma non_mem_exp_PMSFCR_EL1_SysRegRead_30b07ff27088a488[non_mem_expI]:
  "non_mem_exp (PMSFCR_EL1_SysRegRead_30b07ff27088a488 el op0 op1 CRn op2 CRm)"
  by (unfold PMSFCR_EL1_SysRegRead_30b07ff27088a488_def, non_mem_expI)

lemma non_mem_exp_PMSICR_EL1_SysRegRead_1b4bf4bb07470e4c[non_mem_expI]:
  "non_mem_exp (PMSICR_EL1_SysRegRead_1b4bf4bb07470e4c el op0 op1 CRn op2 CRm)"
  by (unfold PMSICR_EL1_SysRegRead_1b4bf4bb07470e4c_def, non_mem_expI)

lemma non_mem_exp_PMSIDR_EL1_SysRegRead_062cecff79d24b4d[non_mem_expI]:
  "non_mem_exp (PMSIDR_EL1_SysRegRead_062cecff79d24b4d el op0 op1 CRn op2 CRm)"
  by (unfold PMSIDR_EL1_SysRegRead_062cecff79d24b4d_def, non_mem_expI)

lemma non_mem_exp_PMSIRR_EL1_SysRegRead_b565329ce30ac491[non_mem_expI]:
  "non_mem_exp (PMSIRR_EL1_SysRegRead_b565329ce30ac491 el op0 op1 CRn op2 CRm)"
  by (unfold PMSIRR_EL1_SysRegRead_b565329ce30ac491_def, non_mem_expI)

lemma non_mem_exp_PMSLATFR_EL1_SysRegRead_f82542fec2521a41[non_mem_expI]:
  "non_mem_exp (PMSLATFR_EL1_SysRegRead_f82542fec2521a41 el op0 op1 CRn op2 CRm)"
  by (unfold PMSLATFR_EL1_SysRegRead_f82542fec2521a41_def, non_mem_expI)

lemma non_mem_exp_PMUSERENR_EL0_SysRegRead_7efca1a4be376eb7[non_mem_expI]:
  "non_mem_exp (PMUSERENR_EL0_SysRegRead_7efca1a4be376eb7 el op0 op1 CRn op2 CRm)"
  by (unfold PMUSERENR_EL0_SysRegRead_7efca1a4be376eb7_def, non_mem_expI)

lemma non_mem_exp_PMXEVCNTR_EL0_SysRegRead_193921f886161922[non_mem_expI]:
  "non_mem_exp (PMXEVCNTR_EL0_SysRegRead_193921f886161922 el op0 op1 CRn op2 CRm)"
  by (unfold PMXEVCNTR_EL0_SysRegRead_193921f886161922_def, non_mem_expI)

lemma non_mem_exp_PMXEVTYPER_EL0_SysRegRead_a34d7cb6f32074c5[non_mem_expI]:
  "non_mem_exp (PMXEVTYPER_EL0_SysRegRead_a34d7cb6f32074c5 el op0 op1 CRn op2 CRm)"
  by (unfold PMXEVTYPER_EL0_SysRegRead_a34d7cb6f32074c5_def, non_mem_expI)

lemma non_mem_exp_REVIDR_EL1_SysRegRead_06ac796f098a1e84[non_mem_expI]:
  "non_mem_exp (REVIDR_EL1_SysRegRead_06ac796f098a1e84 el op0 op1 CRn op2 CRm)"
  by (unfold REVIDR_EL1_SysRegRead_06ac796f098a1e84_def, non_mem_expI)

lemma non_mem_exp_RMR_EL1_SysRegRead_69f4933c1a574580[non_mem_expI]:
  "non_mem_exp (RMR_EL1_SysRegRead_69f4933c1a574580 el op0 op1 CRn op2 CRm)"
  by (unfold RMR_EL1_SysRegRead_69f4933c1a574580_def, non_mem_expI)

lemma non_mem_exp_RMR_EL2_SysRegRead_75749340e0828f00[non_mem_expI]:
  "non_mem_exp (RMR_EL2_SysRegRead_75749340e0828f00 el op0 op1 CRn op2 CRm)"
  by (unfold RMR_EL2_SysRegRead_75749340e0828f00_def, non_mem_expI)

lemma non_mem_exp_RMR_EL3_SysRegRead_fa5f18c3b20f8894[non_mem_expI]:
  "non_mem_exp (RMR_EL3_SysRegRead_fa5f18c3b20f8894 el op0 op1 CRn op2 CRm)"
  by (unfold RMR_EL3_SysRegRead_fa5f18c3b20f8894_def, non_mem_expI)

lemma non_mem_exp_RSP_EL0_SysRegRead_b64c62bd96d973e3[non_mem_expI]:
  "non_mem_exp (RSP_EL0_SysRegRead_b64c62bd96d973e3 el op0 op1 CRn op2 CRm)"
  by (unfold RSP_EL0_SysRegRead_b64c62bd96d973e3_def, non_mem_expI)

lemma non_mem_exp_RTPIDR_EL0_SysRegRead_0ce5a74dba936523[non_mem_expI]:
  "non_mem_exp (RTPIDR_EL0_SysRegRead_0ce5a74dba936523 el op0 op1 CRn op2 CRm)"
  by (unfold RTPIDR_EL0_SysRegRead_0ce5a74dba936523_def, non_mem_expI)

lemma non_mem_exp_RVBAR_EL1_SysRegRead_48a958c9250293d1[non_mem_expI]:
  "non_mem_exp (RVBAR_EL1_SysRegRead_48a958c9250293d1 el op0 op1 CRn op2 CRm)"
  by (unfold RVBAR_EL1_SysRegRead_48a958c9250293d1_def, non_mem_expI)

lemma non_mem_exp_RVBAR_EL2_SysRegRead_2fb802203150f4cc[non_mem_expI]:
  "non_mem_exp (RVBAR_EL2_SysRegRead_2fb802203150f4cc el op0 op1 CRn op2 CRm)"
  by (unfold RVBAR_EL2_SysRegRead_2fb802203150f4cc_def, non_mem_expI)

lemma non_mem_exp_RVBAR_EL3_SysRegRead_000d1ea4b77ffa21[non_mem_expI]:
  "non_mem_exp (RVBAR_EL3_SysRegRead_000d1ea4b77ffa21 el op0 op1 CRn op2 CRm)"
  by (unfold RVBAR_EL3_SysRegRead_000d1ea4b77ffa21_def, non_mem_expI)

lemma non_mem_exp_S3_op1_CCn_CCm_op2_SysRegRead_d72a7245384bbc0e[non_mem_expI]:
  "non_mem_exp (S3_op1_CCn_CCm_op2_SysRegRead_d72a7245384bbc0e el op0 op1 CRn op2 CRm)"
  by (unfold S3_op1_CCn_CCm_op2_SysRegRead_d72a7245384bbc0e_def, non_mem_expI)

lemma non_mem_exp_SCR_EL3_SysRegRead_082a69b26890132d[non_mem_expI]:
  "non_mem_exp (SCR_EL3_SysRegRead_082a69b26890132d el op0 op1 CRn op2 CRm)"
  by (unfold SCR_EL3_SysRegRead_082a69b26890132d_def, non_mem_expI)

lemma non_mem_exp_SCTLR_EL12_SysRegRead_81ba00bca4ce39dc[non_mem_expI]:
  "non_mem_exp (SCTLR_EL12_SysRegRead_81ba00bca4ce39dc el op0 op1 CRn op2 CRm)"
  by (unfold SCTLR_EL12_SysRegRead_81ba00bca4ce39dc_def, non_mem_expI)

lemma non_mem_exp_SCTLR_EL1_SysRegRead_cc5fb072b0cb85eb[non_mem_expI]:
  "non_mem_exp (SCTLR_EL1_SysRegRead_cc5fb072b0cb85eb el op0 op1 CRn op2 CRm)"
  by (unfold SCTLR_EL1_SysRegRead_cc5fb072b0cb85eb_def, non_mem_expI)

lemma non_mem_exp_SCTLR_EL2_SysRegRead_3cc208f3abf97e34[non_mem_expI]:
  "non_mem_exp (SCTLR_EL2_SysRegRead_3cc208f3abf97e34 el op0 op1 CRn op2 CRm)"
  by (unfold SCTLR_EL2_SysRegRead_3cc208f3abf97e34_def, non_mem_expI)

lemma non_mem_exp_SCTLR_EL3_SysRegRead_9c537c9c01007c3e[non_mem_expI]:
  "non_mem_exp (SCTLR_EL3_SysRegRead_9c537c9c01007c3e el op0 op1 CRn op2 CRm)"
  by (unfold SCTLR_EL3_SysRegRead_9c537c9c01007c3e_def, non_mem_expI)

lemma non_mem_exp_SCXTNUM_EL0_read[non_mem_expI]:
  "non_mem_exp (SCXTNUM_EL0_read arg0)"
  by (unfold SCXTNUM_EL0_read_def, non_mem_expI)

lemma non_mem_exp_SCXTNUM_EL0_SysRegRead_ee5b769fc7f044cc[non_mem_expI]:
  "non_mem_exp (SCXTNUM_EL0_SysRegRead_ee5b769fc7f044cc el op0 op1 CRn op2 CRm)"
  by (unfold SCXTNUM_EL0_SysRegRead_ee5b769fc7f044cc_def, non_mem_expI)

lemma non_mem_exp_SCXTNUM_EL12_SysRegRead_d31f345333a78d48[non_mem_expI]:
  "non_mem_exp (SCXTNUM_EL12_SysRegRead_d31f345333a78d48 el op0 op1 CRn op2 CRm)"
  by (unfold SCXTNUM_EL12_SysRegRead_d31f345333a78d48_def, non_mem_expI)

lemma non_mem_exp_SCXTNUM_EL1_SysRegRead_dd27b7ad05ded1ab[non_mem_expI]:
  "non_mem_exp (SCXTNUM_EL1_SysRegRead_dd27b7ad05ded1ab el op0 op1 CRn op2 CRm)"
  by (unfold SCXTNUM_EL1_SysRegRead_dd27b7ad05ded1ab_def, non_mem_expI)

lemma non_mem_exp_SCXTNUM_EL2_SysRegRead_421b17f19f5fdd2a[non_mem_expI]:
  "non_mem_exp (SCXTNUM_EL2_SysRegRead_421b17f19f5fdd2a el op0 op1 CRn op2 CRm)"
  by (unfold SCXTNUM_EL2_SysRegRead_421b17f19f5fdd2a_def, non_mem_expI)

lemma non_mem_exp_SCXTNUM_EL3_SysRegRead_5f15a3b4da1bd4bb[non_mem_expI]:
  "non_mem_exp (SCXTNUM_EL3_SysRegRead_5f15a3b4da1bd4bb el op0 op1 CRn op2 CRm)"
  by (unfold SCXTNUM_EL3_SysRegRead_5f15a3b4da1bd4bb_def, non_mem_expI)

lemma non_mem_exp_SDER32_EL3_SysRegRead_e21f871563c7e34e[non_mem_expI]:
  "non_mem_exp (SDER32_EL3_SysRegRead_e21f871563c7e34e el op0 op1 CRn op2 CRm)"
  by (unfold SDER32_EL3_SysRegRead_e21f871563c7e34e_def, non_mem_expI)

lemma non_mem_exp_SPSel_SysRegRead_ac7632fd1580b15b[non_mem_expI]:
  "non_mem_exp (SPSel_SysRegRead_ac7632fd1580b15b el op0 op1 CRn op2 CRm)"
  by (unfold SPSel_SysRegRead_ac7632fd1580b15b_def, non_mem_expI)

lemma non_mem_exp_SP_EL0_SysRegRead_4b07157e43cd0456[non_mem_expI]:
  "non_mem_exp (SP_EL0_SysRegRead_4b07157e43cd0456 el op0 op1 CRn op2 CRm)"
  by (unfold SP_EL0_SysRegRead_4b07157e43cd0456_def, non_mem_expI)

lemma non_mem_exp_SP_EL1_SysRegRead_44ac23d2a7608550[non_mem_expI]:
  "non_mem_exp (SP_EL1_SysRegRead_44ac23d2a7608550 el op0 op1 CRn op2 CRm)"
  by (unfold SP_EL1_SysRegRead_44ac23d2a7608550_def, non_mem_expI)

lemma non_mem_exp_SP_EL2_SysRegRead_9c4b7d596526b300[non_mem_expI]:
  "non_mem_exp (SP_EL2_SysRegRead_9c4b7d596526b300 el op0 op1 CRn op2 CRm)"
  by (unfold SP_EL2_SysRegRead_9c4b7d596526b300_def, non_mem_expI)

lemma non_mem_exp_TCR_EL12_SysRegRead_cefcc3f131a70a7f[non_mem_expI]:
  "non_mem_exp (TCR_EL12_SysRegRead_cefcc3f131a70a7f el op0 op1 CRn op2 CRm)"
  by (unfold TCR_EL12_SysRegRead_cefcc3f131a70a7f_def, non_mem_expI)

lemma non_mem_exp_TCR_EL1_SysRegRead_fbe255888fba9865[non_mem_expI]:
  "non_mem_exp (TCR_EL1_SysRegRead_fbe255888fba9865 el op0 op1 CRn op2 CRm)"
  by (unfold TCR_EL1_SysRegRead_fbe255888fba9865_def, non_mem_expI)

lemma non_mem_exp_TCR_EL2_SysRegRead_3467687df9c2aec1[non_mem_expI]:
  "non_mem_exp (TCR_EL2_SysRegRead_3467687df9c2aec1 el op0 op1 CRn op2 CRm)"
  by (unfold TCR_EL2_SysRegRead_3467687df9c2aec1_def, non_mem_expI)

lemma non_mem_exp_TCR_EL3_SysRegRead_7da88d4a232f9451[non_mem_expI]:
  "non_mem_exp (TCR_EL3_SysRegRead_7da88d4a232f9451 el op0 op1 CRn op2 CRm)"
  by (unfold TCR_EL3_SysRegRead_7da88d4a232f9451_def, non_mem_expI)

lemma non_mem_exp_TPIDRRO_EL0_SysRegRead_3dc5dc323922fcfa[non_mem_expI]:
  "non_mem_exp (TPIDRRO_EL0_SysRegRead_3dc5dc323922fcfa el op0 op1 CRn op2 CRm)"
  by (unfold TPIDRRO_EL0_SysRegRead_3dc5dc323922fcfa_def, non_mem_expI)

lemma non_mem_exp_TPIDR_EL0_SysRegRead_7b944c4fc3d3f60f[non_mem_expI]:
  "non_mem_exp (TPIDR_EL0_SysRegRead_7b944c4fc3d3f60f el op0 op1 CRn op2 CRm)"
  by (unfold TPIDR_EL0_SysRegRead_7b944c4fc3d3f60f_def, non_mem_expI)

lemma non_mem_exp_TPIDR_EL1_SysRegRead_8db91ea8b9abc411[non_mem_expI]:
  "non_mem_exp (TPIDR_EL1_SysRegRead_8db91ea8b9abc411 el op0 op1 CRn op2 CRm)"
  by (unfold TPIDR_EL1_SysRegRead_8db91ea8b9abc411_def, non_mem_expI)

lemma non_mem_exp_TPIDR_EL2_SysRegRead_fc4633f7449b5b4a[non_mem_expI]:
  "non_mem_exp (TPIDR_EL2_SysRegRead_fc4633f7449b5b4a el op0 op1 CRn op2 CRm)"
  by (unfold TPIDR_EL2_SysRegRead_fc4633f7449b5b4a_def, non_mem_expI)

lemma non_mem_exp_TPIDR_EL3_SysRegRead_c6069d62b310a137[non_mem_expI]:
  "non_mem_exp (TPIDR_EL3_SysRegRead_c6069d62b310a137 el op0 op1 CRn op2 CRm)"
  by (unfold TPIDR_EL3_SysRegRead_c6069d62b310a137_def, non_mem_expI)

lemma non_mem_exp_TTBR0_EL12_SysRegRead_73f9bd4d027badee[non_mem_expI]:
  "non_mem_exp (TTBR0_EL12_SysRegRead_73f9bd4d027badee el op0 op1 CRn op2 CRm)"
  by (unfold TTBR0_EL12_SysRegRead_73f9bd4d027badee_def, non_mem_expI)

lemma non_mem_exp_TTBR0_EL1_SysRegRead_2e8a6c25b2e4759a[non_mem_expI]:
  "non_mem_exp (TTBR0_EL1_SysRegRead_2e8a6c25b2e4759a el op0 op1 CRn op2 CRm)"
  by (unfold TTBR0_EL1_SysRegRead_2e8a6c25b2e4759a_def, non_mem_expI)

lemma non_mem_exp_TTBR0_EL2_SysRegRead_8d4de9e080477354[non_mem_expI]:
  "non_mem_exp (TTBR0_EL2_SysRegRead_8d4de9e080477354 el op0 op1 CRn op2 CRm)"
  by (unfold TTBR0_EL2_SysRegRead_8d4de9e080477354_def, non_mem_expI)

lemma non_mem_exp_TTBR0_EL3_SysRegRead_a46e35edfe45a273[non_mem_expI]:
  "non_mem_exp (TTBR0_EL3_SysRegRead_a46e35edfe45a273 el op0 op1 CRn op2 CRm)"
  by (unfold TTBR0_EL3_SysRegRead_a46e35edfe45a273_def, non_mem_expI)

lemma non_mem_exp_TTBR1_EL12_SysRegRead_bfbc2899eb278d2b[non_mem_expI]:
  "non_mem_exp (TTBR1_EL12_SysRegRead_bfbc2899eb278d2b el op0 op1 CRn op2 CRm)"
  by (unfold TTBR1_EL12_SysRegRead_bfbc2899eb278d2b_def, non_mem_expI)

lemma non_mem_exp_TTBR1_EL1_SysRegRead_2cb2fb59089165c5[non_mem_expI]:
  "non_mem_exp (TTBR1_EL1_SysRegRead_2cb2fb59089165c5 el op0 op1 CRn op2 CRm)"
  by (unfold TTBR1_EL1_SysRegRead_2cb2fb59089165c5_def, non_mem_expI)

lemma non_mem_exp_TTBR1_EL2_SysRegRead_08cd28a9b17bc317[non_mem_expI]:
  "non_mem_exp (TTBR1_EL2_SysRegRead_08cd28a9b17bc317 el op0 op1 CRn op2 CRm)"
  by (unfold TTBR1_EL2_SysRegRead_08cd28a9b17bc317_def, non_mem_expI)

lemma non_mem_exp_VBAR_EL12_SysRegRead_2ad4e02fbe99cf3d[non_mem_expI]:
  "non_mem_exp (VBAR_EL12_SysRegRead_2ad4e02fbe99cf3d el op0 op1 CRn op2 CRm)"
  by (unfold VBAR_EL12_SysRegRead_2ad4e02fbe99cf3d_def, non_mem_expI)

lemma non_mem_exp_VBAR_EL1_SysRegRead_4d14cb3b6fe16ab6[non_mem_expI]:
  "non_mem_exp (VBAR_EL1_SysRegRead_4d14cb3b6fe16ab6 el op0 op1 CRn op2 CRm)"
  by (unfold VBAR_EL1_SysRegRead_4d14cb3b6fe16ab6_def, non_mem_expI)

lemma non_mem_exp_VBAR_EL2_SysRegRead_1f6b3c94ccfecacf[non_mem_expI]:
  "non_mem_exp (VBAR_EL2_SysRegRead_1f6b3c94ccfecacf el op0 op1 CRn op2 CRm)"
  by (unfold VBAR_EL2_SysRegRead_1f6b3c94ccfecacf_def, non_mem_expI)

lemma non_mem_exp_VBAR_EL3_SysRegRead_32f42cb574998654[non_mem_expI]:
  "non_mem_exp (VBAR_EL3_SysRegRead_32f42cb574998654 el op0 op1 CRn op2 CRm)"
  by (unfold VBAR_EL3_SysRegRead_32f42cb574998654_def, non_mem_expI)

lemma non_mem_exp_VDISR_EL2_SysRegRead_14dff4ad4ae8c3a2[non_mem_expI]:
  "non_mem_exp (VDISR_EL2_SysRegRead_14dff4ad4ae8c3a2 el op0 op1 CRn op2 CRm)"
  by (unfold VDISR_EL2_SysRegRead_14dff4ad4ae8c3a2_def, non_mem_expI)

lemma non_mem_exp_VMPIDR_EL2_SysRegRead_49b7c13dd1b0804c[non_mem_expI]:
  "non_mem_exp (VMPIDR_EL2_SysRegRead_49b7c13dd1b0804c el op0 op1 CRn op2 CRm)"
  by (unfold VMPIDR_EL2_SysRegRead_49b7c13dd1b0804c_def, non_mem_expI)

lemma non_mem_exp_VPIDR_EL2_SysRegRead_f6520cd6a1f62bd8[non_mem_expI]:
  "non_mem_exp (VPIDR_EL2_SysRegRead_f6520cd6a1f62bd8 el op0 op1 CRn op2 CRm)"
  by (unfold VPIDR_EL2_SysRegRead_f6520cd6a1f62bd8_def, non_mem_expI)

lemma non_mem_exp_VSESR_EL2_SysRegRead_401c063e57574698[non_mem_expI]:
  "non_mem_exp (VSESR_EL2_SysRegRead_401c063e57574698 el op0 op1 CRn op2 CRm)"
  by (unfold VSESR_EL2_SysRegRead_401c063e57574698_def, non_mem_expI)

lemma non_mem_exp_VTCR_EL2_SysRegRead_5c8ea980dc5cc1d1[non_mem_expI]:
  "non_mem_exp (VTCR_EL2_SysRegRead_5c8ea980dc5cc1d1 el op0 op1 CRn op2 CRm)"
  by (unfold VTCR_EL2_SysRegRead_5c8ea980dc5cc1d1_def, non_mem_expI)

lemma non_mem_exp_VTTBR_EL2_SysRegRead_2fbbdccc9485564d[non_mem_expI]:
  "non_mem_exp (VTTBR_EL2_SysRegRead_2fbbdccc9485564d el op0 op1 CRn op2 CRm)"
  by (unfold VTTBR_EL2_SysRegRead_2fbbdccc9485564d_def, non_mem_expI)

lemma non_mem_exp_AArch64_AutoGen_SysRegRead[non_mem_expI]:
  "non_mem_exp (AArch64_AutoGen_SysRegRead el op0 op1 CRn op2 CRm)"
  by (unfold AArch64_AutoGen_SysRegRead_def, non_mem_expI)

lemma non_mem_exp_AArch64_SysRegRead[non_mem_expI]:
  "non_mem_exp (AArch64_SysRegRead op0 op1 crn crm op2)"
  by (unfold AArch64_SysRegRead_def, non_mem_expI)

lemma non_mem_exp_CDBGDTR_EL0_CapSysRegRead_8e23daae0e60af34[non_mem_expI]:
  "non_mem_exp (CDBGDTR_EL0_CapSysRegRead_8e23daae0e60af34 el op0 op1 CRn op2 CRm)"
  by (unfold CDBGDTR_EL0_CapSysRegRead_8e23daae0e60af34_def, non_mem_expI)

lemma non_mem_exp_CDLR_EL0_CapSysRegRead_619c852c71c0978d[non_mem_expI]:
  "non_mem_exp (CDLR_EL0_CapSysRegRead_619c852c71c0978d el op0 op1 CRn op2 CRm)"
  by (unfold CDLR_EL0_CapSysRegRead_619c852c71c0978d_def, non_mem_expI)

lemma non_mem_exp_CELR_EL12_CapSysRegRead_4bf271777fe55d1c[non_mem_expI]:
  "non_mem_exp (CELR_EL12_CapSysRegRead_4bf271777fe55d1c el op0 op1 CRn op2 CRm)"
  by (unfold CELR_EL12_CapSysRegRead_4bf271777fe55d1c_def, non_mem_expI)

lemma non_mem_exp_CELR_EL1_CapSysRegRead_da9869d2314a30d5[non_mem_expI]:
  "non_mem_exp (CELR_EL1_CapSysRegRead_da9869d2314a30d5 el op0 op1 CRn op2 CRm)"
  by (unfold CELR_EL1_CapSysRegRead_da9869d2314a30d5_def, non_mem_expI)

lemma non_mem_exp_CELR_EL2_CapSysRegRead_a9e9661da428a6d4[non_mem_expI]:
  "non_mem_exp (CELR_EL2_CapSysRegRead_a9e9661da428a6d4 el op0 op1 CRn op2 CRm)"
  by (unfold CELR_EL2_CapSysRegRead_a9e9661da428a6d4_def, non_mem_expI)

lemma non_mem_exp_CELR_EL3_CapSysRegRead_d0424a232c45967e[non_mem_expI]:
  "non_mem_exp (CELR_EL3_CapSysRegRead_d0424a232c45967e el op0 op1 CRn op2 CRm)"
  by (unfold CELR_EL3_CapSysRegRead_d0424a232c45967e_def, non_mem_expI)

lemma non_mem_exp_CID_EL0_CapSysRegRead_d560f6b1104266f1[non_mem_expI]:
  "non_mem_exp (CID_EL0_CapSysRegRead_d560f6b1104266f1 el op0 op1 CRn op2 CRm)"
  by (unfold CID_EL0_CapSysRegRead_d560f6b1104266f1_def, non_mem_expI)

lemma non_mem_exp_CSP_EL0_CapSysRegRead_e5b1ba121f8be4da[non_mem_expI]:
  "non_mem_exp (CSP_EL0_CapSysRegRead_e5b1ba121f8be4da el op0 op1 CRn op2 CRm)"
  by (unfold CSP_EL0_CapSysRegRead_e5b1ba121f8be4da_def, non_mem_expI)

lemma non_mem_exp_CSP_EL1_CapSysRegRead_bb8b6c0ba689eafb[non_mem_expI]:
  "non_mem_exp (CSP_EL1_CapSysRegRead_bb8b6c0ba689eafb el op0 op1 CRn op2 CRm)"
  by (unfold CSP_EL1_CapSysRegRead_bb8b6c0ba689eafb_def, non_mem_expI)

lemma non_mem_exp_CSP_EL2_CapSysRegRead_9b50d2f92d5520da[non_mem_expI]:
  "non_mem_exp (CSP_EL2_CapSysRegRead_9b50d2f92d5520da el op0 op1 CRn op2 CRm)"
  by (unfold CSP_EL2_CapSysRegRead_9b50d2f92d5520da_def, non_mem_expI)

lemma non_mem_exp_CTPIDRRO_EL0_CapSysRegRead_2def4a85803ae7cc[non_mem_expI]:
  "non_mem_exp (CTPIDRRO_EL0_CapSysRegRead_2def4a85803ae7cc el op0 op1 CRn op2 CRm)"
  by (unfold CTPIDRRO_EL0_CapSysRegRead_2def4a85803ae7cc_def, non_mem_expI)

lemma non_mem_exp_CTPIDR_EL0_CapSysRegRead_84b933ea55a77369[non_mem_expI]:
  "non_mem_exp (CTPIDR_EL0_CapSysRegRead_84b933ea55a77369 el op0 op1 CRn op2 CRm)"
  by (unfold CTPIDR_EL0_CapSysRegRead_84b933ea55a77369_def, non_mem_expI)

lemma non_mem_exp_CTPIDR_EL1_CapSysRegRead_016308c12b886084[non_mem_expI]:
  "non_mem_exp (CTPIDR_EL1_CapSysRegRead_016308c12b886084 el op0 op1 CRn op2 CRm)"
  by (unfold CTPIDR_EL1_CapSysRegRead_016308c12b886084_def, non_mem_expI)

lemma non_mem_exp_CTPIDR_EL2_CapSysRegRead_b7d4714a1ce62544[non_mem_expI]:
  "non_mem_exp (CTPIDR_EL2_CapSysRegRead_b7d4714a1ce62544 el op0 op1 CRn op2 CRm)"
  by (unfold CTPIDR_EL2_CapSysRegRead_b7d4714a1ce62544_def, non_mem_expI)

lemma non_mem_exp_CTPIDR_EL3_CapSysRegRead_c1307a9bc7bc1449[non_mem_expI]:
  "non_mem_exp (CTPIDR_EL3_CapSysRegRead_c1307a9bc7bc1449 el op0 op1 CRn op2 CRm)"
  by (unfold CTPIDR_EL3_CapSysRegRead_c1307a9bc7bc1449_def, non_mem_expI)

lemma non_mem_exp_CVBAR_EL12_CapSysRegRead_845c94ac498ff593[non_mem_expI]:
  "non_mem_exp (CVBAR_EL12_CapSysRegRead_845c94ac498ff593 el op0 op1 CRn op2 CRm)"
  by (unfold CVBAR_EL12_CapSysRegRead_845c94ac498ff593_def, non_mem_expI)

lemma non_mem_exp_CVBAR_EL1_CapSysRegRead_c42109445741a0d0[non_mem_expI]:
  "non_mem_exp (CVBAR_EL1_CapSysRegRead_c42109445741a0d0 el op0 op1 CRn op2 CRm)"
  by (unfold CVBAR_EL1_CapSysRegRead_c42109445741a0d0_def, non_mem_expI)

lemma non_mem_exp_CVBAR_EL2_CapSysRegRead_537232bbd7d69e00[non_mem_expI]:
  "non_mem_exp (CVBAR_EL2_CapSysRegRead_537232bbd7d69e00 el op0 op1 CRn op2 CRm)"
  by (unfold CVBAR_EL2_CapSysRegRead_537232bbd7d69e00_def, non_mem_expI)

lemma non_mem_exp_CVBAR_EL3_CapSysRegRead_587d4a028f8f0ef1[non_mem_expI]:
  "non_mem_exp (CVBAR_EL3_CapSysRegRead_587d4a028f8f0ef1 el op0 op1 CRn op2 CRm)"
  by (unfold CVBAR_EL3_CapSysRegRead_587d4a028f8f0ef1_def, non_mem_expI)

lemma non_mem_exp_DDC_CapSysRegRead_eabc4ea34a10a962[non_mem_expI]:
  "non_mem_exp (DDC_CapSysRegRead_eabc4ea34a10a962 el op0 op1 CRn op2 CRm)"
  by (unfold DDC_CapSysRegRead_eabc4ea34a10a962_def, non_mem_expI)

lemma non_mem_exp_DDC_EL0_CapSysRegRead_e02bc676dce7fb51[non_mem_expI]:
  "non_mem_exp (DDC_EL0_CapSysRegRead_e02bc676dce7fb51 el op0 op1 CRn op2 CRm)"
  by (unfold DDC_EL0_CapSysRegRead_e02bc676dce7fb51_def, non_mem_expI)

lemma non_mem_exp_DDC_EL1_CapSysRegRead_08f46354e9afc01e[non_mem_expI]:
  "non_mem_exp (DDC_EL1_CapSysRegRead_08f46354e9afc01e el op0 op1 CRn op2 CRm)"
  by (unfold DDC_EL1_CapSysRegRead_08f46354e9afc01e_def, non_mem_expI)

lemma non_mem_exp_DDC_EL2_CapSysRegRead_6d2409222a719403[non_mem_expI]:
  "non_mem_exp (DDC_EL2_CapSysRegRead_6d2409222a719403 el op0 op1 CRn op2 CRm)"
  by (unfold DDC_EL2_CapSysRegRead_6d2409222a719403_def, non_mem_expI)

lemma non_mem_exp_RCSP_EL0_CapSysRegRead_6a9b29b9027548c3[non_mem_expI]:
  "non_mem_exp (RCSP_EL0_CapSysRegRead_6a9b29b9027548c3 el op0 op1 CRn op2 CRm)"
  by (unfold RCSP_EL0_CapSysRegRead_6a9b29b9027548c3_def, non_mem_expI)

lemma non_mem_exp_RCTPIDR_EL0_CapSysRegRead_0a3ce9d2144ddba7[non_mem_expI]:
  "non_mem_exp (RCTPIDR_EL0_CapSysRegRead_0a3ce9d2144ddba7 el op0 op1 CRn op2 CRm)"
  by (unfold RCTPIDR_EL0_CapSysRegRead_0a3ce9d2144ddba7_def, non_mem_expI)

lemma non_mem_exp_RDDC_EL0_CapSysRegRead_c188e736aa7b9beb[non_mem_expI]:
  "non_mem_exp (RDDC_EL0_CapSysRegRead_c188e736aa7b9beb el op0 op1 CRn op2 CRm)"
  by (unfold RDDC_EL0_CapSysRegRead_c188e736aa7b9beb_def, non_mem_expI)

lemma non_mem_exp_AArch64_AutoGen_CapSysRegRead[non_mem_expI]:
  "non_mem_exp (AArch64_AutoGen_CapSysRegRead el op0 op1 CRn op2 CRm)"
  by (unfold AArch64_AutoGen_CapSysRegRead_def, non_mem_expI)

lemma non_mem_exp_DDC_read[non_mem_expI]:
  "non_mem_exp (DDC_read arg0)"
  by (unfold DDC_read_def, non_mem_expI)

lemma non_mem_exp_AArch64_CapSysRegRead[non_mem_expI]:
  "non_mem_exp (AArch64_CapSysRegRead op0 op1 crn crm op2)"
  by (unfold AArch64_CapSysRegRead_def, non_mem_expI)

lemma non_mem_exp_ACTLR_EL1_SysRegWrite_338051dbe9bdf650[non_mem_expI]:
  "non_mem_exp (ACTLR_EL1_SysRegWrite_338051dbe9bdf650 el op0 op1 CRn op2 CRm val_name)"
  by (unfold ACTLR_EL1_SysRegWrite_338051dbe9bdf650_def, non_mem_expI)

lemma non_mem_exp_ACTLR_EL2_SysRegWrite_416ec7c6fadd122d[non_mem_expI]:
  "non_mem_exp (ACTLR_EL2_SysRegWrite_416ec7c6fadd122d el op0 op1 CRn op2 CRm val_name)"
  by (unfold ACTLR_EL2_SysRegWrite_416ec7c6fadd122d_def, non_mem_expI)

lemma non_mem_exp_ACTLR_EL3_SysRegWrite_c797d5a80525afa4[non_mem_expI]:
  "non_mem_exp (ACTLR_EL3_SysRegWrite_c797d5a80525afa4 el op0 op1 CRn op2 CRm val_name)"
  by (unfold ACTLR_EL3_SysRegWrite_c797d5a80525afa4_def, non_mem_expI)

lemma non_mem_exp_AFSR0_EL12_SysRegWrite_9fafb4f6dbddd904[non_mem_expI]:
  "non_mem_exp (AFSR0_EL12_SysRegWrite_9fafb4f6dbddd904 el op0 op1 CRn op2 CRm val_name)"
  by (unfold AFSR0_EL12_SysRegWrite_9fafb4f6dbddd904_def, non_mem_expI)

lemma non_mem_exp_AFSR0_EL1_SysRegWrite_04474930979e1c86[non_mem_expI]:
  "non_mem_exp (AFSR0_EL1_SysRegWrite_04474930979e1c86 el op0 op1 CRn op2 CRm val_name)"
  by (unfold AFSR0_EL1_SysRegWrite_04474930979e1c86_def, non_mem_expI)

lemma non_mem_exp_AFSR0_EL2_SysRegWrite_2f9da4789f5b4073[non_mem_expI]:
  "non_mem_exp (AFSR0_EL2_SysRegWrite_2f9da4789f5b4073 el op0 op1 CRn op2 CRm val_name)"
  by (unfold AFSR0_EL2_SysRegWrite_2f9da4789f5b4073_def, non_mem_expI)

lemma non_mem_exp_AFSR0_EL3_SysRegWrite_e615501306210a25[non_mem_expI]:
  "non_mem_exp (AFSR0_EL3_SysRegWrite_e615501306210a25 el op0 op1 CRn op2 CRm val_name)"
  by (unfold AFSR0_EL3_SysRegWrite_e615501306210a25_def, non_mem_expI)

lemma non_mem_exp_AFSR1_EL12_SysRegWrite_9dbf207cccd92d9d[non_mem_expI]:
  "non_mem_exp (AFSR1_EL12_SysRegWrite_9dbf207cccd92d9d el op0 op1 CRn op2 CRm val_name)"
  by (unfold AFSR1_EL12_SysRegWrite_9dbf207cccd92d9d_def, non_mem_expI)

lemma non_mem_exp_AFSR1_EL1_SysRegWrite_6690138c9fdd136c[non_mem_expI]:
  "non_mem_exp (AFSR1_EL1_SysRegWrite_6690138c9fdd136c el op0 op1 CRn op2 CRm val_name)"
  by (unfold AFSR1_EL1_SysRegWrite_6690138c9fdd136c_def, non_mem_expI)

lemma non_mem_exp_AFSR1_EL2_SysRegWrite_c0ebc4cc65472544[non_mem_expI]:
  "non_mem_exp (AFSR1_EL2_SysRegWrite_c0ebc4cc65472544 el op0 op1 CRn op2 CRm val_name)"
  by (unfold AFSR1_EL2_SysRegWrite_c0ebc4cc65472544_def, non_mem_expI)

lemma non_mem_exp_AFSR1_EL3_SysRegWrite_d776cc264803f49e[non_mem_expI]:
  "non_mem_exp (AFSR1_EL3_SysRegWrite_d776cc264803f49e el op0 op1 CRn op2 CRm val_name)"
  by (unfold AFSR1_EL3_SysRegWrite_d776cc264803f49e_def, non_mem_expI)

lemma non_mem_exp_AMAIR_EL12_SysRegWrite_9c44aba2de7c2ff8[non_mem_expI]:
  "non_mem_exp (AMAIR_EL12_SysRegWrite_9c44aba2de7c2ff8 el op0 op1 CRn op2 CRm val_name)"
  by (unfold AMAIR_EL12_SysRegWrite_9c44aba2de7c2ff8_def, non_mem_expI)

lemma non_mem_exp_AMAIR_EL1_SysRegWrite_0d9c3d92d9a71703[non_mem_expI]:
  "non_mem_exp (AMAIR_EL1_SysRegWrite_0d9c3d92d9a71703 el op0 op1 CRn op2 CRm val_name)"
  by (unfold AMAIR_EL1_SysRegWrite_0d9c3d92d9a71703_def, non_mem_expI)

lemma non_mem_exp_AMAIR_EL2_SysRegWrite_9345da970d78b298[non_mem_expI]:
  "non_mem_exp (AMAIR_EL2_SysRegWrite_9345da970d78b298 el op0 op1 CRn op2 CRm val_name)"
  by (unfold AMAIR_EL2_SysRegWrite_9345da970d78b298_def, non_mem_expI)

lemma non_mem_exp_AMAIR_EL3_SysRegWrite_622c473bfedac80a[non_mem_expI]:
  "non_mem_exp (AMAIR_EL3_SysRegWrite_622c473bfedac80a el op0 op1 CRn op2 CRm val_name)"
  by (unfold AMAIR_EL3_SysRegWrite_622c473bfedac80a_def, non_mem_expI)

lemma non_mem_exp_CCTLR_EL0_SysRegWrite_a4d8c57cb436292b[non_mem_expI]:
  "non_mem_exp (CCTLR_EL0_SysRegWrite_a4d8c57cb436292b el op0 op1 CRn op2 CRm val_name)"
  by (unfold CCTLR_EL0_SysRegWrite_a4d8c57cb436292b_def, non_mem_expI)

lemma non_mem_exp_CCTLR_EL12_SysRegWrite_c7d9d6463096d910[non_mem_expI]:
  "non_mem_exp (CCTLR_EL12_SysRegWrite_c7d9d6463096d910 el op0 op1 CRn op2 CRm val_name)"
  by (unfold CCTLR_EL12_SysRegWrite_c7d9d6463096d910_def, non_mem_expI)

lemma non_mem_exp_CCTLR_EL1_SysRegWrite_dc20ad2a867ac9bf[non_mem_expI]:
  "non_mem_exp (CCTLR_EL1_SysRegWrite_dc20ad2a867ac9bf el op0 op1 CRn op2 CRm val_name)"
  by (unfold CCTLR_EL1_SysRegWrite_dc20ad2a867ac9bf_def, non_mem_expI)

lemma non_mem_exp_CCTLR_EL2_SysRegWrite_65620c8ccb1113a5[non_mem_expI]:
  "non_mem_exp (CCTLR_EL2_SysRegWrite_65620c8ccb1113a5 el op0 op1 CRn op2 CRm val_name)"
  by (unfold CCTLR_EL2_SysRegWrite_65620c8ccb1113a5_def, non_mem_expI)

lemma non_mem_exp_CCTLR_EL3_SysRegWrite_f5e936c8846e6fc7[non_mem_expI]:
  "non_mem_exp (CCTLR_EL3_SysRegWrite_f5e936c8846e6fc7 el op0 op1 CRn op2 CRm val_name)"
  by (unfold CCTLR_EL3_SysRegWrite_f5e936c8846e6fc7_def, non_mem_expI)

lemma non_mem_exp_CHCR_EL2_SysRegWrite_dadda8ecf053e448[non_mem_expI]:
  "non_mem_exp (CHCR_EL2_SysRegWrite_dadda8ecf053e448 el op0 op1 CRn op2 CRm val_name)"
  by (unfold CHCR_EL2_SysRegWrite_dadda8ecf053e448_def, non_mem_expI)

lemma non_mem_exp_CNTFRQ_EL0_SysRegWrite_0fac77f077759456[non_mem_expI]:
  "non_mem_exp (CNTFRQ_EL0_SysRegWrite_0fac77f077759456 el op0 op1 CRn op2 CRm val_name)"
  by (unfold CNTFRQ_EL0_SysRegWrite_0fac77f077759456_def, non_mem_expI)

lemma non_mem_exp_CNTHCTL_EL2_SysRegWrite_eb0cbec9f9398e0e[non_mem_expI]:
  "non_mem_exp (CNTHCTL_EL2_SysRegWrite_eb0cbec9f9398e0e el op0 op1 CRn op2 CRm val_name)"
  by (unfold CNTHCTL_EL2_SysRegWrite_eb0cbec9f9398e0e_def, non_mem_expI)

lemma non_mem_exp_CNTHP_CTL_EL2_SysRegWrite_92034fc54290a7b8[non_mem_expI]:
  "non_mem_exp (CNTHP_CTL_EL2_SysRegWrite_92034fc54290a7b8 el op0 op1 CRn op2 CRm val_name)"
  by (unfold CNTHP_CTL_EL2_SysRegWrite_92034fc54290a7b8_def, non_mem_expI)

lemma non_mem_exp_CNTHP_CVAL_EL2_SysRegWrite_36de219faded7cbc[non_mem_expI]:
  "non_mem_exp (CNTHP_CVAL_EL2_SysRegWrite_36de219faded7cbc el op0 op1 CRn op2 CRm val_name)"
  by (unfold CNTHP_CVAL_EL2_SysRegWrite_36de219faded7cbc_def, non_mem_expI)

lemma non_mem_exp_CNTHP_TVAL_EL2_SysRegWrite_877bbf4f78f810b9[non_mem_expI]:
  "non_mem_exp (CNTHP_TVAL_EL2_SysRegWrite_877bbf4f78f810b9 el op0 op1 CRn op2 CRm val_name)"
  by (unfold CNTHP_TVAL_EL2_SysRegWrite_877bbf4f78f810b9_def, non_mem_expI)

lemma non_mem_exp_CNTHV_CTL_EL2_SysRegWrite_ecc786a588fc8ab9[non_mem_expI]:
  "non_mem_exp (CNTHV_CTL_EL2_SysRegWrite_ecc786a588fc8ab9 el op0 op1 CRn op2 CRm val_name)"
  by (unfold CNTHV_CTL_EL2_SysRegWrite_ecc786a588fc8ab9_def, non_mem_expI)

lemma non_mem_exp_CNTHV_CVAL_EL2_SysRegWrite_b3d7c631e2b3eaab[non_mem_expI]:
  "non_mem_exp (CNTHV_CVAL_EL2_SysRegWrite_b3d7c631e2b3eaab el op0 op1 CRn op2 CRm val_name)"
  by (unfold CNTHV_CVAL_EL2_SysRegWrite_b3d7c631e2b3eaab_def, non_mem_expI)

lemma non_mem_exp_CNTHV_TVAL_EL2_SysRegWrite_e215d12d330397f1[non_mem_expI]:
  "non_mem_exp (CNTHV_TVAL_EL2_SysRegWrite_e215d12d330397f1 el op0 op1 CRn op2 CRm val_name)"
  by (unfold CNTHV_TVAL_EL2_SysRegWrite_e215d12d330397f1_def, non_mem_expI)

lemma non_mem_exp_CNTKCTL_EL12_SysRegWrite_518123f17a6402e4[non_mem_expI]:
  "non_mem_exp (CNTKCTL_EL12_SysRegWrite_518123f17a6402e4 el op0 op1 CRn op2 CRm val_name)"
  by (unfold CNTKCTL_EL12_SysRegWrite_518123f17a6402e4_def, non_mem_expI)

lemma non_mem_exp_CNTKCTL_EL1_SysRegWrite_9a7be69aa33bb9c2[non_mem_expI]:
  "non_mem_exp (CNTKCTL_EL1_SysRegWrite_9a7be69aa33bb9c2 el op0 op1 CRn op2 CRm val_name)"
  by (unfold CNTKCTL_EL1_SysRegWrite_9a7be69aa33bb9c2_def, non_mem_expI)

lemma non_mem_exp_CNTPS_CTL_EL1_SysRegWrite_a0625fd9f7b035a8[non_mem_expI]:
  "non_mem_exp (CNTPS_CTL_EL1_SysRegWrite_a0625fd9f7b035a8 el op0 op1 CRn op2 CRm val_name)"
  by (unfold CNTPS_CTL_EL1_SysRegWrite_a0625fd9f7b035a8_def, non_mem_expI)

lemma non_mem_exp_CNTPS_CVAL_EL1_SysRegWrite_f09243080b7c260d[non_mem_expI]:
  "non_mem_exp (CNTPS_CVAL_EL1_SysRegWrite_f09243080b7c260d el op0 op1 CRn op2 CRm val_name)"
  by (unfold CNTPS_CVAL_EL1_SysRegWrite_f09243080b7c260d_def, non_mem_expI)

lemma non_mem_exp_CNTPS_TVAL_EL1_SysRegWrite_a9b16e60037fa746[non_mem_expI]:
  "non_mem_exp (CNTPS_TVAL_EL1_SysRegWrite_a9b16e60037fa746 el op0 op1 CRn op2 CRm val_name)"
  by (unfold CNTPS_TVAL_EL1_SysRegWrite_a9b16e60037fa746_def, non_mem_expI)

lemma non_mem_exp_CNTP_CTL_EL02_SysRegWrite_99a9da3e2454714e[non_mem_expI]:
  "non_mem_exp (CNTP_CTL_EL02_SysRegWrite_99a9da3e2454714e el op0 op1 CRn op2 CRm val_name)"
  by (unfold CNTP_CTL_EL02_SysRegWrite_99a9da3e2454714e_def, non_mem_expI)

lemma non_mem_exp_CNTP_CTL_EL0_SysRegWrite_137f81090c1357e6[non_mem_expI]:
  "non_mem_exp (CNTP_CTL_EL0_SysRegWrite_137f81090c1357e6 el op0 op1 CRn op2 CRm val_name)"
  by (unfold CNTP_CTL_EL0_SysRegWrite_137f81090c1357e6_def, non_mem_expI)

lemma non_mem_exp_CNTP_CVAL_EL02_SysRegWrite_2b3e9ccfce186a4f[non_mem_expI]:
  "non_mem_exp (CNTP_CVAL_EL02_SysRegWrite_2b3e9ccfce186a4f el op0 op1 CRn op2 CRm val_name)"
  by (unfold CNTP_CVAL_EL02_SysRegWrite_2b3e9ccfce186a4f_def, non_mem_expI)

lemma non_mem_exp_CNTP_CVAL_EL0_SysRegWrite_d54c08ee0cf9aaf7[non_mem_expI]:
  "non_mem_exp (CNTP_CVAL_EL0_SysRegWrite_d54c08ee0cf9aaf7 el op0 op1 CRn op2 CRm val_name)"
  by (unfold CNTP_CVAL_EL0_SysRegWrite_d54c08ee0cf9aaf7_def, non_mem_expI)

lemma non_mem_exp_CNTP_TVAL_EL02_SysRegWrite_caa9f2aa73cb6b96[non_mem_expI]:
  "non_mem_exp (CNTP_TVAL_EL02_SysRegWrite_caa9f2aa73cb6b96 el op0 op1 CRn op2 CRm val_name)"
  by (unfold CNTP_TVAL_EL02_SysRegWrite_caa9f2aa73cb6b96_def, non_mem_expI)

lemma non_mem_exp_CNTP_TVAL_EL0_SysRegWrite_d7441eec23c3d524[non_mem_expI]:
  "non_mem_exp (CNTP_TVAL_EL0_SysRegWrite_d7441eec23c3d524 el op0 op1 CRn op2 CRm val_name)"
  by (unfold CNTP_TVAL_EL0_SysRegWrite_d7441eec23c3d524_def, non_mem_expI)

lemma non_mem_exp_CNTVOFF_EL2_SysRegWrite_621ada4cfda60bcb[non_mem_expI]:
  "non_mem_exp (CNTVOFF_EL2_SysRegWrite_621ada4cfda60bcb el op0 op1 CRn op2 CRm val_name)"
  by (unfold CNTVOFF_EL2_SysRegWrite_621ada4cfda60bcb_def, non_mem_expI)

lemma non_mem_exp_CNTV_CTL_EL02_SysRegWrite_d6cac9cc52dd8fec[non_mem_expI]:
  "non_mem_exp (CNTV_CTL_EL02_SysRegWrite_d6cac9cc52dd8fec el op0 op1 CRn op2 CRm val_name)"
  by (unfold CNTV_CTL_EL02_SysRegWrite_d6cac9cc52dd8fec_def, non_mem_expI)

lemma non_mem_exp_CNTV_CTL_EL0_SysRegWrite_e9fd22bae4b06064[non_mem_expI]:
  "non_mem_exp (CNTV_CTL_EL0_SysRegWrite_e9fd22bae4b06064 el op0 op1 CRn op2 CRm val_name)"
  by (unfold CNTV_CTL_EL0_SysRegWrite_e9fd22bae4b06064_def, non_mem_expI)

lemma non_mem_exp_CNTV_CVAL_EL02_SysRegWrite_7548964ed28b5abb[non_mem_expI]:
  "non_mem_exp (CNTV_CVAL_EL02_SysRegWrite_7548964ed28b5abb el op0 op1 CRn op2 CRm val_name)"
  by (unfold CNTV_CVAL_EL02_SysRegWrite_7548964ed28b5abb_def, non_mem_expI)

lemma non_mem_exp_CNTV_CVAL_EL0_SysRegWrite_f237c5c94ec92951[non_mem_expI]:
  "non_mem_exp (CNTV_CVAL_EL0_SysRegWrite_f237c5c94ec92951 el op0 op1 CRn op2 CRm val_name)"
  by (unfold CNTV_CVAL_EL0_SysRegWrite_f237c5c94ec92951_def, non_mem_expI)

lemma non_mem_exp_CNTV_TVAL_EL02_SysRegWrite_dc97f79a5f74078f[non_mem_expI]:
  "non_mem_exp (CNTV_TVAL_EL02_SysRegWrite_dc97f79a5f74078f el op0 op1 CRn op2 CRm val_name)"
  by (unfold CNTV_TVAL_EL02_SysRegWrite_dc97f79a5f74078f_def, non_mem_expI)

lemma non_mem_exp_CNTV_TVAL_EL0_SysRegWrite_903191acca729cda[non_mem_expI]:
  "non_mem_exp (CNTV_TVAL_EL0_SysRegWrite_903191acca729cda el op0 op1 CRn op2 CRm val_name)"
  by (unfold CNTV_TVAL_EL0_SysRegWrite_903191acca729cda_def, non_mem_expI)

lemma non_mem_exp_CONTEXTIDR_EL12_SysRegWrite_33154953ae1b01d5[non_mem_expI]:
  "non_mem_exp (CONTEXTIDR_EL12_SysRegWrite_33154953ae1b01d5 el op0 op1 CRn op2 CRm val_name)"
  by (unfold CONTEXTIDR_EL12_SysRegWrite_33154953ae1b01d5_def, non_mem_expI)

lemma non_mem_exp_CONTEXTIDR_EL1_SysRegWrite_5408e4e72af4e23d[non_mem_expI]:
  "non_mem_exp (CONTEXTIDR_EL1_SysRegWrite_5408e4e72af4e23d el op0 op1 CRn op2 CRm val_name)"
  by (unfold CONTEXTIDR_EL1_SysRegWrite_5408e4e72af4e23d_def, non_mem_expI)

lemma non_mem_exp_CONTEXTIDR_EL2_SysRegWrite_27187b6dc7c5a748[non_mem_expI]:
  "non_mem_exp (CONTEXTIDR_EL2_SysRegWrite_27187b6dc7c5a748 el op0 op1 CRn op2 CRm val_name)"
  by (unfold CONTEXTIDR_EL2_SysRegWrite_27187b6dc7c5a748_def, non_mem_expI)

lemma non_mem_exp_CPACR_EL12_SysRegWrite_637092a999939f8b[non_mem_expI]:
  "non_mem_exp (CPACR_EL12_SysRegWrite_637092a999939f8b el op0 op1 CRn op2 CRm val_name)"
  by (unfold CPACR_EL12_SysRegWrite_637092a999939f8b_def, non_mem_expI)

lemma non_mem_exp_CPACR_EL1_SysRegWrite_00878a1f3e87823c[non_mem_expI]:
  "non_mem_exp (CPACR_EL1_SysRegWrite_00878a1f3e87823c el op0 op1 CRn op2 CRm val_name)"
  by (unfold CPACR_EL1_SysRegWrite_00878a1f3e87823c_def, non_mem_expI)

lemma non_mem_exp_CPTR_EL2_SysRegWrite_5a082f460b1b2308[non_mem_expI]:
  "non_mem_exp (CPTR_EL2_SysRegWrite_5a082f460b1b2308 el op0 op1 CRn op2 CRm val_name)"
  by (unfold CPTR_EL2_SysRegWrite_5a082f460b1b2308_def, non_mem_expI)

lemma non_mem_exp_CPTR_EL3_SysRegWrite_879d4b1bad53408b[non_mem_expI]:
  "non_mem_exp (CPTR_EL3_SysRegWrite_879d4b1bad53408b el op0 op1 CRn op2 CRm val_name)"
  by (unfold CPTR_EL3_SysRegWrite_879d4b1bad53408b_def, non_mem_expI)

lemma non_mem_exp_CSCR_EL3_SysRegWrite_22b95c83b04d6c91[non_mem_expI]:
  "non_mem_exp (CSCR_EL3_SysRegWrite_22b95c83b04d6c91 el op0 op1 CRn op2 CRm val_name)"
  by (unfold CSCR_EL3_SysRegWrite_22b95c83b04d6c91_def, non_mem_expI)

lemma non_mem_exp_CSSELR_EL1_SysRegWrite_1f9e1e0300c8783c[non_mem_expI]:
  "non_mem_exp (CSSELR_EL1_SysRegWrite_1f9e1e0300c8783c el op0 op1 CRn op2 CRm val_name)"
  by (unfold CSSELR_EL1_SysRegWrite_1f9e1e0300c8783c_def, non_mem_expI)

lemma non_mem_exp_DACR32_EL2_SysRegWrite_a8bad0131817f121[non_mem_expI]:
  "non_mem_exp (DACR32_EL2_SysRegWrite_a8bad0131817f121 el op0 op1 CRn op2 CRm val_name)"
  by (unfold DACR32_EL2_SysRegWrite_a8bad0131817f121_def, non_mem_expI)

lemma non_mem_exp_DAIF_SysRegWrite_3d31f214debf624b[non_mem_expI]:
  "non_mem_exp (DAIF_SysRegWrite_3d31f214debf624b el op0 op1 CRn op2 CRm val_name)"
  by (unfold DAIF_SysRegWrite_3d31f214debf624b_def, non_mem_expI)

lemma non_mem_exp_DBGBCR_EL1_SysRegWrite_6730f3e3839510c5[non_mem_expI]:
  "non_mem_exp (DBGBCR_EL1_SysRegWrite_6730f3e3839510c5 el op0 op1 CRn op2 CRm val_name)"
  by (unfold DBGBCR_EL1_SysRegWrite_6730f3e3839510c5_def, non_mem_expI)

lemma non_mem_exp_DBGBVR_EL1_SysRegWrite_915752bfd6a41a2b[non_mem_expI]:
  "non_mem_exp (DBGBVR_EL1_SysRegWrite_915752bfd6a41a2b el op0 op1 CRn op2 CRm val_name)"
  by (unfold DBGBVR_EL1_SysRegWrite_915752bfd6a41a2b_def, non_mem_expI)

lemma non_mem_exp_DBGCLAIMCLR_EL1_SysRegWrite_2a099a67767e57cf[non_mem_expI]:
  "non_mem_exp (DBGCLAIMCLR_EL1_SysRegWrite_2a099a67767e57cf el op0 op1 CRn op2 CRm val_name)"
  by (unfold DBGCLAIMCLR_EL1_SysRegWrite_2a099a67767e57cf_def, non_mem_expI)

lemma non_mem_exp_DBGCLAIMSET_EL1_SysRegWrite_90e355b6a5730770[non_mem_expI]:
  "non_mem_exp (DBGCLAIMSET_EL1_SysRegWrite_90e355b6a5730770 el op0 op1 CRn op2 CRm val_name)"
  by (unfold DBGCLAIMSET_EL1_SysRegWrite_90e355b6a5730770_def, non_mem_expI)

lemma non_mem_exp_DBGDTRTX_EL0_SysRegWrite_057e8c91e001a69f[non_mem_expI]:
  "non_mem_exp (DBGDTRTX_EL0_SysRegWrite_057e8c91e001a69f el op0 op1 CRn op2 CRm val_name)"
  by (unfold DBGDTRTX_EL0_SysRegWrite_057e8c91e001a69f_def, non_mem_expI)

lemma non_mem_exp_DBGDTR_EL0_write[non_mem_expI]:
  "non_mem_exp (DBGDTR_EL0_write val_name)"
  by (unfold DBGDTR_EL0_write_def, non_mem_expI)

lemma non_mem_exp_DBGDTR_EL0_SysRegWrite_c7246a22e06c7729[non_mem_expI]:
  "non_mem_exp (DBGDTR_EL0_SysRegWrite_c7246a22e06c7729 el op0 op1 CRn op2 CRm val_name)"
  by (unfold DBGDTR_EL0_SysRegWrite_c7246a22e06c7729_def, non_mem_expI)

lemma non_mem_exp_DBGPRCR_EL1_SysRegWrite_710b60256172548e[non_mem_expI]:
  "non_mem_exp (DBGPRCR_EL1_SysRegWrite_710b60256172548e el op0 op1 CRn op2 CRm val_name)"
  by (unfold DBGPRCR_EL1_SysRegWrite_710b60256172548e_def, non_mem_expI)

lemma non_mem_exp_DBGVCR32_EL2_SysRegWrite_769fbfe4fa51a4e5[non_mem_expI]:
  "non_mem_exp (DBGVCR32_EL2_SysRegWrite_769fbfe4fa51a4e5 el op0 op1 CRn op2 CRm val_name)"
  by (unfold DBGVCR32_EL2_SysRegWrite_769fbfe4fa51a4e5_def, non_mem_expI)

lemma non_mem_exp_DBGWCR_EL1_SysRegWrite_6bda3acb5910d354[non_mem_expI]:
  "non_mem_exp (DBGWCR_EL1_SysRegWrite_6bda3acb5910d354 el op0 op1 CRn op2 CRm val_name)"
  by (unfold DBGWCR_EL1_SysRegWrite_6bda3acb5910d354_def, non_mem_expI)

lemma non_mem_exp_DBGWVR_EL1_SysRegWrite_745b296ee53305ea[non_mem_expI]:
  "non_mem_exp (DBGWVR_EL1_SysRegWrite_745b296ee53305ea el op0 op1 CRn op2 CRm val_name)"
  by (unfold DBGWVR_EL1_SysRegWrite_745b296ee53305ea_def, non_mem_expI)

lemma non_mem_exp_DISR_EL1_SysRegWrite_64517664b9260065[non_mem_expI]:
  "non_mem_exp (DISR_EL1_SysRegWrite_64517664b9260065 el op0 op1 CRn op2 CRm val_name)"
  by (unfold DISR_EL1_SysRegWrite_64517664b9260065_def, non_mem_expI)

lemma non_mem_exp_DLR_EL0_write[non_mem_expI]:
  "non_mem_exp (DLR_EL0_write val_name)"
  by (unfold DLR_EL0_write_def, non_mem_expI)

lemma non_mem_exp_DLR_EL0_SysRegWrite_a2d10a509fed3a63[non_mem_expI]:
  "non_mem_exp (DLR_EL0_SysRegWrite_a2d10a509fed3a63 el op0 op1 CRn op2 CRm val_name)"
  by (unfold DLR_EL0_SysRegWrite_a2d10a509fed3a63_def, non_mem_expI)

lemma non_mem_exp_ELR_EL12_SysRegWrite_6720e93c266dadea[non_mem_expI]:
  "non_mem_exp (ELR_EL12_SysRegWrite_6720e93c266dadea el op0 op1 CRn op2 CRm val_name)"
  by (unfold ELR_EL12_SysRegWrite_6720e93c266dadea_def, non_mem_expI)

lemma non_mem_exp_ELR_EL1_SysRegWrite_b6bd589b2dd79575[non_mem_expI]:
  "non_mem_exp (ELR_EL1_SysRegWrite_b6bd589b2dd79575 el op0 op1 CRn op2 CRm val_name)"
  by (unfold ELR_EL1_SysRegWrite_b6bd589b2dd79575_def, non_mem_expI)

lemma non_mem_exp_ELR_EL2_SysRegWrite_9f4ca59c1a88f1a9[non_mem_expI]:
  "non_mem_exp (ELR_EL2_SysRegWrite_9f4ca59c1a88f1a9 el op0 op1 CRn op2 CRm val_name)"
  by (unfold ELR_EL2_SysRegWrite_9f4ca59c1a88f1a9_def, non_mem_expI)

lemma non_mem_exp_ELR_EL3_SysRegWrite_8cd0b0c7f61ee7aa[non_mem_expI]:
  "non_mem_exp (ELR_EL3_SysRegWrite_8cd0b0c7f61ee7aa el op0 op1 CRn op2 CRm val_name)"
  by (unfold ELR_EL3_SysRegWrite_8cd0b0c7f61ee7aa_def, non_mem_expI)

lemma non_mem_exp_ERRSELR_EL1_SysRegWrite_551535eed30e26f9[non_mem_expI]:
  "non_mem_exp (ERRSELR_EL1_SysRegWrite_551535eed30e26f9 el op0 op1 CRn op2 CRm val_name)"
  by (unfold ERRSELR_EL1_SysRegWrite_551535eed30e26f9_def, non_mem_expI)

lemma non_mem_exp_ERXADDR_EL1_SysRegWrite_8a1eabc2959662e8[non_mem_expI]:
  "non_mem_exp (ERXADDR_EL1_SysRegWrite_8a1eabc2959662e8 el op0 op1 CRn op2 CRm val_name)"
  by (unfold ERXADDR_EL1_SysRegWrite_8a1eabc2959662e8_def, non_mem_expI)

lemma non_mem_exp_ERXCTLR_EL1_SysRegWrite_acca1e102ba86b42[non_mem_expI]:
  "non_mem_exp (ERXCTLR_EL1_SysRegWrite_acca1e102ba86b42 el op0 op1 CRn op2 CRm val_name)"
  by (unfold ERXCTLR_EL1_SysRegWrite_acca1e102ba86b42_def, non_mem_expI)

lemma non_mem_exp_ERXMISC0_EL1_SysRegWrite_822ceca9b10b2621[non_mem_expI]:
  "non_mem_exp (ERXMISC0_EL1_SysRegWrite_822ceca9b10b2621 el op0 op1 CRn op2 CRm val_name)"
  by (unfold ERXMISC0_EL1_SysRegWrite_822ceca9b10b2621_def, non_mem_expI)

lemma non_mem_exp_ERXMISC1_EL1_SysRegWrite_9a9ef77b5fd82587[non_mem_expI]:
  "non_mem_exp (ERXMISC1_EL1_SysRegWrite_9a9ef77b5fd82587 el op0 op1 CRn op2 CRm val_name)"
  by (unfold ERXMISC1_EL1_SysRegWrite_9a9ef77b5fd82587_def, non_mem_expI)

lemma non_mem_exp_ERXSTATUS_EL1_SysRegWrite_f0798b4207ec0193[non_mem_expI]:
  "non_mem_exp (ERXSTATUS_EL1_SysRegWrite_f0798b4207ec0193 el op0 op1 CRn op2 CRm val_name)"
  by (unfold ERXSTATUS_EL1_SysRegWrite_f0798b4207ec0193_def, non_mem_expI)

lemma non_mem_exp_ESR_EL12_SysRegWrite_2b2d6012ba438548[non_mem_expI]:
  "non_mem_exp (ESR_EL12_SysRegWrite_2b2d6012ba438548 el op0 op1 CRn op2 CRm val_name)"
  by (unfold ESR_EL12_SysRegWrite_2b2d6012ba438548_def, non_mem_expI)

lemma non_mem_exp_ESR_EL1_SysRegWrite_a8ce40896bd70a6b[non_mem_expI]:
  "non_mem_exp (ESR_EL1_SysRegWrite_a8ce40896bd70a6b el op0 op1 CRn op2 CRm val_name)"
  by (unfold ESR_EL1_SysRegWrite_a8ce40896bd70a6b_def, non_mem_expI)

lemma non_mem_exp_ESR_EL2_SysRegWrite_a10e84e3bd1020c8[non_mem_expI]:
  "non_mem_exp (ESR_EL2_SysRegWrite_a10e84e3bd1020c8 el op0 op1 CRn op2 CRm val_name)"
  by (unfold ESR_EL2_SysRegWrite_a10e84e3bd1020c8_def, non_mem_expI)

lemma non_mem_exp_ESR_EL3_SysRegWrite_195a2e1a5b40464e[non_mem_expI]:
  "non_mem_exp (ESR_EL3_SysRegWrite_195a2e1a5b40464e el op0 op1 CRn op2 CRm val_name)"
  by (unfold ESR_EL3_SysRegWrite_195a2e1a5b40464e_def, non_mem_expI)

lemma non_mem_exp_FAR_EL12_SysRegWrite_78f825940e556299[non_mem_expI]:
  "non_mem_exp (FAR_EL12_SysRegWrite_78f825940e556299 el op0 op1 CRn op2 CRm val_name)"
  by (unfold FAR_EL12_SysRegWrite_78f825940e556299_def, non_mem_expI)

lemma non_mem_exp_FAR_EL1_SysRegWrite_fc0bd224b62cc089[non_mem_expI]:
  "non_mem_exp (FAR_EL1_SysRegWrite_fc0bd224b62cc089 el op0 op1 CRn op2 CRm val_name)"
  by (unfold FAR_EL1_SysRegWrite_fc0bd224b62cc089_def, non_mem_expI)

lemma non_mem_exp_FAR_EL2_SysRegWrite_6370aabce83a1613[non_mem_expI]:
  "non_mem_exp (FAR_EL2_SysRegWrite_6370aabce83a1613 el op0 op1 CRn op2 CRm val_name)"
  by (unfold FAR_EL2_SysRegWrite_6370aabce83a1613_def, non_mem_expI)

lemma non_mem_exp_FAR_EL3_SysRegWrite_397cfda85a093e9d[non_mem_expI]:
  "non_mem_exp (FAR_EL3_SysRegWrite_397cfda85a093e9d el op0 op1 CRn op2 CRm val_name)"
  by (unfold FAR_EL3_SysRegWrite_397cfda85a093e9d_def, non_mem_expI)

lemma non_mem_exp_FPCR_SysRegWrite_4f255cf55390cebb[non_mem_expI]:
  "non_mem_exp (FPCR_SysRegWrite_4f255cf55390cebb el op0 op1 CRn op2 CRm val_name)"
  by (unfold FPCR_SysRegWrite_4f255cf55390cebb_def, non_mem_expI)

lemma non_mem_exp_FPEXC32_EL2_SysRegWrite_9f180ead5c4d6735[non_mem_expI]:
  "non_mem_exp (FPEXC32_EL2_SysRegWrite_9f180ead5c4d6735 el op0 op1 CRn op2 CRm val_name)"
  by (unfold FPEXC32_EL2_SysRegWrite_9f180ead5c4d6735_def, non_mem_expI)

lemma non_mem_exp_FPSR_SysRegWrite_413aed98a94900de[non_mem_expI]:
  "non_mem_exp (FPSR_SysRegWrite_413aed98a94900de el op0 op1 CRn op2 CRm val_name)"
  by (unfold FPSR_SysRegWrite_413aed98a94900de_def, non_mem_expI)

lemma non_mem_exp_HACR_EL2_SysRegWrite_5b2ca32fcb39ecab[non_mem_expI]:
  "non_mem_exp (HACR_EL2_SysRegWrite_5b2ca32fcb39ecab el op0 op1 CRn op2 CRm val_name)"
  by (unfold HACR_EL2_SysRegWrite_5b2ca32fcb39ecab_def, non_mem_expI)

lemma non_mem_exp_HCR_EL2_SysRegWrite_6fc18e07a17fd5a2[non_mem_expI]:
  "non_mem_exp (HCR_EL2_SysRegWrite_6fc18e07a17fd5a2 el op0 op1 CRn op2 CRm val_name)"
  by (unfold HCR_EL2_SysRegWrite_6fc18e07a17fd5a2_def, non_mem_expI)

lemma non_mem_exp_HPFAR_EL2_SysRegWrite_20417eccdd6b4768[non_mem_expI]:
  "non_mem_exp (HPFAR_EL2_SysRegWrite_20417eccdd6b4768 el op0 op1 CRn op2 CRm val_name)"
  by (unfold HPFAR_EL2_SysRegWrite_20417eccdd6b4768_def, non_mem_expI)

lemma non_mem_exp_HSTR_EL2_SysRegWrite_391a605c0bfb9d1e[non_mem_expI]:
  "non_mem_exp (HSTR_EL2_SysRegWrite_391a605c0bfb9d1e el op0 op1 CRn op2 CRm val_name)"
  by (unfold HSTR_EL2_SysRegWrite_391a605c0bfb9d1e_def, non_mem_expI)

lemma non_mem_exp_ICC_AP0R_EL1_SysRegWrite_949897f971748acc[non_mem_expI]:
  "non_mem_exp (ICC_AP0R_EL1_SysRegWrite_949897f971748acc el op0 op1 CRn op2 CRm val_name)"
  by (unfold ICC_AP0R_EL1_SysRegWrite_949897f971748acc_def, non_mem_expI)

lemma non_mem_exp_ICC_AP1R_EL1_SysRegWrite_55167410f7650dea[non_mem_expI]:
  "non_mem_exp (ICC_AP1R_EL1_SysRegWrite_55167410f7650dea el op0 op1 CRn op2 CRm val_name)"
  by (unfold ICC_AP1R_EL1_SysRegWrite_55167410f7650dea_def, non_mem_expI)

lemma non_mem_exp_ICC_ASGI1R_EL1_SysRegWrite_c163c25adc1b1354[non_mem_expI]:
  "non_mem_exp (ICC_ASGI1R_EL1_SysRegWrite_c163c25adc1b1354 el op0 op1 CRn op2 CRm val_name)"
  by (unfold ICC_ASGI1R_EL1_SysRegWrite_c163c25adc1b1354_def, non_mem_expI)

lemma non_mem_exp_ICC_BPR0_EL1_SysRegWrite_10028206553f3655[non_mem_expI]:
  "non_mem_exp (ICC_BPR0_EL1_SysRegWrite_10028206553f3655 el op0 op1 CRn op2 CRm val_name)"
  by (unfold ICC_BPR0_EL1_SysRegWrite_10028206553f3655_def, non_mem_expI)

lemma non_mem_exp_ICC_BPR1_EL1_SysRegWrite_a633b2e9f3626d9b[non_mem_expI]:
  "non_mem_exp (ICC_BPR1_EL1_SysRegWrite_a633b2e9f3626d9b el op0 op1 CRn op2 CRm val_name)"
  by (unfold ICC_BPR1_EL1_SysRegWrite_a633b2e9f3626d9b_def, non_mem_expI)

lemma non_mem_exp_ICC_CTLR_EL1_SysRegWrite_8ec3f4b67393eba8[non_mem_expI]:
  "non_mem_exp (ICC_CTLR_EL1_SysRegWrite_8ec3f4b67393eba8 el op0 op1 CRn op2 CRm val_name)"
  by (unfold ICC_CTLR_EL1_SysRegWrite_8ec3f4b67393eba8_def, non_mem_expI)

lemma non_mem_exp_ICC_CTLR_EL3_SysRegWrite_ecc8b41b177c53e8[non_mem_expI]:
  "non_mem_exp (ICC_CTLR_EL3_SysRegWrite_ecc8b41b177c53e8 el op0 op1 CRn op2 CRm val_name)"
  by (unfold ICC_CTLR_EL3_SysRegWrite_ecc8b41b177c53e8_def, non_mem_expI)

lemma non_mem_exp_ICC_DIR_EL1_SysRegWrite_77fadeda7efde9c5[non_mem_expI]:
  "non_mem_exp (ICC_DIR_EL1_SysRegWrite_77fadeda7efde9c5 el op0 op1 CRn op2 CRm val_name)"
  by (unfold ICC_DIR_EL1_SysRegWrite_77fadeda7efde9c5_def, non_mem_expI)

lemma non_mem_exp_ICC_EOIR0_EL1_SysRegWrite_9c0fae08cd7a2444[non_mem_expI]:
  "non_mem_exp (ICC_EOIR0_EL1_SysRegWrite_9c0fae08cd7a2444 el op0 op1 CRn op2 CRm val_name)"
  by (unfold ICC_EOIR0_EL1_SysRegWrite_9c0fae08cd7a2444_def, non_mem_expI)

lemma non_mem_exp_ICC_EOIR1_EL1_SysRegWrite_f065db56e179bf6e[non_mem_expI]:
  "non_mem_exp (ICC_EOIR1_EL1_SysRegWrite_f065db56e179bf6e el op0 op1 CRn op2 CRm val_name)"
  by (unfold ICC_EOIR1_EL1_SysRegWrite_f065db56e179bf6e_def, non_mem_expI)

lemma non_mem_exp_ICC_IGRPEN0_EL1_SysRegWrite_b94e4d10f7a33382[non_mem_expI]:
  "non_mem_exp (ICC_IGRPEN0_EL1_SysRegWrite_b94e4d10f7a33382 el op0 op1 CRn op2 CRm val_name)"
  by (unfold ICC_IGRPEN0_EL1_SysRegWrite_b94e4d10f7a33382_def, non_mem_expI)

lemma non_mem_exp_ICC_IGRPEN1_EL1_SysRegWrite_c36dfa556252f6b4[non_mem_expI]:
  "non_mem_exp (ICC_IGRPEN1_EL1_SysRegWrite_c36dfa556252f6b4 el op0 op1 CRn op2 CRm val_name)"
  by (unfold ICC_IGRPEN1_EL1_SysRegWrite_c36dfa556252f6b4_def, non_mem_expI)

lemma non_mem_exp_ICC_IGRPEN1_EL3_SysRegWrite_6f1db000a53b40ca[non_mem_expI]:
  "non_mem_exp (ICC_IGRPEN1_EL3_SysRegWrite_6f1db000a53b40ca el op0 op1 CRn op2 CRm val_name)"
  by (unfold ICC_IGRPEN1_EL3_SysRegWrite_6f1db000a53b40ca_def, non_mem_expI)

lemma non_mem_exp_ICC_PMR_EL1_SysRegWrite_8bb2caa31e7d5e1b[non_mem_expI]:
  "non_mem_exp (ICC_PMR_EL1_SysRegWrite_8bb2caa31e7d5e1b el op0 op1 CRn op2 CRm val_name)"
  by (unfold ICC_PMR_EL1_SysRegWrite_8bb2caa31e7d5e1b_def, non_mem_expI)

lemma non_mem_exp_ICC_SGI0R_EL1_SysRegWrite_ba6d1066ea6fbbb7[non_mem_expI]:
  "non_mem_exp (ICC_SGI0R_EL1_SysRegWrite_ba6d1066ea6fbbb7 el op0 op1 CRn op2 CRm val_name)"
  by (unfold ICC_SGI0R_EL1_SysRegWrite_ba6d1066ea6fbbb7_def, non_mem_expI)

lemma non_mem_exp_ICC_SGI1R_EL1_SysRegWrite_0da31fe6c2e1b098[non_mem_expI]:
  "non_mem_exp (ICC_SGI1R_EL1_SysRegWrite_0da31fe6c2e1b098 el op0 op1 CRn op2 CRm val_name)"
  by (unfold ICC_SGI1R_EL1_SysRegWrite_0da31fe6c2e1b098_def, non_mem_expI)

lemma non_mem_exp_ICC_SRE_EL1_SysRegWrite_d2efb75caa67d019[non_mem_expI]:
  "non_mem_exp (ICC_SRE_EL1_SysRegWrite_d2efb75caa67d019 el op0 op1 CRn op2 CRm val_name)"
  by (unfold ICC_SRE_EL1_SysRegWrite_d2efb75caa67d019_def, non_mem_expI)

lemma non_mem_exp_ICC_SRE_EL2_SysRegWrite_39c314f677b8ec2e[non_mem_expI]:
  "non_mem_exp (ICC_SRE_EL2_SysRegWrite_39c314f677b8ec2e el op0 op1 CRn op2 CRm val_name)"
  by (unfold ICC_SRE_EL2_SysRegWrite_39c314f677b8ec2e_def, non_mem_expI)

lemma non_mem_exp_ICC_SRE_EL3_SysRegWrite_c0af2dd58a7e1d22[non_mem_expI]:
  "non_mem_exp (ICC_SRE_EL3_SysRegWrite_c0af2dd58a7e1d22 el op0 op1 CRn op2 CRm val_name)"
  by (unfold ICC_SRE_EL3_SysRegWrite_c0af2dd58a7e1d22_def, non_mem_expI)

lemma non_mem_exp_ICH_AP0R_EL2_SysRegWrite_9517857bb550d699[non_mem_expI]:
  "non_mem_exp (ICH_AP0R_EL2_SysRegWrite_9517857bb550d699 el op0 op1 CRn op2 CRm val_name)"
  by (unfold ICH_AP0R_EL2_SysRegWrite_9517857bb550d699_def, non_mem_expI)

lemma non_mem_exp_ICH_AP1R_EL2_SysRegWrite_20f46016b54a3395[non_mem_expI]:
  "non_mem_exp (ICH_AP1R_EL2_SysRegWrite_20f46016b54a3395 el op0 op1 CRn op2 CRm val_name)"
  by (unfold ICH_AP1R_EL2_SysRegWrite_20f46016b54a3395_def, non_mem_expI)

lemma non_mem_exp_ICH_HCR_EL2_SysRegWrite_2fea52a15cd7dbe5[non_mem_expI]:
  "non_mem_exp (ICH_HCR_EL2_SysRegWrite_2fea52a15cd7dbe5 el op0 op1 CRn op2 CRm val_name)"
  by (unfold ICH_HCR_EL2_SysRegWrite_2fea52a15cd7dbe5_def, non_mem_expI)

lemma non_mem_exp_ICH_LR_EL2_SysRegWrite_8b291f94259261d2[non_mem_expI]:
  "non_mem_exp (ICH_LR_EL2_SysRegWrite_8b291f94259261d2 el op0 op1 CRn op2 CRm val_name)"
  by (unfold ICH_LR_EL2_SysRegWrite_8b291f94259261d2_def, non_mem_expI)

lemma non_mem_exp_ICH_VMCR_EL2_SysRegWrite_86a315374f6b5205[non_mem_expI]:
  "non_mem_exp (ICH_VMCR_EL2_SysRegWrite_86a315374f6b5205 el op0 op1 CRn op2 CRm val_name)"
  by (unfold ICH_VMCR_EL2_SysRegWrite_86a315374f6b5205_def, non_mem_expI)

lemma non_mem_exp_IFSR32_EL2_SysRegWrite_6ce25b2b11e30403[non_mem_expI]:
  "non_mem_exp (IFSR32_EL2_SysRegWrite_6ce25b2b11e30403 el op0 op1 CRn op2 CRm val_name)"
  by (unfold IFSR32_EL2_SysRegWrite_6ce25b2b11e30403_def, non_mem_expI)

lemma non_mem_exp_LORC_EL1_SysRegWrite_7100b979c23fc52e[non_mem_expI]:
  "non_mem_exp (LORC_EL1_SysRegWrite_7100b979c23fc52e el op0 op1 CRn op2 CRm val_name)"
  by (unfold LORC_EL1_SysRegWrite_7100b979c23fc52e_def, non_mem_expI)

lemma non_mem_exp_LOREA_EL1_SysRegWrite_2d068511b7f5ce7b[non_mem_expI]:
  "non_mem_exp (LOREA_EL1_SysRegWrite_2d068511b7f5ce7b el op0 op1 CRn op2 CRm val_name)"
  by (unfold LOREA_EL1_SysRegWrite_2d068511b7f5ce7b_def, non_mem_expI)

lemma non_mem_exp_LORN_EL1_SysRegWrite_bde03c74e878b099[non_mem_expI]:
  "non_mem_exp (LORN_EL1_SysRegWrite_bde03c74e878b099 el op0 op1 CRn op2 CRm val_name)"
  by (unfold LORN_EL1_SysRegWrite_bde03c74e878b099_def, non_mem_expI)

lemma non_mem_exp_LORSA_EL1_SysRegWrite_9ba633e967136731[non_mem_expI]:
  "non_mem_exp (LORSA_EL1_SysRegWrite_9ba633e967136731 el op0 op1 CRn op2 CRm val_name)"
  by (unfold LORSA_EL1_SysRegWrite_9ba633e967136731_def, non_mem_expI)

lemma non_mem_exp_MAIR_EL12_SysRegWrite_da2526ed2008ed50[non_mem_expI]:
  "non_mem_exp (MAIR_EL12_SysRegWrite_da2526ed2008ed50 el op0 op1 CRn op2 CRm val_name)"
  by (unfold MAIR_EL12_SysRegWrite_da2526ed2008ed50_def, non_mem_expI)

lemma non_mem_exp_MAIR_EL1_SysRegWrite_45d8150aaf31e3b9[non_mem_expI]:
  "non_mem_exp (MAIR_EL1_SysRegWrite_45d8150aaf31e3b9 el op0 op1 CRn op2 CRm val_name)"
  by (unfold MAIR_EL1_SysRegWrite_45d8150aaf31e3b9_def, non_mem_expI)

lemma non_mem_exp_MAIR_EL2_SysRegWrite_4e3422c1776528f5[non_mem_expI]:
  "non_mem_exp (MAIR_EL2_SysRegWrite_4e3422c1776528f5 el op0 op1 CRn op2 CRm val_name)"
  by (unfold MAIR_EL2_SysRegWrite_4e3422c1776528f5_def, non_mem_expI)

lemma non_mem_exp_MAIR_EL3_SysRegWrite_d15af780e0b4e771[non_mem_expI]:
  "non_mem_exp (MAIR_EL3_SysRegWrite_d15af780e0b4e771 el op0 op1 CRn op2 CRm val_name)"
  by (unfold MAIR_EL3_SysRegWrite_d15af780e0b4e771_def, non_mem_expI)

lemma non_mem_exp_MDCCINT_EL1_SysRegWrite_1e6a37984aec7145[non_mem_expI]:
  "non_mem_exp (MDCCINT_EL1_SysRegWrite_1e6a37984aec7145 el op0 op1 CRn op2 CRm val_name)"
  by (unfold MDCCINT_EL1_SysRegWrite_1e6a37984aec7145_def, non_mem_expI)

lemma non_mem_exp_MDCR_EL2_SysRegWrite_3f12005c8c459bf3[non_mem_expI]:
  "non_mem_exp (MDCR_EL2_SysRegWrite_3f12005c8c459bf3 el op0 op1 CRn op2 CRm val_name)"
  by (unfold MDCR_EL2_SysRegWrite_3f12005c8c459bf3_def, non_mem_expI)

lemma non_mem_exp_MDCR_EL3_SysRegWrite_37dff5fa83ad16ed[non_mem_expI]:
  "non_mem_exp (MDCR_EL3_SysRegWrite_37dff5fa83ad16ed el op0 op1 CRn op2 CRm val_name)"
  by (unfold MDCR_EL3_SysRegWrite_37dff5fa83ad16ed_def, non_mem_expI)

lemma non_mem_exp_MDSCR_EL1_SysRegWrite_94ddb1e46aff4dfa[non_mem_expI]:
  "non_mem_exp (MDSCR_EL1_SysRegWrite_94ddb1e46aff4dfa el op0 op1 CRn op2 CRm val_name)"
  by (unfold MDSCR_EL1_SysRegWrite_94ddb1e46aff4dfa_def, non_mem_expI)

lemma non_mem_exp_MPAM0_EL1_SysRegWrite_88f6c0c61a59ac23[non_mem_expI]:
  "non_mem_exp (MPAM0_EL1_SysRegWrite_88f6c0c61a59ac23 el op0 op1 CRn op2 CRm val_name)"
  by (unfold MPAM0_EL1_SysRegWrite_88f6c0c61a59ac23_def, non_mem_expI)

lemma non_mem_exp_MPAM2_EL2_write[non_mem_expI]:
  "non_mem_exp (MPAM2_EL2_write val_name)"
  by (unfold MPAM2_EL2_write_def, non_mem_expI)

lemma non_mem_exp_MPAM1_EL1_write[non_mem_expI]:
  "non_mem_exp (MPAM1_EL1_write val_name)"
  by (unfold MPAM1_EL1_write_def, non_mem_expI)

lemma non_mem_exp_MPAM1_EL12_SysRegWrite_2cbbb0edf5787671[non_mem_expI]:
  "non_mem_exp (MPAM1_EL12_SysRegWrite_2cbbb0edf5787671 el op0 op1 CRn op2 CRm val_name)"
  by (unfold MPAM1_EL12_SysRegWrite_2cbbb0edf5787671_def, non_mem_expI)

lemma non_mem_exp_MPAM1_EL1_SysRegWrite_cd02720a3298b1c6[non_mem_expI]:
  "non_mem_exp (MPAM1_EL1_SysRegWrite_cd02720a3298b1c6 el op0 op1 CRn op2 CRm val_name)"
  by (unfold MPAM1_EL1_SysRegWrite_cd02720a3298b1c6_def, non_mem_expI)

lemma non_mem_exp_MPAM2_EL2_SysRegWrite_d6bae8d18aebb554[non_mem_expI]:
  "non_mem_exp (MPAM2_EL2_SysRegWrite_d6bae8d18aebb554 el op0 op1 CRn op2 CRm val_name)"
  by (unfold MPAM2_EL2_SysRegWrite_d6bae8d18aebb554_def, non_mem_expI)

lemma non_mem_exp_MPAM3_EL3_SysRegWrite_bb55d8a9d90e05e3[non_mem_expI]:
  "non_mem_exp (MPAM3_EL3_SysRegWrite_bb55d8a9d90e05e3 el op0 op1 CRn op2 CRm val_name)"
  by (unfold MPAM3_EL3_SysRegWrite_bb55d8a9d90e05e3_def, non_mem_expI)

lemma non_mem_exp_MPAMHCR_EL2_SysRegWrite_e38755d6111336b8[non_mem_expI]:
  "non_mem_exp (MPAMHCR_EL2_SysRegWrite_e38755d6111336b8 el op0 op1 CRn op2 CRm val_name)"
  by (unfold MPAMHCR_EL2_SysRegWrite_e38755d6111336b8_def, non_mem_expI)

lemma non_mem_exp_MPAMVPM0_EL2_SysRegWrite_c00108111630aa84[non_mem_expI]:
  "non_mem_exp (MPAMVPM0_EL2_SysRegWrite_c00108111630aa84 el op0 op1 CRn op2 CRm val_name)"
  by (unfold MPAMVPM0_EL2_SysRegWrite_c00108111630aa84_def, non_mem_expI)

lemma non_mem_exp_MPAMVPM1_EL2_SysRegWrite_81a739cc4bd1cd46[non_mem_expI]:
  "non_mem_exp (MPAMVPM1_EL2_SysRegWrite_81a739cc4bd1cd46 el op0 op1 CRn op2 CRm val_name)"
  by (unfold MPAMVPM1_EL2_SysRegWrite_81a739cc4bd1cd46_def, non_mem_expI)

lemma non_mem_exp_MPAMVPM2_EL2_SysRegWrite_20a1b54bc18980b1[non_mem_expI]:
  "non_mem_exp (MPAMVPM2_EL2_SysRegWrite_20a1b54bc18980b1 el op0 op1 CRn op2 CRm val_name)"
  by (unfold MPAMVPM2_EL2_SysRegWrite_20a1b54bc18980b1_def, non_mem_expI)

lemma non_mem_exp_MPAMVPM3_EL2_SysRegWrite_d2a71d8e23cc67af[non_mem_expI]:
  "non_mem_exp (MPAMVPM3_EL2_SysRegWrite_d2a71d8e23cc67af el op0 op1 CRn op2 CRm val_name)"
  by (unfold MPAMVPM3_EL2_SysRegWrite_d2a71d8e23cc67af_def, non_mem_expI)

lemma non_mem_exp_MPAMVPM4_EL2_SysRegWrite_2d0a10731399829d[non_mem_expI]:
  "non_mem_exp (MPAMVPM4_EL2_SysRegWrite_2d0a10731399829d el op0 op1 CRn op2 CRm val_name)"
  by (unfold MPAMVPM4_EL2_SysRegWrite_2d0a10731399829d_def, non_mem_expI)

lemma non_mem_exp_MPAMVPM5_EL2_SysRegWrite_ec98ca57d40ac9ec[non_mem_expI]:
  "non_mem_exp (MPAMVPM5_EL2_SysRegWrite_ec98ca57d40ac9ec el op0 op1 CRn op2 CRm val_name)"
  by (unfold MPAMVPM5_EL2_SysRegWrite_ec98ca57d40ac9ec_def, non_mem_expI)

lemma non_mem_exp_MPAMVPM6_EL2_SysRegWrite_0934853fee68e9bd[non_mem_expI]:
  "non_mem_exp (MPAMVPM6_EL2_SysRegWrite_0934853fee68e9bd el op0 op1 CRn op2 CRm val_name)"
  by (unfold MPAMVPM6_EL2_SysRegWrite_0934853fee68e9bd_def, non_mem_expI)

lemma non_mem_exp_MPAMVPM7_EL2_SysRegWrite_dfb7f68750df7012[non_mem_expI]:
  "non_mem_exp (MPAMVPM7_EL2_SysRegWrite_dfb7f68750df7012 el op0 op1 CRn op2 CRm val_name)"
  by (unfold MPAMVPM7_EL2_SysRegWrite_dfb7f68750df7012_def, non_mem_expI)

lemma non_mem_exp_MPAMVPMV_EL2_SysRegWrite_abd8d27e91fadf85[non_mem_expI]:
  "non_mem_exp (MPAMVPMV_EL2_SysRegWrite_abd8d27e91fadf85 el op0 op1 CRn op2 CRm val_name)"
  by (unfold MPAMVPMV_EL2_SysRegWrite_abd8d27e91fadf85_def, non_mem_expI)

lemma non_mem_exp_OSDLR_EL1_SysRegWrite_591fd96d91652c64[non_mem_expI]:
  "non_mem_exp (OSDLR_EL1_SysRegWrite_591fd96d91652c64 el op0 op1 CRn op2 CRm val_name)"
  by (unfold OSDLR_EL1_SysRegWrite_591fd96d91652c64_def, non_mem_expI)

lemma non_mem_exp_OSDTRRX_EL1_SysRegWrite_6dc5d8521b60df8a[non_mem_expI]:
  "non_mem_exp (OSDTRRX_EL1_SysRegWrite_6dc5d8521b60df8a el op0 op1 CRn op2 CRm val_name)"
  by (unfold OSDTRRX_EL1_SysRegWrite_6dc5d8521b60df8a_def, non_mem_expI)

lemma non_mem_exp_OSDTRTX_EL1_SysRegWrite_9ba0c4a85d0c1de5[non_mem_expI]:
  "non_mem_exp (OSDTRTX_EL1_SysRegWrite_9ba0c4a85d0c1de5 el op0 op1 CRn op2 CRm val_name)"
  by (unfold OSDTRTX_EL1_SysRegWrite_9ba0c4a85d0c1de5_def, non_mem_expI)

lemma non_mem_exp_OSECCR_EL1_SysRegWrite_cabf381bfb822732[non_mem_expI]:
  "non_mem_exp (OSECCR_EL1_SysRegWrite_cabf381bfb822732 el op0 op1 CRn op2 CRm val_name)"
  by (unfold OSECCR_EL1_SysRegWrite_cabf381bfb822732_def, non_mem_expI)

lemma non_mem_exp_OSLAR_EL1_SysRegWrite_582d77c57653b2c4[non_mem_expI]:
  "non_mem_exp (OSLAR_EL1_SysRegWrite_582d77c57653b2c4 el op0 op1 CRn op2 CRm val_name)"
  by (unfold OSLAR_EL1_SysRegWrite_582d77c57653b2c4_def, non_mem_expI)

lemma non_mem_exp_PAR_EL1_SysRegWrite_aa92c70a4b5d5873[non_mem_expI]:
  "non_mem_exp (PAR_EL1_SysRegWrite_aa92c70a4b5d5873 el op0 op1 CRn op2 CRm val_name)"
  by (unfold PAR_EL1_SysRegWrite_aa92c70a4b5d5873_def, non_mem_expI)

lemma non_mem_exp_PMBLIMITR_EL1_SysRegWrite_ddfe2ba603df6628[non_mem_expI]:
  "non_mem_exp (PMBLIMITR_EL1_SysRegWrite_ddfe2ba603df6628 el op0 op1 CRn op2 CRm val_name)"
  by (unfold PMBLIMITR_EL1_SysRegWrite_ddfe2ba603df6628_def, non_mem_expI)

lemma non_mem_exp_PMBPTR_EL1_SysRegWrite_32441d8a7a2b9601[non_mem_expI]:
  "non_mem_exp (PMBPTR_EL1_SysRegWrite_32441d8a7a2b9601 el op0 op1 CRn op2 CRm val_name)"
  by (unfold PMBPTR_EL1_SysRegWrite_32441d8a7a2b9601_def, non_mem_expI)

lemma non_mem_exp_PMBSR_EL1_SysRegWrite_ff19dc948509312f[non_mem_expI]:
  "non_mem_exp (PMBSR_EL1_SysRegWrite_ff19dc948509312f el op0 op1 CRn op2 CRm val_name)"
  by (unfold PMBSR_EL1_SysRegWrite_ff19dc948509312f_def, non_mem_expI)

lemma non_mem_exp_PMCCFILTR_EL0_SysRegWrite_42277f001664525c[non_mem_expI]:
  "non_mem_exp (PMCCFILTR_EL0_SysRegWrite_42277f001664525c el op0 op1 CRn op2 CRm val_name)"
  by (unfold PMCCFILTR_EL0_SysRegWrite_42277f001664525c_def, non_mem_expI)

lemma non_mem_exp_PMCCNTR_EL0_SysRegWrite_1d21e0789830cbf9[non_mem_expI]:
  "non_mem_exp (PMCCNTR_EL0_SysRegWrite_1d21e0789830cbf9 el op0 op1 CRn op2 CRm val_name)"
  by (unfold PMCCNTR_EL0_SysRegWrite_1d21e0789830cbf9_def, non_mem_expI)

lemma non_mem_exp_PMCNTENCLR_EL0_SysRegWrite_bf2c4fae1a891e1b[non_mem_expI]:
  "non_mem_exp (PMCNTENCLR_EL0_SysRegWrite_bf2c4fae1a891e1b el op0 op1 CRn op2 CRm val_name)"
  by (unfold PMCNTENCLR_EL0_SysRegWrite_bf2c4fae1a891e1b_def, non_mem_expI)

lemma non_mem_exp_PMCNTENSET_EL0_SysRegWrite_227af2773d320cb1[non_mem_expI]:
  "non_mem_exp (PMCNTENSET_EL0_SysRegWrite_227af2773d320cb1 el op0 op1 CRn op2 CRm val_name)"
  by (unfold PMCNTENSET_EL0_SysRegWrite_227af2773d320cb1_def, non_mem_expI)

lemma non_mem_exp_PMCR_EL0_SysRegWrite_87ae64466e09f89a[non_mem_expI]:
  "non_mem_exp (PMCR_EL0_SysRegWrite_87ae64466e09f89a el op0 op1 CRn op2 CRm val_name)"
  by (unfold PMCR_EL0_SysRegWrite_87ae64466e09f89a_def, non_mem_expI)

lemma non_mem_exp_PMEVCNTR_EL0_SysRegWrite_c197579331ed9cbb[non_mem_expI]:
  "non_mem_exp (PMEVCNTR_EL0_SysRegWrite_c197579331ed9cbb el op0 op1 CRn op2 CRm val_name)"
  by (unfold PMEVCNTR_EL0_SysRegWrite_c197579331ed9cbb_def, non_mem_expI)

lemma non_mem_exp_PMEVTYPER_EL0_SysRegWrite_3e6ae16cd645ec0d[non_mem_expI]:
  "non_mem_exp (PMEVTYPER_EL0_SysRegWrite_3e6ae16cd645ec0d el op0 op1 CRn op2 CRm val_name)"
  by (unfold PMEVTYPER_EL0_SysRegWrite_3e6ae16cd645ec0d_def, non_mem_expI)

lemma non_mem_exp_PMINTENCLR_EL1_SysRegWrite_1ebd7bf3738fe872[non_mem_expI]:
  "non_mem_exp (PMINTENCLR_EL1_SysRegWrite_1ebd7bf3738fe872 el op0 op1 CRn op2 CRm val_name)"
  by (unfold PMINTENCLR_EL1_SysRegWrite_1ebd7bf3738fe872_def, non_mem_expI)

lemma non_mem_exp_PMINTENSET_EL1_SysRegWrite_dd2481ad892e3441[non_mem_expI]:
  "non_mem_exp (PMINTENSET_EL1_SysRegWrite_dd2481ad892e3441 el op0 op1 CRn op2 CRm val_name)"
  by (unfold PMINTENSET_EL1_SysRegWrite_dd2481ad892e3441_def, non_mem_expI)

lemma non_mem_exp_PMOVSCLR_EL0_SysRegWrite_9dfa73cda394af99[non_mem_expI]:
  "non_mem_exp (PMOVSCLR_EL0_SysRegWrite_9dfa73cda394af99 el op0 op1 CRn op2 CRm val_name)"
  by (unfold PMOVSCLR_EL0_SysRegWrite_9dfa73cda394af99_def, non_mem_expI)

lemma non_mem_exp_PMOVSSET_EL0_SysRegWrite_cfbbfe3b81fe4290[non_mem_expI]:
  "non_mem_exp (PMOVSSET_EL0_SysRegWrite_cfbbfe3b81fe4290 el op0 op1 CRn op2 CRm val_name)"
  by (unfold PMOVSSET_EL0_SysRegWrite_cfbbfe3b81fe4290_def, non_mem_expI)

lemma non_mem_exp_PMSCR_EL12_SysRegWrite_fef9a94f50c2763b[non_mem_expI]:
  "non_mem_exp (PMSCR_EL12_SysRegWrite_fef9a94f50c2763b el op0 op1 CRn op2 CRm val_name)"
  by (unfold PMSCR_EL12_SysRegWrite_fef9a94f50c2763b_def, non_mem_expI)

lemma non_mem_exp_PMSCR_EL1_SysRegWrite_9798a89ab6804fe0[non_mem_expI]:
  "non_mem_exp (PMSCR_EL1_SysRegWrite_9798a89ab6804fe0 el op0 op1 CRn op2 CRm val_name)"
  by (unfold PMSCR_EL1_SysRegWrite_9798a89ab6804fe0_def, non_mem_expI)

lemma non_mem_exp_PMSCR_EL2_SysRegWrite_02cd14dd325ed94b[non_mem_expI]:
  "non_mem_exp (PMSCR_EL2_SysRegWrite_02cd14dd325ed94b el op0 op1 CRn op2 CRm val_name)"
  by (unfold PMSCR_EL2_SysRegWrite_02cd14dd325ed94b_def, non_mem_expI)

lemma non_mem_exp_PMSELR_EL0_SysRegWrite_18613307de8564a3[non_mem_expI]:
  "non_mem_exp (PMSELR_EL0_SysRegWrite_18613307de8564a3 el op0 op1 CRn op2 CRm val_name)"
  by (unfold PMSELR_EL0_SysRegWrite_18613307de8564a3_def, non_mem_expI)

lemma non_mem_exp_PMSEVFR_EL1_SysRegWrite_6524c56cd8a10057[non_mem_expI]:
  "non_mem_exp (PMSEVFR_EL1_SysRegWrite_6524c56cd8a10057 el op0 op1 CRn op2 CRm val_name)"
  by (unfold PMSEVFR_EL1_SysRegWrite_6524c56cd8a10057_def, non_mem_expI)

lemma non_mem_exp_PMSFCR_EL1_SysRegWrite_44d58271848f0db1[non_mem_expI]:
  "non_mem_exp (PMSFCR_EL1_SysRegWrite_44d58271848f0db1 el op0 op1 CRn op2 CRm val_name)"
  by (unfold PMSFCR_EL1_SysRegWrite_44d58271848f0db1_def, non_mem_expI)

lemma non_mem_exp_PMSICR_EL1_SysRegWrite_1e74423ea1c96ae7[non_mem_expI]:
  "non_mem_exp (PMSICR_EL1_SysRegWrite_1e74423ea1c96ae7 el op0 op1 CRn op2 CRm val_name)"
  by (unfold PMSICR_EL1_SysRegWrite_1e74423ea1c96ae7_def, non_mem_expI)

lemma non_mem_exp_PMSIRR_EL1_SysRegWrite_bb25878486c35a36[non_mem_expI]:
  "non_mem_exp (PMSIRR_EL1_SysRegWrite_bb25878486c35a36 el op0 op1 CRn op2 CRm val_name)"
  by (unfold PMSIRR_EL1_SysRegWrite_bb25878486c35a36_def, non_mem_expI)

lemma non_mem_exp_PMSLATFR_EL1_SysRegWrite_5c8b43a6a65c8272[non_mem_expI]:
  "non_mem_exp (PMSLATFR_EL1_SysRegWrite_5c8b43a6a65c8272 el op0 op1 CRn op2 CRm val_name)"
  by (unfold PMSLATFR_EL1_SysRegWrite_5c8b43a6a65c8272_def, non_mem_expI)

lemma non_mem_exp_PMSWINC_EL0_SysRegWrite_cce1d915b163d5e3[non_mem_expI]:
  "non_mem_exp (PMSWINC_EL0_SysRegWrite_cce1d915b163d5e3 el op0 op1 CRn op2 CRm val_name)"
  by (unfold PMSWINC_EL0_SysRegWrite_cce1d915b163d5e3_def, non_mem_expI)

lemma non_mem_exp_PMUSERENR_EL0_SysRegWrite_e7535626e3360c36[non_mem_expI]:
  "non_mem_exp (PMUSERENR_EL0_SysRegWrite_e7535626e3360c36 el op0 op1 CRn op2 CRm val_name)"
  by (unfold PMUSERENR_EL0_SysRegWrite_e7535626e3360c36_def, non_mem_expI)

lemma non_mem_exp_PMXEVCNTR_EL0_SysRegWrite_20b0a6df43a7d4ef[non_mem_expI]:
  "non_mem_exp (PMXEVCNTR_EL0_SysRegWrite_20b0a6df43a7d4ef el op0 op1 CRn op2 CRm val_name)"
  by (unfold PMXEVCNTR_EL0_SysRegWrite_20b0a6df43a7d4ef_def, non_mem_expI)

lemma non_mem_exp_PMXEVTYPER_EL0_SysRegWrite_82fb55a6e723e983[non_mem_expI]:
  "non_mem_exp (PMXEVTYPER_EL0_SysRegWrite_82fb55a6e723e983 el op0 op1 CRn op2 CRm val_name)"
  by (unfold PMXEVTYPER_EL0_SysRegWrite_82fb55a6e723e983_def, non_mem_expI)

lemma non_mem_exp_RMR_EL1_SysRegWrite_0ae19f794f511c7a[non_mem_expI]:
  "non_mem_exp (RMR_EL1_SysRegWrite_0ae19f794f511c7a el op0 op1 CRn op2 CRm val_name)"
  by (unfold RMR_EL1_SysRegWrite_0ae19f794f511c7a_def, non_mem_expI)

lemma non_mem_exp_RMR_EL2_SysRegWrite_df7b9a989e2495d2[non_mem_expI]:
  "non_mem_exp (RMR_EL2_SysRegWrite_df7b9a989e2495d2 el op0 op1 CRn op2 CRm val_name)"
  by (unfold RMR_EL2_SysRegWrite_df7b9a989e2495d2_def, non_mem_expI)

lemma non_mem_exp_RMR_EL3_SysRegWrite_2849130fc457929e[non_mem_expI]:
  "non_mem_exp (RMR_EL3_SysRegWrite_2849130fc457929e el op0 op1 CRn op2 CRm val_name)"
  by (unfold RMR_EL3_SysRegWrite_2849130fc457929e_def, non_mem_expI)

lemma non_mem_exp_RSP_EL0_SysRegWrite_5b2edb6edd27507d[non_mem_expI]:
  "non_mem_exp (RSP_EL0_SysRegWrite_5b2edb6edd27507d el op0 op1 CRn op2 CRm val_name)"
  by (unfold RSP_EL0_SysRegWrite_5b2edb6edd27507d_def, non_mem_expI)

lemma non_mem_exp_RTPIDR_EL0_SysRegWrite_74d55919bd0ab5f3[non_mem_expI]:
  "non_mem_exp (RTPIDR_EL0_SysRegWrite_74d55919bd0ab5f3 el op0 op1 CRn op2 CRm val_name)"
  by (unfold RTPIDR_EL0_SysRegWrite_74d55919bd0ab5f3_def, non_mem_expI)

lemma non_mem_exp_S3_op1_CCn_CCm_op2_SysRegWrite_22dd63287f599042[non_mem_expI]:
  "non_mem_exp (S3_op1_CCn_CCm_op2_SysRegWrite_22dd63287f599042 el op0 op1 CRn op2 CRm val_name)"
  by (unfold S3_op1_CCn_CCm_op2_SysRegWrite_22dd63287f599042_def, non_mem_expI)

lemma non_mem_exp_SCR_EL3_SysRegWrite_020d082781fa9b72[non_mem_expI]:
  "non_mem_exp (SCR_EL3_SysRegWrite_020d082781fa9b72 el op0 op1 CRn op2 CRm val_name)"
  by (unfold SCR_EL3_SysRegWrite_020d082781fa9b72_def, non_mem_expI)

lemma non_mem_exp_SCTLR_EL12_SysRegWrite_302de25977d2a0ca[non_mem_expI]:
  "non_mem_exp (SCTLR_EL12_SysRegWrite_302de25977d2a0ca el op0 op1 CRn op2 CRm val_name)"
  by (unfold SCTLR_EL12_SysRegWrite_302de25977d2a0ca_def, non_mem_expI)

lemma non_mem_exp_SCTLR_EL1_SysRegWrite_711b0546c662c54d[non_mem_expI]:
  "non_mem_exp (SCTLR_EL1_SysRegWrite_711b0546c662c54d el op0 op1 CRn op2 CRm val_name)"
  by (unfold SCTLR_EL1_SysRegWrite_711b0546c662c54d_def, non_mem_expI)

lemma non_mem_exp_SCTLR_EL2_SysRegWrite_ff61a6f00288b28a[non_mem_expI]:
  "non_mem_exp (SCTLR_EL2_SysRegWrite_ff61a6f00288b28a el op0 op1 CRn op2 CRm val_name)"
  by (unfold SCTLR_EL2_SysRegWrite_ff61a6f00288b28a_def, non_mem_expI)

lemma non_mem_exp_SCTLR_EL3_SysRegWrite_5b7cc79e5ea93a8f[non_mem_expI]:
  "non_mem_exp (SCTLR_EL3_SysRegWrite_5b7cc79e5ea93a8f el op0 op1 CRn op2 CRm val_name)"
  by (unfold SCTLR_EL3_SysRegWrite_5b7cc79e5ea93a8f_def, non_mem_expI)

lemma non_mem_exp_SCXTNUM_EL0_write[non_mem_expI]:
  "non_mem_exp (SCXTNUM_EL0_write val_name)"
  by (unfold SCXTNUM_EL0_write_def, non_mem_expI)

lemma non_mem_exp_SCXTNUM_EL0_SysRegWrite_9dbee2793d69c02e[non_mem_expI]:
  "non_mem_exp (SCXTNUM_EL0_SysRegWrite_9dbee2793d69c02e el op0 op1 CRn op2 CRm val_name)"
  by (unfold SCXTNUM_EL0_SysRegWrite_9dbee2793d69c02e_def, non_mem_expI)

lemma non_mem_exp_SCXTNUM_EL12_SysRegWrite_ba74367909393c9b[non_mem_expI]:
  "non_mem_exp (SCXTNUM_EL12_SysRegWrite_ba74367909393c9b el op0 op1 CRn op2 CRm val_name)"
  by (unfold SCXTNUM_EL12_SysRegWrite_ba74367909393c9b_def, non_mem_expI)

lemma non_mem_exp_SCXTNUM_EL1_SysRegWrite_6467f6f26a31cece[non_mem_expI]:
  "non_mem_exp (SCXTNUM_EL1_SysRegWrite_6467f6f26a31cece el op0 op1 CRn op2 CRm val_name)"
  by (unfold SCXTNUM_EL1_SysRegWrite_6467f6f26a31cece_def, non_mem_expI)

lemma non_mem_exp_SCXTNUM_EL2_SysRegWrite_2fcbb6503badb23c[non_mem_expI]:
  "non_mem_exp (SCXTNUM_EL2_SysRegWrite_2fcbb6503badb23c el op0 op1 CRn op2 CRm val_name)"
  by (unfold SCXTNUM_EL2_SysRegWrite_2fcbb6503badb23c_def, non_mem_expI)

lemma non_mem_exp_SCXTNUM_EL3_SysRegWrite_b39fe9ab09a67ecd[non_mem_expI]:
  "non_mem_exp (SCXTNUM_EL3_SysRegWrite_b39fe9ab09a67ecd el op0 op1 CRn op2 CRm val_name)"
  by (unfold SCXTNUM_EL3_SysRegWrite_b39fe9ab09a67ecd_def, non_mem_expI)

lemma non_mem_exp_SDER32_EL3_SysRegWrite_69011ff5e95ac923[non_mem_expI]:
  "non_mem_exp (SDER32_EL3_SysRegWrite_69011ff5e95ac923 el op0 op1 CRn op2 CRm val_name)"
  by (unfold SDER32_EL3_SysRegWrite_69011ff5e95ac923_def, non_mem_expI)

lemma non_mem_exp_SPSel_SysRegWrite_c849e120e8533c8c[non_mem_expI]:
  "non_mem_exp (SPSel_SysRegWrite_c849e120e8533c8c el op0 op1 CRn op2 CRm val_name)"
  by (unfold SPSel_SysRegWrite_c849e120e8533c8c_def, non_mem_expI)

lemma non_mem_exp_SP_EL0_SysRegWrite_78f870c69d82f9e2[non_mem_expI]:
  "non_mem_exp (SP_EL0_SysRegWrite_78f870c69d82f9e2 el op0 op1 CRn op2 CRm val_name)"
  by (unfold SP_EL0_SysRegWrite_78f870c69d82f9e2_def, non_mem_expI)

lemma non_mem_exp_SP_EL1_SysRegWrite_84ae51cf4bf77caa[non_mem_expI]:
  "non_mem_exp (SP_EL1_SysRegWrite_84ae51cf4bf77caa el op0 op1 CRn op2 CRm val_name)"
  by (unfold SP_EL1_SysRegWrite_84ae51cf4bf77caa_def, non_mem_expI)

lemma non_mem_exp_SP_EL2_SysRegWrite_a29ffeac6d3856e5[non_mem_expI]:
  "non_mem_exp (SP_EL2_SysRegWrite_a29ffeac6d3856e5 el op0 op1 CRn op2 CRm val_name)"
  by (unfold SP_EL2_SysRegWrite_a29ffeac6d3856e5_def, non_mem_expI)

lemma non_mem_exp_TCR_EL12_SysRegWrite_64a7f44c6ddaa0f8[non_mem_expI]:
  "non_mem_exp (TCR_EL12_SysRegWrite_64a7f44c6ddaa0f8 el op0 op1 CRn op2 CRm val_name)"
  by (unfold TCR_EL12_SysRegWrite_64a7f44c6ddaa0f8_def, non_mem_expI)

lemma non_mem_exp_TCR_EL1_SysRegWrite_c27e6fc190bb0f0b[non_mem_expI]:
  "non_mem_exp (TCR_EL1_SysRegWrite_c27e6fc190bb0f0b el op0 op1 CRn op2 CRm val_name)"
  by (unfold TCR_EL1_SysRegWrite_c27e6fc190bb0f0b_def, non_mem_expI)

lemma non_mem_exp_TCR_EL2_SysRegWrite_5e38279a245750c4[non_mem_expI]:
  "non_mem_exp (TCR_EL2_SysRegWrite_5e38279a245750c4 el op0 op1 CRn op2 CRm val_name)"
  by (unfold TCR_EL2_SysRegWrite_5e38279a245750c4_def, non_mem_expI)

lemma non_mem_exp_TCR_EL3_SysRegWrite_3b3587015a3d20f4[non_mem_expI]:
  "non_mem_exp (TCR_EL3_SysRegWrite_3b3587015a3d20f4 el op0 op1 CRn op2 CRm val_name)"
  by (unfold TCR_EL3_SysRegWrite_3b3587015a3d20f4_def, non_mem_expI)

lemma non_mem_exp_TPIDRRO_EL0_SysRegWrite_20bedffb2581e57d[non_mem_expI]:
  "non_mem_exp (TPIDRRO_EL0_SysRegWrite_20bedffb2581e57d el op0 op1 CRn op2 CRm val_name)"
  by (unfold TPIDRRO_EL0_SysRegWrite_20bedffb2581e57d_def, non_mem_expI)

lemma non_mem_exp_TPIDR_EL0_SysRegWrite_6b1ef76c828f0bf5[non_mem_expI]:
  "non_mem_exp (TPIDR_EL0_SysRegWrite_6b1ef76c828f0bf5 el op0 op1 CRn op2 CRm val_name)"
  by (unfold TPIDR_EL0_SysRegWrite_6b1ef76c828f0bf5_def, non_mem_expI)

lemma non_mem_exp_TPIDR_EL1_SysRegWrite_566127c19bf948d1[non_mem_expI]:
  "non_mem_exp (TPIDR_EL1_SysRegWrite_566127c19bf948d1 el op0 op1 CRn op2 CRm val_name)"
  by (unfold TPIDR_EL1_SysRegWrite_566127c19bf948d1_def, non_mem_expI)

lemma non_mem_exp_TPIDR_EL2_SysRegWrite_adfab02a898d4b19[non_mem_expI]:
  "non_mem_exp (TPIDR_EL2_SysRegWrite_adfab02a898d4b19 el op0 op1 CRn op2 CRm val_name)"
  by (unfold TPIDR_EL2_SysRegWrite_adfab02a898d4b19_def, non_mem_expI)

lemma non_mem_exp_TPIDR_EL3_SysRegWrite_08e0e9cc5d3f6f5c[non_mem_expI]:
  "non_mem_exp (TPIDR_EL3_SysRegWrite_08e0e9cc5d3f6f5c el op0 op1 CRn op2 CRm val_name)"
  by (unfold TPIDR_EL3_SysRegWrite_08e0e9cc5d3f6f5c_def, non_mem_expI)

lemma non_mem_exp_TTBR0_EL12_SysRegWrite_fd9df8519bfad5c0[non_mem_expI]:
  "non_mem_exp (TTBR0_EL12_SysRegWrite_fd9df8519bfad5c0 el op0 op1 CRn op2 CRm val_name)"
  by (unfold TTBR0_EL12_SysRegWrite_fd9df8519bfad5c0_def, non_mem_expI)

lemma non_mem_exp_TTBR0_EL1_SysRegWrite_8a149790a79e2eab[non_mem_expI]:
  "non_mem_exp (TTBR0_EL1_SysRegWrite_8a149790a79e2eab el op0 op1 CRn op2 CRm val_name)"
  by (unfold TTBR0_EL1_SysRegWrite_8a149790a79e2eab_def, non_mem_expI)

lemma non_mem_exp_TTBR0_EL2_SysRegWrite_7cd39d4a24a70e7f[non_mem_expI]:
  "non_mem_exp (TTBR0_EL2_SysRegWrite_7cd39d4a24a70e7f el op0 op1 CRn op2 CRm val_name)"
  by (unfold TTBR0_EL2_SysRegWrite_7cd39d4a24a70e7f_def, non_mem_expI)

lemma non_mem_exp_TTBR0_EL3_SysRegWrite_7e091a8effc9ee7f[non_mem_expI]:
  "non_mem_exp (TTBR0_EL3_SysRegWrite_7e091a8effc9ee7f el op0 op1 CRn op2 CRm val_name)"
  by (unfold TTBR0_EL3_SysRegWrite_7e091a8effc9ee7f_def, non_mem_expI)

lemma non_mem_exp_TTBR1_EL12_SysRegWrite_4fbeb1f28c2e8107[non_mem_expI]:
  "non_mem_exp (TTBR1_EL12_SysRegWrite_4fbeb1f28c2e8107 el op0 op1 CRn op2 CRm val_name)"
  by (unfold TTBR1_EL12_SysRegWrite_4fbeb1f28c2e8107_def, non_mem_expI)

lemma non_mem_exp_TTBR1_EL1_SysRegWrite_89690e4d3c87217b[non_mem_expI]:
  "non_mem_exp (TTBR1_EL1_SysRegWrite_89690e4d3c87217b el op0 op1 CRn op2 CRm val_name)"
  by (unfold TTBR1_EL1_SysRegWrite_89690e4d3c87217b_def, non_mem_expI)

lemma non_mem_exp_TTBR1_EL2_SysRegWrite_59fad32bc548b47a[non_mem_expI]:
  "non_mem_exp (TTBR1_EL2_SysRegWrite_59fad32bc548b47a el op0 op1 CRn op2 CRm val_name)"
  by (unfold TTBR1_EL2_SysRegWrite_59fad32bc548b47a_def, non_mem_expI)

lemma non_mem_exp_VBAR_EL12_SysRegWrite_a20f8f7f07b5cf7a[non_mem_expI]:
  "non_mem_exp (VBAR_EL12_SysRegWrite_a20f8f7f07b5cf7a el op0 op1 CRn op2 CRm val_name)"
  by (unfold VBAR_EL12_SysRegWrite_a20f8f7f07b5cf7a_def, non_mem_expI)

lemma non_mem_exp_VBAR_EL1_SysRegWrite_29ba7540e032fce6[non_mem_expI]:
  "non_mem_exp (VBAR_EL1_SysRegWrite_29ba7540e032fce6 el op0 op1 CRn op2 CRm val_name)"
  by (unfold VBAR_EL1_SysRegWrite_29ba7540e032fce6_def, non_mem_expI)

lemma non_mem_exp_VBAR_EL2_SysRegWrite_d5657e8591e8e22a[non_mem_expI]:
  "non_mem_exp (VBAR_EL2_SysRegWrite_d5657e8591e8e22a el op0 op1 CRn op2 CRm val_name)"
  by (unfold VBAR_EL2_SysRegWrite_d5657e8591e8e22a_def, non_mem_expI)

lemma non_mem_exp_VBAR_EL3_SysRegWrite_1da603c27eb5f668[non_mem_expI]:
  "non_mem_exp (VBAR_EL3_SysRegWrite_1da603c27eb5f668 el op0 op1 CRn op2 CRm val_name)"
  by (unfold VBAR_EL3_SysRegWrite_1da603c27eb5f668_def, non_mem_expI)

lemma non_mem_exp_VDISR_EL2_SysRegWrite_8b2c23874e253f64[non_mem_expI]:
  "non_mem_exp (VDISR_EL2_SysRegWrite_8b2c23874e253f64 el op0 op1 CRn op2 CRm val_name)"
  by (unfold VDISR_EL2_SysRegWrite_8b2c23874e253f64_def, non_mem_expI)

lemma non_mem_exp_VMPIDR_EL2_SysRegWrite_c153d7c8b5628bd5[non_mem_expI]:
  "non_mem_exp (VMPIDR_EL2_SysRegWrite_c153d7c8b5628bd5 el op0 op1 CRn op2 CRm val_name)"
  by (unfold VMPIDR_EL2_SysRegWrite_c153d7c8b5628bd5_def, non_mem_expI)

lemma non_mem_exp_VPIDR_EL2_SysRegWrite_0dbf139af5a73d1f[non_mem_expI]:
  "non_mem_exp (VPIDR_EL2_SysRegWrite_0dbf139af5a73d1f el op0 op1 CRn op2 CRm val_name)"
  by (unfold VPIDR_EL2_SysRegWrite_0dbf139af5a73d1f_def, non_mem_expI)

lemma non_mem_exp_VSESR_EL2_SysRegWrite_e989f4bcf0ae8aa6[non_mem_expI]:
  "non_mem_exp (VSESR_EL2_SysRegWrite_e989f4bcf0ae8aa6 el op0 op1 CRn op2 CRm val_name)"
  by (unfold VSESR_EL2_SysRegWrite_e989f4bcf0ae8aa6_def, non_mem_expI)

lemma non_mem_exp_VTCR_EL2_SysRegWrite_d49abb8b3aa0eff3[non_mem_expI]:
  "non_mem_exp (VTCR_EL2_SysRegWrite_d49abb8b3aa0eff3 el op0 op1 CRn op2 CRm val_name)"
  by (unfold VTCR_EL2_SysRegWrite_d49abb8b3aa0eff3_def, non_mem_expI)

lemma non_mem_exp_VTTBR_EL2_SysRegWrite_5198ee0e793550a5[non_mem_expI]:
  "non_mem_exp (VTTBR_EL2_SysRegWrite_5198ee0e793550a5 el op0 op1 CRn op2 CRm val_name)"
  by (unfold VTTBR_EL2_SysRegWrite_5198ee0e793550a5_def, non_mem_expI)

lemma non_mem_exp_AArch64_AutoGen_SysRegWrite[non_mem_expI]:
  "non_mem_exp (AArch64_AutoGen_SysRegWrite el op0 op1 CRn op2 CRm val_name)"
  by (unfold AArch64_AutoGen_SysRegWrite_def, non_mem_expI)

lemma non_mem_exp_AArch64_IMPDEFResets[non_mem_expI]:
  "non_mem_exp (AArch64_IMPDEFResets arg0)"
  by (unfold AArch64_IMPDEFResets_def, non_mem_expI)

lemma non_mem_exp_AArch64_AutoGen_ArchitectureReset[non_mem_expI]:
  "non_mem_exp (AArch64_AutoGen_ArchitectureReset cold)"
  by (unfold AArch64_AutoGen_ArchitectureReset_def, non_mem_expI)

lemma non_mem_exp_AArch64_ResetControlRegisters[non_mem_expI]:
  "non_mem_exp (AArch64_ResetControlRegisters cold)"
  by (unfold AArch64_ResetControlRegisters_def, non_mem_expI)

lemma non_mem_exp_C_set[non_mem_expI]:
  "non_mem_exp (C_set n value_name)"
  by (unfold C_set_def, non_mem_expI)

lemma non_mem_exp_AArch64_ResetGeneralRegisters[non_mem_expI]:
  "non_mem_exp (AArch64_ResetGeneralRegisters arg0)"
  by (unfold AArch64_ResetGeneralRegisters_def, non_mem_expI)

lemma non_mem_exp_AArch64_ResetSpecialRegisters[non_mem_expI]:
  "non_mem_exp (AArch64_ResetSpecialRegisters arg0)"
  by (unfold AArch64_ResetSpecialRegisters_def, non_mem_expI)

lemma non_mem_exp_AArch64_TakeReset[non_mem_expI]:
  "non_mem_exp (AArch64_TakeReset cold_reset)"
  by (unfold AArch64_TakeReset_def, non_mem_expI)

lemma non_mem_exp_TakeReset[non_mem_expI]:
  "non_mem_exp (TakeReset cold)"
  by (unfold TakeReset_def, non_mem_expI)

lemma non_mem_exp_AArch64_SysRegWrite[non_mem_expI]:
  "non_mem_exp (AArch64_SysRegWrite op0 op1 crn crm op2 val_name)"
  by (unfold AArch64_SysRegWrite_def TakeReset_def AArch64_TakeReset_def AArch64_ResetControlRegisters_def AArch64_ResetSpecialRegisters_def AArch64_IMPDEFResets_def AArch64_AutoGen_ArchitectureReset_def MPAM2_EL2_read_def MPAM1_EL1_read_def MPAM2_EL2_write_def MPAM1_EL1_write_def ICC_CTLR_EL1_write_def ICC_CTLR_EL1_read_def Let_def bind_assoc, non_mem_expI intro: non_mem_exp_bind_no_asm non_mem_exp_if_no_asm)

lemma non_mem_exp_CDBGDTR_EL0_CapSysRegWrite_336052f10e4a36b7[non_mem_expI]:
  "non_mem_exp (CDBGDTR_EL0_CapSysRegWrite_336052f10e4a36b7 el op0 op1 CRn op2 CRm val_name)"
  by (unfold CDBGDTR_EL0_CapSysRegWrite_336052f10e4a36b7_def, non_mem_expI)

lemma non_mem_exp_CDLR_EL0_CapSysRegWrite_2763be7daadf3c03[non_mem_expI]:
  "non_mem_exp (CDLR_EL0_CapSysRegWrite_2763be7daadf3c03 el op0 op1 CRn op2 CRm val_name)"
  by (unfold CDLR_EL0_CapSysRegWrite_2763be7daadf3c03_def, non_mem_expI)

lemma non_mem_exp_CELR_EL12_CapSysRegWrite_a1507df00ba9d725[non_mem_expI]:
  "non_mem_exp (CELR_EL12_CapSysRegWrite_a1507df00ba9d725 el op0 op1 CRn op2 CRm val_name)"
  by (unfold CELR_EL12_CapSysRegWrite_a1507df00ba9d725_def, non_mem_expI)

lemma non_mem_exp_CELR_EL1_CapSysRegWrite_33a9b4f0fad89fe8[non_mem_expI]:
  "non_mem_exp (CELR_EL1_CapSysRegWrite_33a9b4f0fad89fe8 el op0 op1 CRn op2 CRm val_name)"
  by (unfold CELR_EL1_CapSysRegWrite_33a9b4f0fad89fe8_def, non_mem_expI)

lemma non_mem_exp_CELR_EL2_CapSysRegWrite_8d32fe1dd5ad0417[non_mem_expI]:
  "non_mem_exp (CELR_EL2_CapSysRegWrite_8d32fe1dd5ad0417 el op0 op1 CRn op2 CRm val_name)"
  by (unfold CELR_EL2_CapSysRegWrite_8d32fe1dd5ad0417_def, non_mem_expI)

lemma non_mem_exp_CELR_EL3_CapSysRegWrite_55e82fec5d907003[non_mem_expI]:
  "non_mem_exp (CELR_EL3_CapSysRegWrite_55e82fec5d907003 el op0 op1 CRn op2 CRm val_name)"
  by (unfold CELR_EL3_CapSysRegWrite_55e82fec5d907003_def, non_mem_expI)

lemma non_mem_exp_CID_EL0_CapSysRegWrite_8c1c5cf69181759f[non_mem_expI]:
  "non_mem_exp (CID_EL0_CapSysRegWrite_8c1c5cf69181759f el op0 op1 CRn op2 CRm val_name)"
  by (unfold CID_EL0_CapSysRegWrite_8c1c5cf69181759f_def, non_mem_expI)

lemma non_mem_exp_CSP_EL0_CapSysRegWrite_ee1d127810ef0f04[non_mem_expI]:
  "non_mem_exp (CSP_EL0_CapSysRegWrite_ee1d127810ef0f04 el op0 op1 CRn op2 CRm val_name)"
  by (unfold CSP_EL0_CapSysRegWrite_ee1d127810ef0f04_def, non_mem_expI)

lemma non_mem_exp_CSP_EL1_CapSysRegWrite_f4579d836810c21a[non_mem_expI]:
  "non_mem_exp (CSP_EL1_CapSysRegWrite_f4579d836810c21a el op0 op1 CRn op2 CRm val_name)"
  by (unfold CSP_EL1_CapSysRegWrite_f4579d836810c21a_def, non_mem_expI)

lemma non_mem_exp_CSP_EL2_CapSysRegWrite_59c69d74679ef283[non_mem_expI]:
  "non_mem_exp (CSP_EL2_CapSysRegWrite_59c69d74679ef283 el op0 op1 CRn op2 CRm val_name)"
  by (unfold CSP_EL2_CapSysRegWrite_59c69d74679ef283_def, non_mem_expI)

lemma non_mem_exp_CTPIDRRO_EL0_CapSysRegWrite_e64109ff95ad4800[non_mem_expI]:
  "non_mem_exp (CTPIDRRO_EL0_CapSysRegWrite_e64109ff95ad4800 el op0 op1 CRn op2 CRm val_name)"
  by (unfold CTPIDRRO_EL0_CapSysRegWrite_e64109ff95ad4800_def, non_mem_expI)

lemma non_mem_exp_CTPIDR_EL0_CapSysRegWrite_8f94c4d256adadf0[non_mem_expI]:
  "non_mem_exp (CTPIDR_EL0_CapSysRegWrite_8f94c4d256adadf0 el op0 op1 CRn op2 CRm val_name)"
  by (unfold CTPIDR_EL0_CapSysRegWrite_8f94c4d256adadf0_def, non_mem_expI)

lemma non_mem_exp_CTPIDR_EL1_CapSysRegWrite_3190df090d2d128f[non_mem_expI]:
  "non_mem_exp (CTPIDR_EL1_CapSysRegWrite_3190df090d2d128f el op0 op1 CRn op2 CRm val_name)"
  by (unfold CTPIDR_EL1_CapSysRegWrite_3190df090d2d128f_def, non_mem_expI)

lemma non_mem_exp_CTPIDR_EL2_CapSysRegWrite_a740113e578c9b32[non_mem_expI]:
  "non_mem_exp (CTPIDR_EL2_CapSysRegWrite_a740113e578c9b32 el op0 op1 CRn op2 CRm val_name)"
  by (unfold CTPIDR_EL2_CapSysRegWrite_a740113e578c9b32_def, non_mem_expI)

lemma non_mem_exp_CTPIDR_EL3_CapSysRegWrite_376b7d525b15b21b[non_mem_expI]:
  "non_mem_exp (CTPIDR_EL3_CapSysRegWrite_376b7d525b15b21b el op0 op1 CRn op2 CRm val_name)"
  by (unfold CTPIDR_EL3_CapSysRegWrite_376b7d525b15b21b_def, non_mem_expI)

lemma non_mem_exp_CVBAR_EL12_CapSysRegWrite_3fd157cf974c31e5[non_mem_expI]:
  "non_mem_exp (CVBAR_EL12_CapSysRegWrite_3fd157cf974c31e5 el op0 op1 CRn op2 CRm val_name)"
  by (unfold CVBAR_EL12_CapSysRegWrite_3fd157cf974c31e5_def, non_mem_expI)

lemma non_mem_exp_CVBAR_EL1_CapSysRegWrite_bbad0575f41fce2f[non_mem_expI]:
  "non_mem_exp (CVBAR_EL1_CapSysRegWrite_bbad0575f41fce2f el op0 op1 CRn op2 CRm val_name)"
  by (unfold CVBAR_EL1_CapSysRegWrite_bbad0575f41fce2f_def, non_mem_expI)

lemma non_mem_exp_CVBAR_EL2_CapSysRegWrite_2a412e2b2c0a0a2b[non_mem_expI]:
  "non_mem_exp (CVBAR_EL2_CapSysRegWrite_2a412e2b2c0a0a2b el op0 op1 CRn op2 CRm val_name)"
  by (unfold CVBAR_EL2_CapSysRegWrite_2a412e2b2c0a0a2b_def, non_mem_expI)

lemma non_mem_exp_CVBAR_EL3_CapSysRegWrite_f3c8bbee84b292db[non_mem_expI]:
  "non_mem_exp (CVBAR_EL3_CapSysRegWrite_f3c8bbee84b292db el op0 op1 CRn op2 CRm val_name)"
  by (unfold CVBAR_EL3_CapSysRegWrite_f3c8bbee84b292db_def, non_mem_expI)

lemma non_mem_exp_DDC_CapSysRegWrite_9bc98e4e82148914[non_mem_expI]:
  "non_mem_exp (DDC_CapSysRegWrite_9bc98e4e82148914 el op0 op1 CRn op2 CRm val_name)"
  by (unfold DDC_CapSysRegWrite_9bc98e4e82148914_def, non_mem_expI)

lemma non_mem_exp_DDC_EL0_CapSysRegWrite_1a928678ff9b43a6[non_mem_expI]:
  "non_mem_exp (DDC_EL0_CapSysRegWrite_1a928678ff9b43a6 el op0 op1 CRn op2 CRm val_name)"
  by (unfold DDC_EL0_CapSysRegWrite_1a928678ff9b43a6_def, non_mem_expI)

lemma non_mem_exp_DDC_EL1_CapSysRegWrite_e7ecb5b1f0c49d28[non_mem_expI]:
  "non_mem_exp (DDC_EL1_CapSysRegWrite_e7ecb5b1f0c49d28 el op0 op1 CRn op2 CRm val_name)"
  by (unfold DDC_EL1_CapSysRegWrite_e7ecb5b1f0c49d28_def, non_mem_expI)

lemma non_mem_exp_DDC_EL2_CapSysRegWrite_b4142a2dcadf2a34[non_mem_expI]:
  "non_mem_exp (DDC_EL2_CapSysRegWrite_b4142a2dcadf2a34 el op0 op1 CRn op2 CRm val_name)"
  by (unfold DDC_EL2_CapSysRegWrite_b4142a2dcadf2a34_def, non_mem_expI)

lemma non_mem_exp_RCSP_EL0_CapSysRegWrite_d8f83400674fbeeb[non_mem_expI]:
  "non_mem_exp (RCSP_EL0_CapSysRegWrite_d8f83400674fbeeb el op0 op1 CRn op2 CRm val_name)"
  by (unfold RCSP_EL0_CapSysRegWrite_d8f83400674fbeeb_def, non_mem_expI)

lemma non_mem_exp_RCTPIDR_EL0_CapSysRegWrite_27f7c47e137c72f8[non_mem_expI]:
  "non_mem_exp (RCTPIDR_EL0_CapSysRegWrite_27f7c47e137c72f8 el op0 op1 CRn op2 CRm val_name)"
  by (unfold RCTPIDR_EL0_CapSysRegWrite_27f7c47e137c72f8_def, non_mem_expI)

lemma non_mem_exp_RDDC_EL0_CapSysRegWrite_c528d1b2eb785ad7[non_mem_expI]:
  "non_mem_exp (RDDC_EL0_CapSysRegWrite_c528d1b2eb785ad7 el op0 op1 CRn op2 CRm val_name)"
  by (unfold RDDC_EL0_CapSysRegWrite_c528d1b2eb785ad7_def, non_mem_expI)

lemma non_mem_exp_AArch64_AutoGen_CapSysRegWrite[non_mem_expI]:
  "non_mem_exp (AArch64_AutoGen_CapSysRegWrite el op0 op1 CRn op2 CRm val_name)"
  by (unfold AArch64_AutoGen_CapSysRegWrite_def, non_mem_expI)

lemma non_mem_exp_DDC_set[non_mem_expI]:
  "non_mem_exp (DDC_set value_name)"
  by (unfold DDC_set_def, non_mem_expI)

lemma non_mem_exp_AArch64_CapSysRegWrite[non_mem_expI]:
  "non_mem_exp (AArch64_CapSysRegWrite op0 op1 crn crm op2 val_name)"
  by (unfold AArch64_CapSysRegWrite_def, non_mem_expI)

lemma non_mem_exp_ALLE1IS_SysOpsWrite_8b81b55e2116aad3[non_mem_expI]:
  "non_mem_exp (ALLE1IS_SysOpsWrite_8b81b55e2116aad3 el op0 op1 CRn op2 CRm val_name)"
  by (unfold ALLE1IS_SysOpsWrite_8b81b55e2116aad3_def, non_mem_expI)

lemma non_mem_exp_ALLE1_SysOpsWrite_69364bedc72cbe96[non_mem_expI]:
  "non_mem_exp (ALLE1_SysOpsWrite_69364bedc72cbe96 el op0 op1 CRn op2 CRm val_name)"
  by (unfold ALLE1_SysOpsWrite_69364bedc72cbe96_def, non_mem_expI)

lemma non_mem_exp_AArch64_UndefinedFault[non_mem_expI]:
  "non_mem_exp (AArch64_UndefinedFault arg0)"
  by (unfold AArch64_UndefinedFault_def, non_mem_expI)

lemma non_mem_exp_UndefinedFault[non_mem_expI]:
  "non_mem_exp (UndefinedFault arg0)"
  by (unfold UndefinedFault_def, non_mem_expI)

lemma non_mem_exp_TLBI_ALLE2IS[non_mem_expI]:
  "non_mem_exp (TLBI_ALLE2IS arg0)"
  by (unfold TLBI_ALLE2IS_def, non_mem_expI)

lemma non_mem_exp_ALLE2IS_SysOpsWrite_3a173239947b2c25[non_mem_expI]:
  "non_mem_exp (ALLE2IS_SysOpsWrite_3a173239947b2c25 el op0 op1 CRn op2 CRm val_name)"
  by (unfold ALLE2IS_SysOpsWrite_3a173239947b2c25_def, non_mem_expI)

lemma non_mem_exp_TLBI_ALLE2[non_mem_expI]:
  "non_mem_exp (TLBI_ALLE2 arg0)"
  by (unfold TLBI_ALLE2_def, non_mem_expI)

lemma non_mem_exp_ALLE2_SysOpsWrite_19c7b5110a5efe1d[non_mem_expI]:
  "non_mem_exp (ALLE2_SysOpsWrite_19c7b5110a5efe1d el op0 op1 CRn op2 CRm val_name)"
  by (unfold ALLE2_SysOpsWrite_19c7b5110a5efe1d_def, non_mem_expI)

lemma non_mem_exp_ALLE3IS_SysOpsWrite_e64b79b4c41910fb[non_mem_expI]:
  "non_mem_exp (ALLE3IS_SysOpsWrite_e64b79b4c41910fb el op0 op1 CRn op2 CRm val_name)"
  by (unfold ALLE3IS_SysOpsWrite_e64b79b4c41910fb_def, non_mem_expI)

lemma non_mem_exp_ALLE3_SysOpsWrite_5835ce2f987f3d36[non_mem_expI]:
  "non_mem_exp (ALLE3_SysOpsWrite_5835ce2f987f3d36 el op0 op1 CRn op2 CRm val_name)"
  by (unfold ALLE3_SysOpsWrite_5835ce2f987f3d36_def, non_mem_expI)

lemma non_mem_exp_ASIDE1IS_SysOpsWrite_5a5dff91f113e41e[non_mem_expI]:
  "non_mem_exp (ASIDE1IS_SysOpsWrite_5a5dff91f113e41e el op0 op1 CRn op2 CRm val_name)"
  by (unfold ASIDE1IS_SysOpsWrite_5a5dff91f113e41e_def, non_mem_expI)

lemma non_mem_exp_ASIDE1_SysOpsWrite_7ba7a3df395925e0[non_mem_expI]:
  "non_mem_exp (ASIDE1_SysOpsWrite_7ba7a3df395925e0 el op0 op1 CRn op2 CRm val_name)"
  by (unfold ASIDE1_SysOpsWrite_7ba7a3df395925e0_def, non_mem_expI)

lemma non_mem_exp_DC_CISW[non_mem_expI]:
  "non_mem_exp (DC_CISW val_name)"
  by (unfold DC_CISW_def, non_mem_expI)

lemma non_mem_exp_CISW_SysOpsWrite_5321b1c3157dccce[non_mem_expI]:
  "non_mem_exp (CISW_SysOpsWrite_5321b1c3157dccce el op0 op1 CRn op2 CRm val_name)"
  by (unfold CISW_SysOpsWrite_5321b1c3157dccce_def, non_mem_expI)

lemma non_mem_exp_AArch64_BreakpointException[non_mem_expI]:
  "non_mem_exp (AArch64_BreakpointException fault)"
  by (unfold AArch64_BreakpointException_def, non_mem_expI)

lemma non_mem_exp_AArch64_DataAbort[non_mem_expI]:
  "non_mem_exp (AArch64_DataAbort vaddress fault)"
  by (unfold AArch64_DataAbort_def, non_mem_expI)

lemma non_mem_exp_AArch64_InstructionAbort[non_mem_expI]:
  "non_mem_exp (AArch64_InstructionAbort vaddress fault)"
  by (unfold AArch64_InstructionAbort_def, non_mem_expI)

lemma non_mem_exp_AArch64_WatchpointException[non_mem_expI]:
  "non_mem_exp (AArch64_WatchpointException vaddress fault)"
  by (unfold AArch64_WatchpointException_def, non_mem_expI)

lemma non_mem_exp_AArch64_Abort[non_mem_expI]:
  "non_mem_exp (AArch64_Abort vaddress fault)"
  by (unfold AArch64_Abort_def, non_mem_expI)

lemma non_mem_exp_AArch64_CheckBreakpoint[non_mem_expI]:
  "non_mem_exp (AArch64_CheckBreakpoint vaddress size__arg)"
  by (unfold AArch64_CheckBreakpoint_def, non_mem_expI)

lemma non_mem_exp_AArch64_CheckWatchpoint[non_mem_expI]:
  "non_mem_exp (AArch64_CheckWatchpoint vaddress acctype iswrite size__arg)"
  by (unfold AArch64_CheckWatchpoint_def, non_mem_expI)

lemma non_mem_exp_AArch64_CheckDebug[non_mem_expI]:
  "non_mem_exp (AArch64_CheckDebug vaddress acctype iswrite size__arg)"
  by (unfold AArch64_CheckDebug_def, non_mem_expI)

lemma non_mem_exp_AArch64_TranslateAddressWithTag[non_mem_expI]:
  "non_mem_exp (AArch64_TranslateAddressWithTag vaddress acctype iswrite wasaligned size__arg iswritevalidcap)"
  by (unfold AArch64_TranslateAddressWithTag_def, non_mem_expI)

lemma non_mem_exp_AArch64_TranslateAddress[non_mem_expI]:
  "non_mem_exp (AArch64_TranslateAddress vaddress acctype iswrite wasaligned size__arg)"
  by (unfold AArch64_TranslateAddress_def, non_mem_expI)

lemma non_mem_exp_DC_CIVAC[non_mem_expI]:
  "non_mem_exp (DC_CIVAC val_name)"
  by (unfold DC_CIVAC_def, non_mem_expI)

lemma non_mem_exp_VAddress[non_mem_expI]:
  "non_mem_exp (VAddress addr)"
  by (unfold VAddress_def, non_mem_expI)

lemma non_mem_exp_MorelloCheckForCMO[non_mem_expI]:
  "non_mem_exp (MorelloCheckForCMO cval requested_perms acctype)"
  by (unfold MorelloCheckForCMO_def, non_mem_expI)

lemma non_mem_exp_DC_CIVAC0[non_mem_expI]:
  "non_mem_exp (DC_CIVAC0 val_name__arg)"
  by (unfold DC_CIVAC0_def, non_mem_expI)

lemma non_mem_exp_CIVAC_SysOpsWrite_47ad60ecb930d217[non_mem_expI]:
  "non_mem_exp (CIVAC_SysOpsWrite_47ad60ecb930d217 el op0 op1 CRn op2 CRm val_name)"
  by (unfold CIVAC_SysOpsWrite_47ad60ecb930d217_def, non_mem_expI)

lemma non_mem_exp_DC_CSW[non_mem_expI]:
  "non_mem_exp (DC_CSW val_name)"
  by (unfold DC_CSW_def, non_mem_expI)

lemma non_mem_exp_CSW_SysOpsWrite_9544819da3ebaa1b[non_mem_expI]:
  "non_mem_exp (CSW_SysOpsWrite_9544819da3ebaa1b el op0 op1 CRn op2 CRm val_name)"
  by (unfold CSW_SysOpsWrite_9544819da3ebaa1b_def, non_mem_expI)

lemma non_mem_exp_DC_CVAC[non_mem_expI]:
  "non_mem_exp (DC_CVAC val_name)"
  by (unfold DC_CVAC_def, non_mem_expI)

lemma non_mem_exp_DC_CVAC0[non_mem_expI]:
  "non_mem_exp (DC_CVAC0 val_name__arg)"
  by (unfold DC_CVAC0_def, non_mem_expI)

lemma non_mem_exp_CVAC_SysOpsWrite_c7d2e911c691cc6b[non_mem_expI]:
  "non_mem_exp (CVAC_SysOpsWrite_c7d2e911c691cc6b el op0 op1 CRn op2 CRm val_name)"
  by (unfold CVAC_SysOpsWrite_c7d2e911c691cc6b_def, non_mem_expI)

lemma non_mem_exp_DC_CVAP[non_mem_expI]:
  "non_mem_exp (DC_CVAP val_name)"
  by (unfold DC_CVAP_def, non_mem_expI)

lemma non_mem_exp_DC_CVADP[non_mem_expI]:
  "non_mem_exp (DC_CVADP val_name)"
  by (unfold DC_CVADP_def, non_mem_expI)

lemma non_mem_exp_CVADP_SysOpsWrite_9953ef108c01d34a[non_mem_expI]:
  "non_mem_exp (CVADP_SysOpsWrite_9953ef108c01d34a el op0 op1 CRn op2 CRm val_name)"
  by (unfold CVADP_SysOpsWrite_9953ef108c01d34a_def, non_mem_expI)

lemma non_mem_exp_CVAP_SysOpsWrite_a43f75867888e74a[non_mem_expI]:
  "non_mem_exp (CVAP_SysOpsWrite_a43f75867888e74a el op0 op1 CRn op2 CRm val_name)"
  by (unfold CVAP_SysOpsWrite_a43f75867888e74a_def, non_mem_expI)

lemma non_mem_exp_DC_CVAU[non_mem_expI]:
  "non_mem_exp (DC_CVAU val_name)"
  by (unfold DC_CVAU_def, non_mem_expI)

lemma non_mem_exp_DC_CVAU0[non_mem_expI]:
  "non_mem_exp (DC_CVAU0 val_name__arg)"
  by (unfold DC_CVAU0_def, non_mem_expI)

lemma non_mem_exp_CVAU_SysOpsWrite_4a72bbc98a17973c[non_mem_expI]:
  "non_mem_exp (CVAU_SysOpsWrite_4a72bbc98a17973c el op0 op1 CRn op2 CRm val_name)"
  by (unfold CVAU_SysOpsWrite_4a72bbc98a17973c_def, non_mem_expI)

lemma non_mem_exp_IC_IALLUIS[non_mem_expI]:
  "non_mem_exp (IC_IALLUIS arg0)"
  by (unfold IC_IALLUIS_def, non_mem_expI)

lemma non_mem_exp_IALLUIS_SysOpsWrite_9a906c8365100aff[non_mem_expI]:
  "non_mem_exp (IALLUIS_SysOpsWrite_9a906c8365100aff el op0 op1 CRn op2 CRm val_name)"
  by (unfold IALLUIS_SysOpsWrite_9a906c8365100aff_def, non_mem_expI)

lemma non_mem_exp_IC_IALLU[non_mem_expI]:
  "non_mem_exp (IC_IALLU arg0)"
  by (unfold IC_IALLU_def, non_mem_expI)

lemma non_mem_exp_IALLU_SysOpsWrite_81563797a4921929[non_mem_expI]:
  "non_mem_exp (IALLU_SysOpsWrite_81563797a4921929 el op0 op1 CRn op2 CRm val_name)"
  by (unfold IALLU_SysOpsWrite_81563797a4921929_def, non_mem_expI)

lemma non_mem_exp_IPAS2E1IS_SysOpsWrite_ed4be1feae90b987[non_mem_expI]:
  "non_mem_exp (IPAS2E1IS_SysOpsWrite_ed4be1feae90b987 el op0 op1 CRn op2 CRm val_name)"
  by (unfold IPAS2E1IS_SysOpsWrite_ed4be1feae90b987_def, non_mem_expI)

lemma non_mem_exp_IPAS2E1_SysOpsWrite_a65fef0d99f9428f[non_mem_expI]:
  "non_mem_exp (IPAS2E1_SysOpsWrite_a65fef0d99f9428f el op0 op1 CRn op2 CRm val_name)"
  by (unfold IPAS2E1_SysOpsWrite_a65fef0d99f9428f_def, non_mem_expI)

lemma non_mem_exp_IPAS2LE1IS_SysOpsWrite_5a72848dfefa19f3[non_mem_expI]:
  "non_mem_exp (IPAS2LE1IS_SysOpsWrite_5a72848dfefa19f3 el op0 op1 CRn op2 CRm val_name)"
  by (unfold IPAS2LE1IS_SysOpsWrite_5a72848dfefa19f3_def, non_mem_expI)

lemma non_mem_exp_IPAS2LE1_SysOpsWrite_10ca7ac6abdfed50[non_mem_expI]:
  "non_mem_exp (IPAS2LE1_SysOpsWrite_10ca7ac6abdfed50 el op0 op1 CRn op2 CRm val_name)"
  by (unfold IPAS2LE1_SysOpsWrite_10ca7ac6abdfed50_def, non_mem_expI)

lemma non_mem_exp_DC_ISW[non_mem_expI]:
  "non_mem_exp (DC_ISW val_name)"
  by (unfold DC_ISW_def, non_mem_expI)

lemma non_mem_exp_ISW_SysOpsWrite_d5fceb001aa0aa7a[non_mem_expI]:
  "non_mem_exp (ISW_SysOpsWrite_d5fceb001aa0aa7a el op0 op1 CRn op2 CRm val_name)"
  by (unfold ISW_SysOpsWrite_d5fceb001aa0aa7a_def, non_mem_expI)

lemma non_mem_exp_DC_IVAC[non_mem_expI]:
  "non_mem_exp (DC_IVAC val_name)"
  by (unfold DC_IVAC_def, non_mem_expI)

lemma non_mem_exp_DC_IVAC0[non_mem_expI]:
  "non_mem_exp (DC_IVAC0 val_name__arg)"
  by (unfold DC_IVAC0_def, non_mem_expI)

lemma non_mem_exp_IVAC_SysOpsWrite_41b93e0e56e4f107[non_mem_expI]:
  "non_mem_exp (IVAC_SysOpsWrite_41b93e0e56e4f107 el op0 op1 CRn op2 CRm val_name)"
  by (unfold IVAC_SysOpsWrite_41b93e0e56e4f107_def, non_mem_expI)

lemma non_mem_exp_IC_IVAU[non_mem_expI]:
  "non_mem_exp (IC_IVAU val_name)"
  by (unfold IC_IVAU_def, non_mem_expI)

lemma non_mem_exp_IVAU_SysOpsWrite_2dfe97b748dd324e[non_mem_expI]:
  "non_mem_exp (IVAU_SysOpsWrite_2dfe97b748dd324e el op0 op1 CRn op2 CRm val_name)"
  by (unfold IVAU_SysOpsWrite_2dfe97b748dd324e_def, non_mem_expI)

lemma non_mem_exp_RCTX_SysOpsWrite_bcc8cd10f2e68999[non_mem_expI]:
  "non_mem_exp (RCTX_SysOpsWrite_bcc8cd10f2e68999 el op0 op1 CRn op2 CRm val_name)"
  by (unfold RCTX_SysOpsWrite_bcc8cd10f2e68999_def, non_mem_expI)

lemma non_mem_exp_RCTX_SysOpsWrite_c287513d0d3e8e92[non_mem_expI]:
  "non_mem_exp (RCTX_SysOpsWrite_c287513d0d3e8e92 el op0 op1 CRn op2 CRm val_name)"
  by (unfold RCTX_SysOpsWrite_c287513d0d3e8e92_def, non_mem_expI)

lemma non_mem_exp_RCTX_SysOpsWrite_d614ec87236c038f[non_mem_expI]:
  "non_mem_exp (RCTX_SysOpsWrite_d614ec87236c038f el op0 op1 CRn op2 CRm val_name)"
  by (unfold RCTX_SysOpsWrite_d614ec87236c038f_def, non_mem_expI)

lemma non_mem_exp_AArch64_AT_S1Ex[non_mem_expI]:
  "non_mem_exp (AArch64_AT_S1Ex val_name el iswrite)"
  by (unfold AArch64_AT_S1Ex_def, non_mem_expI)

lemma non_mem_exp_AArch64_AT_S12Ex[non_mem_expI]:
  "non_mem_exp (AArch64_AT_S12Ex val_name el iswrite)"
  by (unfold AArch64_AT_S12Ex_def, non_mem_expI)

lemma non_mem_exp_AT_S12E0R[non_mem_expI]:
  "non_mem_exp (AT_S12E0R val_name)"
  by (unfold AT_S12E0R_def, non_mem_expI)

lemma non_mem_exp_AT_S1E0R[non_mem_expI]:
  "non_mem_exp (AT_S1E0R val_name)"
  by (unfold AT_S1E0R_def, non_mem_expI)

lemma non_mem_exp_S12E0R_SysOpsWrite_4df3d544cba811b7[non_mem_expI]:
  "non_mem_exp (S12E0R_SysOpsWrite_4df3d544cba811b7 el op0 op1 CRn op2 CRm val_name)"
  by (unfold S12E0R_SysOpsWrite_4df3d544cba811b7_def, non_mem_expI)

lemma non_mem_exp_AT_S12E0W[non_mem_expI]:
  "non_mem_exp (AT_S12E0W val_name)"
  by (unfold AT_S12E0W_def, non_mem_expI)

lemma non_mem_exp_AT_S1E0W[non_mem_expI]:
  "non_mem_exp (AT_S1E0W val_name)"
  by (unfold AT_S1E0W_def, non_mem_expI)

lemma non_mem_exp_S12E0W_SysOpsWrite_1dbb37d4af097406[non_mem_expI]:
  "non_mem_exp (S12E0W_SysOpsWrite_1dbb37d4af097406 el op0 op1 CRn op2 CRm val_name)"
  by (unfold S12E0W_SysOpsWrite_1dbb37d4af097406_def, non_mem_expI)

lemma non_mem_exp_AT_S12E1R[non_mem_expI]:
  "non_mem_exp (AT_S12E1R val_name)"
  by (unfold AT_S12E1R_def, non_mem_expI)

lemma non_mem_exp_AT_S1E1R[non_mem_expI]:
  "non_mem_exp (AT_S1E1R val_name)"
  by (unfold AT_S1E1R_def, non_mem_expI)

lemma non_mem_exp_S12E1R_SysOpsWrite_e44276c8f24d398f[non_mem_expI]:
  "non_mem_exp (S12E1R_SysOpsWrite_e44276c8f24d398f el op0 op1 CRn op2 CRm val_name)"
  by (unfold S12E1R_SysOpsWrite_e44276c8f24d398f_def, non_mem_expI)

lemma non_mem_exp_AT_S12E1W[non_mem_expI]:
  "non_mem_exp (AT_S12E1W val_name)"
  by (unfold AT_S12E1W_def, non_mem_expI)

lemma non_mem_exp_AT_S1E1W[non_mem_expI]:
  "non_mem_exp (AT_S1E1W val_name)"
  by (unfold AT_S1E1W_def, non_mem_expI)

lemma non_mem_exp_S12E1W_SysOpsWrite_c8b72d75cad90601[non_mem_expI]:
  "non_mem_exp (S12E1W_SysOpsWrite_c8b72d75cad90601 el op0 op1 CRn op2 CRm val_name)"
  by (unfold S12E1W_SysOpsWrite_c8b72d75cad90601_def, non_mem_expI)

lemma non_mem_exp_S1E0R_SysOpsWrite_0a1e21ea5b4c8722[non_mem_expI]:
  "non_mem_exp (S1E0R_SysOpsWrite_0a1e21ea5b4c8722 el op0 op1 CRn op2 CRm val_name)"
  by (unfold S1E0R_SysOpsWrite_0a1e21ea5b4c8722_def, non_mem_expI)

lemma non_mem_exp_S1E0W_SysOpsWrite_d102d49fd92af65a[non_mem_expI]:
  "non_mem_exp (S1E0W_SysOpsWrite_d102d49fd92af65a el op0 op1 CRn op2 CRm val_name)"
  by (unfold S1E0W_SysOpsWrite_d102d49fd92af65a_def, non_mem_expI)

lemma non_mem_exp_AT_S1E1RP[non_mem_expI]:
  "non_mem_exp (AT_S1E1RP val_name)"
  by (unfold AT_S1E1RP_def, non_mem_expI)

lemma non_mem_exp_S1E1RP_SysOpsWrite_4a6b1f71ee0182ab[non_mem_expI]:
  "non_mem_exp (S1E1RP_SysOpsWrite_4a6b1f71ee0182ab el op0 op1 CRn op2 CRm val_name)"
  by (unfold S1E1RP_SysOpsWrite_4a6b1f71ee0182ab_def, non_mem_expI)

lemma non_mem_exp_S1E1R_SysOpsWrite_018a577644c5d23c[non_mem_expI]:
  "non_mem_exp (S1E1R_SysOpsWrite_018a577644c5d23c el op0 op1 CRn op2 CRm val_name)"
  by (unfold S1E1R_SysOpsWrite_018a577644c5d23c_def, non_mem_expI)

lemma non_mem_exp_AT_S1E1WP[non_mem_expI]:
  "non_mem_exp (AT_S1E1WP val_name)"
  by (unfold AT_S1E1WP_def, non_mem_expI)

lemma non_mem_exp_S1E1WP_SysOpsWrite_bb1ddb9112effe2a[non_mem_expI]:
  "non_mem_exp (S1E1WP_SysOpsWrite_bb1ddb9112effe2a el op0 op1 CRn op2 CRm val_name)"
  by (unfold S1E1WP_SysOpsWrite_bb1ddb9112effe2a_def, non_mem_expI)

lemma non_mem_exp_S1E1W_SysOpsWrite_df64f2f63c0911fd[non_mem_expI]:
  "non_mem_exp (S1E1W_SysOpsWrite_df64f2f63c0911fd el op0 op1 CRn op2 CRm val_name)"
  by (unfold S1E1W_SysOpsWrite_df64f2f63c0911fd_def, non_mem_expI)

lemma non_mem_exp_AT_S1E2R[non_mem_expI]:
  "non_mem_exp (AT_S1E2R val_name)"
  by (unfold AT_S1E2R_def, non_mem_expI)

lemma non_mem_exp_S1E2R_SysOpsWrite_5e865a96c06417c8[non_mem_expI]:
  "non_mem_exp (S1E2R_SysOpsWrite_5e865a96c06417c8 el op0 op1 CRn op2 CRm val_name)"
  by (unfold S1E2R_SysOpsWrite_5e865a96c06417c8_def, non_mem_expI)

lemma non_mem_exp_AT_S1E2W[non_mem_expI]:
  "non_mem_exp (AT_S1E2W val_name)"
  by (unfold AT_S1E2W_def, non_mem_expI)

lemma non_mem_exp_S1E2W_SysOpsWrite_1649806418453f02[non_mem_expI]:
  "non_mem_exp (S1E2W_SysOpsWrite_1649806418453f02 el op0 op1 CRn op2 CRm val_name)"
  by (unfold S1E2W_SysOpsWrite_1649806418453f02_def, non_mem_expI)

lemma non_mem_exp_AT_S1E3R[non_mem_expI]:
  "non_mem_exp (AT_S1E3R val_name)"
  by (unfold AT_S1E3R_def, non_mem_expI)

lemma non_mem_exp_S1E3R_SysOpsWrite_6476f20e79e358be[non_mem_expI]:
  "non_mem_exp (S1E3R_SysOpsWrite_6476f20e79e358be el op0 op1 CRn op2 CRm val_name)"
  by (unfold S1E3R_SysOpsWrite_6476f20e79e358be_def, non_mem_expI)

lemma non_mem_exp_AT_S1E3W[non_mem_expI]:
  "non_mem_exp (AT_S1E3W val_name)"
  by (unfold AT_S1E3W_def, non_mem_expI)

lemma non_mem_exp_S1E3W_SysOpsWrite_e92e083e28fa4dd0[non_mem_expI]:
  "non_mem_exp (S1E3W_SysOpsWrite_e92e083e28fa4dd0 el op0 op1 CRn op2 CRm val_name)"
  by (unfold S1E3W_SysOpsWrite_e92e083e28fa4dd0_def, non_mem_expI)

lemma non_mem_exp_S1_op1_Cn_Cm_op2_SysOpsWrite_d6b17d94c0df44bc[non_mem_expI]:
  "non_mem_exp (S1_op1_Cn_Cm_op2_SysOpsWrite_d6b17d94c0df44bc el op0 op1 CRn op2 CRm val_name)"
  by (unfold S1_op1_Cn_Cm_op2_SysOpsWrite_d6b17d94c0df44bc_def, non_mem_expI)

lemma non_mem_exp_VAAE1IS_SysOpsWrite_c22cd5a1dc8e7320[non_mem_expI]:
  "non_mem_exp (VAAE1IS_SysOpsWrite_c22cd5a1dc8e7320 el op0 op1 CRn op2 CRm val_name)"
  by (unfold VAAE1IS_SysOpsWrite_c22cd5a1dc8e7320_def, non_mem_expI)

lemma non_mem_exp_VAAE1_SysOpsWrite_8498b4db5afbed38[non_mem_expI]:
  "non_mem_exp (VAAE1_SysOpsWrite_8498b4db5afbed38 el op0 op1 CRn op2 CRm val_name)"
  by (unfold VAAE1_SysOpsWrite_8498b4db5afbed38_def, non_mem_expI)

lemma non_mem_exp_VAALE1IS_SysOpsWrite_5c8056a5b649fe2e[non_mem_expI]:
  "non_mem_exp (VAALE1IS_SysOpsWrite_5c8056a5b649fe2e el op0 op1 CRn op2 CRm val_name)"
  by (unfold VAALE1IS_SysOpsWrite_5c8056a5b649fe2e_def, non_mem_expI)

lemma non_mem_exp_VAALE1_SysOpsWrite_d3bec3a19881fb1c[non_mem_expI]:
  "non_mem_exp (VAALE1_SysOpsWrite_d3bec3a19881fb1c el op0 op1 CRn op2 CRm val_name)"
  by (unfold VAALE1_SysOpsWrite_d3bec3a19881fb1c_def, non_mem_expI)

lemma non_mem_exp_VAE1IS_SysOpsWrite_5eac1ac5cb4e76ff[non_mem_expI]:
  "non_mem_exp (VAE1IS_SysOpsWrite_5eac1ac5cb4e76ff el op0 op1 CRn op2 CRm val_name)"
  by (unfold VAE1IS_SysOpsWrite_5eac1ac5cb4e76ff_def, non_mem_expI)

lemma non_mem_exp_VAE1_SysOpsWrite_09dbfc0bf1b19b11[non_mem_expI]:
  "non_mem_exp (VAE1_SysOpsWrite_09dbfc0bf1b19b11 el op0 op1 CRn op2 CRm val_name)"
  by (unfold VAE1_SysOpsWrite_09dbfc0bf1b19b11_def, non_mem_expI)

lemma non_mem_exp_TLBI_VAE2IS[non_mem_expI]:
  "non_mem_exp (TLBI_VAE2IS val_name)"
  by (unfold TLBI_VAE2IS_def, non_mem_expI)

lemma non_mem_exp_VAE2IS_SysOpsWrite_f81411101129df7b[non_mem_expI]:
  "non_mem_exp (VAE2IS_SysOpsWrite_f81411101129df7b el op0 op1 CRn op2 CRm val_name)"
  by (unfold VAE2IS_SysOpsWrite_f81411101129df7b_def, non_mem_expI)

lemma non_mem_exp_TLBI_VAE2[non_mem_expI]:
  "non_mem_exp (TLBI_VAE2 val_name)"
  by (unfold TLBI_VAE2_def, non_mem_expI)

lemma non_mem_exp_VAE2_SysOpsWrite_78002df18993a4b5[non_mem_expI]:
  "non_mem_exp (VAE2_SysOpsWrite_78002df18993a4b5 el op0 op1 CRn op2 CRm val_name)"
  by (unfold VAE2_SysOpsWrite_78002df18993a4b5_def, non_mem_expI)

lemma non_mem_exp_VAE3IS_SysOpsWrite_7dc759c51bb69ced[non_mem_expI]:
  "non_mem_exp (VAE3IS_SysOpsWrite_7dc759c51bb69ced el op0 op1 CRn op2 CRm val_name)"
  by (unfold VAE3IS_SysOpsWrite_7dc759c51bb69ced_def, non_mem_expI)

lemma non_mem_exp_VAE3_SysOpsWrite_90b5c3b60d3bd152[non_mem_expI]:
  "non_mem_exp (VAE3_SysOpsWrite_90b5c3b60d3bd152 el op0 op1 CRn op2 CRm val_name)"
  by (unfold VAE3_SysOpsWrite_90b5c3b60d3bd152_def, non_mem_expI)

lemma non_mem_exp_VALE1IS_SysOpsWrite_7bb7ad05a900b833[non_mem_expI]:
  "non_mem_exp (VALE1IS_SysOpsWrite_7bb7ad05a900b833 el op0 op1 CRn op2 CRm val_name)"
  by (unfold VALE1IS_SysOpsWrite_7bb7ad05a900b833_def, non_mem_expI)

lemma non_mem_exp_VALE1_SysOpsWrite_c1766c627b3960ca[non_mem_expI]:
  "non_mem_exp (VALE1_SysOpsWrite_c1766c627b3960ca el op0 op1 CRn op2 CRm val_name)"
  by (unfold VALE1_SysOpsWrite_c1766c627b3960ca_def, non_mem_expI)

lemma non_mem_exp_TLBI_VALE2IS[non_mem_expI]:
  "non_mem_exp (TLBI_VALE2IS val_name)"
  by (unfold TLBI_VALE2IS_def, non_mem_expI)

lemma non_mem_exp_VALE2IS_SysOpsWrite_a1084cefbce599af[non_mem_expI]:
  "non_mem_exp (VALE2IS_SysOpsWrite_a1084cefbce599af el op0 op1 CRn op2 CRm val_name)"
  by (unfold VALE2IS_SysOpsWrite_a1084cefbce599af_def, non_mem_expI)

lemma non_mem_exp_TLBI_VALE2[non_mem_expI]:
  "non_mem_exp (TLBI_VALE2 val_name)"
  by (unfold TLBI_VALE2_def, non_mem_expI)

lemma non_mem_exp_VALE2_SysOpsWrite_dce4b2b057d036da[non_mem_expI]:
  "non_mem_exp (VALE2_SysOpsWrite_dce4b2b057d036da el op0 op1 CRn op2 CRm val_name)"
  by (unfold VALE2_SysOpsWrite_dce4b2b057d036da_def, non_mem_expI)

lemma non_mem_exp_VALE3IS_SysOpsWrite_8b70cb86db2abfcd[non_mem_expI]:
  "non_mem_exp (VALE3IS_SysOpsWrite_8b70cb86db2abfcd el op0 op1 CRn op2 CRm val_name)"
  by (unfold VALE3IS_SysOpsWrite_8b70cb86db2abfcd_def, non_mem_expI)

lemma non_mem_exp_VALE3_SysOpsWrite_df1f91b1bea42ec8[non_mem_expI]:
  "non_mem_exp (VALE3_SysOpsWrite_df1f91b1bea42ec8 el op0 op1 CRn op2 CRm val_name)"
  by (unfold VALE3_SysOpsWrite_df1f91b1bea42ec8_def, non_mem_expI)

lemma non_mem_exp_VMALLE1IS_SysOpsWrite_08cfba716c4ca8db[non_mem_expI]:
  "non_mem_exp (VMALLE1IS_SysOpsWrite_08cfba716c4ca8db el op0 op1 CRn op2 CRm val_name)"
  by (unfold VMALLE1IS_SysOpsWrite_08cfba716c4ca8db_def, non_mem_expI)

lemma non_mem_exp_VMALLE1_SysOpsWrite_c64f2572b311d9b9[non_mem_expI]:
  "non_mem_exp (VMALLE1_SysOpsWrite_c64f2572b311d9b9 el op0 op1 CRn op2 CRm val_name)"
  by (unfold VMALLE1_SysOpsWrite_c64f2572b311d9b9_def, non_mem_expI)

lemma non_mem_exp_VMALLS12E1IS_SysOpsWrite_92a1ba1461a19d4c[non_mem_expI]:
  "non_mem_exp (VMALLS12E1IS_SysOpsWrite_92a1ba1461a19d4c el op0 op1 CRn op2 CRm val_name)"
  by (unfold VMALLS12E1IS_SysOpsWrite_92a1ba1461a19d4c_def, non_mem_expI)

lemma non_mem_exp_VMALLS12E1_SysOpsWrite_8f5c303094061f20[non_mem_expI]:
  "non_mem_exp (VMALLS12E1_SysOpsWrite_8f5c303094061f20 el op0 op1 CRn op2 CRm val_name)"
  by (unfold VMALLS12E1_SysOpsWrite_8f5c303094061f20_def, non_mem_expI)

lemma non_mem_exp_AArch64_SysInstrWithResult[non_mem_expI]:
  "non_mem_exp (AArch64_SysInstrWithResult op0 op1 crn crm op2)"
  by (unfold AArch64_SysInstrWithResult_def, non_mem_expI)

lemma non_mem_exp_AArch64_FPTrappedException[non_mem_expI]:
  "non_mem_exp (AArch64_FPTrappedException is_ase element accumulated_exceptions)"
  by (unfold AArch64_FPTrappedException_def, non_mem_expI)

lemma non_mem_exp_FPProcessException[non_mem_expI]:
  "non_mem_exp (FPProcessException exception fpcr)"
  by (unfold FPProcessException_def, non_mem_expI)

lemma non_mem_exp_FPRoundBase[non_mem_expI]:
  "non_mem_exp (FPRoundBase arg0 arg1 arg2 arg3 arg4)"
  by (unfold FPRoundBase_def, non_mem_expI)

lemma non_mem_exp_FPRound[non_mem_expI]:
  "non_mem_exp (FPRound N op fpcr__arg rounding)"
  by (unfold FPRound_def, non_mem_expI)

lemma non_mem_exp_FPRound__1[non_mem_expI]:
  "non_mem_exp (FPRound__1 N op fpcr)"
  by (unfold FPRound__1_def, non_mem_expI)

lemma non_mem_exp_FixedToFP[non_mem_expI]:
  "non_mem_exp (FixedToFP N op fbits is_unsigned fpcr rounding)"
  by (unfold FixedToFP_def, non_mem_expI)

lemma non_mem_exp_FPProcessNaN[non_mem_expI]:
  "non_mem_exp (FPProcessNaN fptype op fpcr)"
  by (unfold FPProcessNaN_def, non_mem_expI)

lemma non_mem_exp_FPProcessNaNs[non_mem_expI]:
  "non_mem_exp (FPProcessNaNs type1 type2 op1 op2 fpcr)"
  by (unfold FPProcessNaNs_def, non_mem_expI)

lemma non_mem_exp_FPUnpackBase[non_mem_expI]:
  "non_mem_exp (FPUnpackBase fpval fpcr)"
  by (unfold FPUnpackBase_def, non_mem_expI)

lemma non_mem_exp_FPUnpack[non_mem_expI]:
  "non_mem_exp (FPUnpack fpval fpcr__arg)"
  by (unfold FPUnpack_def, non_mem_expI)

lemma non_mem_exp_FPAdd[non_mem_expI]:
  "non_mem_exp (FPAdd op1 op2 fpcr)"
  by (unfold FPAdd_def, non_mem_expI)

lemma non_mem_exp_FPCompare[non_mem_expI]:
  "non_mem_exp (FPCompare op1 op2 signal_nans fpcr)"
  by (unfold FPCompare_def, non_mem_expI)

lemma non_mem_exp_FPCompareEQ[non_mem_expI]:
  "non_mem_exp (FPCompareEQ op1 op2 fpcr)"
  by (unfold FPCompareEQ_def, non_mem_expI)

lemma non_mem_exp_FPCompareGE[non_mem_expI]:
  "non_mem_exp (FPCompareGE op1 op2 fpcr)"
  by (unfold FPCompareGE_def, non_mem_expI)

lemma non_mem_exp_FPCompareGT[non_mem_expI]:
  "non_mem_exp (FPCompareGT op1 op2 fpcr)"
  by (unfold FPCompareGT_def, non_mem_expI)

lemma non_mem_exp_FPRoundCV[non_mem_expI]:
  "non_mem_exp (FPRoundCV N op fpcr__arg rounding)"
  by (unfold FPRoundCV_def, non_mem_expI)

lemma non_mem_exp_FPUnpackCV[non_mem_expI]:
  "non_mem_exp (FPUnpackCV fpval fpcr__arg)"
  by (unfold FPUnpackCV_def, non_mem_expI)

lemma non_mem_exp_FPConvert[non_mem_expI]:
  "non_mem_exp (FPConvert l__604 op fpcr rounding)"
  by (unfold FPConvert_def, non_mem_expI)

lemma non_mem_exp_FPConvert__1[non_mem_expI]:
  "non_mem_exp (FPConvert__1 M op fpcr)"
  by (unfold FPConvert__1_def, non_mem_expI)

lemma non_mem_exp_FPDiv[non_mem_expI]:
  "non_mem_exp (FPDiv op1 op2 fpcr)"
  by (unfold FPDiv_def, non_mem_expI)

lemma non_mem_exp_FPMax[non_mem_expI]:
  "non_mem_exp (FPMax op1 op2 fpcr)"
  by (unfold FPMax_def, non_mem_expI)

lemma non_mem_exp_FPMaxNum[non_mem_expI]:
  "non_mem_exp (FPMaxNum op1__arg op2__arg fpcr)"
  by (unfold FPMaxNum_def, non_mem_expI)

lemma non_mem_exp_FPMin[non_mem_expI]:
  "non_mem_exp (FPMin op1 op2 fpcr)"
  by (unfold FPMin_def, non_mem_expI)

lemma non_mem_exp_FPMinNum[non_mem_expI]:
  "non_mem_exp (FPMinNum op1__arg op2__arg fpcr)"
  by (unfold FPMinNum_def, non_mem_expI)

lemma non_mem_exp_FPMul[non_mem_expI]:
  "non_mem_exp (FPMul op1 op2 fpcr)"
  by (unfold FPMul_def, non_mem_expI)

lemma non_mem_exp_FPProcessNaNs3[non_mem_expI]:
  "non_mem_exp (FPProcessNaNs3 type1 type2 type3 op1 op2 op3 fpcr)"
  by (unfold FPProcessNaNs3_def, non_mem_expI)

lemma non_mem_exp_FPMulAdd[non_mem_expI]:
  "non_mem_exp (FPMulAdd addend op1 op2 fpcr)"
  by (unfold FPMulAdd_def, non_mem_expI)

lemma non_mem_exp_FPMulX[non_mem_expI]:
  "non_mem_exp (FPMulX op1 op2 fpcr)"
  by (unfold FPMulX_def, non_mem_expI)

lemma non_mem_exp_FPRecipEstimate[non_mem_expI]:
  "non_mem_exp (FPRecipEstimate operand fpcr)"
  by (unfold FPRecipEstimate_def, non_mem_expI)

lemma non_mem_exp_FPRecpX[non_mem_expI]:
  "non_mem_exp (FPRecpX l__583 op fpcr)"
  by (unfold FPRecpX_def, non_mem_expI)

lemma non_mem_exp_FPRoundInt[non_mem_expI]:
  "non_mem_exp (FPRoundInt op fpcr rounding exact)"
  by (unfold FPRoundInt_def, non_mem_expI)

lemma non_mem_exp_FPRSqrtEstimate[non_mem_expI]:
  "non_mem_exp (FPRSqrtEstimate operand fpcr)"
  by (unfold FPRSqrtEstimate_def, non_mem_expI)

lemma non_mem_exp_FPSqrt[non_mem_expI]:
  "non_mem_exp (FPSqrt op fpcr)"
  by (unfold FPSqrt_def, non_mem_expI)

lemma non_mem_exp_FPSub[non_mem_expI]:
  "non_mem_exp (FPSub op1 op2 fpcr)"
  by (unfold FPSub_def, non_mem_expI)

lemma non_mem_exp_FPToFixed[non_mem_expI]:
  "non_mem_exp (FPToFixed M op fbits is_unsigned fpcr rounding)"
  by (unfold FPToFixed_def, non_mem_expI)

lemma non_mem_exp_BranchXToCapability[non_mem_expI]:
  "non_mem_exp (BranchXToCapability target__arg branch_type)"
  by (unfold BranchXToCapability_def, non_mem_expI)

lemma non_mem_exp_BranchToOffset[non_mem_expI]:
  "non_mem_exp (BranchToOffset offset branch_type)"
  by (unfold BranchToOffset_def, non_mem_expI)

lemma non_mem_exp_X_set[non_mem_expI]:
  "non_mem_exp (X_set width n value_name)"
  by (unfold X_set_def, non_mem_expI)

lemma non_mem_exp_X_read[non_mem_expI]:
  "non_mem_exp (X_read width n)"
  by (unfold X_read_def, non_mem_expI)

lemma non_mem_exp_C_read[non_mem_expI]:
  "non_mem_exp (C_read n)"
  by (unfold C_read_def, non_mem_expI)

lemma non_mem_exp_SP_set[non_mem_expI]:
  "non_mem_exp (SP_set width value_name)"
  by (unfold SP_set_def, non_mem_expI)

lemma non_mem_exp_SP_read[non_mem_expI]:
  "non_mem_exp (SP_read width)"
  by (unfold SP_read_def, non_mem_expI)

lemma non_mem_exp_CSP_set[non_mem_expI]:
  "non_mem_exp (CSP_set value_name)"
  by (unfold CSP_set_def, non_mem_expI)

lemma non_mem_exp_CSP_read[non_mem_expI]:
  "non_mem_exp (CSP_read arg0)"
  by (unfold CSP_read_def, non_mem_expI)

lemma non_mem_exp_PC_read[non_mem_expI]:
  "non_mem_exp (PC_read arg0)"
  by (unfold PC_read_def, non_mem_expI)

lemma non_mem_exp_AArch64_SPAlignmentFault[non_mem_expI]:
  "non_mem_exp (AArch64_SPAlignmentFault arg0)"
  by (unfold AArch64_SPAlignmentFault_def, non_mem_expI)

lemma non_mem_exp_CheckSPAlignment[non_mem_expI]:
  "non_mem_exp (CheckSPAlignment arg0)"
  by (unfold CheckSPAlignment_def, non_mem_expI)

lemma non_mem_exp_BaseReg_read[non_mem_expI]:
  "non_mem_exp (BaseReg_read n is_prefetch)"
  by (unfold BaseReg_read_def, non_mem_expI)

lemma non_mem_exp_BaseReg_read__1[non_mem_expI]:
  "non_mem_exp (BaseReg_read__1 n)"
  by (unfold BaseReg_read__1_def, non_mem_expI)

lemma non_mem_exp_AltBaseReg_read[non_mem_expI]:
  "non_mem_exp (AltBaseReg_read n is_prefetch)"
  by (unfold AltBaseReg_read_def, non_mem_expI)

lemma non_mem_exp_AltBaseReg_read__1[non_mem_expI]:
  "non_mem_exp (AltBaseReg_read__1 n)"
  by (unfold AltBaseReg_read__1_def, non_mem_expI)

lemma non_mem_exp_BaseReg_set[non_mem_expI]:
  "non_mem_exp (BaseReg_set n address)"
  by (unfold BaseReg_set_def, non_mem_expI)

lemma non_mem_exp_ELR_read[non_mem_expI]:
  "non_mem_exp (ELR_read el)"
  by (unfold ELR_read_def, non_mem_expI)

lemma non_mem_exp_ELR_read__1[non_mem_expI]:
  "non_mem_exp (ELR_read__1 arg0)"
  by (unfold ELR_read__1_def, non_mem_expI)

lemma non_mem_exp_CELR_read[non_mem_expI]:
  "non_mem_exp (CELR_read el)"
  by (unfold CELR_read_def, non_mem_expI)

lemma non_mem_exp_CELR_read__1[non_mem_expI]:
  "non_mem_exp (CELR_read__1 arg0)"
  by (unfold CELR_read__1_def, non_mem_expI)

lemma non_mem_exp_AArch64_CheckSystemAccess[non_mem_expI]:
  "non_mem_exp (AArch64_CheckSystemAccess op0 op1 crn crm op2 rt read)"
  by (unfold AArch64_CheckSystemAccess_def, non_mem_expI)

lemma non_mem_exp_AArch64_CheckAlignment[non_mem_expI]:
  "non_mem_exp (AArch64_CheckAlignment address alignment acctype iswrite)"
  by (unfold AArch64_CheckAlignment_def, non_mem_expI)

lemma non_mem_exp_CheckLoadTagsPermission[non_mem_expI]:
  "non_mem_exp (CheckLoadTagsPermission desc acctype)"
  by (unfold CheckLoadTagsPermission_def, non_mem_expI)

lemma non_mem_exp_CheckStoreTagsPermission[non_mem_expI]:
  "non_mem_exp (CheckStoreTagsPermission desc acctype)"
  by (unfold CheckStoreTagsPermission_def, non_mem_expI)

lemma non_mem_exp_CheckCapabilityAlignment[non_mem_expI]:
  "non_mem_exp (CheckCapabilityAlignment address acctype iswrite)"
  by (unfold CheckCapabilityAlignment_def, non_mem_expI)

lemma non_mem_exp_CheckCapabilityStorePairAlignment[non_mem_expI]:
  "non_mem_exp (CheckCapabilityStorePairAlignment address acctype iswrite)"
  by (unfold CheckCapabilityStorePairAlignment_def, non_mem_expI)

lemma non_mem_exp_AArch64_TranslateAddressForAtomicAccess[non_mem_expI]:
  "non_mem_exp (AArch64_TranslateAddressForAtomicAccess address sizeinbits)"
  by (unfold AArch64_TranslateAddressForAtomicAccess_def, non_mem_expI)

lemma non_mem_exp_CheckCapability[non_mem_expI]:
  "non_mem_exp (CheckCapability c__arg address size__arg requested_perms acctype)"
  by (unfold CheckCapability_def, non_mem_expI)

lemma non_mem_exp_VACheckAddress[non_mem_expI]:
  "non_mem_exp (VACheckAddress base addr64 size__arg requested_perms acctype)"
  by (unfold VACheckAddress_def, non_mem_expI)

lemma non_mem_exp_CapSquashPostLoadCap[non_mem_expI]:
  "non_mem_exp (CapSquashPostLoadCap data__arg addr)"
  by (unfold CapSquashPostLoadCap_def, non_mem_expI)

lemma non_mem_exp_AArch64_SetExclusiveMonitors[non_mem_expI]:
  "non_mem_exp (AArch64_SetExclusiveMonitors address size__arg)"
  by (unfold AArch64_SetExclusiveMonitors_def, non_mem_expI)

lemma non_mem_exp_AArch64_ExclusiveMonitorsPass[non_mem_expI]:
  "non_mem_exp (AArch64_ExclusiveMonitorsPass address size__arg)"
  by (unfold AArch64_ExclusiveMonitorsPass_def, non_mem_expI)

lemma non_mem_exp_FPRecipStepFused[non_mem_expI]:
  "non_mem_exp (FPRecipStepFused op1__arg op2)"
  by (unfold FPRecipStepFused_def, non_mem_expI)

lemma non_mem_exp_FPRSqrtStepFused[non_mem_expI]:
  "non_mem_exp (FPRSqrtStepFused op1__arg op2)"
  by (unfold FPRSqrtStepFused_def, non_mem_expI)

lemma non_mem_exp_AArch64_CallSecureMonitor[non_mem_expI]:
  "non_mem_exp (AArch64_CallSecureMonitor immediate)"
  by (unfold AArch64_CallSecureMonitor_def, non_mem_expI)

lemma non_mem_exp_AArch64_CallHypervisor[non_mem_expI]:
  "non_mem_exp (AArch64_CallHypervisor immediate)"
  by (unfold AArch64_CallHypervisor_def, non_mem_expI)

lemma non_mem_exp_AArch64_CallSupervisor[non_mem_expI]:
  "non_mem_exp (AArch64_CallSupervisor immediate)"
  by (unfold AArch64_CallSupervisor_def, non_mem_expI)

lemma non_mem_exp_AArch64_CheckIllegalState[non_mem_expI]:
  "non_mem_exp (AArch64_CheckIllegalState arg0)"
  by (unfold AArch64_CheckIllegalState_def, non_mem_expI)

lemma non_mem_exp_AArch64_CheckForSMCUndefOrTrap[non_mem_expI]:
  "non_mem_exp (AArch64_CheckForSMCUndefOrTrap imm)"
  by (unfold AArch64_CheckForSMCUndefOrTrap_def, non_mem_expI)

lemma non_mem_exp_AArch64_WFxTrap[non_mem_expI]:
  "non_mem_exp (AArch64_WFxTrap target_el is_wfe)"
  by (unfold AArch64_WFxTrap_def, non_mem_expI)

lemma non_mem_exp_AArch64_CheckForWFxTrap[non_mem_expI]:
  "non_mem_exp (AArch64_CheckForWFxTrap target_el is_wfe)"
  by (unfold AArch64_CheckForWFxTrap_def, non_mem_expI)

lemma non_mem_exp_AArch64_AdvSIMDFPAccessTrap[non_mem_expI]:
  "non_mem_exp (AArch64_AdvSIMDFPAccessTrap target_el)"
  by (unfold AArch64_AdvSIMDFPAccessTrap_def, non_mem_expI)

lemma non_mem_exp_AArch64_CheckFPAdvSIMDTrap[non_mem_expI]:
  "non_mem_exp (AArch64_CheckFPAdvSIMDTrap arg0)"
  by (unfold AArch64_CheckFPAdvSIMDTrap_def, non_mem_expI)

lemma non_mem_exp_AArch64_CheckFPAdvSIMDEnabled[non_mem_expI]:
  "non_mem_exp (AArch64_CheckFPAdvSIMDEnabled arg0)"
  by (unfold AArch64_CheckFPAdvSIMDEnabled_def, non_mem_expI)

lemma non_mem_exp_CheckFPAdvSIMDEnabled64[non_mem_expI]:
  "non_mem_exp (CheckFPAdvSIMDEnabled64 arg0)"
  by (unfold CheckFPAdvSIMDEnabled64_def, non_mem_expI)

lemma non_mem_exp_CapabilityAccessTrap[non_mem_expI]:
  "non_mem_exp (CapabilityAccessTrap target_el)"
  by (unfold CapabilityAccessTrap_def, non_mem_expI)

lemma non_mem_exp_CheckCapabilitiesEnabled[non_mem_expI]:
  "non_mem_exp (CheckCapabilitiesEnabled arg0)"
  by (unfold CheckCapabilitiesEnabled_def, non_mem_expI)

lemma non_mem_exp_AArch64_TakePhysicalIRQException[non_mem_expI]:
  "non_mem_exp (AArch64_TakePhysicalIRQException arg0)"
  by (unfold AArch64_TakePhysicalIRQException_def, non_mem_expI)

lemma non_mem_exp_AArch64_SoftwareBreakpoint[non_mem_expI]:
  "non_mem_exp (AArch64_SoftwareBreakpoint immediate)"
  by (unfold AArch64_SoftwareBreakpoint_def, non_mem_expI)

lemma non_mem_exp_AArch64_PCAlignmentFault[non_mem_expI]:
  "non_mem_exp (AArch64_PCAlignmentFault arg0)"
  by (unfold AArch64_PCAlignmentFault_def, non_mem_expI)

lemma non_mem_exp_AArch64_CheckPCAlignment[non_mem_expI]:
  "non_mem_exp (AArch64_CheckPCAlignment arg0)"
  by (unfold AArch64_CheckPCAlignment_def, non_mem_expI)

lemma non_mem_exp_CheckPCCCapability[non_mem_expI]:
  "non_mem_exp (CheckPCCCapability arg0)"
  by (unfold CheckPCCCapability_def, non_mem_expI)

lemma non_mem_exp_AArch64_ExceptionReturnToCapability[non_mem_expI]:
  "non_mem_exp (AArch64_ExceptionReturnToCapability new_pcc__arg spsr)"
  by (unfold AArch64_ExceptionReturnToCapability_def, non_mem_expI)

lemma non_mem_exp_ExtendReg[non_mem_expI]:
  "non_mem_exp (ExtendReg N reg exttype shift)"
  by (unfold ExtendReg_def, non_mem_expI)

lemma non_mem_exp_ShiftReg[non_mem_expI]:
  "non_mem_exp (ShiftReg N reg shiftype amount)"
  by (unfold ShiftReg_def, non_mem_expI)

lemma non_mem_exp_ReduceCombine[non_mem_expI]:
  "non_mem_exp (ReduceCombine op lo hi)"
  by (unfold ReduceCombine_def, non_mem_expI)

lemma non_mem_exp_Reduce16[non_mem_expI]:
  "non_mem_exp (Reduce16 op input esize)"
  by (unfold Reduce16_def, non_mem_expI)

lemma non_mem_exp_Reduce32[non_mem_expI]:
  "non_mem_exp (Reduce32 op input esize)"
  by (unfold Reduce32_def, non_mem_expI)

lemma non_mem_exp_Reduce64[non_mem_expI]:
  "non_mem_exp (Reduce64 op input esize)"
  by (unfold Reduce64_def, non_mem_expI)

lemma non_mem_exp_Reduce128[non_mem_expI]:
  "non_mem_exp (Reduce128 op input esize)"
  by (unfold Reduce128_def, non_mem_expI)

lemma non_mem_exp_Reduce256[non_mem_expI]:
  "non_mem_exp (Reduce256 op input esize)"
  by (unfold Reduce256_def, non_mem_expI)

lemma non_mem_exp_Reduce512[non_mem_expI]:
  "non_mem_exp (Reduce512 op input esize)"
  by (unfold Reduce512_def, non_mem_expI)

lemma non_mem_exp_Reduce1024[non_mem_expI]:
  "non_mem_exp (Reduce1024 op input esize)"
  by (unfold Reduce1024_def, non_mem_expI)

lemma non_mem_exp_Reduce2048[non_mem_expI]:
  "non_mem_exp (Reduce2048 op input esize)"
  by (unfold Reduce2048_def, non_mem_expI)

lemma non_mem_exp_Reduce[non_mem_expI]:
  "non_mem_exp (Reduce op input esize)"
  by (unfold Reduce_def, non_mem_expI)

lemma non_mem_exp_DCPSInstruction[non_mem_expI]:
  "non_mem_exp (DCPSInstruction target_el)"
  by (unfold DCPSInstruction_def, non_mem_expI)

lemma non_mem_exp_DRPSInstruction[non_mem_expI]:
  "non_mem_exp (DRPSInstruction arg0)"
  by (unfold DRPSInstruction_def, non_mem_expI)

lemma non_mem_exp_VACheckPerm[non_mem_expI]:
  "non_mem_exp (VACheckPerm base requested_perms)"
  by (unfold VACheckPerm_def, non_mem_expI)

lemma non_mem_exp_CAP_DC_CIVAC[non_mem_expI]:
  "non_mem_exp (CAP_DC_CIVAC cval)"
  by (unfold CAP_DC_CIVAC_def, non_mem_expI)

lemma non_mem_exp_CAP_DC_CVAC[non_mem_expI]:
  "non_mem_exp (CAP_DC_CVAC cval)"
  by (unfold CAP_DC_CVAC_def, non_mem_expI)

lemma non_mem_exp_CAP_DC_CVADP[non_mem_expI]:
  "non_mem_exp (CAP_DC_CVADP cval)"
  by (unfold CAP_DC_CVADP_def, non_mem_expI)

lemma non_mem_exp_CAP_DC_CVAP[non_mem_expI]:
  "non_mem_exp (CAP_DC_CVAP cval)"
  by (unfold CAP_DC_CVAP_def, non_mem_expI)

lemma non_mem_exp_CAP_DC_CVAU[non_mem_expI]:
  "non_mem_exp (CAP_DC_CVAU cval)"
  by (unfold CAP_DC_CVAU_def, non_mem_expI)

lemma non_mem_exp_CAP_DC_IVAC[non_mem_expI]:
  "non_mem_exp (CAP_DC_IVAC cval)"
  by (unfold CAP_DC_IVAC_def, non_mem_expI)

lemma non_mem_exp_CAP_IC_IVAU[non_mem_expI]:
  "non_mem_exp (CAP_IC_IVAU cval)"
  by (unfold CAP_IC_IVAU_def, non_mem_expI)

lemma non_mem_exp_Step_PC[non_mem_expI]:
  "non_mem_exp (Step_PC arg0)"
  by (unfold Step_PC_def, non_mem_expI)

lemma non_mem_exp_execute_ADD_C_CIS_C[non_mem_expI]:
  "non_mem_exp (execute_ADD_C_CIS_C d imm n)"
  by (unfold execute_ADD_C_CIS_C_def, non_mem_expI)

lemma non_mem_exp_decode_ADD_C_CIS_C[non_mem_expI]:
  "non_mem_exp (decode_ADD_C_CIS_C A sh imm12 Cn Cd)"
  by (unfold decode_ADD_C_CIS_C_def, non_mem_expI)

lemma non_mem_exp_execute_ADD_C_CRI_C[non_mem_expI]:
  "non_mem_exp (execute_ADD_C_CRI_C d extend_type m n shift)"
  by (unfold execute_ADD_C_CRI_C_def, non_mem_expI)

lemma non_mem_exp_decode_ADD_C_CRI_C[non_mem_expI]:
  "non_mem_exp (decode_ADD_C_CRI_C Rm option_name imm3 Cn Cd)"
  by (unfold decode_ADD_C_CRI_C_def, non_mem_expI)

lemma non_mem_exp_execute_ADRDP_C_ID_C[non_mem_expI]:
  "non_mem_exp (execute_ADRDP_C_ID_C P d imm)"
  by (unfold execute_ADRDP_C_ID_C_def, non_mem_expI)

lemma non_mem_exp_decode_ADRDP_C_ID_C[non_mem_expI]:
  "non_mem_exp (decode_ADRDP_C_ID_C op immlo P immhi Rd)"
  by (unfold decode_ADRDP_C_ID_C_def, non_mem_expI)

lemma non_mem_exp_execute_ADRP_C_IP_C[non_mem_expI]:
  "non_mem_exp (execute_ADRP_C_IP_C P d imm)"
  by (unfold execute_ADRP_C_IP_C_def, non_mem_expI)

lemma non_mem_exp_decode_ADRP_C_IP_C[non_mem_expI]:
  "non_mem_exp (decode_ADRP_C_IP_C op immlo P immhi Rd)"
  by (unfold decode_ADRP_C_IP_C_def, non_mem_expI)

lemma non_mem_exp_execute_ADRP_C_I_C[non_mem_expI]:
  "non_mem_exp (execute_ADRP_C_I_C P d imm)"
  by (unfold execute_ADRP_C_I_C_def, non_mem_expI)

lemma non_mem_exp_decode_ADRP_C_I_C[non_mem_expI]:
  "non_mem_exp (decode_ADRP_C_I_C op immlo P immhi Rd)"
  by (unfold decode_ADRP_C_I_C_def, non_mem_expI)

lemma non_mem_exp_execute_ADR_C_I_C[non_mem_expI]:
  "non_mem_exp (execute_ADR_C_I_C d imm)"
  by (unfold execute_ADR_C_I_C_def, non_mem_expI)

lemma non_mem_exp_decode_ADR_C_I_C[non_mem_expI]:
  "non_mem_exp (decode_ADR_C_I_C op immlo P immhi Rd)"
  by (unfold decode_ADR_C_I_C_def, non_mem_expI)

lemma non_mem_exp_execute_ALIGND_C_CI_C[non_mem_expI]:
  "non_mem_exp (execute_ALIGND_C_CI_C align d n)"
  by (unfold execute_ALIGND_C_CI_C_def, non_mem_expI)

lemma non_mem_exp_decode_ALIGND_C_CI_C[non_mem_expI]:
  "non_mem_exp (decode_ALIGND_C_CI_C imm6 U Cn Cd)"
  by (unfold decode_ALIGND_C_CI_C_def, non_mem_expI)

lemma non_mem_exp_execute_ALIGNU_C_CI_C[non_mem_expI]:
  "non_mem_exp (execute_ALIGNU_C_CI_C align d n)"
  by (unfold execute_ALIGNU_C_CI_C_def, non_mem_expI)

lemma non_mem_exp_decode_ALIGNU_C_CI_C[non_mem_expI]:
  "non_mem_exp (decode_ALIGNU_C_CI_C imm6 U Cn Cd)"
  by (unfold decode_ALIGNU_C_CI_C_def, non_mem_expI)

lemma non_mem_exp_execute_BICFLGS_C_CI_C[non_mem_expI]:
  "non_mem_exp (execute_BICFLGS_C_CI_C d mask__arg n)"
  by (unfold execute_BICFLGS_C_CI_C_def, non_mem_expI)

lemma non_mem_exp_decode_BICFLGS_C_CI_C[non_mem_expI]:
  "non_mem_exp (decode_BICFLGS_C_CI_C imm8 Cn Cd)"
  by (unfold decode_BICFLGS_C_CI_C_def, non_mem_expI)

lemma non_mem_exp_execute_BICFLGS_C_CR_C[non_mem_expI]:
  "non_mem_exp (execute_BICFLGS_C_CR_C d m n)"
  by (unfold execute_BICFLGS_C_CR_C_def, non_mem_expI)

lemma non_mem_exp_decode_BICFLGS_C_CR_C[non_mem_expI]:
  "non_mem_exp (decode_BICFLGS_C_CR_C Rm opc Cn Cd)"
  by (unfold decode_BICFLGS_C_CR_C_def, non_mem_expI)

lemma non_mem_exp_execute_BLRR_C_C[non_mem_expI]:
  "non_mem_exp (execute_BLRR_C_C branch_type n)"
  by (unfold execute_BLRR_C_C_def, non_mem_expI)

lemma non_mem_exp_decode_BLRR_C_C[non_mem_expI]:
  "non_mem_exp (decode_BLRR_C_C opc Cn)"
  by (unfold decode_BLRR_C_C_def, non_mem_expI)

lemma non_mem_exp_execute_BLRS_C_C[non_mem_expI]:
  "non_mem_exp (execute_BLRS_C_C branch_type n)"
  by (unfold execute_BLRS_C_C_def, non_mem_expI)

lemma non_mem_exp_decode_BLRS_C_C[non_mem_expI]:
  "non_mem_exp (decode_BLRS_C_C opc Cn)"
  by (unfold decode_BLRS_C_C_def, non_mem_expI)

lemma non_mem_exp_execute_BLRS_C_C_C[non_mem_expI]:
  "non_mem_exp (execute_BLRS_C_C_C branch_type m n)"
  by (unfold execute_BLRS_C_C_C_def, non_mem_expI)

lemma non_mem_exp_decode_BLRS_C_C_C[non_mem_expI]:
  "non_mem_exp (decode_BLRS_C_C_C Cm opc Cn)"
  by (unfold decode_BLRS_C_C_C_def, non_mem_expI)

lemma non_mem_exp_execute_BLR_C_C[non_mem_expI]:
  "non_mem_exp (execute_BLR_C_C branch_type n)"
  by (unfold execute_BLR_C_C_def, non_mem_expI)

lemma non_mem_exp_decode_BLR_C_C[non_mem_expI]:
  "non_mem_exp (decode_BLR_C_C opc Cn)"
  by (unfold decode_BLR_C_C_def, non_mem_expI)

lemma non_mem_exp_execute_BRR_C_C[non_mem_expI]:
  "non_mem_exp (execute_BRR_C_C branch_type n)"
  by (unfold execute_BRR_C_C_def, non_mem_expI)

lemma non_mem_exp_decode_BRR_C_C[non_mem_expI]:
  "non_mem_exp (decode_BRR_C_C opc Cn)"
  by (unfold decode_BRR_C_C_def, non_mem_expI)

lemma non_mem_exp_execute_BRS_C_C[non_mem_expI]:
  "non_mem_exp (execute_BRS_C_C branch_type n)"
  by (unfold execute_BRS_C_C_def, non_mem_expI)

lemma non_mem_exp_decode_BRS_C_C[non_mem_expI]:
  "non_mem_exp (decode_BRS_C_C opc Cn)"
  by (unfold decode_BRS_C_C_def, non_mem_expI)

lemma non_mem_exp_execute_BRS_C_C_C[non_mem_expI]:
  "non_mem_exp (execute_BRS_C_C_C branch_type m n)"
  by (unfold execute_BRS_C_C_C_def, non_mem_expI)

lemma non_mem_exp_decode_BRS_C_C_C[non_mem_expI]:
  "non_mem_exp (decode_BRS_C_C_C Cm opc Cn)"
  by (unfold decode_BRS_C_C_C_def, non_mem_expI)

lemma non_mem_exp_execute_BR_C_C[non_mem_expI]:
  "non_mem_exp (execute_BR_C_C branch_type n)"
  by (unfold execute_BR_C_C_def, non_mem_expI)

lemma non_mem_exp_decode_BR_C_C[non_mem_expI]:
  "non_mem_exp (decode_BR_C_C opc Cn)"
  by (unfold decode_BR_C_C_def, non_mem_expI)

lemma non_mem_exp_execute_BUILD_C_C_C[non_mem_expI]:
  "non_mem_exp (execute_BUILD_C_C_C d m n)"
  by (unfold execute_BUILD_C_C_C_def, non_mem_expI)

lemma non_mem_exp_decode_BUILD_C_C_C[non_mem_expI]:
  "non_mem_exp (decode_BUILD_C_C_C Cm opc Cn Cd)"
  by (unfold decode_BUILD_C_C_C_def, non_mem_expI)

lemma non_mem_exp_execute_BX___C[non_mem_expI]:
  "non_mem_exp (execute_BX___C branch_type)"
  by (unfold execute_BX___C_def, non_mem_expI)

lemma non_mem_exp_decode_BX___C[non_mem_expI]:
  "non_mem_exp (decode_BX___C opc)"
  by (unfold decode_BX___C_def, non_mem_expI)

lemma non_mem_exp_execute_CFHI_R_C_C[non_mem_expI]:
  "non_mem_exp (execute_CFHI_R_C_C d n)"
  by (unfold execute_CFHI_R_C_C_def, non_mem_expI)

lemma non_mem_exp_decode_CFHI_R_C_C[non_mem_expI]:
  "non_mem_exp (decode_CFHI_R_C_C opc Cn Rd)"
  by (unfold decode_CFHI_R_C_C_def, non_mem_expI)

lemma non_mem_exp_execute_CHKEQ___CC_C[non_mem_expI]:
  "non_mem_exp (execute_CHKEQ___CC_C m n)"
  by (unfold execute_CHKEQ___CC_C_def, non_mem_expI)

lemma non_mem_exp_decode_CHKEQ___CC_C[non_mem_expI]:
  "non_mem_exp (decode_CHKEQ___CC_C Cm opc Cn)"
  by (unfold decode_CHKEQ___CC_C_def, non_mem_expI)

lemma non_mem_exp_execute_CHKSLD_C_C[non_mem_expI]:
  "non_mem_exp (execute_CHKSLD_C_C n)"
  by (unfold execute_CHKSLD_C_C_def, non_mem_expI)

lemma non_mem_exp_decode_CHKSLD_C_C[non_mem_expI]:
  "non_mem_exp (decode_CHKSLD_C_C opc Cn)"
  by (unfold decode_CHKSLD_C_C_def, non_mem_expI)

lemma non_mem_exp_execute_CHKSSU_C_CC_C[non_mem_expI]:
  "non_mem_exp (execute_CHKSSU_C_CC_C d m n)"
  by (unfold execute_CHKSSU_C_CC_C_def, non_mem_expI)

lemma non_mem_exp_decode_CHKSSU_C_CC_C[non_mem_expI]:
  "non_mem_exp (decode_CHKSSU_C_CC_C Cm opc Cn Cd)"
  by (unfold decode_CHKSSU_C_CC_C_def, non_mem_expI)

lemma non_mem_exp_execute_CHKSS___CC_C[non_mem_expI]:
  "non_mem_exp (execute_CHKSS___CC_C m n)"
  by (unfold execute_CHKSS___CC_C_def, non_mem_expI)

lemma non_mem_exp_decode_CHKSS___CC_C[non_mem_expI]:
  "non_mem_exp (decode_CHKSS___CC_C Cm opc Cn)"
  by (unfold decode_CHKSS___CC_C_def, non_mem_expI)

lemma non_mem_exp_execute_CHKTGD_C_C[non_mem_expI]:
  "non_mem_exp (execute_CHKTGD_C_C n)"
  by (unfold execute_CHKTGD_C_C_def, non_mem_expI)

lemma non_mem_exp_decode_CHKTGD_C_C[non_mem_expI]:
  "non_mem_exp (decode_CHKTGD_C_C opc Cn)"
  by (unfold decode_CHKTGD_C_C_def, non_mem_expI)

lemma non_mem_exp_execute_CLRPERM_C_CI_C[non_mem_expI]:
  "non_mem_exp (execute_CLRPERM_C_CI_C d imm n)"
  by (unfold execute_CLRPERM_C_CI_C_def, non_mem_expI)

lemma non_mem_exp_decode_CLRPERM_C_CI_C[non_mem_expI]:
  "non_mem_exp (decode_CLRPERM_C_CI_C perm__arg Cn Cd)"
  by (unfold decode_CLRPERM_C_CI_C_def, non_mem_expI)

lemma non_mem_exp_execute_CLRPERM_C_CR_C[non_mem_expI]:
  "non_mem_exp (execute_CLRPERM_C_CR_C d m n)"
  by (unfold execute_CLRPERM_C_CR_C_def, non_mem_expI)

lemma non_mem_exp_decode_CLRPERM_C_CR_C[non_mem_expI]:
  "non_mem_exp (decode_CLRPERM_C_CR_C Rm Cn Cd)"
  by (unfold decode_CLRPERM_C_CR_C_def, non_mem_expI)

lemma non_mem_exp_execute_CLRTAG_C_C_C[non_mem_expI]:
  "non_mem_exp (execute_CLRTAG_C_C_C d n)"
  by (unfold execute_CLRTAG_C_C_C_def, non_mem_expI)

lemma non_mem_exp_decode_CLRTAG_C_C_C[non_mem_expI]:
  "non_mem_exp (decode_CLRTAG_C_C_C opc Cn Cd)"
  by (unfold decode_CLRTAG_C_C_C_def, non_mem_expI)

lemma non_mem_exp_execute_CPYTYPE_C_C_C[non_mem_expI]:
  "non_mem_exp (execute_CPYTYPE_C_C_C d m n)"
  by (unfold execute_CPYTYPE_C_C_C_def, non_mem_expI)

lemma non_mem_exp_decode_CPYTYPE_C_C_C[non_mem_expI]:
  "non_mem_exp (decode_CPYTYPE_C_C_C Cm opc Cn Cd)"
  by (unfold decode_CPYTYPE_C_C_C_def, non_mem_expI)

lemma non_mem_exp_execute_CPYVALUE_C_C_C[non_mem_expI]:
  "non_mem_exp (execute_CPYVALUE_C_C_C d m n)"
  by (unfold execute_CPYVALUE_C_C_C_def, non_mem_expI)

lemma non_mem_exp_decode_CPYVALUE_C_C_C[non_mem_expI]:
  "non_mem_exp (decode_CPYVALUE_C_C_C Cm opc Cn Cd)"
  by (unfold decode_CPYVALUE_C_C_C_def, non_mem_expI)

lemma non_mem_exp_execute_CPY_C_C_C[non_mem_expI]:
  "non_mem_exp (execute_CPY_C_C_C d n)"
  by (unfold execute_CPY_C_C_C_def, non_mem_expI)

lemma non_mem_exp_decode_CPY_C_C_C[non_mem_expI]:
  "non_mem_exp (decode_CPY_C_C_C opc Cn Cd)"
  by (unfold decode_CPY_C_C_C_def, non_mem_expI)

lemma non_mem_exp_execute_CSEAL_C_C_C[non_mem_expI]:
  "non_mem_exp (execute_CSEAL_C_C_C d m n)"
  by (unfold execute_CSEAL_C_C_C_def, non_mem_expI)

lemma non_mem_exp_decode_CSEAL_C_C_C[non_mem_expI]:
  "non_mem_exp (decode_CSEAL_C_C_C Cm opc Cn Cd)"
  by (unfold decode_CSEAL_C_C_C_def, non_mem_expI)

lemma non_mem_exp_execute_CSEL_C_CI_C[non_mem_expI]:
  "non_mem_exp (execute_CSEL_C_CI_C cond d m n)"
  by (unfold execute_CSEL_C_CI_C_def, non_mem_expI)

lemma non_mem_exp_decode_CSEL_C_CI_C[non_mem_expI]:
  "non_mem_exp (decode_CSEL_C_CI_C Cm cond Cn Cd)"
  by (unfold decode_CSEL_C_CI_C_def, non_mem_expI)

lemma non_mem_exp_execute_CTHI_C_CR_C[non_mem_expI]:
  "non_mem_exp (execute_CTHI_C_CR_C d m n)"
  by (unfold execute_CTHI_C_CR_C_def, non_mem_expI)

lemma non_mem_exp_decode_CTHI_C_CR_C[non_mem_expI]:
  "non_mem_exp (decode_CTHI_C_CR_C Rm opc Cn Cd)"
  by (unfold decode_CTHI_C_CR_C_def, non_mem_expI)

lemma non_mem_exp_execute_CVTDZ_C_R_C[non_mem_expI]:
  "non_mem_exp (execute_CVTDZ_C_R_C d n)"
  by (unfold execute_CVTDZ_C_R_C_def, non_mem_expI)

lemma non_mem_exp_decode_CVTDZ_C_R_C[non_mem_expI]:
  "non_mem_exp (decode_CVTDZ_C_R_C opc Rn Cd)"
  by (unfold decode_CVTDZ_C_R_C_def, non_mem_expI)

lemma non_mem_exp_execute_CVTD_C_R_C[non_mem_expI]:
  "non_mem_exp (execute_CVTD_C_R_C d n)"
  by (unfold execute_CVTD_C_R_C_def, non_mem_expI)

lemma non_mem_exp_decode_CVTD_C_R_C[non_mem_expI]:
  "non_mem_exp (decode_CVTD_C_R_C opc Rn Cd)"
  by (unfold decode_CVTD_C_R_C_def, non_mem_expI)

lemma non_mem_exp_execute_CVTD_R_C_C[non_mem_expI]:
  "non_mem_exp (execute_CVTD_R_C_C d n)"
  by (unfold execute_CVTD_R_C_C_def, non_mem_expI)

lemma non_mem_exp_decode_CVTD_R_C_C[non_mem_expI]:
  "non_mem_exp (decode_CVTD_R_C_C opc Cn Rd)"
  by (unfold decode_CVTD_R_C_C_def, non_mem_expI)

lemma non_mem_exp_execute_CVTPZ_C_R_C[non_mem_expI]:
  "non_mem_exp (execute_CVTPZ_C_R_C d n)"
  by (unfold execute_CVTPZ_C_R_C_def, non_mem_expI)

lemma non_mem_exp_decode_CVTPZ_C_R_C[non_mem_expI]:
  "non_mem_exp (decode_CVTPZ_C_R_C opc Rn Cd)"
  by (unfold decode_CVTPZ_C_R_C_def, non_mem_expI)

lemma non_mem_exp_execute_CVTP_C_R_C[non_mem_expI]:
  "non_mem_exp (execute_CVTP_C_R_C d n)"
  by (unfold execute_CVTP_C_R_C_def, non_mem_expI)

lemma non_mem_exp_decode_CVTP_C_R_C[non_mem_expI]:
  "non_mem_exp (decode_CVTP_C_R_C opc Rn Cd)"
  by (unfold decode_CVTP_C_R_C_def, non_mem_expI)

lemma non_mem_exp_execute_CVTP_R_C_C[non_mem_expI]:
  "non_mem_exp (execute_CVTP_R_C_C d n)"
  by (unfold execute_CVTP_R_C_C_def, non_mem_expI)

lemma non_mem_exp_decode_CVTP_R_C_C[non_mem_expI]:
  "non_mem_exp (decode_CVTP_R_C_C opc Cn Rd)"
  by (unfold decode_CVTP_R_C_C_def, non_mem_expI)

lemma non_mem_exp_execute_CVTZ_C_CR_C[non_mem_expI]:
  "non_mem_exp (execute_CVTZ_C_CR_C d m n)"
  by (unfold execute_CVTZ_C_CR_C_def, non_mem_expI)

lemma non_mem_exp_decode_CVTZ_C_CR_C[non_mem_expI]:
  "non_mem_exp (decode_CVTZ_C_CR_C Rm Cn Cd)"
  by (unfold decode_CVTZ_C_CR_C_def, non_mem_expI)

lemma non_mem_exp_execute_CVT_C_CR_C[non_mem_expI]:
  "non_mem_exp (execute_CVT_C_CR_C d m n)"
  by (unfold execute_CVT_C_CR_C_def, non_mem_expI)

lemma non_mem_exp_decode_CVT_C_CR_C[non_mem_expI]:
  "non_mem_exp (decode_CVT_C_CR_C Rm Cn Cd)"
  by (unfold decode_CVT_C_CR_C_def, non_mem_expI)

lemma non_mem_exp_execute_CVT_R_CC_C[non_mem_expI]:
  "non_mem_exp (execute_CVT_R_CC_C d m n)"
  by (unfold execute_CVT_R_CC_C_def, non_mem_expI)

lemma non_mem_exp_decode_CVT_R_CC_C[non_mem_expI]:
  "non_mem_exp (decode_CVT_R_CC_C Cm Cn Rd)"
  by (unfold decode_CVT_R_CC_C_def, non_mem_expI)

lemma non_mem_exp_execute_EORFLGS_C_CI_C[non_mem_expI]:
  "non_mem_exp (execute_EORFLGS_C_CI_C d mask__arg n)"
  by (unfold execute_EORFLGS_C_CI_C_def, non_mem_expI)

lemma non_mem_exp_decode_EORFLGS_C_CI_C[non_mem_expI]:
  "non_mem_exp (decode_EORFLGS_C_CI_C imm8 Cn Cd)"
  by (unfold decode_EORFLGS_C_CI_C_def, non_mem_expI)

lemma non_mem_exp_execute_EORFLGS_C_CR_C[non_mem_expI]:
  "non_mem_exp (execute_EORFLGS_C_CR_C d m n)"
  by (unfold execute_EORFLGS_C_CR_C_def, non_mem_expI)

lemma non_mem_exp_decode_EORFLGS_C_CR_C[non_mem_expI]:
  "non_mem_exp (decode_EORFLGS_C_CR_C Rm opc Cn Cd)"
  by (unfold decode_EORFLGS_C_CR_C_def, non_mem_expI)

lemma non_mem_exp_execute_GCBASE_R_C_C[non_mem_expI]:
  "non_mem_exp (execute_GCBASE_R_C_C d n)"
  by (unfold execute_GCBASE_R_C_C_def, non_mem_expI)

lemma non_mem_exp_decode_GCBASE_R_C_C[non_mem_expI]:
  "non_mem_exp (decode_GCBASE_R_C_C opc Cn Rd)"
  by (unfold decode_GCBASE_R_C_C_def, non_mem_expI)

lemma non_mem_exp_execute_GCFLGS_R_C_C[non_mem_expI]:
  "non_mem_exp (execute_GCFLGS_R_C_C d n)"
  by (unfold execute_GCFLGS_R_C_C_def, non_mem_expI)

lemma non_mem_exp_decode_GCFLGS_R_C_C[non_mem_expI]:
  "non_mem_exp (decode_GCFLGS_R_C_C opc Cn Rd)"
  by (unfold decode_GCFLGS_R_C_C_def, non_mem_expI)

lemma non_mem_exp_execute_GCLEN_R_C_C[non_mem_expI]:
  "non_mem_exp (execute_GCLEN_R_C_C d n)"
  by (unfold execute_GCLEN_R_C_C_def, non_mem_expI)

lemma non_mem_exp_decode_GCLEN_R_C_C[non_mem_expI]:
  "non_mem_exp (decode_GCLEN_R_C_C opc Cn Rd)"
  by (unfold decode_GCLEN_R_C_C_def, non_mem_expI)

lemma non_mem_exp_execute_GCLIM_R_C_C[non_mem_expI]:
  "non_mem_exp (execute_GCLIM_R_C_C d n)"
  by (unfold execute_GCLIM_R_C_C_def, non_mem_expI)

lemma non_mem_exp_decode_GCLIM_R_C_C[non_mem_expI]:
  "non_mem_exp (decode_GCLIM_R_C_C opc Cn Rd)"
  by (unfold decode_GCLIM_R_C_C_def, non_mem_expI)

lemma non_mem_exp_execute_GCOFF_R_C_C[non_mem_expI]:
  "non_mem_exp (execute_GCOFF_R_C_C d n)"
  by (unfold execute_GCOFF_R_C_C_def, non_mem_expI)

lemma non_mem_exp_decode_GCOFF_R_C_C[non_mem_expI]:
  "non_mem_exp (decode_GCOFF_R_C_C opc Cn Rd)"
  by (unfold decode_GCOFF_R_C_C_def, non_mem_expI)

lemma non_mem_exp_execute_GCPERM_R_C_C[non_mem_expI]:
  "non_mem_exp (execute_GCPERM_R_C_C d n)"
  by (unfold execute_GCPERM_R_C_C_def, non_mem_expI)

lemma non_mem_exp_decode_GCPERM_R_C_C[non_mem_expI]:
  "non_mem_exp (decode_GCPERM_R_C_C opc Cn Rd)"
  by (unfold decode_GCPERM_R_C_C_def, non_mem_expI)

lemma non_mem_exp_execute_GCSEAL_R_C_C[non_mem_expI]:
  "non_mem_exp (execute_GCSEAL_R_C_C d n)"
  by (unfold execute_GCSEAL_R_C_C_def, non_mem_expI)

lemma non_mem_exp_decode_GCSEAL_R_C_C[non_mem_expI]:
  "non_mem_exp (decode_GCSEAL_R_C_C opc Cn Rd)"
  by (unfold decode_GCSEAL_R_C_C_def, non_mem_expI)

lemma non_mem_exp_execute_GCTAG_R_C_C[non_mem_expI]:
  "non_mem_exp (execute_GCTAG_R_C_C d n)"
  by (unfold execute_GCTAG_R_C_C_def, non_mem_expI)

lemma non_mem_exp_decode_GCTAG_R_C_C[non_mem_expI]:
  "non_mem_exp (decode_GCTAG_R_C_C opc Cn Rd)"
  by (unfold decode_GCTAG_R_C_C_def, non_mem_expI)

lemma non_mem_exp_execute_GCTYPE_R_C_C[non_mem_expI]:
  "non_mem_exp (execute_GCTYPE_R_C_C d n)"
  by (unfold execute_GCTYPE_R_C_C_def, non_mem_expI)

lemma non_mem_exp_decode_GCTYPE_R_C_C[non_mem_expI]:
  "non_mem_exp (decode_GCTYPE_R_C_C opc Cn Rd)"
  by (unfold decode_GCTYPE_R_C_C_def, non_mem_expI)

lemma non_mem_exp_execute_GCVALUE_R_C_C[non_mem_expI]:
  "non_mem_exp (execute_GCVALUE_R_C_C d n)"
  by (unfold execute_GCVALUE_R_C_C_def, non_mem_expI)

lemma non_mem_exp_decode_GCVALUE_R_C_C[non_mem_expI]:
  "non_mem_exp (decode_GCVALUE_R_C_C opc Cn Rd)"
  by (unfold decode_GCVALUE_R_C_C_def, non_mem_expI)

lemma non_mem_exp_execute_MRS_C_I_C[non_mem_expI]:
  "non_mem_exp (execute_MRS_C_I_C sys_crm sys_crn sys_op0 sys_op1 sys_op2 t__arg)"
  by (unfold execute_MRS_C_I_C_def, non_mem_expI)

lemma non_mem_exp_decode_MRS_C_I_C[non_mem_expI]:
  "non_mem_exp (decode_MRS_C_I_C L o0 op1 CRn CRm op2 Ct)"
  by (unfold decode_MRS_C_I_C_def, non_mem_expI)

lemma non_mem_exp_execute_MSR_C_I_C[non_mem_expI]:
  "non_mem_exp (execute_MSR_C_I_C sys_crm sys_crn sys_op0 sys_op1 sys_op2 t__arg)"
  by (unfold execute_MSR_C_I_C_def, non_mem_expI)

lemma non_mem_exp_decode_MSR_C_I_C[non_mem_expI]:
  "non_mem_exp (decode_MSR_C_I_C L o0 op1 CRn CRm op2 Ct)"
  by (unfold decode_MSR_C_I_C_def, non_mem_expI)

lemma non_mem_exp_execute_ORRFLGS_C_CI_C[non_mem_expI]:
  "non_mem_exp (execute_ORRFLGS_C_CI_C d mask__arg n)"
  by (unfold execute_ORRFLGS_C_CI_C_def, non_mem_expI)

lemma non_mem_exp_decode_ORRFLGS_C_CI_C[non_mem_expI]:
  "non_mem_exp (decode_ORRFLGS_C_CI_C imm8 Cn Cd)"
  by (unfold decode_ORRFLGS_C_CI_C_def, non_mem_expI)

lemma non_mem_exp_execute_ORRFLGS_C_CR_C[non_mem_expI]:
  "non_mem_exp (execute_ORRFLGS_C_CR_C d m n)"
  by (unfold execute_ORRFLGS_C_CR_C_def, non_mem_expI)

lemma non_mem_exp_decode_ORRFLGS_C_CR_C[non_mem_expI]:
  "non_mem_exp (decode_ORRFLGS_C_CR_C Rm opc Cn Cd)"
  by (unfold decode_ORRFLGS_C_CR_C_def, non_mem_expI)

lemma non_mem_exp_execute_RETR_C_C[non_mem_expI]:
  "non_mem_exp (execute_RETR_C_C branch_type n)"
  by (unfold execute_RETR_C_C_def, non_mem_expI)

lemma non_mem_exp_decode_RETR_C_C[non_mem_expI]:
  "non_mem_exp (decode_RETR_C_C opc Cn)"
  by (unfold decode_RETR_C_C_def, non_mem_expI)

lemma non_mem_exp_execute_RETS_C_C[non_mem_expI]:
  "non_mem_exp (execute_RETS_C_C branch_type n)"
  by (unfold execute_RETS_C_C_def, non_mem_expI)

lemma non_mem_exp_decode_RETS_C_C[non_mem_expI]:
  "non_mem_exp (decode_RETS_C_C opc Cn)"
  by (unfold decode_RETS_C_C_def, non_mem_expI)

lemma non_mem_exp_execute_RETS_C_C_C[non_mem_expI]:
  "non_mem_exp (execute_RETS_C_C_C branch_type m n)"
  by (unfold execute_RETS_C_C_C_def, non_mem_expI)

lemma non_mem_exp_decode_RETS_C_C_C[non_mem_expI]:
  "non_mem_exp (decode_RETS_C_C_C Cm opc Cn)"
  by (unfold decode_RETS_C_C_C_def, non_mem_expI)

lemma non_mem_exp_execute_RET_C_C[non_mem_expI]:
  "non_mem_exp (execute_RET_C_C branch_type n)"
  by (unfold execute_RET_C_C_def, non_mem_expI)

lemma non_mem_exp_decode_RET_C_C[non_mem_expI]:
  "non_mem_exp (decode_RET_C_C opc Cn)"
  by (unfold decode_RET_C_C_def, non_mem_expI)

lemma non_mem_exp_execute_RRLEN_R_R_C[non_mem_expI]:
  "non_mem_exp (execute_RRLEN_R_R_C d n)"
  by (unfold execute_RRLEN_R_R_C_def, non_mem_expI)

lemma non_mem_exp_decode_RRLEN_R_R_C[non_mem_expI]:
  "non_mem_exp (decode_RRLEN_R_R_C opc Rn Rd)"
  by (unfold decode_RRLEN_R_R_C_def, non_mem_expI)

lemma non_mem_exp_execute_RRMASK_R_R_C[non_mem_expI]:
  "non_mem_exp (execute_RRMASK_R_R_C d n)"
  by (unfold execute_RRMASK_R_R_C_def, non_mem_expI)

lemma non_mem_exp_decode_RRMASK_R_R_C[non_mem_expI]:
  "non_mem_exp (decode_RRMASK_R_R_C opc Rn Rd)"
  by (unfold decode_RRMASK_R_R_C_def, non_mem_expI)

lemma non_mem_exp_execute_SCBNDSE_C_CR_C[non_mem_expI]:
  "non_mem_exp (execute_SCBNDSE_C_CR_C d m n)"
  by (unfold execute_SCBNDSE_C_CR_C_def, non_mem_expI)

lemma non_mem_exp_decode_SCBNDSE_C_CR_C[non_mem_expI]:
  "non_mem_exp (decode_SCBNDSE_C_CR_C Rm opc Cn Cd)"
  by (unfold decode_SCBNDSE_C_CR_C_def, non_mem_expI)

lemma non_mem_exp_execute_SCBNDS_C_CI_C[non_mem_expI]:
  "non_mem_exp (execute_SCBNDS_C_CI_C d length__arg n)"
  by (unfold execute_SCBNDS_C_CI_C_def, non_mem_expI)

lemma non_mem_exp_decode_SCBNDS_C_CI_C[non_mem_expI]:
  "non_mem_exp (decode_SCBNDS_C_CI_C imm6 S Cn Cd)"
  by (unfold decode_SCBNDS_C_CI_C_def, non_mem_expI)

lemma non_mem_exp_execute_SCBNDS_C_CI_S[non_mem_expI]:
  "non_mem_exp (execute_SCBNDS_C_CI_S d length__arg n)"
  by (unfold execute_SCBNDS_C_CI_S_def, non_mem_expI)

lemma non_mem_exp_decode_SCBNDS_C_CI_S[non_mem_expI]:
  "non_mem_exp (decode_SCBNDS_C_CI_S imm6 S Cn Cd)"
  by (unfold decode_SCBNDS_C_CI_S_def, non_mem_expI)

lemma non_mem_exp_execute_SCBNDS_C_CR_C[non_mem_expI]:
  "non_mem_exp (execute_SCBNDS_C_CR_C d m n)"
  by (unfold execute_SCBNDS_C_CR_C_def, non_mem_expI)

lemma non_mem_exp_decode_SCBNDS_C_CR_C[non_mem_expI]:
  "non_mem_exp (decode_SCBNDS_C_CR_C Rm opc Cn Cd)"
  by (unfold decode_SCBNDS_C_CR_C_def, non_mem_expI)

lemma non_mem_exp_execute_SCFLGS_C_CR_C[non_mem_expI]:
  "non_mem_exp (execute_SCFLGS_C_CR_C d m n)"
  by (unfold execute_SCFLGS_C_CR_C_def, non_mem_expI)

lemma non_mem_exp_decode_SCFLGS_C_CR_C[non_mem_expI]:
  "non_mem_exp (decode_SCFLGS_C_CR_C Rm Cn Cd)"
  by (unfold decode_SCFLGS_C_CR_C_def, non_mem_expI)

lemma non_mem_exp_execute_SCOFF_C_CR_C[non_mem_expI]:
  "non_mem_exp (execute_SCOFF_C_CR_C d m n)"
  by (unfold execute_SCOFF_C_CR_C_def, non_mem_expI)

lemma non_mem_exp_decode_SCOFF_C_CR_C[non_mem_expI]:
  "non_mem_exp (decode_SCOFF_C_CR_C Rm opc Cn Cd)"
  by (unfold decode_SCOFF_C_CR_C_def, non_mem_expI)

lemma non_mem_exp_execute_SCTAG_C_CR_C[non_mem_expI]:
  "non_mem_exp (execute_SCTAG_C_CR_C d m n)"
  by (unfold execute_SCTAG_C_CR_C_def, non_mem_expI)

lemma non_mem_exp_decode_SCTAG_C_CR_C[non_mem_expI]:
  "non_mem_exp (decode_SCTAG_C_CR_C Rm Cn Cd)"
  by (unfold decode_SCTAG_C_CR_C_def, non_mem_expI)

lemma non_mem_exp_execute_SCVALUE_C_CR_C[non_mem_expI]:
  "non_mem_exp (execute_SCVALUE_C_CR_C d m n)"
  by (unfold execute_SCVALUE_C_CR_C_def, non_mem_expI)

lemma non_mem_exp_decode_SCVALUE_C_CR_C[non_mem_expI]:
  "non_mem_exp (decode_SCVALUE_C_CR_C Rm opc Cn Cd)"
  by (unfold decode_SCVALUE_C_CR_C_def, non_mem_expI)

lemma non_mem_exp_execute_SEAL_C_CC_C[non_mem_expI]:
  "non_mem_exp (execute_SEAL_C_CC_C d m n)"
  by (unfold execute_SEAL_C_CC_C_def, non_mem_expI)

lemma non_mem_exp_decode_SEAL_C_CC_C[non_mem_expI]:
  "non_mem_exp (decode_SEAL_C_CC_C Cm opc Cn Cd)"
  by (unfold decode_SEAL_C_CC_C_def, non_mem_expI)

lemma non_mem_exp_execute_SEAL_C_CI_C[non_mem_expI]:
  "non_mem_exp (execute_SEAL_C_CI_C d f n)"
  by (unfold execute_SEAL_C_CI_C_def, non_mem_expI)

lemma non_mem_exp_decode_SEAL_C_CI_C[non_mem_expI]:
  "non_mem_exp (decode_SEAL_C_CI_C form Cn Cd)"
  by (unfold decode_SEAL_C_CI_C_def, non_mem_expI)

lemma non_mem_exp_execute_SUBS_R_CC_C[non_mem_expI]:
  "non_mem_exp (execute_SUBS_R_CC_C d m n)"
  by (unfold execute_SUBS_R_CC_C_def, non_mem_expI)

lemma non_mem_exp_decode_SUBS_R_CC_C[non_mem_expI]:
  "non_mem_exp (decode_SUBS_R_CC_C Cm Cn Rd)"
  by (unfold decode_SUBS_R_CC_C_def, non_mem_expI)

lemma non_mem_exp_execute_SUB_C_CIS_C[non_mem_expI]:
  "non_mem_exp (execute_SUB_C_CIS_C d imm n)"
  by (unfold execute_SUB_C_CIS_C_def, non_mem_expI)

lemma non_mem_exp_decode_SUB_C_CIS_C[non_mem_expI]:
  "non_mem_exp (decode_SUB_C_CIS_C A sh imm12 Cn Cd)"
  by (unfold decode_SUB_C_CIS_C_def, non_mem_expI)

lemma non_mem_exp_execute_UNSEAL_C_CC_C[non_mem_expI]:
  "non_mem_exp (execute_UNSEAL_C_CC_C d m n)"
  by (unfold execute_UNSEAL_C_CC_C_def, non_mem_expI)

lemma non_mem_exp_decode_UNSEAL_C_CC_C[non_mem_expI]:
  "non_mem_exp (decode_UNSEAL_C_CC_C Cm opc Cn Cd)"
  by (unfold decode_UNSEAL_C_CC_C_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_arithmetic_unary_diff_neg_int_sisd[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_arithmetic_unary_diff_neg_int_sisd d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) n neg)"
  by (unfold execute_aarch64_instrs_vector_arithmetic_unary_diff_neg_int_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_abs_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_int_simd[non_mem_expI]:
  "non_mem_exp (decode_abs_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_int_simd Rd Rn b__0 U b__1)"
  by (unfold decode_abs_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_int_simd_def, non_mem_expI)

lemma non_mem_exp_decode_abs_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_int_sisd[non_mem_expI]:
  "non_mem_exp (decode_abs_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_int_sisd Rd Rn b__0 U)"
  by (unfold decode_abs_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_int_sisd_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_integer_arithmetic_add_sub_carry[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_integer_arithmetic_add_sub_carry d (datasize :: 'datasize::len itself) m n setflags sub_op)"
  by (unfold execute_aarch64_instrs_integer_arithmetic_add_sub_carry_def, non_mem_expI)

lemma non_mem_exp_decode_adc_aarch64_instrs_integer_arithmetic_add_sub_carry[non_mem_expI]:
  "non_mem_exp (decode_adc_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn Rm S op b__0)"
  by (unfold decode_adc_aarch64_instrs_integer_arithmetic_add_sub_carry_def, non_mem_expI)

lemma non_mem_exp_decode_adcs_aarch64_instrs_integer_arithmetic_add_sub_carry[non_mem_expI]:
  "non_mem_exp (decode_adcs_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn Rm S op b__0)"
  by (unfold decode_adcs_aarch64_instrs_integer_arithmetic_add_sub_carry_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_integer_arithmetic_add_sub_extendedreg[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_integer_arithmetic_add_sub_extendedreg d (datasize :: 'datasize::len itself) extend_type m n setflags shift sub_op)"
  by (unfold execute_aarch64_instrs_integer_arithmetic_add_sub_extendedreg_def, non_mem_expI)

lemma non_mem_exp_decode_add_addsub_ext_aarch64_instrs_integer_arithmetic_add_sub_extendedreg[non_mem_expI]:
  "non_mem_exp (decode_add_addsub_ext_aarch64_instrs_integer_arithmetic_add_sub_extendedreg Rd Rn imm3 option_name Rm S op b__0)"
  by (unfold decode_add_addsub_ext_aarch64_instrs_integer_arithmetic_add_sub_extendedreg_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_integer_arithmetic_add_sub_immediate[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_integer_arithmetic_add_sub_immediate d datasize imm n setflags sub_op)"
  by (unfold execute_aarch64_instrs_integer_arithmetic_add_sub_immediate_def, non_mem_expI)

lemma non_mem_exp_decode_add_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate[non_mem_expI]:
  "non_mem_exp (decode_add_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate Rd Rn imm12 sh S op b__0)"
  by (unfold decode_add_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg d (datasize :: 'datasize::len itself) m n setflags shift_amount shift_type sub_op)"
  by (unfold execute_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg_def, non_mem_expI)

lemma non_mem_exp_decode_add_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg[non_mem_expI]:
  "non_mem_exp (decode_add_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg Rd Rn imm6 Rm shift S op b__0)"
  by (unfold decode_add_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_arithmetic_binary_uniform_add_wrapping_single_sisd[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_arithmetic_binary_uniform_add_wrapping_single_sisd d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) m n sub_op)"
  by (unfold execute_aarch64_instrs_vector_arithmetic_binary_uniform_add_wrapping_single_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_add_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_wrapping_single_simd[non_mem_expI]:
  "non_mem_exp (decode_add_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_wrapping_single_simd Rd Rn Rm b__0 U b__1)"
  by (unfold decode_add_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_wrapping_single_simd_def, non_mem_expI)

lemma non_mem_exp_decode_add_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_wrapping_single_sisd[non_mem_expI]:
  "non_mem_exp (decode_add_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_wrapping_single_sisd Rd Rn Rm b__0 U)"
  by (unfold decode_add_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_wrapping_single_sisd_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_narrow[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_narrow d datasize elements l__40 m n part round__arg sub_op)"
  by (unfold execute_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_narrow_def, non_mem_expI)

lemma non_mem_exp_decode_addhn_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_narrow[non_mem_expI]:
  "non_mem_exp (decode_addhn_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_narrow Rd Rn o1 Rm b__0 U Q)"
  by (unfold decode_addhn_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_narrow_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_reduce_add_sisd[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_reduce_add_sisd d (datasize :: 'datasize::len itself) (esize :: 'esize::len itself) n op)"
  by (unfold execute_aarch64_instrs_vector_reduce_add_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_addp_advsimd_pair_aarch64_instrs_vector_reduce_add_sisd[non_mem_expI]:
  "non_mem_exp (decode_addp_advsimd_pair_aarch64_instrs_vector_reduce_add_sisd Rd Rn b__0)"
  by (unfold decode_addp_advsimd_pair_aarch64_instrs_vector_reduce_add_sisd_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_arithmetic_binary_uniform_add_wrapping_pair[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_arithmetic_binary_uniform_add_wrapping_pair d l__179 elements (esize :: 'esize::len itself) m n)"
  by (unfold execute_aarch64_instrs_vector_arithmetic_binary_uniform_add_wrapping_pair_def, non_mem_expI)

lemma non_mem_exp_decode_addp_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_add_wrapping_pair[non_mem_expI]:
  "non_mem_exp (decode_addp_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_add_wrapping_pair Rd Rn Rm b__0 b__1)"
  by (unfold decode_addp_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_add_wrapping_pair_def, non_mem_expI)

lemma non_mem_exp_decode_adds_addsub_ext_aarch64_instrs_integer_arithmetic_add_sub_extendedreg[non_mem_expI]:
  "non_mem_exp (decode_adds_addsub_ext_aarch64_instrs_integer_arithmetic_add_sub_extendedreg Rd Rn imm3 option_name Rm S op b__0)"
  by (unfold decode_adds_addsub_ext_aarch64_instrs_integer_arithmetic_add_sub_extendedreg_def, non_mem_expI)

lemma non_mem_exp_decode_adds_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate[non_mem_expI]:
  "non_mem_exp (decode_adds_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate Rd Rn imm12 sh S op b__0)"
  by (unfold decode_adds_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate_def, non_mem_expI)

lemma non_mem_exp_decode_adds_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg[non_mem_expI]:
  "non_mem_exp (decode_adds_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg Rd Rn imm6 Rm shift S op b__0)"
  by (unfold decode_adds_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_reduce_add_simd[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_reduce_add_simd d (datasize :: 'datasize::len itself) (esize :: 'esize::len itself) n op)"
  by (unfold execute_aarch64_instrs_vector_reduce_add_simd_def, non_mem_expI)

lemma non_mem_exp_decode_addv_advsimd_aarch64_instrs_vector_reduce_add_simd[non_mem_expI]:
  "non_mem_exp (decode_addv_advsimd_aarch64_instrs_vector_reduce_add_simd Rd Rn b__0 b__1)"
  by (unfold decode_addv_advsimd_aarch64_instrs_vector_reduce_add_simd_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_crypto_aes_round[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_crypto_aes_round d decrypt n)"
  by (unfold execute_aarch64_instrs_vector_crypto_aes_round_def, non_mem_expI)

lemma non_mem_exp_decode_aesd_advsimd_aarch64_instrs_vector_crypto_aes_round[non_mem_expI]:
  "non_mem_exp (decode_aesd_advsimd_aarch64_instrs_vector_crypto_aes_round Rd Rn D)"
  by (unfold decode_aesd_advsimd_aarch64_instrs_vector_crypto_aes_round_def, non_mem_expI)

lemma non_mem_exp_decode_aese_advsimd_aarch64_instrs_vector_crypto_aes_round[non_mem_expI]:
  "non_mem_exp (decode_aese_advsimd_aarch64_instrs_vector_crypto_aes_round Rd Rn D)"
  by (unfold decode_aese_advsimd_aarch64_instrs_vector_crypto_aes_round_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_crypto_aes_mix[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_crypto_aes_mix d decrypt n)"
  by (unfold execute_aarch64_instrs_vector_crypto_aes_mix_def, non_mem_expI)

lemma non_mem_exp_decode_aesimc_advsimd_aarch64_instrs_vector_crypto_aes_mix[non_mem_expI]:
  "non_mem_exp (decode_aesimc_advsimd_aarch64_instrs_vector_crypto_aes_mix Rd Rn D)"
  by (unfold decode_aesimc_advsimd_aarch64_instrs_vector_crypto_aes_mix_def, non_mem_expI)

lemma non_mem_exp_decode_aesmc_advsimd_aarch64_instrs_vector_crypto_aes_mix[non_mem_expI]:
  "non_mem_exp (decode_aesmc_advsimd_aarch64_instrs_vector_crypto_aes_mix Rd Rn D)"
  by (unfold decode_aesmc_advsimd_aarch64_instrs_vector_crypto_aes_mix_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_arithmetic_binary_uniform_logical_and_orr[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_arithmetic_binary_uniform_logical_and_orr d (datasize :: 'datasize::len itself) invert m n op)"
  by (unfold execute_aarch64_instrs_vector_arithmetic_binary_uniform_logical_and_orr_def, non_mem_expI)

lemma non_mem_exp_decode_and_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_logical_and_orr[non_mem_expI]:
  "non_mem_exp (decode_and_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_logical_and_orr Rd Rn Rm size__arg b__0)"
  by (unfold decode_and_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_logical_and_orr_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_integer_logical_immediate[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_integer_logical_immediate d datasize imm n op setflags)"
  by (unfold execute_aarch64_instrs_integer_logical_immediate_def, non_mem_expI)

lemma non_mem_exp_decode_and_log_imm_aarch64_instrs_integer_logical_immediate[non_mem_expI]:
  "non_mem_exp (decode_and_log_imm_aarch64_instrs_integer_logical_immediate Rd Rn imms immr N opc b__0)"
  by (unfold decode_and_log_imm_aarch64_instrs_integer_logical_immediate_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_integer_logical_shiftedreg[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_integer_logical_shiftedreg d (datasize :: 'datasize::len itself) invert m n op setflags shift_amount shift_type)"
  by (unfold execute_aarch64_instrs_integer_logical_shiftedreg_def, non_mem_expI)

lemma non_mem_exp_decode_and_log_shift_aarch64_instrs_integer_logical_shiftedreg[non_mem_expI]:
  "non_mem_exp (decode_and_log_shift_aarch64_instrs_integer_logical_shiftedreg Rd Rn imm6 Rm N shift opc b__0)"
  by (unfold decode_and_log_shift_aarch64_instrs_integer_logical_shiftedreg_def, non_mem_expI)

lemma non_mem_exp_decode_ands_log_imm_aarch64_instrs_integer_logical_immediate[non_mem_expI]:
  "non_mem_exp (decode_ands_log_imm_aarch64_instrs_integer_logical_immediate Rd Rn imms immr N opc b__0)"
  by (unfold decode_ands_log_imm_aarch64_instrs_integer_logical_immediate_def, non_mem_expI)

lemma non_mem_exp_decode_ands_log_shift_aarch64_instrs_integer_logical_shiftedreg[non_mem_expI]:
  "non_mem_exp (decode_ands_log_shift_aarch64_instrs_integer_logical_shiftedreg Rd Rn imm6 Rm N shift opc b__0)"
  by (unfold decode_ands_log_shift_aarch64_instrs_integer_logical_shiftedreg_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_integer_shift_variable[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_integer_shift_variable d (datasize :: 'datasize::len itself) m n shift_type)"
  by (unfold execute_aarch64_instrs_integer_shift_variable_def, non_mem_expI)

lemma non_mem_exp_decode_asrv_aarch64_instrs_integer_shift_variable[non_mem_expI]:
  "non_mem_exp (decode_asrv_aarch64_instrs_integer_shift_variable Rd Rn op2 Rm b__0)"
  by (unfold decode_asrv_aarch64_instrs_integer_shift_variable_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_branch_conditional_cond[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_branch_conditional_cond condition offset)"
  by (unfold execute_aarch64_instrs_branch_conditional_cond_def, non_mem_expI)

lemma non_mem_exp_decode_b_cond_aarch64_instrs_branch_conditional_cond[non_mem_expI]:
  "non_mem_exp (decode_b_cond_aarch64_instrs_branch_conditional_cond cond imm19)"
  by (unfold decode_b_cond_aarch64_instrs_branch_conditional_cond_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_branch_unconditional_immediate[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_branch_unconditional_immediate branch_type offset)"
  by (unfold execute_aarch64_instrs_branch_unconditional_immediate_def, non_mem_expI)

lemma non_mem_exp_decode_b_uncond_aarch64_instrs_branch_unconditional_immediate[non_mem_expI]:
  "non_mem_exp (decode_b_uncond_aarch64_instrs_branch_unconditional_immediate imm26 op)"
  by (unfold decode_b_uncond_aarch64_instrs_branch_unconditional_immediate_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_crypto_sha3_bcax[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_crypto_sha3_bcax a d m n)"
  by (unfold execute_aarch64_instrs_vector_crypto_sha3_bcax_def, non_mem_expI)

lemma non_mem_exp_decode_bcax_advsimd_aarch64_instrs_vector_crypto_sha3_bcax[non_mem_expI]:
  "non_mem_exp (decode_bcax_advsimd_aarch64_instrs_vector_crypto_sha3_bcax Rd Rn Ra Rm)"
  by (unfold decode_bcax_advsimd_aarch64_instrs_vector_crypto_sha3_bcax_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_integer_bitfield[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_integer_bitfield R S d datasize extend__arg inzero n tmask wmask)"
  by (unfold execute_aarch64_instrs_integer_bitfield_def, non_mem_expI)

lemma non_mem_exp_decode_bfm_aarch64_instrs_integer_bitfield[non_mem_expI]:
  "non_mem_exp (decode_bfm_aarch64_instrs_integer_bitfield Rd Rn imms immr N opc b__0)"
  by (unfold decode_bfm_aarch64_instrs_integer_bitfield_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_logical[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_logical datasize imm operation rd)"
  by (unfold execute_aarch64_instrs_vector_logical_def, non_mem_expI)

lemma non_mem_exp_decode_bic_advsimd_imm_aarch64_instrs_vector_logical[non_mem_expI]:
  "non_mem_exp (decode_bic_advsimd_imm_aarch64_instrs_vector_logical Rd h g f e d cmode c__arg b a op b__0)"
  by (unfold decode_bic_advsimd_imm_aarch64_instrs_vector_logical_def, non_mem_expI)

lemma non_mem_exp_decode_bic_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_logical_and_orr[non_mem_expI]:
  "non_mem_exp (decode_bic_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_logical_and_orr Rd Rn Rm size__arg b__0)"
  by (unfold decode_bic_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_logical_and_orr_def, non_mem_expI)

lemma non_mem_exp_decode_bic_log_shift_aarch64_instrs_integer_logical_shiftedreg[non_mem_expI]:
  "non_mem_exp (decode_bic_log_shift_aarch64_instrs_integer_logical_shiftedreg Rd Rn imm6 Rm N shift opc b__0)"
  by (unfold decode_bic_log_shift_aarch64_instrs_integer_logical_shiftedreg_def, non_mem_expI)

lemma non_mem_exp_decode_bics_aarch64_instrs_integer_logical_shiftedreg[non_mem_expI]:
  "non_mem_exp (decode_bics_aarch64_instrs_integer_logical_shiftedreg Rd Rn imm6 Rm N shift opc b__0)"
  by (unfold decode_bics_aarch64_instrs_integer_logical_shiftedreg_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_arithmetic_binary_uniform_logical_bsl_eor[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_arithmetic_binary_uniform_logical_bsl_eor d (datasize :: 'datasize::len itself) m n op)"
  by (unfold execute_aarch64_instrs_vector_arithmetic_binary_uniform_logical_bsl_eor_def, non_mem_expI)

lemma non_mem_exp_decode_bif_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_logical_bsl_eor[non_mem_expI]:
  "non_mem_exp (decode_bif_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_logical_bsl_eor Rd Rn Rm opc2 b__0)"
  by (unfold decode_bif_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_logical_bsl_eor_def, non_mem_expI)

lemma non_mem_exp_decode_bit_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_logical_bsl_eor[non_mem_expI]:
  "non_mem_exp (decode_bit_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_logical_bsl_eor Rd Rn Rm opc2 b__0)"
  by (unfold decode_bit_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_logical_bsl_eor_def, non_mem_expI)

lemma non_mem_exp_decode_bl_aarch64_instrs_branch_unconditional_immediate[non_mem_expI]:
  "non_mem_exp (decode_bl_aarch64_instrs_branch_unconditional_immediate imm26 op)"
  by (unfold decode_bl_aarch64_instrs_branch_unconditional_immediate_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_branch_unconditional_register[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_branch_unconditional_register branch_type n)"
  by (unfold execute_aarch64_instrs_branch_unconditional_register_def, non_mem_expI)

lemma non_mem_exp_decode_blr_aarch64_instrs_branch_unconditional_register[non_mem_expI]:
  "non_mem_exp (decode_blr_aarch64_instrs_branch_unconditional_register Rm Rn M A op Z)"
  by (unfold decode_blr_aarch64_instrs_branch_unconditional_register_def, non_mem_expI)

lemma non_mem_exp_decode_blra_aarch64_instrs_branch_unconditional_register[non_mem_expI]:
  "non_mem_exp (decode_blra_aarch64_instrs_branch_unconditional_register Rm Rn M A op Z)"
  by (unfold decode_blra_aarch64_instrs_branch_unconditional_register_def, non_mem_expI)

lemma non_mem_exp_decode_br_aarch64_instrs_branch_unconditional_register[non_mem_expI]:
  "non_mem_exp (decode_br_aarch64_instrs_branch_unconditional_register Rm Rn M A op Z)"
  by (unfold decode_br_aarch64_instrs_branch_unconditional_register_def, non_mem_expI)

lemma non_mem_exp_decode_bra_aarch64_instrs_branch_unconditional_register[non_mem_expI]:
  "non_mem_exp (decode_bra_aarch64_instrs_branch_unconditional_register Rm Rn M A op Z)"
  by (unfold decode_bra_aarch64_instrs_branch_unconditional_register_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_system_exceptions_debug_breakpoint[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_system_exceptions_debug_breakpoint comment)"
  by (unfold execute_aarch64_instrs_system_exceptions_debug_breakpoint_def, non_mem_expI)

lemma non_mem_exp_decode_brk_aarch64_instrs_system_exceptions_debug_breakpoint[non_mem_expI]:
  "non_mem_exp (decode_brk_aarch64_instrs_system_exceptions_debug_breakpoint imm16)"
  by (unfold decode_brk_aarch64_instrs_system_exceptions_debug_breakpoint_def, non_mem_expI)

lemma non_mem_exp_decode_bsl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_logical_bsl_eor[non_mem_expI]:
  "non_mem_exp (decode_bsl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_logical_bsl_eor Rd Rn Rm opc2 b__0)"
  by (unfold decode_bsl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_logical_bsl_eor_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_branch_conditional_compare[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_branch_conditional_compare (datasize :: 'datasize::len itself) iszero__arg offset t__arg)"
  by (unfold execute_aarch64_instrs_branch_conditional_compare_def, non_mem_expI)

lemma non_mem_exp_decode_cbnz_aarch64_instrs_branch_conditional_compare[non_mem_expI]:
  "non_mem_exp (decode_cbnz_aarch64_instrs_branch_conditional_compare Rt imm19 op b__0)"
  by (unfold decode_cbnz_aarch64_instrs_branch_conditional_compare_def, non_mem_expI)

lemma non_mem_exp_decode_cbz_aarch64_instrs_branch_conditional_compare[non_mem_expI]:
  "non_mem_exp (decode_cbz_aarch64_instrs_branch_conditional_compare Rt imm19 op b__0)"
  by (unfold decode_cbz_aarch64_instrs_branch_conditional_compare_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_integer_conditional_compare_immediate[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_integer_conditional_compare_immediate condition datasize flags__arg imm n sub_op)"
  by (unfold execute_aarch64_instrs_integer_conditional_compare_immediate_def, non_mem_expI)

lemma non_mem_exp_decode_ccmn_imm_aarch64_instrs_integer_conditional_compare_immediate[non_mem_expI]:
  "non_mem_exp (decode_ccmn_imm_aarch64_instrs_integer_conditional_compare_immediate nzcv Rn cond imm5 op b__0)"
  by (unfold decode_ccmn_imm_aarch64_instrs_integer_conditional_compare_immediate_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_integer_conditional_compare_register[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_integer_conditional_compare_register condition (datasize :: 'datasize::len itself) flags__arg m n sub_op)"
  by (unfold execute_aarch64_instrs_integer_conditional_compare_register_def, non_mem_expI)

lemma non_mem_exp_decode_ccmn_reg_aarch64_instrs_integer_conditional_compare_register[non_mem_expI]:
  "non_mem_exp (decode_ccmn_reg_aarch64_instrs_integer_conditional_compare_register nzcv Rn cond Rm op b__0)"
  by (unfold decode_ccmn_reg_aarch64_instrs_integer_conditional_compare_register_def, non_mem_expI)

lemma non_mem_exp_decode_ccmp_imm_aarch64_instrs_integer_conditional_compare_immediate[non_mem_expI]:
  "non_mem_exp (decode_ccmp_imm_aarch64_instrs_integer_conditional_compare_immediate nzcv Rn cond imm5 op b__0)"
  by (unfold decode_ccmp_imm_aarch64_instrs_integer_conditional_compare_immediate_def, non_mem_expI)

lemma non_mem_exp_decode_ccmp_reg_aarch64_instrs_integer_conditional_compare_register[non_mem_expI]:
  "non_mem_exp (decode_ccmp_reg_aarch64_instrs_integer_conditional_compare_register nzcv Rn cond Rm op b__0)"
  by (unfold decode_ccmp_reg_aarch64_instrs_integer_conditional_compare_register_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_arithmetic_unary_clsz[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_arithmetic_unary_clsz countop d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) n)"
  by (unfold execute_aarch64_instrs_vector_arithmetic_unary_clsz_def, non_mem_expI)

lemma non_mem_exp_decode_cls_advsimd_aarch64_instrs_vector_arithmetic_unary_clsz[non_mem_expI]:
  "non_mem_exp (decode_cls_advsimd_aarch64_instrs_vector_arithmetic_unary_clsz Rd Rn b__0 U b__1)"
  by (unfold decode_cls_advsimd_aarch64_instrs_vector_arithmetic_unary_clsz_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_integer_arithmetic_cnt[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_integer_arithmetic_cnt d (datasize :: 'datasize::len itself) n opcode)"
  by (unfold execute_aarch64_instrs_integer_arithmetic_cnt_def, non_mem_expI)

lemma non_mem_exp_decode_cls_int_aarch64_instrs_integer_arithmetic_cnt[non_mem_expI]:
  "non_mem_exp (decode_cls_int_aarch64_instrs_integer_arithmetic_cnt Rd Rn op b__0)"
  by (unfold decode_cls_int_aarch64_instrs_integer_arithmetic_cnt_def, non_mem_expI)

lemma non_mem_exp_decode_clz_advsimd_aarch64_instrs_vector_arithmetic_unary_clsz[non_mem_expI]:
  "non_mem_exp (decode_clz_advsimd_aarch64_instrs_vector_arithmetic_unary_clsz Rd Rn b__0 U b__1)"
  by (unfold decode_clz_advsimd_aarch64_instrs_vector_arithmetic_unary_clsz_def, non_mem_expI)

lemma non_mem_exp_decode_clz_int_aarch64_instrs_integer_arithmetic_cnt[non_mem_expI]:
  "non_mem_exp (decode_clz_int_aarch64_instrs_integer_arithmetic_cnt Rd Rn op b__0)"
  by (unfold decode_clz_int_aarch64_instrs_integer_arithmetic_cnt_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_bitwise_sisd[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_bitwise_sisd and_test d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) m n)"
  by (unfold execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_bitwise_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_cmeq_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_bitwise_simd[non_mem_expI]:
  "non_mem_exp (decode_cmeq_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_bitwise_simd Rd Rn Rm b__0 U b__1)"
  by (unfold decode_cmeq_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_bitwise_simd_def, non_mem_expI)

lemma non_mem_exp_decode_cmeq_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_bitwise_sisd[non_mem_expI]:
  "non_mem_exp (decode_cmeq_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_bitwise_sisd Rd Rn Rm b__0 U)"
  by (unfold decode_cmeq_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_bitwise_sisd_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_sisd[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_sisd comparison d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) n)"
  by (unfold execute_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_cmeq_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_simd[non_mem_expI]:
  "non_mem_exp (decode_cmeq_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_simd Rd Rn op b__0 U b__1)"
  by (unfold decode_cmeq_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_simd_def, non_mem_expI)

lemma non_mem_exp_decode_cmeq_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_sisd[non_mem_expI]:
  "non_mem_exp (decode_cmeq_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_sisd Rd Rn op b__0 U)"
  by (unfold decode_cmeq_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_sisd_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_sisd[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_sisd cmp_eq d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) m n is_unsigned)"
  by (unfold execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_cmge_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_simd[non_mem_expI]:
  "non_mem_exp (decode_cmge_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_simd Rd Rn eq Rm b__0 U b__1)"
  by (unfold decode_cmge_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_simd_def, non_mem_expI)

lemma non_mem_exp_decode_cmge_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_sisd[non_mem_expI]:
  "non_mem_exp (decode_cmge_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_sisd Rd Rn eq Rm b__0 U)"
  by (unfold decode_cmge_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_cmge_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_simd[non_mem_expI]:
  "non_mem_exp (decode_cmge_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_simd Rd Rn op b__0 U b__1)"
  by (unfold decode_cmge_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_simd_def, non_mem_expI)

lemma non_mem_exp_decode_cmge_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_sisd[non_mem_expI]:
  "non_mem_exp (decode_cmge_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_sisd Rd Rn op b__0 U)"
  by (unfold decode_cmge_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_cmgt_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_simd[non_mem_expI]:
  "non_mem_exp (decode_cmgt_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_simd Rd Rn eq Rm b__0 U b__1)"
  by (unfold decode_cmgt_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_simd_def, non_mem_expI)

lemma non_mem_exp_decode_cmgt_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_sisd[non_mem_expI]:
  "non_mem_exp (decode_cmgt_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_sisd Rd Rn eq Rm b__0 U)"
  by (unfold decode_cmgt_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_cmgt_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_simd[non_mem_expI]:
  "non_mem_exp (decode_cmgt_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_simd Rd Rn op b__0 U b__1)"
  by (unfold decode_cmgt_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_simd_def, non_mem_expI)

lemma non_mem_exp_decode_cmgt_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_sisd[non_mem_expI]:
  "non_mem_exp (decode_cmgt_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_sisd Rd Rn op b__0 U)"
  by (unfold decode_cmgt_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_cmhi_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_simd[non_mem_expI]:
  "non_mem_exp (decode_cmhi_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_simd Rd Rn eq Rm b__0 U b__1)"
  by (unfold decode_cmhi_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_simd_def, non_mem_expI)

lemma non_mem_exp_decode_cmhi_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_sisd[non_mem_expI]:
  "non_mem_exp (decode_cmhi_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_sisd Rd Rn eq Rm b__0 U)"
  by (unfold decode_cmhi_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_cmhs_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_simd[non_mem_expI]:
  "non_mem_exp (decode_cmhs_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_simd Rd Rn eq Rm b__0 U b__1)"
  by (unfold decode_cmhs_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_simd_def, non_mem_expI)

lemma non_mem_exp_decode_cmhs_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_sisd[non_mem_expI]:
  "non_mem_exp (decode_cmhs_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_sisd Rd Rn eq Rm b__0 U)"
  by (unfold decode_cmhs_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_cmle_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_simd[non_mem_expI]:
  "non_mem_exp (decode_cmle_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_simd Rd Rn op b__0 U b__1)"
  by (unfold decode_cmle_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_simd_def, non_mem_expI)

lemma non_mem_exp_decode_cmle_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_sisd[non_mem_expI]:
  "non_mem_exp (decode_cmle_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_sisd Rd Rn op b__0 U)"
  by (unfold decode_cmle_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_sisd_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_arithmetic_unary_cmp_int_lessthan_sisd[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_arithmetic_unary_cmp_int_lessthan_sisd comparison d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) n)"
  by (unfold execute_aarch64_instrs_vector_arithmetic_unary_cmp_int_lessthan_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_cmlt_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_int_lessthan_simd[non_mem_expI]:
  "non_mem_exp (decode_cmlt_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_int_lessthan_simd Rd Rn b__0 b__1)"
  by (unfold decode_cmlt_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_int_lessthan_simd_def, non_mem_expI)

lemma non_mem_exp_decode_cmlt_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_int_lessthan_sisd[non_mem_expI]:
  "non_mem_exp (decode_cmlt_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_int_lessthan_sisd Rd Rn b__0)"
  by (unfold decode_cmlt_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_int_lessthan_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_cmtst_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_bitwise_simd[non_mem_expI]:
  "non_mem_exp (decode_cmtst_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_bitwise_simd Rd Rn Rm b__0 U b__1)"
  by (unfold decode_cmtst_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_bitwise_simd_def, non_mem_expI)

lemma non_mem_exp_decode_cmtst_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_bitwise_sisd[non_mem_expI]:
  "non_mem_exp (decode_cmtst_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_bitwise_sisd Rd Rn Rm b__0 U)"
  by (unfold decode_cmtst_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_bitwise_sisd_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_arithmetic_unary_cnt[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_arithmetic_unary_cnt d (datasize :: 'datasize::len itself) elements esize n)"
  by (unfold execute_aarch64_instrs_vector_arithmetic_unary_cnt_def, non_mem_expI)

lemma non_mem_exp_decode_cnt_advsimd_aarch64_instrs_vector_arithmetic_unary_cnt[non_mem_expI]:
  "non_mem_exp (decode_cnt_advsimd_aarch64_instrs_vector_arithmetic_unary_cnt Rd Rn size__arg b__0)"
  by (unfold decode_cnt_advsimd_aarch64_instrs_vector_arithmetic_unary_cnt_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_integer_crc[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_integer_crc crc32c d m n l__155)"
  by (unfold execute_aarch64_instrs_integer_crc_def, non_mem_expI)

lemma non_mem_exp_decode_crc32_aarch64_instrs_integer_crc[non_mem_expI]:
  "non_mem_exp (decode_crc32_aarch64_instrs_integer_crc Rd Rn b__0 C Rm sf)"
  by (unfold decode_crc32_aarch64_instrs_integer_crc_def, non_mem_expI)

lemma non_mem_exp_decode_crc32c_aarch64_instrs_integer_crc[non_mem_expI]:
  "non_mem_exp (decode_crc32c_aarch64_instrs_integer_crc Rd Rn b__0 C Rm sf)"
  by (unfold decode_crc32c_aarch64_instrs_integer_crc_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_integer_conditional_select[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_integer_conditional_select condition d (datasize :: 'datasize::len itself) else_inc else_inv m n)"
  by (unfold execute_aarch64_instrs_integer_conditional_select_def, non_mem_expI)

lemma non_mem_exp_decode_csel_aarch64_instrs_integer_conditional_select[non_mem_expI]:
  "non_mem_exp (decode_csel_aarch64_instrs_integer_conditional_select Rd Rn o2 cond Rm op b__0)"
  by (unfold decode_csel_aarch64_instrs_integer_conditional_select_def, non_mem_expI)

lemma non_mem_exp_decode_csinc_aarch64_instrs_integer_conditional_select[non_mem_expI]:
  "non_mem_exp (decode_csinc_aarch64_instrs_integer_conditional_select Rd Rn o2 cond Rm op b__0)"
  by (unfold decode_csinc_aarch64_instrs_integer_conditional_select_def, non_mem_expI)

lemma non_mem_exp_decode_csinv_aarch64_instrs_integer_conditional_select[non_mem_expI]:
  "non_mem_exp (decode_csinv_aarch64_instrs_integer_conditional_select Rd Rn o2 cond Rm op b__0)"
  by (unfold decode_csinv_aarch64_instrs_integer_conditional_select_def, non_mem_expI)

lemma non_mem_exp_decode_csneg_aarch64_instrs_integer_conditional_select[non_mem_expI]:
  "non_mem_exp (decode_csneg_aarch64_instrs_integer_conditional_select Rd Rn o2 cond Rm op b__0)"
  by (unfold decode_csneg_aarch64_instrs_integer_conditional_select_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_system_exceptions_debug_exception[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_system_exceptions_debug_exception target_level)"
  by (unfold execute_aarch64_instrs_system_exceptions_debug_exception_def, non_mem_expI)

lemma non_mem_exp_decode_dcps1_aarch64_instrs_system_exceptions_debug_exception[non_mem_expI]:
  "non_mem_exp (decode_dcps1_aarch64_instrs_system_exceptions_debug_exception LL imm16)"
  by (unfold decode_dcps1_aarch64_instrs_system_exceptions_debug_exception_def, non_mem_expI)

lemma non_mem_exp_decode_dcps2_aarch64_instrs_system_exceptions_debug_exception[non_mem_expI]:
  "non_mem_exp (decode_dcps2_aarch64_instrs_system_exceptions_debug_exception LL imm16)"
  by (unfold decode_dcps2_aarch64_instrs_system_exceptions_debug_exception_def, non_mem_expI)

lemma non_mem_exp_decode_dcps3_aarch64_instrs_system_exceptions_debug_exception[non_mem_expI]:
  "non_mem_exp (decode_dcps3_aarch64_instrs_system_exceptions_debug_exception LL imm16)"
  by (unfold decode_dcps3_aarch64_instrs_system_exceptions_debug_exception_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_branch_unconditional_dret[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_branch_unconditional_dret arg0)"
  by (unfold execute_aarch64_instrs_branch_unconditional_dret_def, non_mem_expI)

lemma non_mem_exp_decode_drps_aarch64_instrs_branch_unconditional_dret[non_mem_expI]:
  "non_mem_exp (decode_drps_aarch64_instrs_branch_unconditional_dret arg0)"
  by (unfold decode_drps_aarch64_instrs_branch_unconditional_dret_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_transfer_vector_cpy_dup_sisd[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_transfer_vector_cpy_dup_sisd d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) (idxdsize :: 'idxdsize::len itself) index__arg n)"
  by (unfold execute_aarch64_instrs_vector_transfer_vector_cpy_dup_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_dup_advsimd_elt_aarch64_instrs_vector_transfer_vector_cpy_dup_simd[non_mem_expI]:
  "non_mem_exp (decode_dup_advsimd_elt_aarch64_instrs_vector_transfer_vector_cpy_dup_simd Rd Rn b__0 b__1)"
  by (unfold decode_dup_advsimd_elt_aarch64_instrs_vector_transfer_vector_cpy_dup_simd_def, non_mem_expI)

lemma non_mem_exp_decode_dup_advsimd_elt_aarch64_instrs_vector_transfer_vector_cpy_dup_sisd[non_mem_expI]:
  "non_mem_exp (decode_dup_advsimd_elt_aarch64_instrs_vector_transfer_vector_cpy_dup_sisd Rd Rn b__0)"
  by (unfold decode_dup_advsimd_elt_aarch64_instrs_vector_transfer_vector_cpy_dup_sisd_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_transfer_integer_dup[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_transfer_integer_dup d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) n)"
  by (unfold execute_aarch64_instrs_vector_transfer_integer_dup_def, non_mem_expI)

lemma non_mem_exp_decode_dup_advsimd_gen_aarch64_instrs_vector_transfer_integer_dup[non_mem_expI]:
  "non_mem_exp (decode_dup_advsimd_gen_aarch64_instrs_vector_transfer_integer_dup Rd Rn b__0 b__1)"
  by (unfold decode_dup_advsimd_gen_aarch64_instrs_vector_transfer_integer_dup_def, non_mem_expI)

lemma non_mem_exp_decode_eon_aarch64_instrs_integer_logical_shiftedreg[non_mem_expI]:
  "non_mem_exp (decode_eon_aarch64_instrs_integer_logical_shiftedreg Rd Rn imm6 Rm N shift opc b__0)"
  by (unfold decode_eon_aarch64_instrs_integer_logical_shiftedreg_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_crypto_sha3_eor3[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_crypto_sha3_eor3 a d m n)"
  by (unfold execute_aarch64_instrs_vector_crypto_sha3_eor3_def, non_mem_expI)

lemma non_mem_exp_decode_eor3_advsimd_aarch64_instrs_vector_crypto_sha3_eor3[non_mem_expI]:
  "non_mem_exp (decode_eor3_advsimd_aarch64_instrs_vector_crypto_sha3_eor3 Rd Rn Ra Rm)"
  by (unfold decode_eor3_advsimd_aarch64_instrs_vector_crypto_sha3_eor3_def, non_mem_expI)

lemma non_mem_exp_decode_eor_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_logical_bsl_eor[non_mem_expI]:
  "non_mem_exp (decode_eor_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_logical_bsl_eor Rd Rn Rm opc2 b__0)"
  by (unfold decode_eor_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_logical_bsl_eor_def, non_mem_expI)

lemma non_mem_exp_decode_eor_log_imm_aarch64_instrs_integer_logical_immediate[non_mem_expI]:
  "non_mem_exp (decode_eor_log_imm_aarch64_instrs_integer_logical_immediate Rd Rn imms immr N opc b__0)"
  by (unfold decode_eor_log_imm_aarch64_instrs_integer_logical_immediate_def, non_mem_expI)

lemma non_mem_exp_decode_eor_log_shift_aarch64_instrs_integer_logical_shiftedreg[non_mem_expI]:
  "non_mem_exp (decode_eor_log_shift_aarch64_instrs_integer_logical_shiftedreg Rd Rn imm6 Rm N shift opc b__0)"
  by (unfold decode_eor_log_shift_aarch64_instrs_integer_logical_shiftedreg_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_branch_unconditional_eret[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_branch_unconditional_eret arg0)"
  by (unfold execute_aarch64_instrs_branch_unconditional_eret_def, non_mem_expI)

lemma non_mem_exp_decode_eret_aarch64_instrs_branch_unconditional_eret[non_mem_expI]:
  "non_mem_exp (decode_eret_aarch64_instrs_branch_unconditional_eret op4 Rn M A)"
  by (unfold decode_eret_aarch64_instrs_branch_unconditional_eret_def, non_mem_expI)

lemma non_mem_exp_decode_ereta_aarch64_instrs_branch_unconditional_eret[non_mem_expI]:
  "non_mem_exp (decode_ereta_aarch64_instrs_branch_unconditional_eret op4 Rn M A)"
  by (unfold decode_ereta_aarch64_instrs_branch_unconditional_eret_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_system_hints[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_system_hints op)"
  by (cases op; simp; non_mem_expI)

lemma non_mem_exp_decode_esb_aarch64_instrs_system_hints[non_mem_expI]:
  "non_mem_exp (decode_esb_aarch64_instrs_system_hints op2 CRm)"
  by (unfold decode_esb_aarch64_instrs_system_hints_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_transfer_vector_extract[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_transfer_vector_extract d l__47 m n position)"
  by (unfold execute_aarch64_instrs_vector_transfer_vector_extract_def, non_mem_expI)

lemma non_mem_exp_decode_ext_advsimd_aarch64_instrs_vector_transfer_vector_extract[non_mem_expI]:
  "non_mem_exp (decode_ext_advsimd_aarch64_instrs_vector_transfer_vector_extract Rd Rn imm4 Rm b__0)"
  by (unfold decode_ext_advsimd_aarch64_instrs_vector_transfer_vector_extract_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_integer_ins_ext_extract_immediate[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_integer_ins_ext_extract_immediate d l__36 lsb__arg m n)"
  by (unfold execute_aarch64_instrs_integer_ins_ext_extract_immediate_def, non_mem_expI)

lemma non_mem_exp_decode_extr_aarch64_instrs_integer_ins_ext_extract_immediate[non_mem_expI]:
  "non_mem_exp (decode_extr_aarch64_instrs_integer_ins_ext_extract_immediate Rd Rn imms Rm N b__0)"
  by (unfold decode_extr_aarch64_instrs_integer_ins_ext_extract_immediate_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_arithmetic_binary_uniform_sub_fp16_sisd[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_arithmetic_binary_uniform_sub_fp16_sisd abs__arg d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) m n)"
  by (unfold execute_aarch64_instrs_vector_arithmetic_binary_uniform_sub_fp16_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_fabd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_fp16_simd[non_mem_expI]:
  "non_mem_exp (decode_fabd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_fp16_simd Rd Rn Rm U b__0)"
  by (unfold decode_fabd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_fp16_simd_def, non_mem_expI)

lemma non_mem_exp_decode_fabd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_fp16_sisd[non_mem_expI]:
  "non_mem_exp (decode_fabd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_fp16_sisd Rd Rn Rm)"
  by (unfold decode_fabd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_fp16_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_fabd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_fp_simd[non_mem_expI]:
  "non_mem_exp (decode_fabd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_fp_simd Rd Rn Rm b__0 U b__1)"
  by (unfold decode_fabd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_fp_simd_def, non_mem_expI)

lemma non_mem_exp_decode_fabd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_fp_sisd[non_mem_expI]:
  "non_mem_exp (decode_fabd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_fp_sisd Rd Rn Rm b__0)"
  by (unfold decode_fabd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_fp_sisd_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_arithmetic_unary_diff_neg_fp16[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_arithmetic_unary_diff_neg_fp16 d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) n neg)"
  by (unfold execute_aarch64_instrs_vector_arithmetic_unary_diff_neg_fp16_def, non_mem_expI)

lemma non_mem_exp_decode_fabs_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_float[non_mem_expI]:
  "non_mem_exp (decode_fabs_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_float Rd Rn b__0 U b__1)"
  by (unfold decode_fabs_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_float_def, non_mem_expI)

lemma non_mem_exp_decode_fabs_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_fp16[non_mem_expI]:
  "non_mem_exp (decode_fabs_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_fp16 Rd Rn U b__0)"
  by (unfold decode_fabs_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_fp16_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_float_arithmetic_unary[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_float_arithmetic_unary d (datasize :: 'datasize::len itself) fpop n)"
  by (unfold execute_aarch64_instrs_float_arithmetic_unary_def, non_mem_expI)

lemma non_mem_exp_decode_fabs_float_aarch64_instrs_float_arithmetic_unary[non_mem_expI]:
  "non_mem_exp (decode_fabs_float_aarch64_instrs_float_arithmetic_unary Rd Rn opc b__0)"
  by (unfold decode_fabs_float_aarch64_instrs_float_arithmetic_unary_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_sisd[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_sisd abs__arg cmp d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) m n)"
  by (unfold execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_facge_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_simd[non_mem_expI]:
  "non_mem_exp (decode_facge_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_simd Rd Rn ac Rm E U b__0)"
  by (unfold decode_facge_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_simd_def, non_mem_expI)

lemma non_mem_exp_decode_facge_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_sisd[non_mem_expI]:
  "non_mem_exp (decode_facge_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_sisd Rd Rn ac Rm E U)"
  by (unfold decode_facge_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_facge_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp_simd[non_mem_expI]:
  "non_mem_exp (decode_facge_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp_simd Rd Rn ac Rm b__0 E U b__1)"
  by (unfold decode_facge_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp_simd_def, non_mem_expI)

lemma non_mem_exp_decode_facge_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp_sisd[non_mem_expI]:
  "non_mem_exp (decode_facge_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp_sisd Rd Rn ac Rm b__0 E U)"
  by (unfold decode_facge_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_facgt_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_simd[non_mem_expI]:
  "non_mem_exp (decode_facgt_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_simd Rd Rn ac Rm E U b__0)"
  by (unfold decode_facgt_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_simd_def, non_mem_expI)

lemma non_mem_exp_decode_facgt_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_sisd[non_mem_expI]:
  "non_mem_exp (decode_facgt_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_sisd Rd Rn ac Rm E U)"
  by (unfold decode_facgt_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_facgt_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp_simd[non_mem_expI]:
  "non_mem_exp (decode_facgt_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp_simd Rd Rn ac Rm b__0 E U b__1)"
  by (unfold decode_facgt_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp_simd_def, non_mem_expI)

lemma non_mem_exp_decode_facgt_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp_sisd[non_mem_expI]:
  "non_mem_exp (decode_facgt_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp_sisd Rd Rn ac Rm b__0 E U)"
  by (unfold decode_facgt_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp_sisd_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_arithmetic_binary_uniform_add_fp16[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_arithmetic_binary_uniform_add_fp16 d l__163 elements (esize :: 'esize::len itself) m n pair)"
  by (unfold execute_aarch64_instrs_vector_arithmetic_binary_uniform_add_fp16_def, non_mem_expI)

lemma non_mem_exp_decode_fadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_fp[non_mem_expI]:
  "non_mem_exp (decode_fadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_fp Rd Rn Rm b__0 U b__1)"
  by (unfold decode_fadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_fp_def, non_mem_expI)

lemma non_mem_exp_decode_fadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_fp16[non_mem_expI]:
  "non_mem_exp (decode_fadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_fp16 Rd Rn Rm U b__0)"
  by (unfold decode_fadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_fp16_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_float_arithmetic_add_sub[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_float_arithmetic_add_sub d (datasize :: 'datasize::len itself) m n sub_op)"
  by (unfold execute_aarch64_instrs_float_arithmetic_add_sub_def, non_mem_expI)

lemma non_mem_exp_decode_fadd_float_aarch64_instrs_float_arithmetic_add_sub[non_mem_expI]:
  "non_mem_exp (decode_fadd_float_aarch64_instrs_float_arithmetic_add_sub Rd Rn op Rm b__0)"
  by (unfold decode_fadd_float_aarch64_instrs_float_arithmetic_add_sub_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_reduce_fp16_add_sisd[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_reduce_fp16_add_sisd d (datasize :: 'datasize::len itself) (esize :: 'esize::len itself) n op)"
  by (unfold execute_aarch64_instrs_vector_reduce_fp16_add_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_faddp_advsimd_pair_aarch64_instrs_vector_reduce_fp16_add_sisd[non_mem_expI]:
  "non_mem_exp (decode_faddp_advsimd_pair_aarch64_instrs_vector_reduce_fp16_add_sisd Rd Rn sz)"
  by (unfold decode_faddp_advsimd_pair_aarch64_instrs_vector_reduce_fp16_add_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_faddp_advsimd_pair_aarch64_instrs_vector_reduce_fp_add_sisd[non_mem_expI]:
  "non_mem_exp (decode_faddp_advsimd_pair_aarch64_instrs_vector_reduce_fp_add_sisd Rd Rn b__0)"
  by (unfold decode_faddp_advsimd_pair_aarch64_instrs_vector_reduce_fp_add_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_faddp_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_add_fp[non_mem_expI]:
  "non_mem_exp (decode_faddp_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_add_fp Rd Rn Rm b__0 U b__1)"
  by (unfold decode_faddp_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_add_fp_def, non_mem_expI)

lemma non_mem_exp_decode_faddp_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_add_fp16[non_mem_expI]:
  "non_mem_exp (decode_faddp_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_add_fp16 Rd Rn Rm U b__0)"
  by (unfold decode_faddp_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_add_fp16_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_float_compare_cond[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_float_compare_cond condition (datasize :: 'datasize::len itself) flags__arg m n signal_all_nans)"
  by (unfold execute_aarch64_instrs_float_compare_cond_def, non_mem_expI)

lemma non_mem_exp_decode_fccmp_float_aarch64_instrs_float_compare_cond[non_mem_expI]:
  "non_mem_exp (decode_fccmp_float_aarch64_instrs_float_compare_cond nzcv op Rn cond Rm b__0)"
  by (unfold decode_fccmp_float_aarch64_instrs_float_compare_cond_def, non_mem_expI)

lemma non_mem_exp_decode_fccmpe_float_aarch64_instrs_float_compare_cond[non_mem_expI]:
  "non_mem_exp (decode_fccmpe_float_aarch64_instrs_float_compare_cond nzcv op Rn cond Rm b__0)"
  by (unfold decode_fccmpe_float_aarch64_instrs_float_compare_cond_def, non_mem_expI)

lemma non_mem_exp_decode_fcmeq_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_simd[non_mem_expI]:
  "non_mem_exp (decode_fcmeq_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_simd Rd Rn ac Rm E U b__0)"
  by (unfold decode_fcmeq_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_simd_def, non_mem_expI)

lemma non_mem_exp_decode_fcmeq_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_sisd[non_mem_expI]:
  "non_mem_exp (decode_fcmeq_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_sisd Rd Rn ac Rm E U)"
  by (unfold decode_fcmeq_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_fcmeq_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp_simd[non_mem_expI]:
  "non_mem_exp (decode_fcmeq_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp_simd Rd Rn ac Rm b__0 E U b__1)"
  by (unfold decode_fcmeq_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp_simd_def, non_mem_expI)

lemma non_mem_exp_decode_fcmeq_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp_sisd[non_mem_expI]:
  "non_mem_exp (decode_fcmeq_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp_sisd Rd Rn ac Rm b__0 E U)"
  by (unfold decode_fcmeq_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp_sisd_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_sisd[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_sisd comparison d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) n)"
  by (unfold execute_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_fcmeq_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_float_bulk_simd[non_mem_expI]:
  "non_mem_exp (decode_fcmeq_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_float_bulk_simd Rd Rn op b__0 U b__1)"
  by (unfold decode_fcmeq_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_float_bulk_simd_def, non_mem_expI)

lemma non_mem_exp_decode_fcmeq_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_float_bulk_sisd[non_mem_expI]:
  "non_mem_exp (decode_fcmeq_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_float_bulk_sisd Rd Rn op b__0 U)"
  by (unfold decode_fcmeq_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_float_bulk_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_fcmeq_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_simd[non_mem_expI]:
  "non_mem_exp (decode_fcmeq_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_simd Rd Rn op U b__0)"
  by (unfold decode_fcmeq_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_simd_def, non_mem_expI)

lemma non_mem_exp_decode_fcmeq_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_sisd[non_mem_expI]:
  "non_mem_exp (decode_fcmeq_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_sisd Rd Rn op U)"
  by (unfold decode_fcmeq_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_fcmge_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_simd[non_mem_expI]:
  "non_mem_exp (decode_fcmge_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_simd Rd Rn ac Rm E U b__0)"
  by (unfold decode_fcmge_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_simd_def, non_mem_expI)

lemma non_mem_exp_decode_fcmge_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_sisd[non_mem_expI]:
  "non_mem_exp (decode_fcmge_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_sisd Rd Rn ac Rm E U)"
  by (unfold decode_fcmge_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_fcmge_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp_simd[non_mem_expI]:
  "non_mem_exp (decode_fcmge_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp_simd Rd Rn ac Rm b__0 E U b__1)"
  by (unfold decode_fcmge_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp_simd_def, non_mem_expI)

lemma non_mem_exp_decode_fcmge_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp_sisd[non_mem_expI]:
  "non_mem_exp (decode_fcmge_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp_sisd Rd Rn ac Rm b__0 E U)"
  by (unfold decode_fcmge_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_fcmge_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_float_bulk_simd[non_mem_expI]:
  "non_mem_exp (decode_fcmge_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_float_bulk_simd Rd Rn op b__0 U b__1)"
  by (unfold decode_fcmge_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_float_bulk_simd_def, non_mem_expI)

lemma non_mem_exp_decode_fcmge_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_float_bulk_sisd[non_mem_expI]:
  "non_mem_exp (decode_fcmge_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_float_bulk_sisd Rd Rn op b__0 U)"
  by (unfold decode_fcmge_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_float_bulk_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_fcmge_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_simd[non_mem_expI]:
  "non_mem_exp (decode_fcmge_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_simd Rd Rn op U b__0)"
  by (unfold decode_fcmge_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_simd_def, non_mem_expI)

lemma non_mem_exp_decode_fcmge_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_sisd[non_mem_expI]:
  "non_mem_exp (decode_fcmge_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_sisd Rd Rn op U)"
  by (unfold decode_fcmge_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_fcmgt_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_simd[non_mem_expI]:
  "non_mem_exp (decode_fcmgt_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_simd Rd Rn ac Rm E U b__0)"
  by (unfold decode_fcmgt_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_simd_def, non_mem_expI)

lemma non_mem_exp_decode_fcmgt_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_sisd[non_mem_expI]:
  "non_mem_exp (decode_fcmgt_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_sisd Rd Rn ac Rm E U)"
  by (unfold decode_fcmgt_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_fcmgt_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp_simd[non_mem_expI]:
  "non_mem_exp (decode_fcmgt_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp_simd Rd Rn ac Rm b__0 E U b__1)"
  by (unfold decode_fcmgt_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp_simd_def, non_mem_expI)

lemma non_mem_exp_decode_fcmgt_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp_sisd[non_mem_expI]:
  "non_mem_exp (decode_fcmgt_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp_sisd Rd Rn ac Rm b__0 E U)"
  by (unfold decode_fcmgt_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_fcmgt_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_float_bulk_simd[non_mem_expI]:
  "non_mem_exp (decode_fcmgt_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_float_bulk_simd Rd Rn op b__0 U b__1)"
  by (unfold decode_fcmgt_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_float_bulk_simd_def, non_mem_expI)

lemma non_mem_exp_decode_fcmgt_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_float_bulk_sisd[non_mem_expI]:
  "non_mem_exp (decode_fcmgt_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_float_bulk_sisd Rd Rn op b__0 U)"
  by (unfold decode_fcmgt_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_float_bulk_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_fcmgt_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_simd[non_mem_expI]:
  "non_mem_exp (decode_fcmgt_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_simd Rd Rn op U b__0)"
  by (unfold decode_fcmgt_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_simd_def, non_mem_expI)

lemma non_mem_exp_decode_fcmgt_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_sisd[non_mem_expI]:
  "non_mem_exp (decode_fcmgt_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_sisd Rd Rn op U)"
  by (unfold decode_fcmgt_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_fcmle_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_float_bulk_simd[non_mem_expI]:
  "non_mem_exp (decode_fcmle_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_float_bulk_simd Rd Rn op b__0 U b__1)"
  by (unfold decode_fcmle_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_float_bulk_simd_def, non_mem_expI)

lemma non_mem_exp_decode_fcmle_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_float_bulk_sisd[non_mem_expI]:
  "non_mem_exp (decode_fcmle_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_float_bulk_sisd Rd Rn op b__0 U)"
  by (unfold decode_fcmle_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_float_bulk_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_fcmle_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_simd[non_mem_expI]:
  "non_mem_exp (decode_fcmle_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_simd Rd Rn op U b__0)"
  by (unfold decode_fcmle_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_simd_def, non_mem_expI)

lemma non_mem_exp_decode_fcmle_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_sisd[non_mem_expI]:
  "non_mem_exp (decode_fcmle_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_sisd Rd Rn op U)"
  by (unfold decode_fcmle_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_sisd_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_lessthan_sisd[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_lessthan_sisd comparison d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) n)"
  by (unfold execute_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_lessthan_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_fcmlt_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_float_lessthan_simd[non_mem_expI]:
  "non_mem_exp (decode_fcmlt_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_float_lessthan_simd Rd Rn b__0 b__1)"
  by (unfold decode_fcmlt_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_float_lessthan_simd_def, non_mem_expI)

lemma non_mem_exp_decode_fcmlt_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_float_lessthan_sisd[non_mem_expI]:
  "non_mem_exp (decode_fcmlt_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_float_lessthan_sisd Rd Rn b__0)"
  by (unfold decode_fcmlt_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_float_lessthan_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_fcmlt_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_lessthan_simd[non_mem_expI]:
  "non_mem_exp (decode_fcmlt_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_lessthan_simd Rd Rn b__0)"
  by (unfold decode_fcmlt_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_lessthan_simd_def, non_mem_expI)

lemma non_mem_exp_decode_fcmlt_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_lessthan_sisd[non_mem_expI]:
  "non_mem_exp (decode_fcmlt_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_lessthan_sisd Rd Rn)"
  by (unfold decode_fcmlt_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_lessthan_sisd_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_float_compare_uncond[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_float_compare_uncond cmp_with_zero (datasize :: 'datasize::len itself) m n signal_all_nans)"
  by (unfold execute_aarch64_instrs_float_compare_uncond_def, non_mem_expI)

lemma non_mem_exp_decode_fcmp_float_aarch64_instrs_float_compare_uncond[non_mem_expI]:
  "non_mem_exp (decode_fcmp_float_aarch64_instrs_float_compare_uncond opc Rn Rm b__0)"
  by (unfold decode_fcmp_float_aarch64_instrs_float_compare_uncond_def, non_mem_expI)

lemma non_mem_exp_decode_fcmpe_float_aarch64_instrs_float_compare_uncond[non_mem_expI]:
  "non_mem_exp (decode_fcmpe_float_aarch64_instrs_float_compare_uncond opc Rn Rm b__0)"
  by (unfold decode_fcmpe_float_aarch64_instrs_float_compare_uncond_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_float_move_fp_select[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_float_move_fp_select condition d (datasize :: 'datasize::len itself) m n)"
  by (unfold execute_aarch64_instrs_float_move_fp_select_def, non_mem_expI)

lemma non_mem_exp_decode_fcsel_float_aarch64_instrs_float_move_fp_select[non_mem_expI]:
  "non_mem_exp (decode_fcsel_float_aarch64_instrs_float_move_fp_select Rd Rn cond Rm b__0)"
  by (unfold decode_fcsel_float_aarch64_instrs_float_move_fp_select_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_float_convert_fp[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_float_convert_fp d (dstsize :: 'dstsize::len itself) n (srcsize :: 'srcsize::len itself))"
  by (unfold execute_aarch64_instrs_float_convert_fp_def, non_mem_expI)

lemma non_mem_exp_decode_fcvt_float_aarch64_instrs_float_convert_fp[non_mem_expI]:
  "non_mem_exp (decode_fcvt_float_aarch64_instrs_float_convert_fp Rd Rn b__0 b__1)"
  by (unfold decode_fcvt_float_aarch64_instrs_float_convert_fp_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_tieaway_sisd[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_tieaway_sisd d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) n rounding is_unsigned)"
  by (unfold execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_tieaway_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_fcvtas_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_tieaway_simd[non_mem_expI]:
  "non_mem_exp (decode_fcvtas_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_tieaway_simd Rd Rn b__0 U b__1)"
  by (unfold decode_fcvtas_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_tieaway_simd_def, non_mem_expI)

lemma non_mem_exp_decode_fcvtas_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_tieaway_sisd[non_mem_expI]:
  "non_mem_exp (decode_fcvtas_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_tieaway_sisd Rd Rn b__0 U)"
  by (unfold decode_fcvtas_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_tieaway_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_fcvtas_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_tieaway_simd[non_mem_expI]:
  "non_mem_exp (decode_fcvtas_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_tieaway_simd Rd Rn U b__0)"
  by (unfold decode_fcvtas_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_tieaway_simd_def, non_mem_expI)

lemma non_mem_exp_decode_fcvtas_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_tieaway_sisd[non_mem_expI]:
  "non_mem_exp (decode_fcvtas_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_tieaway_sisd Rd Rn U)"
  by (unfold decode_fcvtas_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_tieaway_sisd_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_float_convert_int[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_float_convert_int d (fltsize :: 'fltsize::len itself) (intsize :: 'intsize::len itself) n op part rounding is_unsigned)"
  by (unfold execute_aarch64_instrs_float_convert_int_def, non_mem_expI)

lemma non_mem_exp_decode_fcvtas_float_aarch64_instrs_float_convert_int[non_mem_expI]:
  "non_mem_exp (decode_fcvtas_float_aarch64_instrs_float_convert_int Rd Rn opcode rmode ftype b__0)"
  by (unfold decode_fcvtas_float_aarch64_instrs_float_convert_int_def, non_mem_expI)

lemma non_mem_exp_decode_fcvtau_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_tieaway_simd[non_mem_expI]:
  "non_mem_exp (decode_fcvtau_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_tieaway_simd Rd Rn b__0 U b__1)"
  by (unfold decode_fcvtau_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_tieaway_simd_def, non_mem_expI)

lemma non_mem_exp_decode_fcvtau_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_tieaway_sisd[non_mem_expI]:
  "non_mem_exp (decode_fcvtau_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_tieaway_sisd Rd Rn b__0 U)"
  by (unfold decode_fcvtau_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_tieaway_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_fcvtau_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_tieaway_simd[non_mem_expI]:
  "non_mem_exp (decode_fcvtau_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_tieaway_simd Rd Rn U b__0)"
  by (unfold decode_fcvtau_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_tieaway_simd_def, non_mem_expI)

lemma non_mem_exp_decode_fcvtau_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_tieaway_sisd[non_mem_expI]:
  "non_mem_exp (decode_fcvtau_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_tieaway_sisd Rd Rn U)"
  by (unfold decode_fcvtau_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_tieaway_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_fcvtau_float_aarch64_instrs_float_convert_int[non_mem_expI]:
  "non_mem_exp (decode_fcvtau_float_aarch64_instrs_float_convert_int Rd Rn opcode rmode ftype b__0)"
  by (unfold decode_fcvtau_float_aarch64_instrs_float_convert_int_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_arithmetic_unary_float_widen[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_arithmetic_unary_float_widen d datasize elements l__177 n part)"
  by (unfold execute_aarch64_instrs_vector_arithmetic_unary_float_widen_def, non_mem_expI)

lemma non_mem_exp_decode_fcvtl_advsimd_aarch64_instrs_vector_arithmetic_unary_float_widen[non_mem_expI]:
  "non_mem_exp (decode_fcvtl_advsimd_aarch64_instrs_vector_arithmetic_unary_float_widen Rd Rn b__0 Q)"
  by (unfold decode_fcvtl_advsimd_aarch64_instrs_vector_arithmetic_unary_float_widen_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) n rounding is_unsigned)"
  by (unfold execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_fcvtms_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd[non_mem_expI]:
  "non_mem_exp (decode_fcvtms_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd Rd Rn o1 b__0 o2 U b__1)"
  by (unfold decode_fcvtms_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd_def, non_mem_expI)

lemma non_mem_exp_decode_fcvtms_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd[non_mem_expI]:
  "non_mem_exp (decode_fcvtms_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd Rd Rn o1 b__0 o2 U)"
  by (unfold decode_fcvtms_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_fcvtms_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd[non_mem_expI]:
  "non_mem_exp (decode_fcvtms_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd Rd Rn o1 o2 U b__0)"
  by (unfold decode_fcvtms_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd_def, non_mem_expI)

lemma non_mem_exp_decode_fcvtms_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd[non_mem_expI]:
  "non_mem_exp (decode_fcvtms_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd Rd Rn o1 o2 U)"
  by (unfold decode_fcvtms_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_fcvtms_float_aarch64_instrs_float_convert_int[non_mem_expI]:
  "non_mem_exp (decode_fcvtms_float_aarch64_instrs_float_convert_int Rd Rn opcode rmode ftype b__0)"
  by (unfold decode_fcvtms_float_aarch64_instrs_float_convert_int_def, non_mem_expI)

lemma non_mem_exp_decode_fcvtmu_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd[non_mem_expI]:
  "non_mem_exp (decode_fcvtmu_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd Rd Rn o1 b__0 o2 U b__1)"
  by (unfold decode_fcvtmu_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd_def, non_mem_expI)

lemma non_mem_exp_decode_fcvtmu_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd[non_mem_expI]:
  "non_mem_exp (decode_fcvtmu_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd Rd Rn o1 b__0 o2 U)"
  by (unfold decode_fcvtmu_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_fcvtmu_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd[non_mem_expI]:
  "non_mem_exp (decode_fcvtmu_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd Rd Rn o1 o2 U b__0)"
  by (unfold decode_fcvtmu_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd_def, non_mem_expI)

lemma non_mem_exp_decode_fcvtmu_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd[non_mem_expI]:
  "non_mem_exp (decode_fcvtmu_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd Rd Rn o1 o2 U)"
  by (unfold decode_fcvtmu_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_fcvtmu_float_aarch64_instrs_float_convert_int[non_mem_expI]:
  "non_mem_exp (decode_fcvtmu_float_aarch64_instrs_float_convert_int Rd Rn opcode rmode ftype b__0)"
  by (unfold decode_fcvtmu_float_aarch64_instrs_float_convert_int_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_arithmetic_unary_float_narrow[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_arithmetic_unary_float_narrow d datasize elements l__202 n part)"
  by (unfold execute_aarch64_instrs_vector_arithmetic_unary_float_narrow_def, non_mem_expI)

lemma non_mem_exp_decode_fcvtn_advsimd_aarch64_instrs_vector_arithmetic_unary_float_narrow[non_mem_expI]:
  "non_mem_exp (decode_fcvtn_advsimd_aarch64_instrs_vector_arithmetic_unary_float_narrow Rd Rn b__0 Q)"
  by (unfold decode_fcvtn_advsimd_aarch64_instrs_vector_arithmetic_unary_float_narrow_def, non_mem_expI)

lemma non_mem_exp_decode_fcvtns_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd[non_mem_expI]:
  "non_mem_exp (decode_fcvtns_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd Rd Rn o1 b__0 o2 U b__1)"
  by (unfold decode_fcvtns_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd_def, non_mem_expI)

lemma non_mem_exp_decode_fcvtns_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd[non_mem_expI]:
  "non_mem_exp (decode_fcvtns_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd Rd Rn o1 b__0 o2 U)"
  by (unfold decode_fcvtns_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_fcvtns_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd[non_mem_expI]:
  "non_mem_exp (decode_fcvtns_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd Rd Rn o1 o2 U b__0)"
  by (unfold decode_fcvtns_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd_def, non_mem_expI)

lemma non_mem_exp_decode_fcvtns_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd[non_mem_expI]:
  "non_mem_exp (decode_fcvtns_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd Rd Rn o1 o2 U)"
  by (unfold decode_fcvtns_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_fcvtns_float_aarch64_instrs_float_convert_int[non_mem_expI]:
  "non_mem_exp (decode_fcvtns_float_aarch64_instrs_float_convert_int Rd Rn opcode rmode ftype b__0)"
  by (unfold decode_fcvtns_float_aarch64_instrs_float_convert_int_def, non_mem_expI)

lemma non_mem_exp_decode_fcvtnu_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd[non_mem_expI]:
  "non_mem_exp (decode_fcvtnu_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd Rd Rn o1 b__0 o2 U b__1)"
  by (unfold decode_fcvtnu_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd_def, non_mem_expI)

lemma non_mem_exp_decode_fcvtnu_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd[non_mem_expI]:
  "non_mem_exp (decode_fcvtnu_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd Rd Rn o1 b__0 o2 U)"
  by (unfold decode_fcvtnu_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_fcvtnu_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd[non_mem_expI]:
  "non_mem_exp (decode_fcvtnu_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd Rd Rn o1 o2 U b__0)"
  by (unfold decode_fcvtnu_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd_def, non_mem_expI)

lemma non_mem_exp_decode_fcvtnu_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd[non_mem_expI]:
  "non_mem_exp (decode_fcvtnu_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd Rd Rn o1 o2 U)"
  by (unfold decode_fcvtnu_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_fcvtnu_float_aarch64_instrs_float_convert_int[non_mem_expI]:
  "non_mem_exp (decode_fcvtnu_float_aarch64_instrs_float_convert_int Rd Rn opcode rmode ftype b__0)"
  by (unfold decode_fcvtnu_float_aarch64_instrs_float_convert_int_def, non_mem_expI)

lemma non_mem_exp_decode_fcvtps_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd[non_mem_expI]:
  "non_mem_exp (decode_fcvtps_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd Rd Rn o1 b__0 o2 U b__1)"
  by (unfold decode_fcvtps_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd_def, non_mem_expI)

lemma non_mem_exp_decode_fcvtps_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd[non_mem_expI]:
  "non_mem_exp (decode_fcvtps_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd Rd Rn o1 b__0 o2 U)"
  by (unfold decode_fcvtps_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_fcvtps_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd[non_mem_expI]:
  "non_mem_exp (decode_fcvtps_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd Rd Rn o1 o2 U b__0)"
  by (unfold decode_fcvtps_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd_def, non_mem_expI)

lemma non_mem_exp_decode_fcvtps_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd[non_mem_expI]:
  "non_mem_exp (decode_fcvtps_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd Rd Rn o1 o2 U)"
  by (unfold decode_fcvtps_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_fcvtps_float_aarch64_instrs_float_convert_int[non_mem_expI]:
  "non_mem_exp (decode_fcvtps_float_aarch64_instrs_float_convert_int Rd Rn opcode rmode ftype b__0)"
  by (unfold decode_fcvtps_float_aarch64_instrs_float_convert_int_def, non_mem_expI)

lemma non_mem_exp_decode_fcvtpu_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd[non_mem_expI]:
  "non_mem_exp (decode_fcvtpu_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd Rd Rn o1 b__0 o2 U b__1)"
  by (unfold decode_fcvtpu_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd_def, non_mem_expI)

lemma non_mem_exp_decode_fcvtpu_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd[non_mem_expI]:
  "non_mem_exp (decode_fcvtpu_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd Rd Rn o1 b__0 o2 U)"
  by (unfold decode_fcvtpu_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_fcvtpu_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd[non_mem_expI]:
  "non_mem_exp (decode_fcvtpu_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd Rd Rn o1 o2 U b__0)"
  by (unfold decode_fcvtpu_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd_def, non_mem_expI)

lemma non_mem_exp_decode_fcvtpu_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd[non_mem_expI]:
  "non_mem_exp (decode_fcvtpu_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd Rd Rn o1 o2 U)"
  by (unfold decode_fcvtpu_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_fcvtpu_float_aarch64_instrs_float_convert_int[non_mem_expI]:
  "non_mem_exp (decode_fcvtpu_float_aarch64_instrs_float_convert_int Rd Rn opcode rmode ftype b__0)"
  by (unfold decode_fcvtpu_float_aarch64_instrs_float_convert_int_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_arithmetic_unary_float_xtn_sisd[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_arithmetic_unary_float_xtn_sisd d l__53 elements esize n part)"
  by (unfold execute_aarch64_instrs_vector_arithmetic_unary_float_xtn_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_fcvtxn_advsimd_aarch64_instrs_vector_arithmetic_unary_float_xtn_simd[non_mem_expI]:
  "non_mem_exp (decode_fcvtxn_advsimd_aarch64_instrs_vector_arithmetic_unary_float_xtn_simd Rd Rn sz Q)"
  by (unfold decode_fcvtxn_advsimd_aarch64_instrs_vector_arithmetic_unary_float_xtn_simd_def, non_mem_expI)

lemma non_mem_exp_decode_fcvtxn_advsimd_aarch64_instrs_vector_arithmetic_unary_float_xtn_sisd[non_mem_expI]:
  "non_mem_exp (decode_fcvtxn_advsimd_aarch64_instrs_vector_arithmetic_unary_float_xtn_sisd Rd Rn sz)"
  by (unfold decode_fcvtxn_advsimd_aarch64_instrs_vector_arithmetic_unary_float_xtn_sisd_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_shift_conv_float_sisd[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_shift_conv_float_sisd d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) fracbits n rounding is_unsigned)"
  by (unfold execute_aarch64_instrs_vector_shift_conv_float_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_fcvtzs_advsimd_fix_aarch64_instrs_vector_shift_conv_float_simd[non_mem_expI]:
  "non_mem_exp (decode_fcvtzs_advsimd_fix_aarch64_instrs_vector_shift_conv_float_simd Rd Rn immb b__0 U b__1)"
  by (unfold decode_fcvtzs_advsimd_fix_aarch64_instrs_vector_shift_conv_float_simd_def, non_mem_expI)

lemma non_mem_exp_decode_fcvtzs_advsimd_fix_aarch64_instrs_vector_shift_conv_float_sisd[non_mem_expI]:
  "non_mem_exp (decode_fcvtzs_advsimd_fix_aarch64_instrs_vector_shift_conv_float_sisd Rd Rn immb b__0 U)"
  by (unfold decode_fcvtzs_advsimd_fix_aarch64_instrs_vector_shift_conv_float_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_fcvtzs_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd[non_mem_expI]:
  "non_mem_exp (decode_fcvtzs_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd Rd Rn o1 b__0 o2 U b__1)"
  by (unfold decode_fcvtzs_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd_def, non_mem_expI)

lemma non_mem_exp_decode_fcvtzs_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd[non_mem_expI]:
  "non_mem_exp (decode_fcvtzs_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd Rd Rn o1 b__0 o2 U)"
  by (unfold decode_fcvtzs_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_fcvtzs_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd[non_mem_expI]:
  "non_mem_exp (decode_fcvtzs_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd Rd Rn o1 o2 U b__0)"
  by (unfold decode_fcvtzs_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd_def, non_mem_expI)

lemma non_mem_exp_decode_fcvtzs_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd[non_mem_expI]:
  "non_mem_exp (decode_fcvtzs_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd Rd Rn o1 o2 U)"
  by (unfold decode_fcvtzs_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_float_convert_fix[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_float_convert_fix d (fltsize :: 'fltsize::len itself) fracbits (intsize :: 'intsize::len itself) n op rounding is_unsigned)"
  by (unfold execute_aarch64_instrs_float_convert_fix_def, non_mem_expI)

lemma non_mem_exp_decode_fcvtzs_float_fix_aarch64_instrs_float_convert_fix[non_mem_expI]:
  "non_mem_exp (decode_fcvtzs_float_fix_aarch64_instrs_float_convert_fix Rd Rn scale opcode rmode b__0 b__1)"
  by (unfold decode_fcvtzs_float_fix_aarch64_instrs_float_convert_fix_def, non_mem_expI)

lemma non_mem_exp_decode_fcvtzs_float_int_aarch64_instrs_float_convert_int[non_mem_expI]:
  "non_mem_exp (decode_fcvtzs_float_int_aarch64_instrs_float_convert_int Rd Rn opcode rmode ftype b__0)"
  by (unfold decode_fcvtzs_float_int_aarch64_instrs_float_convert_int_def, non_mem_expI)

lemma non_mem_exp_decode_fcvtzu_advsimd_fix_aarch64_instrs_vector_shift_conv_float_simd[non_mem_expI]:
  "non_mem_exp (decode_fcvtzu_advsimd_fix_aarch64_instrs_vector_shift_conv_float_simd Rd Rn immb b__0 U b__1)"
  by (unfold decode_fcvtzu_advsimd_fix_aarch64_instrs_vector_shift_conv_float_simd_def, non_mem_expI)

lemma non_mem_exp_decode_fcvtzu_advsimd_fix_aarch64_instrs_vector_shift_conv_float_sisd[non_mem_expI]:
  "non_mem_exp (decode_fcvtzu_advsimd_fix_aarch64_instrs_vector_shift_conv_float_sisd Rd Rn immb b__0 U)"
  by (unfold decode_fcvtzu_advsimd_fix_aarch64_instrs_vector_shift_conv_float_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_fcvtzu_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd[non_mem_expI]:
  "non_mem_exp (decode_fcvtzu_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd Rd Rn o1 b__0 o2 U b__1)"
  by (unfold decode_fcvtzu_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd_def, non_mem_expI)

lemma non_mem_exp_decode_fcvtzu_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd[non_mem_expI]:
  "non_mem_exp (decode_fcvtzu_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd Rd Rn o1 b__0 o2 U)"
  by (unfold decode_fcvtzu_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_fcvtzu_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd[non_mem_expI]:
  "non_mem_exp (decode_fcvtzu_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd Rd Rn o1 o2 U b__0)"
  by (unfold decode_fcvtzu_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd_def, non_mem_expI)

lemma non_mem_exp_decode_fcvtzu_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd[non_mem_expI]:
  "non_mem_exp (decode_fcvtzu_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd Rd Rn o1 o2 U)"
  by (unfold decode_fcvtzu_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_fcvtzu_float_fix_aarch64_instrs_float_convert_fix[non_mem_expI]:
  "non_mem_exp (decode_fcvtzu_float_fix_aarch64_instrs_float_convert_fix Rd Rn scale opcode rmode b__0 b__1)"
  by (unfold decode_fcvtzu_float_fix_aarch64_instrs_float_convert_fix_def, non_mem_expI)

lemma non_mem_exp_decode_fcvtzu_float_int_aarch64_instrs_float_convert_int[non_mem_expI]:
  "non_mem_exp (decode_fcvtzu_float_int_aarch64_instrs_float_convert_int Rd Rn opcode rmode ftype b__0)"
  by (unfold decode_fcvtzu_float_int_aarch64_instrs_float_convert_int_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_arithmetic_binary_uniform_div_fp16[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_arithmetic_binary_uniform_div_fp16 d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) m n)"
  by (unfold execute_aarch64_instrs_vector_arithmetic_binary_uniform_div_fp16_def, non_mem_expI)

lemma non_mem_exp_decode_fdiv_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_div[non_mem_expI]:
  "non_mem_exp (decode_fdiv_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_div Rd Rn Rm b__0 b__1)"
  by (unfold decode_fdiv_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_div_def, non_mem_expI)

lemma non_mem_exp_decode_fdiv_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_div_fp16[non_mem_expI]:
  "non_mem_exp (decode_fdiv_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_div_fp16 Rd Rn Rm b__0)"
  by (unfold decode_fdiv_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_div_fp16_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_float_arithmetic_div[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_float_arithmetic_div d (datasize :: 'datasize::len itself) m n)"
  by (unfold execute_aarch64_instrs_float_arithmetic_div_def, non_mem_expI)

lemma non_mem_exp_decode_fdiv_float_aarch64_instrs_float_arithmetic_div[non_mem_expI]:
  "non_mem_exp (decode_fdiv_float_aarch64_instrs_float_arithmetic_div Rd Rn Rm b__0)"
  by (unfold decode_fdiv_float_aarch64_instrs_float_arithmetic_div_def, non_mem_expI)

lemma non_mem_exp_decode_fjcvtzs_aarch64_instrs_float_convert_int[non_mem_expI]:
  "non_mem_exp (decode_fjcvtzs_aarch64_instrs_float_convert_int Rd Rn opcode rmode ftype b__0)"
  by (unfold decode_fjcvtzs_aarch64_instrs_float_convert_int_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_float_arithmetic_mul_add_sub[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_float_arithmetic_mul_add_sub a d (datasize :: 'datasize::len itself) m n op1_neg opa_neg)"
  by (unfold execute_aarch64_instrs_float_arithmetic_mul_add_sub_def, non_mem_expI)

lemma non_mem_exp_decode_fmadd_float_aarch64_instrs_float_arithmetic_mul_add_sub[non_mem_expI]:
  "non_mem_exp (decode_fmadd_float_aarch64_instrs_float_arithmetic_mul_add_sub Rd Rn Ra o0 Rm o1 b__0)"
  by (unfold decode_fmadd_float_aarch64_instrs_float_arithmetic_mul_add_sub_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp16_1985[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp16_1985 d l__401 elements (esize :: 'esize::len itself) m minimum n pair)"
  by (unfold execute_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp16_1985_def, non_mem_expI)

lemma non_mem_exp_decode_fmax_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp16_1985[non_mem_expI]:
  "non_mem_exp (decode_fmax_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp16_1985 Rd Rn Rm o1 U b__0)"
  by (unfold decode_fmax_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp16_1985_def, non_mem_expI)

lemma non_mem_exp_decode_fmax_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp_1985[non_mem_expI]:
  "non_mem_exp (decode_fmax_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp_1985 Rd Rn Rm b__0 o1 U b__1)"
  by (unfold decode_fmax_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp_1985_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_float_arithmetic_max_min[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_float_arithmetic_max_min d (datasize :: 'datasize::len itself) m n operation)"
  by (unfold execute_aarch64_instrs_float_arithmetic_max_min_def, non_mem_expI)

lemma non_mem_exp_decode_fmax_float_aarch64_instrs_float_arithmetic_max_min[non_mem_expI]:
  "non_mem_exp (decode_fmax_float_aarch64_instrs_float_arithmetic_max_min Rd Rn op Rm b__0)"
  by (unfold decode_fmax_float_aarch64_instrs_float_arithmetic_max_min_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp16_2008[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp16_2008 d l__435 elements (esize :: 'esize::len itself) m minimum n pair)"
  by (unfold execute_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp16_2008_def, non_mem_expI)

lemma non_mem_exp_decode_fmaxnm_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp16_2008[non_mem_expI]:
  "non_mem_exp (decode_fmaxnm_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp16_2008 Rd Rn Rm a U b__0)"
  by (unfold decode_fmaxnm_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp16_2008_def, non_mem_expI)

lemma non_mem_exp_decode_fmaxnm_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp_2008[non_mem_expI]:
  "non_mem_exp (decode_fmaxnm_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp_2008 Rd Rn Rm b__0 o1 U b__1)"
  by (unfold decode_fmaxnm_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp_2008_def, non_mem_expI)

lemma non_mem_exp_decode_fmaxnm_float_aarch64_instrs_float_arithmetic_max_min[non_mem_expI]:
  "non_mem_exp (decode_fmaxnm_float_aarch64_instrs_float_arithmetic_max_min Rd Rn op Rm b__0)"
  by (unfold decode_fmaxnm_float_aarch64_instrs_float_arithmetic_max_min_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_reduce_fp16_maxnm_sisd[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_reduce_fp16_maxnm_sisd d (datasize :: 'datasize::len itself) (esize :: 'esize::len itself) n op)"
  by (unfold execute_aarch64_instrs_vector_reduce_fp16_maxnm_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_fmaxnmp_advsimd_pair_aarch64_instrs_vector_reduce_fp16_maxnm_sisd[non_mem_expI]:
  "non_mem_exp (decode_fmaxnmp_advsimd_pair_aarch64_instrs_vector_reduce_fp16_maxnm_sisd Rd Rn sz o1)"
  by (unfold decode_fmaxnmp_advsimd_pair_aarch64_instrs_vector_reduce_fp16_maxnm_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_fmaxnmp_advsimd_pair_aarch64_instrs_vector_reduce_fp_maxnm_sisd[non_mem_expI]:
  "non_mem_exp (decode_fmaxnmp_advsimd_pair_aarch64_instrs_vector_reduce_fp_maxnm_sisd Rd Rn b__0 o1)"
  by (unfold decode_fmaxnmp_advsimd_pair_aarch64_instrs_vector_reduce_fp_maxnm_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_fmaxnmp_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp16_2008[non_mem_expI]:
  "non_mem_exp (decode_fmaxnmp_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp16_2008 Rd Rn Rm a U b__0)"
  by (unfold decode_fmaxnmp_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp16_2008_def, non_mem_expI)

lemma non_mem_exp_decode_fmaxnmp_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp_2008[non_mem_expI]:
  "non_mem_exp (decode_fmaxnmp_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp_2008 Rd Rn Rm b__0 o1 U b__1)"
  by (unfold decode_fmaxnmp_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp_2008_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_reduce_fp16_maxnm_simd[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_reduce_fp16_maxnm_simd d (datasize :: 'datasize::len itself) (esize :: 'esize::len itself) n op)"
  by (unfold execute_aarch64_instrs_vector_reduce_fp16_maxnm_simd_def, non_mem_expI)

lemma non_mem_exp_decode_fmaxnmv_advsimd_aarch64_instrs_vector_reduce_fp16_maxnm_simd[non_mem_expI]:
  "non_mem_exp (decode_fmaxnmv_advsimd_aarch64_instrs_vector_reduce_fp16_maxnm_simd Rd Rn o1 b__0)"
  by (unfold decode_fmaxnmv_advsimd_aarch64_instrs_vector_reduce_fp16_maxnm_simd_def, non_mem_expI)

lemma non_mem_exp_decode_fmaxnmv_advsimd_aarch64_instrs_vector_reduce_fp_maxnm_simd[non_mem_expI]:
  "non_mem_exp (decode_fmaxnmv_advsimd_aarch64_instrs_vector_reduce_fp_maxnm_simd Rd Rn b__0 o1 b__1)"
  by (unfold decode_fmaxnmv_advsimd_aarch64_instrs_vector_reduce_fp_maxnm_simd_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_reduce_fp16_max_sisd[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_reduce_fp16_max_sisd d (datasize :: 'datasize::len itself) (esize :: 'esize::len itself) n op)"
  by (unfold execute_aarch64_instrs_vector_reduce_fp16_max_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_fmaxp_advsimd_pair_aarch64_instrs_vector_reduce_fp16_max_sisd[non_mem_expI]:
  "non_mem_exp (decode_fmaxp_advsimd_pair_aarch64_instrs_vector_reduce_fp16_max_sisd Rd Rn sz o1)"
  by (unfold decode_fmaxp_advsimd_pair_aarch64_instrs_vector_reduce_fp16_max_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_fmaxp_advsimd_pair_aarch64_instrs_vector_reduce_fp_max_sisd[non_mem_expI]:
  "non_mem_exp (decode_fmaxp_advsimd_pair_aarch64_instrs_vector_reduce_fp_max_sisd Rd Rn b__0 o1)"
  by (unfold decode_fmaxp_advsimd_pair_aarch64_instrs_vector_reduce_fp_max_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_fmaxp_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp16_1985[non_mem_expI]:
  "non_mem_exp (decode_fmaxp_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp16_1985 Rd Rn Rm o1 U b__0)"
  by (unfold decode_fmaxp_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp16_1985_def, non_mem_expI)

lemma non_mem_exp_decode_fmaxp_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp_1985[non_mem_expI]:
  "non_mem_exp (decode_fmaxp_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp_1985 Rd Rn Rm b__0 o1 U b__1)"
  by (unfold decode_fmaxp_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp_1985_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_reduce_fp16_max_simd[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_reduce_fp16_max_simd d (datasize :: 'datasize::len itself) (esize :: 'esize::len itself) n op)"
  by (unfold execute_aarch64_instrs_vector_reduce_fp16_max_simd_def, non_mem_expI)

lemma non_mem_exp_decode_fmaxv_advsimd_aarch64_instrs_vector_reduce_fp16_max_simd[non_mem_expI]:
  "non_mem_exp (decode_fmaxv_advsimd_aarch64_instrs_vector_reduce_fp16_max_simd Rd Rn o1 b__0)"
  by (unfold decode_fmaxv_advsimd_aarch64_instrs_vector_reduce_fp16_max_simd_def, non_mem_expI)

lemma non_mem_exp_decode_fmaxv_advsimd_aarch64_instrs_vector_reduce_fp_max_simd[non_mem_expI]:
  "non_mem_exp (decode_fmaxv_advsimd_aarch64_instrs_vector_reduce_fp_max_simd Rd Rn b__0 o1 b__1)"
  by (unfold decode_fmaxv_advsimd_aarch64_instrs_vector_reduce_fp_max_simd_def, non_mem_expI)

lemma non_mem_exp_decode_fmin_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp16_1985[non_mem_expI]:
  "non_mem_exp (decode_fmin_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp16_1985 Rd Rn Rm o1 U b__0)"
  by (unfold decode_fmin_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp16_1985_def, non_mem_expI)

lemma non_mem_exp_decode_fmin_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp_1985[non_mem_expI]:
  "non_mem_exp (decode_fmin_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp_1985 Rd Rn Rm b__0 o1 U b__1)"
  by (unfold decode_fmin_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp_1985_def, non_mem_expI)

lemma non_mem_exp_decode_fmin_float_aarch64_instrs_float_arithmetic_max_min[non_mem_expI]:
  "non_mem_exp (decode_fmin_float_aarch64_instrs_float_arithmetic_max_min Rd Rn op Rm b__0)"
  by (unfold decode_fmin_float_aarch64_instrs_float_arithmetic_max_min_def, non_mem_expI)

lemma non_mem_exp_decode_fminnm_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp16_2008[non_mem_expI]:
  "non_mem_exp (decode_fminnm_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp16_2008 Rd Rn Rm a U b__0)"
  by (unfold decode_fminnm_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp16_2008_def, non_mem_expI)

lemma non_mem_exp_decode_fminnm_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp_2008[non_mem_expI]:
  "non_mem_exp (decode_fminnm_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp_2008 Rd Rn Rm b__0 o1 U b__1)"
  by (unfold decode_fminnm_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp_2008_def, non_mem_expI)

lemma non_mem_exp_decode_fminnm_float_aarch64_instrs_float_arithmetic_max_min[non_mem_expI]:
  "non_mem_exp (decode_fminnm_float_aarch64_instrs_float_arithmetic_max_min Rd Rn op Rm b__0)"
  by (unfold decode_fminnm_float_aarch64_instrs_float_arithmetic_max_min_def, non_mem_expI)

lemma non_mem_exp_decode_fminnmp_advsimd_pair_aarch64_instrs_vector_reduce_fp16_maxnm_sisd[non_mem_expI]:
  "non_mem_exp (decode_fminnmp_advsimd_pair_aarch64_instrs_vector_reduce_fp16_maxnm_sisd Rd Rn sz o1)"
  by (unfold decode_fminnmp_advsimd_pair_aarch64_instrs_vector_reduce_fp16_maxnm_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_fminnmp_advsimd_pair_aarch64_instrs_vector_reduce_fp_maxnm_sisd[non_mem_expI]:
  "non_mem_exp (decode_fminnmp_advsimd_pair_aarch64_instrs_vector_reduce_fp_maxnm_sisd Rd Rn b__0 o1)"
  by (unfold decode_fminnmp_advsimd_pair_aarch64_instrs_vector_reduce_fp_maxnm_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_fminnmp_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp16_2008[non_mem_expI]:
  "non_mem_exp (decode_fminnmp_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp16_2008 Rd Rn Rm a U b__0)"
  by (unfold decode_fminnmp_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp16_2008_def, non_mem_expI)

lemma non_mem_exp_decode_fminnmp_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp_2008[non_mem_expI]:
  "non_mem_exp (decode_fminnmp_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp_2008 Rd Rn Rm b__0 o1 U b__1)"
  by (unfold decode_fminnmp_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp_2008_def, non_mem_expI)

lemma non_mem_exp_decode_fminnmv_advsimd_aarch64_instrs_vector_reduce_fp16_maxnm_simd[non_mem_expI]:
  "non_mem_exp (decode_fminnmv_advsimd_aarch64_instrs_vector_reduce_fp16_maxnm_simd Rd Rn o1 b__0)"
  by (unfold decode_fminnmv_advsimd_aarch64_instrs_vector_reduce_fp16_maxnm_simd_def, non_mem_expI)

lemma non_mem_exp_decode_fminnmv_advsimd_aarch64_instrs_vector_reduce_fp_maxnm_simd[non_mem_expI]:
  "non_mem_exp (decode_fminnmv_advsimd_aarch64_instrs_vector_reduce_fp_maxnm_simd Rd Rn b__0 o1 b__1)"
  by (unfold decode_fminnmv_advsimd_aarch64_instrs_vector_reduce_fp_maxnm_simd_def, non_mem_expI)

lemma non_mem_exp_decode_fminp_advsimd_pair_aarch64_instrs_vector_reduce_fp16_max_sisd[non_mem_expI]:
  "non_mem_exp (decode_fminp_advsimd_pair_aarch64_instrs_vector_reduce_fp16_max_sisd Rd Rn sz o1)"
  by (unfold decode_fminp_advsimd_pair_aarch64_instrs_vector_reduce_fp16_max_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_fminp_advsimd_pair_aarch64_instrs_vector_reduce_fp_max_sisd[non_mem_expI]:
  "non_mem_exp (decode_fminp_advsimd_pair_aarch64_instrs_vector_reduce_fp_max_sisd Rd Rn b__0 o1)"
  by (unfold decode_fminp_advsimd_pair_aarch64_instrs_vector_reduce_fp_max_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_fminp_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp16_1985[non_mem_expI]:
  "non_mem_exp (decode_fminp_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp16_1985 Rd Rn Rm o1 U b__0)"
  by (unfold decode_fminp_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp16_1985_def, non_mem_expI)

lemma non_mem_exp_decode_fminp_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp_1985[non_mem_expI]:
  "non_mem_exp (decode_fminp_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp_1985 Rd Rn Rm b__0 o1 U b__1)"
  by (unfold decode_fminp_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp_1985_def, non_mem_expI)

lemma non_mem_exp_decode_fminv_advsimd_aarch64_instrs_vector_reduce_fp16_max_simd[non_mem_expI]:
  "non_mem_exp (decode_fminv_advsimd_aarch64_instrs_vector_reduce_fp16_max_simd Rd Rn o1 b__0)"
  by (unfold decode_fminv_advsimd_aarch64_instrs_vector_reduce_fp16_max_simd_def, non_mem_expI)

lemma non_mem_exp_decode_fminv_advsimd_aarch64_instrs_vector_reduce_fp_max_simd[non_mem_expI]:
  "non_mem_exp (decode_fminv_advsimd_aarch64_instrs_vector_reduce_fp_max_simd Rd Rn b__0 o1 b__1)"
  by (unfold decode_fminv_advsimd_aarch64_instrs_vector_reduce_fp_max_simd_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_fp16_sisd[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_fp16_sisd d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) (idxdsize :: 'idxdsize::len itself) index__arg m n sub_op)"
  by (unfold execute_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_fp16_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_fmla_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_fp16_simd[non_mem_expI]:
  "non_mem_exp (decode_fmla_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_fp16_simd Rd Rn b__0 o2 Rm M L b__1)"
  by (unfold decode_fmla_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_fp16_simd_def, non_mem_expI)

lemma non_mem_exp_decode_fmla_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_fp16_sisd[non_mem_expI]:
  "non_mem_exp (decode_fmla_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_fp16_sisd Rd Rn b__0 o2 Rm M L)"
  by (unfold decode_fmla_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_fp16_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_fmla_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_fp_simd[non_mem_expI]:
  "non_mem_exp (decode_fmla_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_fp_simd Rd Rn b__0 o2 Rm M L b__1 b__2)"
  by (unfold decode_fmla_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_fp_simd_def, non_mem_expI)

lemma non_mem_exp_decode_fmla_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_fp_sisd[non_mem_expI]:
  "non_mem_exp (decode_fmla_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_fp_sisd Rd Rn b__0 o2 Rm M L b__1)"
  by (unfold decode_fmla_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_fp_sisd_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp16_fused[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp16_fused d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) m n sub_op)"
  by (unfold execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp16_fused_def, non_mem_expI)

lemma non_mem_exp_decode_fmla_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp16_fused[non_mem_expI]:
  "non_mem_exp (decode_fmla_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp16_fused Rd Rn Rm a b__0)"
  by (unfold decode_fmla_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp16_fused_def, non_mem_expI)

lemma non_mem_exp_decode_fmla_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp_fused[non_mem_expI]:
  "non_mem_exp (decode_fmla_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp_fused Rd Rn Rm b__0 op b__1)"
  by (unfold decode_fmla_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp_fused_def, non_mem_expI)

lemma non_mem_exp_decode_fmls_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_fp16_simd[non_mem_expI]:
  "non_mem_exp (decode_fmls_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_fp16_simd Rd Rn b__0 o2 Rm M L b__1)"
  by (unfold decode_fmls_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_fp16_simd_def, non_mem_expI)

lemma non_mem_exp_decode_fmls_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_fp16_sisd[non_mem_expI]:
  "non_mem_exp (decode_fmls_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_fp16_sisd Rd Rn b__0 o2 Rm M L)"
  by (unfold decode_fmls_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_fp16_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_fmls_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_fp_simd[non_mem_expI]:
  "non_mem_exp (decode_fmls_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_fp_simd Rd Rn b__0 o2 Rm M L b__1 b__2)"
  by (unfold decode_fmls_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_fp_simd_def, non_mem_expI)

lemma non_mem_exp_decode_fmls_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_fp_sisd[non_mem_expI]:
  "non_mem_exp (decode_fmls_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_fp_sisd Rd Rn b__0 o2 Rm M L b__1)"
  by (unfold decode_fmls_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_fp_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_fmls_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp16_fused[non_mem_expI]:
  "non_mem_exp (decode_fmls_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp16_fused Rd Rn Rm a b__0)"
  by (unfold decode_fmls_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp16_fused_def, non_mem_expI)

lemma non_mem_exp_decode_fmls_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp_fused[non_mem_expI]:
  "non_mem_exp (decode_fmls_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp_fused Rd Rn Rm b__0 op b__1)"
  by (unfold decode_fmls_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp_fused_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_fp16_movi[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_fp16_movi datasize imm rd)"
  by (unfold execute_aarch64_instrs_vector_fp16_movi_def, non_mem_expI)

lemma non_mem_exp_decode_fmov_advsimd_aarch64_instrs_vector_fp16_movi[non_mem_expI]:
  "non_mem_exp (decode_fmov_advsimd_aarch64_instrs_vector_fp16_movi Rd h g f e d c__arg b a b__0)"
  by (unfold decode_fmov_advsimd_aarch64_instrs_vector_fp16_movi_def, non_mem_expI)

lemma non_mem_exp_decode_fmov_advsimd_aarch64_instrs_vector_logical[non_mem_expI]:
  "non_mem_exp (decode_fmov_advsimd_aarch64_instrs_vector_logical Rd h g f e d cmode c__arg b a op b__0)"
  by (unfold decode_fmov_advsimd_aarch64_instrs_vector_logical_def, non_mem_expI)

lemma non_mem_exp_decode_fmov_float_aarch64_instrs_float_arithmetic_unary[non_mem_expI]:
  "non_mem_exp (decode_fmov_float_aarch64_instrs_float_arithmetic_unary Rd Rn opc b__0)"
  by (unfold decode_fmov_float_aarch64_instrs_float_arithmetic_unary_def, non_mem_expI)

lemma non_mem_exp_decode_fmov_float_gen_aarch64_instrs_float_convert_int[non_mem_expI]:
  "non_mem_exp (decode_fmov_float_gen_aarch64_instrs_float_convert_int Rd Rn opcode rmode ftype b__0)"
  by (unfold decode_fmov_float_gen_aarch64_instrs_float_convert_int_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_float_move_fp_imm[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_float_move_fp_imm d datasize imm)"
  by (unfold execute_aarch64_instrs_float_move_fp_imm_def, non_mem_expI)

lemma non_mem_exp_decode_fmov_float_imm_aarch64_instrs_float_move_fp_imm[non_mem_expI]:
  "non_mem_exp (decode_fmov_float_imm_aarch64_instrs_float_move_fp_imm Rd imm8 b__0)"
  by (unfold decode_fmov_float_imm_aarch64_instrs_float_move_fp_imm_def, non_mem_expI)

lemma non_mem_exp_decode_fmsub_float_aarch64_instrs_float_arithmetic_mul_add_sub[non_mem_expI]:
  "non_mem_exp (decode_fmsub_float_aarch64_instrs_float_arithmetic_mul_add_sub Rd Rn Ra o0 Rm o1 b__0)"
  by (unfold decode_fmsub_float_aarch64_instrs_float_arithmetic_mul_add_sub_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_arithmetic_binary_element_mul_fp16_sisd[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_fp16_sisd d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) (idxdsize :: 'idxdsize::len itself) index__arg m mulx_op n)"
  by (unfold execute_aarch64_instrs_vector_arithmetic_binary_element_mul_fp16_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_fmul_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_fp16_simd[non_mem_expI]:
  "non_mem_exp (decode_fmul_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_fp16_simd Rd Rn b__0 Rm M L U b__1)"
  by (unfold decode_fmul_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_fp16_simd_def, non_mem_expI)

lemma non_mem_exp_decode_fmul_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_fp16_sisd[non_mem_expI]:
  "non_mem_exp (decode_fmul_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_fp16_sisd Rd Rn b__0 Rm M L U)"
  by (unfold decode_fmul_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_fp16_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_fmul_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_fp_simd[non_mem_expI]:
  "non_mem_exp (decode_fmul_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_fp_simd Rd Rn b__0 Rm M L b__1 U b__2)"
  by (unfold decode_fmul_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_fp_simd_def, non_mem_expI)

lemma non_mem_exp_decode_fmul_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_fp_sisd[non_mem_expI]:
  "non_mem_exp (decode_fmul_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_fp_sisd Rd Rn b__0 Rm M L b__1 U)"
  by (unfold decode_fmul_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_fp_sisd_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp16_product[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp16_product d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) m n)"
  by (unfold execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp16_product_def, non_mem_expI)

lemma non_mem_exp_decode_fmul_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp16_product[non_mem_expI]:
  "non_mem_exp (decode_fmul_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp16_product Rd Rn Rm b__0)"
  by (unfold decode_fmul_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp16_product_def, non_mem_expI)

lemma non_mem_exp_decode_fmul_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp_product[non_mem_expI]:
  "non_mem_exp (decode_fmul_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp_product Rd Rn Rm b__0 b__1)"
  by (unfold decode_fmul_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp_product_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_float_arithmetic_mul_product[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_float_arithmetic_mul_product d (datasize :: 'datasize::len itself) m n negated)"
  by (unfold execute_aarch64_instrs_float_arithmetic_mul_product_def, non_mem_expI)

lemma non_mem_exp_decode_fmul_float_aarch64_instrs_float_arithmetic_mul_product[non_mem_expI]:
  "non_mem_exp (decode_fmul_float_aarch64_instrs_float_arithmetic_mul_product Rd Rn op Rm b__0)"
  by (unfold decode_fmul_float_aarch64_instrs_float_arithmetic_mul_product_def, non_mem_expI)

lemma non_mem_exp_decode_fmulx_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_fp16_simd[non_mem_expI]:
  "non_mem_exp (decode_fmulx_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_fp16_simd Rd Rn b__0 Rm M L U b__1)"
  by (unfold decode_fmulx_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_fp16_simd_def, non_mem_expI)

lemma non_mem_exp_decode_fmulx_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_fp16_sisd[non_mem_expI]:
  "non_mem_exp (decode_fmulx_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_fp16_sisd Rd Rn b__0 Rm M L U)"
  by (unfold decode_fmulx_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_fp16_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_fmulx_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_fp_simd[non_mem_expI]:
  "non_mem_exp (decode_fmulx_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_fp_simd Rd Rn b__0 Rm M L b__1 U b__2)"
  by (unfold decode_fmulx_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_fp_simd_def, non_mem_expI)

lemma non_mem_exp_decode_fmulx_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_fp_sisd[non_mem_expI]:
  "non_mem_exp (decode_fmulx_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_fp_sisd Rd Rn b__0 Rm M L b__1 U)"
  by (unfold decode_fmulx_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_fp_sisd_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp16_extended_sisd[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp16_extended_sisd d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) m n)"
  by (unfold execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp16_extended_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_fmulx_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp16_extended_simd[non_mem_expI]:
  "non_mem_exp (decode_fmulx_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp16_extended_simd Rd Rn Rm b__0)"
  by (unfold decode_fmulx_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp16_extended_simd_def, non_mem_expI)

lemma non_mem_exp_decode_fmulx_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp16_extended_sisd[non_mem_expI]:
  "non_mem_exp (decode_fmulx_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp16_extended_sisd Rd Rn Rm)"
  by (unfold decode_fmulx_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp16_extended_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_fmulx_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp_extended_simd[non_mem_expI]:
  "non_mem_exp (decode_fmulx_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp_extended_simd Rd Rn Rm b__0 b__1)"
  by (unfold decode_fmulx_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp_extended_simd_def, non_mem_expI)

lemma non_mem_exp_decode_fmulx_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp_extended_sisd[non_mem_expI]:
  "non_mem_exp (decode_fmulx_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp_extended_sisd Rd Rn Rm b__0)"
  by (unfold decode_fmulx_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp_extended_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_fneg_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_float[non_mem_expI]:
  "non_mem_exp (decode_fneg_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_float Rd Rn b__0 U b__1)"
  by (unfold decode_fneg_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_float_def, non_mem_expI)

lemma non_mem_exp_decode_fneg_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_fp16[non_mem_expI]:
  "non_mem_exp (decode_fneg_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_fp16 Rd Rn U b__0)"
  by (unfold decode_fneg_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_fp16_def, non_mem_expI)

lemma non_mem_exp_decode_fneg_float_aarch64_instrs_float_arithmetic_unary[non_mem_expI]:
  "non_mem_exp (decode_fneg_float_aarch64_instrs_float_arithmetic_unary Rd Rn opc b__0)"
  by (unfold decode_fneg_float_aarch64_instrs_float_arithmetic_unary_def, non_mem_expI)

lemma non_mem_exp_decode_fnmadd_float_aarch64_instrs_float_arithmetic_mul_add_sub[non_mem_expI]:
  "non_mem_exp (decode_fnmadd_float_aarch64_instrs_float_arithmetic_mul_add_sub Rd Rn Ra o0 Rm o1 b__0)"
  by (unfold decode_fnmadd_float_aarch64_instrs_float_arithmetic_mul_add_sub_def, non_mem_expI)

lemma non_mem_exp_decode_fnmsub_float_aarch64_instrs_float_arithmetic_mul_add_sub[non_mem_expI]:
  "non_mem_exp (decode_fnmsub_float_aarch64_instrs_float_arithmetic_mul_add_sub Rd Rn Ra o0 Rm o1 b__0)"
  by (unfold decode_fnmsub_float_aarch64_instrs_float_arithmetic_mul_add_sub_def, non_mem_expI)

lemma non_mem_exp_decode_fnmul_float_aarch64_instrs_float_arithmetic_mul_product[non_mem_expI]:
  "non_mem_exp (decode_fnmul_float_aarch64_instrs_float_arithmetic_mul_product Rd Rn op Rm b__0)"
  by (unfold decode_fnmul_float_aarch64_instrs_float_arithmetic_mul_product_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_arithmetic_unary_special_recip_fp16_sisd[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_arithmetic_unary_special_recip_fp16_sisd d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) n)"
  by (unfold execute_aarch64_instrs_vector_arithmetic_unary_special_recip_fp16_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_frecpe_advsimd_aarch64_instrs_vector_arithmetic_unary_special_recip_float_simd[non_mem_expI]:
  "non_mem_exp (decode_frecpe_advsimd_aarch64_instrs_vector_arithmetic_unary_special_recip_float_simd Rd Rn b__0 b__1)"
  by (unfold decode_frecpe_advsimd_aarch64_instrs_vector_arithmetic_unary_special_recip_float_simd_def, non_mem_expI)

lemma non_mem_exp_decode_frecpe_advsimd_aarch64_instrs_vector_arithmetic_unary_special_recip_float_sisd[non_mem_expI]:
  "non_mem_exp (decode_frecpe_advsimd_aarch64_instrs_vector_arithmetic_unary_special_recip_float_sisd Rd Rn b__0)"
  by (unfold decode_frecpe_advsimd_aarch64_instrs_vector_arithmetic_unary_special_recip_float_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_frecpe_advsimd_aarch64_instrs_vector_arithmetic_unary_special_recip_fp16_simd[non_mem_expI]:
  "non_mem_exp (decode_frecpe_advsimd_aarch64_instrs_vector_arithmetic_unary_special_recip_fp16_simd Rd Rn b__0)"
  by (unfold decode_frecpe_advsimd_aarch64_instrs_vector_arithmetic_unary_special_recip_fp16_simd_def, non_mem_expI)

lemma non_mem_exp_decode_frecpe_advsimd_aarch64_instrs_vector_arithmetic_unary_special_recip_fp16_sisd[non_mem_expI]:
  "non_mem_exp (decode_frecpe_advsimd_aarch64_instrs_vector_arithmetic_unary_special_recip_fp16_sisd Rd Rn)"
  by (unfold decode_frecpe_advsimd_aarch64_instrs_vector_arithmetic_unary_special_recip_fp16_sisd_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_arithmetic_binary_uniform_recps_fp16_sisd[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_arithmetic_binary_uniform_recps_fp16_sisd d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) m n)"
  by (unfold execute_aarch64_instrs_vector_arithmetic_binary_uniform_recps_fp16_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_frecps_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_recps_fp16_simd[non_mem_expI]:
  "non_mem_exp (decode_frecps_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_recps_fp16_simd Rd Rn Rm b__0)"
  by (unfold decode_frecps_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_recps_fp16_simd_def, non_mem_expI)

lemma non_mem_exp_decode_frecps_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_recps_fp16_sisd[non_mem_expI]:
  "non_mem_exp (decode_frecps_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_recps_fp16_sisd Rd Rn Rm)"
  by (unfold decode_frecps_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_recps_fp16_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_frecps_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_recps_simd[non_mem_expI]:
  "non_mem_exp (decode_frecps_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_recps_simd Rd Rn Rm b__0 b__1)"
  by (unfold decode_frecps_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_recps_simd_def, non_mem_expI)

lemma non_mem_exp_decode_frecps_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_recps_sisd[non_mem_expI]:
  "non_mem_exp (decode_frecps_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_recps_sisd Rd Rn Rm b__0)"
  by (unfold decode_frecps_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_recps_sisd_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_arithmetic_unary_special_frecpx_fp16[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_arithmetic_unary_special_frecpx_fp16 d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) n)"
  by (unfold execute_aarch64_instrs_vector_arithmetic_unary_special_frecpx_fp16_def, non_mem_expI)

lemma non_mem_exp_decode_frecpx_advsimd_aarch64_instrs_vector_arithmetic_unary_special_frecpx[non_mem_expI]:
  "non_mem_exp (decode_frecpx_advsimd_aarch64_instrs_vector_arithmetic_unary_special_frecpx Rd Rn b__0)"
  by (unfold decode_frecpx_advsimd_aarch64_instrs_vector_arithmetic_unary_special_frecpx_def, non_mem_expI)

lemma non_mem_exp_decode_frecpx_advsimd_aarch64_instrs_vector_arithmetic_unary_special_frecpx_fp16[non_mem_expI]:
  "non_mem_exp (decode_frecpx_advsimd_aarch64_instrs_vector_arithmetic_unary_special_frecpx_fp16 Rd Rn)"
  by (unfold decode_frecpx_advsimd_aarch64_instrs_vector_arithmetic_unary_special_frecpx_fp16_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_arithmetic_unary_fp16_round[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_arithmetic_unary_fp16_round d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) exact n rounding)"
  by (unfold execute_aarch64_instrs_vector_arithmetic_unary_fp16_round_def, non_mem_expI)

lemma non_mem_exp_decode_frinta_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round[non_mem_expI]:
  "non_mem_exp (decode_frinta_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round Rd Rn o1 b__0 o2 U b__1)"
  by (unfold decode_frinta_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round_def, non_mem_expI)

lemma non_mem_exp_decode_frinta_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round[non_mem_expI]:
  "non_mem_exp (decode_frinta_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round Rd Rn o1 o2 U b__0)"
  by (unfold decode_frinta_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_float_arithmetic_round_frint[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_float_arithmetic_round_frint d (datasize :: 'datasize::len itself) exact n rounding)"
  by (unfold execute_aarch64_instrs_float_arithmetic_round_frint_def, non_mem_expI)

lemma non_mem_exp_decode_frinta_float_aarch64_instrs_float_arithmetic_round_frint[non_mem_expI]:
  "non_mem_exp (decode_frinta_float_aarch64_instrs_float_arithmetic_round_frint Rd Rn rmode b__0 S M)"
  by (unfold decode_frinta_float_aarch64_instrs_float_arithmetic_round_frint_def, non_mem_expI)

lemma non_mem_exp_decode_frinti_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round[non_mem_expI]:
  "non_mem_exp (decode_frinti_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round Rd Rn o1 b__0 o2 U b__1)"
  by (unfold decode_frinti_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round_def, non_mem_expI)

lemma non_mem_exp_decode_frinti_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round[non_mem_expI]:
  "non_mem_exp (decode_frinti_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round Rd Rn o1 o2 U b__0)"
  by (unfold decode_frinti_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round_def, non_mem_expI)

lemma non_mem_exp_decode_frinti_float_aarch64_instrs_float_arithmetic_round_frint[non_mem_expI]:
  "non_mem_exp (decode_frinti_float_aarch64_instrs_float_arithmetic_round_frint Rd Rn rmode b__0 S M)"
  by (unfold decode_frinti_float_aarch64_instrs_float_arithmetic_round_frint_def, non_mem_expI)

lemma non_mem_exp_decode_frintm_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round[non_mem_expI]:
  "non_mem_exp (decode_frintm_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round Rd Rn o1 b__0 o2 U b__1)"
  by (unfold decode_frintm_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round_def, non_mem_expI)

lemma non_mem_exp_decode_frintm_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round[non_mem_expI]:
  "non_mem_exp (decode_frintm_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round Rd Rn o1 o2 U b__0)"
  by (unfold decode_frintm_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round_def, non_mem_expI)

lemma non_mem_exp_decode_frintm_float_aarch64_instrs_float_arithmetic_round_frint[non_mem_expI]:
  "non_mem_exp (decode_frintm_float_aarch64_instrs_float_arithmetic_round_frint Rd Rn rmode b__0 S M)"
  by (unfold decode_frintm_float_aarch64_instrs_float_arithmetic_round_frint_def, non_mem_expI)

lemma non_mem_exp_decode_frintn_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round[non_mem_expI]:
  "non_mem_exp (decode_frintn_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round Rd Rn o1 b__0 o2 U b__1)"
  by (unfold decode_frintn_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round_def, non_mem_expI)

lemma non_mem_exp_decode_frintn_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round[non_mem_expI]:
  "non_mem_exp (decode_frintn_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round Rd Rn o1 o2 U b__0)"
  by (unfold decode_frintn_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round_def, non_mem_expI)

lemma non_mem_exp_decode_frintn_float_aarch64_instrs_float_arithmetic_round_frint[non_mem_expI]:
  "non_mem_exp (decode_frintn_float_aarch64_instrs_float_arithmetic_round_frint Rd Rn rmode b__0 S M)"
  by (unfold decode_frintn_float_aarch64_instrs_float_arithmetic_round_frint_def, non_mem_expI)

lemma non_mem_exp_decode_frintp_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round[non_mem_expI]:
  "non_mem_exp (decode_frintp_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round Rd Rn o1 b__0 o2 U b__1)"
  by (unfold decode_frintp_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round_def, non_mem_expI)

lemma non_mem_exp_decode_frintp_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round[non_mem_expI]:
  "non_mem_exp (decode_frintp_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round Rd Rn o1 o2 U b__0)"
  by (unfold decode_frintp_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round_def, non_mem_expI)

lemma non_mem_exp_decode_frintp_float_aarch64_instrs_float_arithmetic_round_frint[non_mem_expI]:
  "non_mem_exp (decode_frintp_float_aarch64_instrs_float_arithmetic_round_frint Rd Rn rmode b__0 S M)"
  by (unfold decode_frintp_float_aarch64_instrs_float_arithmetic_round_frint_def, non_mem_expI)

lemma non_mem_exp_decode_frintx_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round[non_mem_expI]:
  "non_mem_exp (decode_frintx_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round Rd Rn o1 b__0 o2 U b__1)"
  by (unfold decode_frintx_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round_def, non_mem_expI)

lemma non_mem_exp_decode_frintx_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round[non_mem_expI]:
  "non_mem_exp (decode_frintx_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round Rd Rn o1 o2 U b__0)"
  by (unfold decode_frintx_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round_def, non_mem_expI)

lemma non_mem_exp_decode_frintx_float_aarch64_instrs_float_arithmetic_round_frint[non_mem_expI]:
  "non_mem_exp (decode_frintx_float_aarch64_instrs_float_arithmetic_round_frint Rd Rn rmode b__0 S M)"
  by (unfold decode_frintx_float_aarch64_instrs_float_arithmetic_round_frint_def, non_mem_expI)

lemma non_mem_exp_decode_frintz_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round[non_mem_expI]:
  "non_mem_exp (decode_frintz_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round Rd Rn o1 b__0 o2 U b__1)"
  by (unfold decode_frintz_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round_def, non_mem_expI)

lemma non_mem_exp_decode_frintz_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round[non_mem_expI]:
  "non_mem_exp (decode_frintz_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round Rd Rn o1 o2 U b__0)"
  by (unfold decode_frintz_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round_def, non_mem_expI)

lemma non_mem_exp_decode_frintz_float_aarch64_instrs_float_arithmetic_round_frint[non_mem_expI]:
  "non_mem_exp (decode_frintz_float_aarch64_instrs_float_arithmetic_round_frint Rd Rn rmode b__0 S M)"
  by (unfold decode_frintz_float_aarch64_instrs_float_arithmetic_round_frint_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_arithmetic_unary_special_sqrt_est_fp16_sisd[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_arithmetic_unary_special_sqrt_est_fp16_sisd d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) n)"
  by (unfold execute_aarch64_instrs_vector_arithmetic_unary_special_sqrt_est_fp16_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_frsqrte_advsimd_aarch64_instrs_vector_arithmetic_unary_special_sqrt_est_float_simd[non_mem_expI]:
  "non_mem_exp (decode_frsqrte_advsimd_aarch64_instrs_vector_arithmetic_unary_special_sqrt_est_float_simd Rd Rn b__0 b__1)"
  by (unfold decode_frsqrte_advsimd_aarch64_instrs_vector_arithmetic_unary_special_sqrt_est_float_simd_def, non_mem_expI)

lemma non_mem_exp_decode_frsqrte_advsimd_aarch64_instrs_vector_arithmetic_unary_special_sqrt_est_float_sisd[non_mem_expI]:
  "non_mem_exp (decode_frsqrte_advsimd_aarch64_instrs_vector_arithmetic_unary_special_sqrt_est_float_sisd Rd Rn b__0)"
  by (unfold decode_frsqrte_advsimd_aarch64_instrs_vector_arithmetic_unary_special_sqrt_est_float_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_frsqrte_advsimd_aarch64_instrs_vector_arithmetic_unary_special_sqrt_est_fp16_simd[non_mem_expI]:
  "non_mem_exp (decode_frsqrte_advsimd_aarch64_instrs_vector_arithmetic_unary_special_sqrt_est_fp16_simd Rd Rn b__0)"
  by (unfold decode_frsqrte_advsimd_aarch64_instrs_vector_arithmetic_unary_special_sqrt_est_fp16_simd_def, non_mem_expI)

lemma non_mem_exp_decode_frsqrte_advsimd_aarch64_instrs_vector_arithmetic_unary_special_sqrt_est_fp16_sisd[non_mem_expI]:
  "non_mem_exp (decode_frsqrte_advsimd_aarch64_instrs_vector_arithmetic_unary_special_sqrt_est_fp16_sisd Rd Rn)"
  by (unfold decode_frsqrte_advsimd_aarch64_instrs_vector_arithmetic_unary_special_sqrt_est_fp16_sisd_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_arithmetic_binary_uniform_rsqrts_fp16_sisd[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_arithmetic_binary_uniform_rsqrts_fp16_sisd d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) m n)"
  by (unfold execute_aarch64_instrs_vector_arithmetic_binary_uniform_rsqrts_fp16_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_frsqrts_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_rsqrts_fp16_simd[non_mem_expI]:
  "non_mem_exp (decode_frsqrts_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_rsqrts_fp16_simd Rd Rn Rm b__0)"
  by (unfold decode_frsqrts_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_rsqrts_fp16_simd_def, non_mem_expI)

lemma non_mem_exp_decode_frsqrts_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_rsqrts_fp16_sisd[non_mem_expI]:
  "non_mem_exp (decode_frsqrts_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_rsqrts_fp16_sisd Rd Rn Rm)"
  by (unfold decode_frsqrts_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_rsqrts_fp16_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_frsqrts_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_rsqrts_simd[non_mem_expI]:
  "non_mem_exp (decode_frsqrts_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_rsqrts_simd Rd Rn Rm b__0 b__1)"
  by (unfold decode_frsqrts_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_rsqrts_simd_def, non_mem_expI)

lemma non_mem_exp_decode_frsqrts_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_rsqrts_sisd[non_mem_expI]:
  "non_mem_exp (decode_frsqrts_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_rsqrts_sisd Rd Rn Rm b__0)"
  by (unfold decode_frsqrts_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_rsqrts_sisd_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_arithmetic_unary_special_sqrt_fp16[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_arithmetic_unary_special_sqrt_fp16 d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) n)"
  by (unfold execute_aarch64_instrs_vector_arithmetic_unary_special_sqrt_fp16_def, non_mem_expI)

lemma non_mem_exp_decode_fsqrt_advsimd_aarch64_instrs_vector_arithmetic_unary_special_sqrt[non_mem_expI]:
  "non_mem_exp (decode_fsqrt_advsimd_aarch64_instrs_vector_arithmetic_unary_special_sqrt Rd Rn b__0 b__1)"
  by (unfold decode_fsqrt_advsimd_aarch64_instrs_vector_arithmetic_unary_special_sqrt_def, non_mem_expI)

lemma non_mem_exp_decode_fsqrt_advsimd_aarch64_instrs_vector_arithmetic_unary_special_sqrt_fp16[non_mem_expI]:
  "non_mem_exp (decode_fsqrt_advsimd_aarch64_instrs_vector_arithmetic_unary_special_sqrt_fp16 Rd Rn b__0)"
  by (unfold decode_fsqrt_advsimd_aarch64_instrs_vector_arithmetic_unary_special_sqrt_fp16_def, non_mem_expI)

lemma non_mem_exp_decode_fsqrt_float_aarch64_instrs_float_arithmetic_unary[non_mem_expI]:
  "non_mem_exp (decode_fsqrt_float_aarch64_instrs_float_arithmetic_unary Rd Rn opc b__0)"
  by (unfold decode_fsqrt_float_aarch64_instrs_float_arithmetic_unary_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_arithmetic_binary_uniform_sub_fp16_simd[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_arithmetic_binary_uniform_sub_fp16_simd abs__arg d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) m n)"
  by (unfold execute_aarch64_instrs_vector_arithmetic_binary_uniform_sub_fp16_simd_def, non_mem_expI)

lemma non_mem_exp_decode_fsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_fp16_simd[non_mem_expI]:
  "non_mem_exp (decode_fsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_fp16_simd Rd Rn Rm U b__0)"
  by (unfold decode_fsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_fp16_simd_def, non_mem_expI)

lemma non_mem_exp_decode_fsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_fp_simd[non_mem_expI]:
  "non_mem_exp (decode_fsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_fp_simd Rd Rn Rm b__0 U b__1)"
  by (unfold decode_fsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_fp_simd_def, non_mem_expI)

lemma non_mem_exp_decode_fsub_float_aarch64_instrs_float_arithmetic_add_sub[non_mem_expI]:
  "non_mem_exp (decode_fsub_float_aarch64_instrs_float_arithmetic_add_sub Rd Rn op Rm b__0)"
  by (unfold decode_fsub_float_aarch64_instrs_float_arithmetic_add_sub_def, non_mem_expI)

lemma non_mem_exp_decode_hint_aarch64_instrs_system_hints[non_mem_expI]:
  "non_mem_exp (decode_hint_aarch64_instrs_system_hints op2 CRm)"
  by (unfold decode_hint_aarch64_instrs_system_hints_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_system_exceptions_debug_halt[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_system_exceptions_debug_halt arg0)"
  by (unfold execute_aarch64_instrs_system_exceptions_debug_halt_def, non_mem_expI)

lemma non_mem_exp_decode_hlt_aarch64_instrs_system_exceptions_debug_halt[non_mem_expI]:
  "non_mem_exp (decode_hlt_aarch64_instrs_system_exceptions_debug_halt imm16)"
  by (unfold decode_hlt_aarch64_instrs_system_exceptions_debug_halt_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_system_exceptions_runtime_hvc[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_system_exceptions_runtime_hvc imm)"
  by (unfold execute_aarch64_instrs_system_exceptions_runtime_hvc_def, non_mem_expI)

lemma non_mem_exp_decode_hvc_aarch64_instrs_system_exceptions_runtime_hvc[non_mem_expI]:
  "non_mem_exp (decode_hvc_aarch64_instrs_system_exceptions_runtime_hvc imm16)"
  by (unfold decode_hvc_aarch64_instrs_system_exceptions_runtime_hvc_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_transfer_vector_insert[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_transfer_vector_insert d dst_index (esize :: 'esize::len itself) (idxdsize :: 'idxdsize::len itself) n src_index)"
  by (unfold execute_aarch64_instrs_vector_transfer_vector_insert_def, non_mem_expI)

lemma non_mem_exp_decode_ins_advsimd_elt_aarch64_instrs_vector_transfer_vector_insert[non_mem_expI]:
  "non_mem_exp (decode_ins_advsimd_elt_aarch64_instrs_vector_transfer_vector_insert Rd Rn imm4 imm5)"
  by (unfold decode_ins_advsimd_elt_aarch64_instrs_vector_transfer_vector_insert_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_transfer_integer_insert[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_transfer_integer_insert d datasize (esize :: 'esize::len itself) index__arg n)"
  by (unfold execute_aarch64_instrs_vector_transfer_integer_insert_def, non_mem_expI)

lemma non_mem_exp_decode_ins_advsimd_gen_aarch64_instrs_vector_transfer_integer_insert[non_mem_expI]:
  "non_mem_exp (decode_ins_advsimd_gen_aarch64_instrs_vector_transfer_integer_insert Rd Rn b__0)"
  by (unfold decode_ins_advsimd_gen_aarch64_instrs_vector_transfer_integer_insert_def, non_mem_expI)

lemma non_mem_exp_decode_lslv_aarch64_instrs_integer_shift_variable[non_mem_expI]:
  "non_mem_exp (decode_lslv_aarch64_instrs_integer_shift_variable Rd Rn op2 Rm b__0)"
  by (unfold decode_lslv_aarch64_instrs_integer_shift_variable_def, non_mem_expI)

lemma non_mem_exp_decode_lsrv_aarch64_instrs_integer_shift_variable[non_mem_expI]:
  "non_mem_exp (decode_lsrv_aarch64_instrs_integer_shift_variable Rd Rn op2 Rm b__0)"
  by (unfold decode_lsrv_aarch64_instrs_integer_shift_variable_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_integer_arithmetic_mul_uniform_add_sub[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_integer_arithmetic_mul_uniform_add_sub a d (datasize :: 'datasize::len itself) (destsize :: 'destsize::len itself) m n sub_op)"
  by (unfold execute_aarch64_instrs_integer_arithmetic_mul_uniform_add_sub_def, non_mem_expI)

lemma non_mem_exp_decode_madd_aarch64_instrs_integer_arithmetic_mul_uniform_add_sub[non_mem_expI]:
  "non_mem_exp (decode_madd_aarch64_instrs_integer_arithmetic_mul_uniform_add_sub Rd Rn Ra o0 Rm b__0)"
  by (unfold decode_madd_aarch64_instrs_integer_arithmetic_mul_uniform_add_sub_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_int[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_int d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) (idxdsize :: 'idxdsize::len itself) index__arg m n sub_op)"
  by (unfold execute_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_int_def, non_mem_expI)

lemma non_mem_exp_decode_mla_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_int[non_mem_expI]:
  "non_mem_exp (decode_mla_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_int Rd Rn b__0 o2 Rm M L b__1 b__2)"
  by (unfold decode_mla_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_int_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_accum[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_accum d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) m n sub_op)"
  by (unfold execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_accum_def, non_mem_expI)

lemma non_mem_exp_decode_mla_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_accum[non_mem_expI]:
  "non_mem_exp (decode_mla_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_accum Rd Rn Rm b__0 U b__1)"
  by (unfold decode_mla_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_accum_def, non_mem_expI)

lemma non_mem_exp_decode_mls_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_int[non_mem_expI]:
  "non_mem_exp (decode_mls_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_int Rd Rn b__0 o2 Rm M L b__1 b__2)"
  by (unfold decode_mls_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_int_def, non_mem_expI)

lemma non_mem_exp_decode_mls_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_accum[non_mem_expI]:
  "non_mem_exp (decode_mls_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_accum Rd Rn Rm b__0 U b__1)"
  by (unfold decode_mls_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_accum_def, non_mem_expI)

lemma non_mem_exp_decode_movi_advsimd_aarch64_instrs_vector_logical[non_mem_expI]:
  "non_mem_exp (decode_movi_advsimd_aarch64_instrs_vector_logical Rd h g f e d cmode c__arg b a op b__0)"
  by (unfold decode_movi_advsimd_aarch64_instrs_vector_logical_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_integer_ins_ext_insert_movewide[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_integer_ins_ext_insert_movewide d (datasize :: 'datasize::len itself) imm opcode pos)"
  by (unfold execute_aarch64_instrs_integer_ins_ext_insert_movewide_def, non_mem_expI)

lemma non_mem_exp_decode_movk_aarch64_instrs_integer_ins_ext_insert_movewide[non_mem_expI]:
  "non_mem_exp (decode_movk_aarch64_instrs_integer_ins_ext_insert_movewide Rd imm16 hw opc b__0)"
  by (unfold decode_movk_aarch64_instrs_integer_ins_ext_insert_movewide_def, non_mem_expI)

lemma non_mem_exp_decode_movn_aarch64_instrs_integer_ins_ext_insert_movewide[non_mem_expI]:
  "non_mem_exp (decode_movn_aarch64_instrs_integer_ins_ext_insert_movewide Rd imm16 hw opc b__0)"
  by (unfold decode_movn_aarch64_instrs_integer_ins_ext_insert_movewide_def, non_mem_expI)

lemma non_mem_exp_decode_movz_aarch64_instrs_integer_ins_ext_insert_movewide[non_mem_expI]:
  "non_mem_exp (decode_movz_aarch64_instrs_integer_ins_ext_insert_movewide Rd imm16 hw opc b__0)"
  by (unfold decode_movz_aarch64_instrs_integer_ins_ext_insert_movewide_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_system_register_system[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_system_register_system read sys_crm sys_crn sys_op0 sys_op1 sys_op2 t__arg)"
  by (unfold execute_aarch64_instrs_system_register_system_def, non_mem_expI)

lemma non_mem_exp_decode_mrs_aarch64_instrs_system_register_system[non_mem_expI]:
  "non_mem_exp (decode_mrs_aarch64_instrs_system_register_system Rt op2 CRm CRn op1 o0 L)"
  by (unfold decode_mrs_aarch64_instrs_system_register_system_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_system_register_cpsr[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_system_register_cpsr field operand)"
  by (cases field; simp; non_mem_expI)

lemma non_mem_exp_decode_msr_imm_aarch64_instrs_system_register_cpsr[non_mem_expI]:
  "non_mem_exp (decode_msr_imm_aarch64_instrs_system_register_cpsr op2 CRm op1)"
  by (unfold decode_msr_imm_aarch64_instrs_system_register_cpsr_def, non_mem_expI)

lemma non_mem_exp_decode_msr_reg_aarch64_instrs_system_register_system[non_mem_expI]:
  "non_mem_exp (decode_msr_reg_aarch64_instrs_system_register_system Rt op2 CRm CRn op1 o0 L)"
  by (unfold decode_msr_reg_aarch64_instrs_system_register_system_def, non_mem_expI)

lemma non_mem_exp_decode_msub_aarch64_instrs_integer_arithmetic_mul_uniform_add_sub[non_mem_expI]:
  "non_mem_exp (decode_msub_aarch64_instrs_integer_arithmetic_mul_uniform_add_sub Rd Rn Ra o0 Rm b__0)"
  by (unfold decode_msub_aarch64_instrs_integer_arithmetic_mul_uniform_add_sub_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_arithmetic_binary_element_mul_int[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_int d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) (idxdsize :: 'idxdsize::len itself) index__arg m n)"
  by (unfold execute_aarch64_instrs_vector_arithmetic_binary_element_mul_int_def, non_mem_expI)

lemma non_mem_exp_decode_mul_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_int[non_mem_expI]:
  "non_mem_exp (decode_mul_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_int Rd Rn b__0 Rm M L b__1 b__2)"
  by (unfold decode_mul_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_int_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_product[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_product d (datasize :: 'datasize::len itself) elements l__55 m n poly)"
  by (unfold execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_product_def, non_mem_expI)

lemma non_mem_exp_decode_mul_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_product[non_mem_expI]:
  "non_mem_exp (decode_mul_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_product Rd Rn Rm b__0 U b__1)"
  by (unfold decode_mul_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_product_def, non_mem_expI)

lemma non_mem_exp_decode_mvni_advsimd_aarch64_instrs_vector_logical[non_mem_expI]:
  "non_mem_exp (decode_mvni_advsimd_aarch64_instrs_vector_logical Rd h g f e d cmode c__arg b a op b__0)"
  by (unfold decode_mvni_advsimd_aarch64_instrs_vector_logical_def, non_mem_expI)

lemma non_mem_exp_decode_neg_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_int_simd[non_mem_expI]:
  "non_mem_exp (decode_neg_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_int_simd Rd Rn b__0 U b__1)"
  by (unfold decode_neg_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_int_simd_def, non_mem_expI)

lemma non_mem_exp_decode_neg_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_int_sisd[non_mem_expI]:
  "non_mem_exp (decode_neg_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_int_sisd Rd Rn b__0 U)"
  by (unfold decode_neg_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_int_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_nop_aarch64_instrs_system_hints[non_mem_expI]:
  "non_mem_exp (decode_nop_aarch64_instrs_system_hints op2 CRm)"
  by (unfold decode_nop_aarch64_instrs_system_hints_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_arithmetic_unary_not[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_arithmetic_unary_not d (datasize :: 'datasize::len itself) elements esize n)"
  by (unfold execute_aarch64_instrs_vector_arithmetic_unary_not_def, non_mem_expI)

lemma non_mem_exp_decode_not_advsimd_aarch64_instrs_vector_arithmetic_unary_not[non_mem_expI]:
  "non_mem_exp (decode_not_advsimd_aarch64_instrs_vector_arithmetic_unary_not Rd Rn b__0)"
  by (unfold decode_not_advsimd_aarch64_instrs_vector_arithmetic_unary_not_def, non_mem_expI)

lemma non_mem_exp_decode_orn_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_logical_and_orr[non_mem_expI]:
  "non_mem_exp (decode_orn_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_logical_and_orr Rd Rn Rm size__arg b__0)"
  by (unfold decode_orn_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_logical_and_orr_def, non_mem_expI)

lemma non_mem_exp_decode_orn_log_shift_aarch64_instrs_integer_logical_shiftedreg[non_mem_expI]:
  "non_mem_exp (decode_orn_log_shift_aarch64_instrs_integer_logical_shiftedreg Rd Rn imm6 Rm N shift opc b__0)"
  by (unfold decode_orn_log_shift_aarch64_instrs_integer_logical_shiftedreg_def, non_mem_expI)

lemma non_mem_exp_decode_orr_advsimd_imm_aarch64_instrs_vector_logical[non_mem_expI]:
  "non_mem_exp (decode_orr_advsimd_imm_aarch64_instrs_vector_logical Rd h g f e d cmode c__arg b a op b__0)"
  by (unfold decode_orr_advsimd_imm_aarch64_instrs_vector_logical_def, non_mem_expI)

lemma non_mem_exp_decode_orr_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_logical_and_orr[non_mem_expI]:
  "non_mem_exp (decode_orr_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_logical_and_orr Rd Rn Rm size__arg b__0)"
  by (unfold decode_orr_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_logical_and_orr_def, non_mem_expI)

lemma non_mem_exp_decode_orr_log_imm_aarch64_instrs_integer_logical_immediate[non_mem_expI]:
  "non_mem_exp (decode_orr_log_imm_aarch64_instrs_integer_logical_immediate Rd Rn imms immr N opc b__0)"
  by (unfold decode_orr_log_imm_aarch64_instrs_integer_logical_immediate_def, non_mem_expI)

lemma non_mem_exp_decode_orr_log_shift_aarch64_instrs_integer_logical_shiftedreg[non_mem_expI]:
  "non_mem_exp (decode_orr_log_shift_aarch64_instrs_integer_logical_shiftedreg Rd Rn imm6 Rm N shift opc b__0)"
  by (unfold decode_orr_log_shift_aarch64_instrs_integer_logical_shiftedreg_def, non_mem_expI)

lemma non_mem_exp_decode_pmul_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_product[non_mem_expI]:
  "non_mem_exp (decode_pmul_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_product Rd Rn Rm b__0 U b__1)"
  by (unfold decode_pmul_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_product_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_arithmetic_binary_disparate_mul_poly[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_arithmetic_binary_disparate_mul_poly d datasize elements l__379 m n part)"
  by (unfold execute_aarch64_instrs_vector_arithmetic_binary_disparate_mul_poly_def, non_mem_expI)

lemma non_mem_exp_decode_pmull_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_mul_poly[non_mem_expI]:
  "non_mem_exp (decode_pmull_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_mul_poly Rd Rn Rm b__0 Q)"
  by (unfold decode_pmull_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_mul_poly_def, non_mem_expI)

lemma non_mem_exp_decode_psb_aarch64_instrs_system_hints[non_mem_expI]:
  "non_mem_exp (decode_psb_aarch64_instrs_system_hints op2 CRm)"
  by (unfold decode_psb_aarch64_instrs_system_hints_def, non_mem_expI)

lemma non_mem_exp_decode_raddhn_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_narrow[non_mem_expI]:
  "non_mem_exp (decode_raddhn_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_narrow Rd Rn o1 Rm b__0 U Q)"
  by (unfold decode_raddhn_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_narrow_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_crypto_sha3_rax1[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_crypto_sha3_rax1 d m n)"
  by (unfold execute_aarch64_instrs_vector_crypto_sha3_rax1_def, non_mem_expI)

lemma non_mem_exp_decode_rax1_advsimd_aarch64_instrs_vector_crypto_sha3_rax1[non_mem_expI]:
  "non_mem_exp (decode_rax1_advsimd_aarch64_instrs_vector_crypto_sha3_rax1 Rd Rn Rm)"
  by (unfold decode_rax1_advsimd_aarch64_instrs_vector_crypto_sha3_rax1_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_integer_arithmetic_rbit[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_integer_arithmetic_rbit d (datasize :: 'datasize::len itself) n)"
  by (unfold execute_aarch64_instrs_integer_arithmetic_rbit_def, non_mem_expI)

lemma non_mem_exp_decode_rbit_int_aarch64_instrs_integer_arithmetic_rbit[non_mem_expI]:
  "non_mem_exp (decode_rbit_int_aarch64_instrs_integer_arithmetic_rbit Rd Rn b__0)"
  by (unfold decode_rbit_int_aarch64_instrs_integer_arithmetic_rbit_def, non_mem_expI)

lemma non_mem_exp_decode_ret_aarch64_instrs_branch_unconditional_register[non_mem_expI]:
  "non_mem_exp (decode_ret_aarch64_instrs_branch_unconditional_register Rm Rn M A op Z)"
  by (unfold decode_ret_aarch64_instrs_branch_unconditional_register_def, non_mem_expI)

lemma non_mem_exp_decode_reta_aarch64_instrs_branch_unconditional_register[non_mem_expI]:
  "non_mem_exp (decode_reta_aarch64_instrs_branch_unconditional_register Rm Rn M A op Z)"
  by (unfold decode_reta_aarch64_instrs_branch_unconditional_register_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_arithmetic_unary_rev[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_arithmetic_unary_rev containers d (datasize :: 'datasize::len itself) elements_per_container (esize :: 'esize::len itself) n)"
  by (unfold execute_aarch64_instrs_vector_arithmetic_unary_rev_def, non_mem_expI)

lemma non_mem_exp_decode_rev16_advsimd_aarch64_instrs_vector_arithmetic_unary_rev[non_mem_expI]:
  "non_mem_exp (decode_rev16_advsimd_aarch64_instrs_vector_arithmetic_unary_rev Rd Rn o0 b__0 U b__1)"
  by (unfold decode_rev16_advsimd_aarch64_instrs_vector_arithmetic_unary_rev_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_integer_arithmetic_rev[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_integer_arithmetic_rev container_size d (datasize :: 'datasize::len itself) n)"
  by (unfold execute_aarch64_instrs_integer_arithmetic_rev_def, non_mem_expI)

lemma non_mem_exp_decode_rev16_int_aarch64_instrs_integer_arithmetic_rev[non_mem_expI]:
  "non_mem_exp (decode_rev16_int_aarch64_instrs_integer_arithmetic_rev Rd Rn opc b__0)"
  by (unfold decode_rev16_int_aarch64_instrs_integer_arithmetic_rev_def, non_mem_expI)

lemma non_mem_exp_decode_rev32_advsimd_aarch64_instrs_vector_arithmetic_unary_rev[non_mem_expI]:
  "non_mem_exp (decode_rev32_advsimd_aarch64_instrs_vector_arithmetic_unary_rev Rd Rn o0 b__0 U b__1)"
  by (unfold decode_rev32_advsimd_aarch64_instrs_vector_arithmetic_unary_rev_def, non_mem_expI)

lemma non_mem_exp_decode_rev32_int_aarch64_instrs_integer_arithmetic_rev[non_mem_expI]:
  "non_mem_exp (decode_rev32_int_aarch64_instrs_integer_arithmetic_rev Rd Rn opc b__0)"
  by (unfold decode_rev32_int_aarch64_instrs_integer_arithmetic_rev_def, non_mem_expI)

lemma non_mem_exp_decode_rev64_advsimd_aarch64_instrs_vector_arithmetic_unary_rev[non_mem_expI]:
  "non_mem_exp (decode_rev64_advsimd_aarch64_instrs_vector_arithmetic_unary_rev Rd Rn o0 b__0 U b__1)"
  by (unfold decode_rev64_advsimd_aarch64_instrs_vector_arithmetic_unary_rev_def, non_mem_expI)

lemma non_mem_exp_decode_rev_aarch64_instrs_integer_arithmetic_rev[non_mem_expI]:
  "non_mem_exp (decode_rev_aarch64_instrs_integer_arithmetic_rev Rd Rn opc b__0)"
  by (unfold decode_rev_aarch64_instrs_integer_arithmetic_rev_def, non_mem_expI)

lemma non_mem_exp_decode_rorv_aarch64_instrs_integer_shift_variable[non_mem_expI]:
  "non_mem_exp (decode_rorv_aarch64_instrs_integer_shift_variable Rd Rn op2 Rm b__0)"
  by (unfold decode_rorv_aarch64_instrs_integer_shift_variable_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_shift_right_narrow_logical[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_shift_right_narrow_logical d datasize elements l__473 n part round__arg shift)"
  by (unfold execute_aarch64_instrs_vector_shift_right_narrow_logical_def, non_mem_expI)

lemma non_mem_exp_decode_rshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_logical[non_mem_expI]:
  "non_mem_exp (decode_rshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_logical Rd Rn op immb b__0 Q)"
  by (unfold decode_rshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_logical_def, non_mem_expI)

lemma non_mem_exp_decode_rsubhn_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_narrow[non_mem_expI]:
  "non_mem_exp (decode_rsubhn_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_narrow Rd Rn o1 Rm b__0 U Q)"
  by (unfold decode_rsubhn_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_narrow_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_arithmetic_binary_uniform_diff[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_arithmetic_binary_uniform_diff accumulate d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) m n is_unsigned)"
  by (unfold execute_aarch64_instrs_vector_arithmetic_binary_uniform_diff_def, non_mem_expI)

lemma non_mem_exp_decode_saba_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_diff[non_mem_expI]:
  "non_mem_exp (decode_saba_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_diff Rd Rn ac Rm b__0 U b__1)"
  by (unfold decode_saba_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_diff_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_arithmetic_binary_disparate_diff[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_arithmetic_binary_disparate_diff accumulate d datasize elements l__469 m n part is_unsigned)"
  by (unfold execute_aarch64_instrs_vector_arithmetic_binary_disparate_diff_def, non_mem_expI)

lemma non_mem_exp_decode_sabal_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_diff[non_mem_expI]:
  "non_mem_exp (decode_sabal_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_diff Rd Rn op Rm b__0 U Q)"
  by (unfold decode_sabal_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_diff_def, non_mem_expI)

lemma non_mem_exp_decode_sabd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_diff[non_mem_expI]:
  "non_mem_exp (decode_sabd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_diff Rd Rn ac Rm b__0 U b__1)"
  by (unfold decode_sabd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_diff_def, non_mem_expI)

lemma non_mem_exp_decode_sabdl_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_diff[non_mem_expI]:
  "non_mem_exp (decode_sabdl_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_diff Rd Rn op Rm b__0 U Q)"
  by (unfold decode_sabdl_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_diff_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_arithmetic_unary_add_pairwise[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_arithmetic_unary_add_pairwise acc d (datasize :: 'datasize::len itself) elements l__169 n is_unsigned)"
  by (unfold execute_aarch64_instrs_vector_arithmetic_unary_add_pairwise_def, non_mem_expI)

lemma non_mem_exp_decode_sadalp_advsimd_aarch64_instrs_vector_arithmetic_unary_add_pairwise[non_mem_expI]:
  "non_mem_exp (decode_sadalp_advsimd_aarch64_instrs_vector_arithmetic_unary_add_pairwise Rd Rn op b__0 U b__1)"
  by (unfold decode_sadalp_advsimd_aarch64_instrs_vector_arithmetic_unary_add_pairwise_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_long[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_long d datasize elements l__316 m n part sub_op is_unsigned)"
  by (unfold execute_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_long_def, non_mem_expI)

lemma non_mem_exp_decode_saddl_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_long[non_mem_expI]:
  "non_mem_exp (decode_saddl_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_long Rd Rn o1 Rm b__0 U Q)"
  by (unfold decode_saddl_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_long_def, non_mem_expI)

lemma non_mem_exp_decode_saddlp_advsimd_aarch64_instrs_vector_arithmetic_unary_add_pairwise[non_mem_expI]:
  "non_mem_exp (decode_saddlp_advsimd_aarch64_instrs_vector_arithmetic_unary_add_pairwise Rd Rn op b__0 U b__1)"
  by (unfold decode_saddlp_advsimd_aarch64_instrs_vector_arithmetic_unary_add_pairwise_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_reduce_add_long[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_reduce_add_long d (datasize :: 'datasize::len itself) elements l__159 n is_unsigned)"
  by (unfold execute_aarch64_instrs_vector_reduce_add_long_def, non_mem_expI)

lemma non_mem_exp_decode_saddlv_advsimd_aarch64_instrs_vector_reduce_add_long[non_mem_expI]:
  "non_mem_exp (decode_saddlv_advsimd_aarch64_instrs_vector_reduce_add_long Rd Rn b__0 U b__1)"
  by (unfold decode_saddlv_advsimd_aarch64_instrs_vector_reduce_add_long_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_wide[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_wide d datasize elements l__478 m n part sub_op is_unsigned)"
  by (unfold execute_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_wide_def, non_mem_expI)

lemma non_mem_exp_decode_saddw_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_wide[non_mem_expI]:
  "non_mem_exp (decode_saddw_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_wide Rd Rn o1 Rm b__0 U Q)"
  by (unfold decode_saddw_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_wide_def, non_mem_expI)

lemma non_mem_exp_decode_sbc_aarch64_instrs_integer_arithmetic_add_sub_carry[non_mem_expI]:
  "non_mem_exp (decode_sbc_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn Rm S op b__0)"
  by (unfold decode_sbc_aarch64_instrs_integer_arithmetic_add_sub_carry_def, non_mem_expI)

lemma non_mem_exp_decode_sbcs_aarch64_instrs_integer_arithmetic_add_sub_carry[non_mem_expI]:
  "non_mem_exp (decode_sbcs_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn Rm S op b__0)"
  by (unfold decode_sbcs_aarch64_instrs_integer_arithmetic_add_sub_carry_def, non_mem_expI)

lemma non_mem_exp_decode_sbfm_aarch64_instrs_integer_bitfield[non_mem_expI]:
  "non_mem_exp (decode_sbfm_aarch64_instrs_integer_bitfield Rd Rn imms immr N opc b__0)"
  by (unfold decode_sbfm_aarch64_instrs_integer_bitfield_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_shift_conv_int_sisd[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_shift_conv_int_sisd d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) fracbits n rounding is_unsigned)"
  by (unfold execute_aarch64_instrs_vector_shift_conv_int_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_scvtf_advsimd_fix_aarch64_instrs_vector_shift_conv_int_simd[non_mem_expI]:
  "non_mem_exp (decode_scvtf_advsimd_fix_aarch64_instrs_vector_shift_conv_int_simd Rd Rn immb b__0 U b__1)"
  by (unfold decode_scvtf_advsimd_fix_aarch64_instrs_vector_shift_conv_int_simd_def, non_mem_expI)

lemma non_mem_exp_decode_scvtf_advsimd_fix_aarch64_instrs_vector_shift_conv_int_sisd[non_mem_expI]:
  "non_mem_exp (decode_scvtf_advsimd_fix_aarch64_instrs_vector_shift_conv_int_sisd Rd Rn immb b__0 U)"
  by (unfold decode_scvtf_advsimd_fix_aarch64_instrs_vector_shift_conv_int_sisd_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_int_sisd[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_int_sisd d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) n is_unsigned)"
  by (unfold execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_int_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_scvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_int_simd[non_mem_expI]:
  "non_mem_exp (decode_scvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_int_simd Rd Rn b__0 U b__1)"
  by (unfold decode_scvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_int_simd_def, non_mem_expI)

lemma non_mem_exp_decode_scvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_int_sisd[non_mem_expI]:
  "non_mem_exp (decode_scvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_int_sisd Rd Rn b__0 U)"
  by (unfold decode_scvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_int_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_scvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_int_simd[non_mem_expI]:
  "non_mem_exp (decode_scvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_int_simd Rd Rn U b__0)"
  by (unfold decode_scvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_int_simd_def, non_mem_expI)

lemma non_mem_exp_decode_scvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_int_sisd[non_mem_expI]:
  "non_mem_exp (decode_scvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_int_sisd Rd Rn U)"
  by (unfold decode_scvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_int_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_scvtf_float_fix_aarch64_instrs_float_convert_fix[non_mem_expI]:
  "non_mem_exp (decode_scvtf_float_fix_aarch64_instrs_float_convert_fix Rd Rn scale opcode rmode b__0 b__1)"
  by (unfold decode_scvtf_float_fix_aarch64_instrs_float_convert_fix_def, non_mem_expI)

lemma non_mem_exp_decode_scvtf_float_int_aarch64_instrs_float_convert_int[non_mem_expI]:
  "non_mem_exp (decode_scvtf_float_int_aarch64_instrs_float_convert_int Rd Rn opcode rmode ftype b__0)"
  by (unfold decode_scvtf_float_int_aarch64_instrs_float_convert_int_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_integer_arithmetic_div[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_integer_arithmetic_div d (datasize :: 'datasize::len itself) m n is_unsigned)"
  by (unfold execute_aarch64_instrs_integer_arithmetic_div_def, non_mem_expI)

lemma non_mem_exp_decode_sdiv_aarch64_instrs_integer_arithmetic_div[non_mem_expI]:
  "non_mem_exp (decode_sdiv_aarch64_instrs_integer_arithmetic_div Rd Rn o1 Rm b__0)"
  by (unfold decode_sdiv_aarch64_instrs_integer_arithmetic_div_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_arithmetic_binary_element_dotp[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_arithmetic_binary_element_dotp d (datasize :: 'datasize::len itself) elements l__375 index__arg m n is_signed)"
  by (unfold execute_aarch64_instrs_vector_arithmetic_binary_element_dotp_def, non_mem_expI)

lemma non_mem_exp_decode_sdot_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_dotp[non_mem_expI]:
  "non_mem_exp (decode_sdot_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_dotp Rd Rn H Rm M L b__0 U b__1)"
  by (unfold decode_sdot_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_dotp_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_dotp[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_dotp d (datasize :: 'datasize::len itself) elements l__165 m n is_signed)"
  by (unfold execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_dotp_def, non_mem_expI)

lemma non_mem_exp_decode_sdot_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_dotp[non_mem_expI]:
  "non_mem_exp (decode_sdot_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_dotp Rd Rn Rm b__0 U b__1)"
  by (unfold decode_sdot_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_dotp_def, non_mem_expI)

lemma non_mem_exp_decode_sev_aarch64_instrs_system_hints[non_mem_expI]:
  "non_mem_exp (decode_sev_aarch64_instrs_system_hints op2 CRm)"
  by (unfold decode_sev_aarch64_instrs_system_hints_def, non_mem_expI)

lemma non_mem_exp_decode_sevl_aarch64_instrs_system_hints[non_mem_expI]:
  "non_mem_exp (decode_sevl_aarch64_instrs_system_hints op2 CRm)"
  by (unfold decode_sevl_aarch64_instrs_system_hints_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_crypto_sha3op_sha1_hash_choose[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_crypto_sha3op_sha1_hash_choose d m n)"
  by (unfold execute_aarch64_instrs_vector_crypto_sha3op_sha1_hash_choose_def, non_mem_expI)

lemma non_mem_exp_decode_sha1c_advsimd_aarch64_instrs_vector_crypto_sha3op_sha1_hash_choose[non_mem_expI]:
  "non_mem_exp (decode_sha1c_advsimd_aarch64_instrs_vector_crypto_sha3op_sha1_hash_choose Rd Rn Rm)"
  by (unfold decode_sha1c_advsimd_aarch64_instrs_vector_crypto_sha3op_sha1_hash_choose_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_crypto_sha2op_sha1_hash[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_crypto_sha2op_sha1_hash d n)"
  by (unfold execute_aarch64_instrs_vector_crypto_sha2op_sha1_hash_def, non_mem_expI)

lemma non_mem_exp_decode_sha1h_advsimd_aarch64_instrs_vector_crypto_sha2op_sha1_hash[non_mem_expI]:
  "non_mem_exp (decode_sha1h_advsimd_aarch64_instrs_vector_crypto_sha2op_sha1_hash Rd Rn)"
  by (unfold decode_sha1h_advsimd_aarch64_instrs_vector_crypto_sha2op_sha1_hash_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_crypto_sha3op_sha1_hash_majority[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_crypto_sha3op_sha1_hash_majority d m n)"
  by (unfold execute_aarch64_instrs_vector_crypto_sha3op_sha1_hash_majority_def, non_mem_expI)

lemma non_mem_exp_decode_sha1m_advsimd_aarch64_instrs_vector_crypto_sha3op_sha1_hash_majority[non_mem_expI]:
  "non_mem_exp (decode_sha1m_advsimd_aarch64_instrs_vector_crypto_sha3op_sha1_hash_majority Rd Rn Rm)"
  by (unfold decode_sha1m_advsimd_aarch64_instrs_vector_crypto_sha3op_sha1_hash_majority_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_crypto_sha3op_sha1_hash_parity[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_crypto_sha3op_sha1_hash_parity d m n)"
  by (unfold execute_aarch64_instrs_vector_crypto_sha3op_sha1_hash_parity_def, non_mem_expI)

lemma non_mem_exp_decode_sha1p_advsimd_aarch64_instrs_vector_crypto_sha3op_sha1_hash_parity[non_mem_expI]:
  "non_mem_exp (decode_sha1p_advsimd_aarch64_instrs_vector_crypto_sha3op_sha1_hash_parity Rd Rn Rm)"
  by (unfold decode_sha1p_advsimd_aarch64_instrs_vector_crypto_sha3op_sha1_hash_parity_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_crypto_sha3op_sha1_sched0[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_crypto_sha3op_sha1_sched0 d m n)"
  by (unfold execute_aarch64_instrs_vector_crypto_sha3op_sha1_sched0_def, non_mem_expI)

lemma non_mem_exp_decode_sha1su0_advsimd_aarch64_instrs_vector_crypto_sha3op_sha1_sched0[non_mem_expI]:
  "non_mem_exp (decode_sha1su0_advsimd_aarch64_instrs_vector_crypto_sha3op_sha1_sched0 Rd Rn Rm)"
  by (unfold decode_sha1su0_advsimd_aarch64_instrs_vector_crypto_sha3op_sha1_sched0_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_crypto_sha2op_sha1_sched1[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_crypto_sha2op_sha1_sched1 d n)"
  by (unfold execute_aarch64_instrs_vector_crypto_sha2op_sha1_sched1_def, non_mem_expI)

lemma non_mem_exp_decode_sha1su1_advsimd_aarch64_instrs_vector_crypto_sha2op_sha1_sched1[non_mem_expI]:
  "non_mem_exp (decode_sha1su1_advsimd_aarch64_instrs_vector_crypto_sha2op_sha1_sched1 Rd Rn)"
  by (unfold decode_sha1su1_advsimd_aarch64_instrs_vector_crypto_sha2op_sha1_sched1_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_crypto_sha3op_sha256_hash[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_crypto_sha3op_sha256_hash d m n part1)"
  by (unfold execute_aarch64_instrs_vector_crypto_sha3op_sha256_hash_def, non_mem_expI)

lemma non_mem_exp_decode_sha256h2_advsimd_aarch64_instrs_vector_crypto_sha3op_sha256_hash[non_mem_expI]:
  "non_mem_exp (decode_sha256h2_advsimd_aarch64_instrs_vector_crypto_sha3op_sha256_hash Rd Rn P Rm)"
  by (unfold decode_sha256h2_advsimd_aarch64_instrs_vector_crypto_sha3op_sha256_hash_def, non_mem_expI)

lemma non_mem_exp_decode_sha256h_advsimd_aarch64_instrs_vector_crypto_sha3op_sha256_hash[non_mem_expI]:
  "non_mem_exp (decode_sha256h_advsimd_aarch64_instrs_vector_crypto_sha3op_sha256_hash Rd Rn P Rm)"
  by (unfold decode_sha256h_advsimd_aarch64_instrs_vector_crypto_sha3op_sha256_hash_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_crypto_sha2op_sha256_sched0[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_crypto_sha2op_sha256_sched0 d n)"
  by (unfold execute_aarch64_instrs_vector_crypto_sha2op_sha256_sched0_def, non_mem_expI)

lemma non_mem_exp_decode_sha256su0_advsimd_aarch64_instrs_vector_crypto_sha2op_sha256_sched0[non_mem_expI]:
  "non_mem_exp (decode_sha256su0_advsimd_aarch64_instrs_vector_crypto_sha2op_sha256_sched0 Rd Rn)"
  by (unfold decode_sha256su0_advsimd_aarch64_instrs_vector_crypto_sha2op_sha256_sched0_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_crypto_sha3op_sha256_sched1[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_crypto_sha3op_sha256_sched1 d m n)"
  by (unfold execute_aarch64_instrs_vector_crypto_sha3op_sha256_sched1_def, non_mem_expI)

lemma non_mem_exp_decode_sha256su1_advsimd_aarch64_instrs_vector_crypto_sha3op_sha256_sched1[non_mem_expI]:
  "non_mem_exp (decode_sha256su1_advsimd_aarch64_instrs_vector_crypto_sha3op_sha256_sched1 Rd Rn Rm)"
  by (unfold decode_sha256su1_advsimd_aarch64_instrs_vector_crypto_sha3op_sha256_sched1_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_crypto_sha512_sha512h2[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_crypto_sha512_sha512h2 d m n)"
  by (unfold execute_aarch64_instrs_vector_crypto_sha512_sha512h2_def, non_mem_expI)

lemma non_mem_exp_decode_sha512h2_advsimd_aarch64_instrs_vector_crypto_sha512_sha512h2[non_mem_expI]:
  "non_mem_exp (decode_sha512h2_advsimd_aarch64_instrs_vector_crypto_sha512_sha512h2 Rd Rn Rm)"
  by (unfold decode_sha512h2_advsimd_aarch64_instrs_vector_crypto_sha512_sha512h2_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_crypto_sha512_sha512h[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_crypto_sha512_sha512h d m n)"
  by (unfold execute_aarch64_instrs_vector_crypto_sha512_sha512h_def, non_mem_expI)

lemma non_mem_exp_decode_sha512h_advsimd_aarch64_instrs_vector_crypto_sha512_sha512h[non_mem_expI]:
  "non_mem_exp (decode_sha512h_advsimd_aarch64_instrs_vector_crypto_sha512_sha512h Rd Rn Rm)"
  by (unfold decode_sha512h_advsimd_aarch64_instrs_vector_crypto_sha512_sha512h_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_crypto_sha512_sha512su0[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_crypto_sha512_sha512su0 d n)"
  by (unfold execute_aarch64_instrs_vector_crypto_sha512_sha512su0_def, non_mem_expI)

lemma non_mem_exp_decode_sha512su0_advsimd_aarch64_instrs_vector_crypto_sha512_sha512su0[non_mem_expI]:
  "non_mem_exp (decode_sha512su0_advsimd_aarch64_instrs_vector_crypto_sha512_sha512su0 Rd Rn)"
  by (unfold decode_sha512su0_advsimd_aarch64_instrs_vector_crypto_sha512_sha512su0_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_crypto_sha512_sha512su1[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_crypto_sha512_sha512su1 d m n)"
  by (unfold execute_aarch64_instrs_vector_crypto_sha512_sha512su1_def, non_mem_expI)

lemma non_mem_exp_decode_sha512su1_advsimd_aarch64_instrs_vector_crypto_sha512_sha512su1[non_mem_expI]:
  "non_mem_exp (decode_sha512su1_advsimd_aarch64_instrs_vector_crypto_sha512_sha512su1 Rd Rn Rm)"
  by (unfold decode_sha512su1_advsimd_aarch64_instrs_vector_crypto_sha512_sha512su1_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_arithmetic_binary_uniform_add_halving_truncating[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_arithmetic_binary_uniform_add_halving_truncating d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) m n is_unsigned)"
  by (unfold execute_aarch64_instrs_vector_arithmetic_binary_uniform_add_halving_truncating_def, non_mem_expI)

lemma non_mem_exp_decode_shadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_halving_truncating[non_mem_expI]:
  "non_mem_exp (decode_shadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_halving_truncating Rd Rn Rm b__0 U b__1)"
  by (unfold decode_shadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_halving_truncating_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_shift_left_sisd[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_shift_left_sisd d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) n shift)"
  by (unfold execute_aarch64_instrs_vector_shift_left_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_shl_advsimd_aarch64_instrs_vector_shift_left_simd[non_mem_expI]:
  "non_mem_exp (decode_shl_advsimd_aarch64_instrs_vector_shift_left_simd Rd Rn immb b__0 b__1)"
  by (unfold decode_shl_advsimd_aarch64_instrs_vector_shift_left_simd_def, non_mem_expI)

lemma non_mem_exp_decode_shl_advsimd_aarch64_instrs_vector_shift_left_sisd[non_mem_expI]:
  "non_mem_exp (decode_shl_advsimd_aarch64_instrs_vector_shift_left_sisd Rd Rn immb immh)"
  by (unfold decode_shl_advsimd_aarch64_instrs_vector_shift_left_sisd_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_arithmetic_unary_shift[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_arithmetic_unary_shift d datasize elements l__49 n part shift is_unsigned)"
  by (unfold execute_aarch64_instrs_vector_arithmetic_unary_shift_def, non_mem_expI)

lemma non_mem_exp_decode_shll_advsimd_aarch64_instrs_vector_arithmetic_unary_shift[non_mem_expI]:
  "non_mem_exp (decode_shll_advsimd_aarch64_instrs_vector_arithmetic_unary_shift Rd Rn b__0 Q)"
  by (unfold decode_shll_advsimd_aarch64_instrs_vector_arithmetic_unary_shift_def, non_mem_expI)

lemma non_mem_exp_decode_shrn_advsimd_aarch64_instrs_vector_shift_right_narrow_logical[non_mem_expI]:
  "non_mem_exp (decode_shrn_advsimd_aarch64_instrs_vector_shift_right_narrow_logical Rd Rn op immb b__0 Q)"
  by (unfold decode_shrn_advsimd_aarch64_instrs_vector_shift_right_narrow_logical_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_arithmetic_binary_uniform_sub_int[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_arithmetic_binary_uniform_sub_int d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) m n is_unsigned)"
  by (unfold execute_aarch64_instrs_vector_arithmetic_binary_uniform_sub_int_def, non_mem_expI)

lemma non_mem_exp_decode_shsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_int[non_mem_expI]:
  "non_mem_exp (decode_shsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_int Rd Rn Rm b__0 U b__1)"
  by (unfold decode_shsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_int_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_shift_left_insert_sisd[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_shift_left_insert_sisd d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) n shift)"
  by (unfold execute_aarch64_instrs_vector_shift_left_insert_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_sli_advsimd_aarch64_instrs_vector_shift_left_insert_simd[non_mem_expI]:
  "non_mem_exp (decode_sli_advsimd_aarch64_instrs_vector_shift_left_insert_simd Rd Rn immb b__0 b__1)"
  by (unfold decode_sli_advsimd_aarch64_instrs_vector_shift_left_insert_simd_def, non_mem_expI)

lemma non_mem_exp_decode_sli_advsimd_aarch64_instrs_vector_shift_left_insert_sisd[non_mem_expI]:
  "non_mem_exp (decode_sli_advsimd_aarch64_instrs_vector_shift_left_insert_sisd Rd Rn immb immh)"
  by (unfold decode_sli_advsimd_aarch64_instrs_vector_shift_left_insert_sisd_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_crypto_sm3_sm3partw1[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_crypto_sm3_sm3partw1 d m n)"
  by (unfold execute_aarch64_instrs_vector_crypto_sm3_sm3partw1_def, non_mem_expI)

lemma non_mem_exp_decode_sm3partw1_advsimd_aarch64_instrs_vector_crypto_sm3_sm3partw1[non_mem_expI]:
  "non_mem_exp (decode_sm3partw1_advsimd_aarch64_instrs_vector_crypto_sm3_sm3partw1 Rd Rn Rm)"
  by (unfold decode_sm3partw1_advsimd_aarch64_instrs_vector_crypto_sm3_sm3partw1_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_crypto_sm3_sm3partw2[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_crypto_sm3_sm3partw2 d m n)"
  by (unfold execute_aarch64_instrs_vector_crypto_sm3_sm3partw2_def, non_mem_expI)

lemma non_mem_exp_decode_sm3partw2_advsimd_aarch64_instrs_vector_crypto_sm3_sm3partw2[non_mem_expI]:
  "non_mem_exp (decode_sm3partw2_advsimd_aarch64_instrs_vector_crypto_sm3_sm3partw2 Rd Rn Rm)"
  by (unfold decode_sm3partw2_advsimd_aarch64_instrs_vector_crypto_sm3_sm3partw2_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_crypto_sm3_sm3ss1[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_crypto_sm3_sm3ss1 a d m n)"
  by (unfold execute_aarch64_instrs_vector_crypto_sm3_sm3ss1_def, non_mem_expI)

lemma non_mem_exp_decode_sm3ss1_advsimd_aarch64_instrs_vector_crypto_sm3_sm3ss1[non_mem_expI]:
  "non_mem_exp (decode_sm3ss1_advsimd_aarch64_instrs_vector_crypto_sm3_sm3ss1 Rd Rn Ra Rm)"
  by (unfold decode_sm3ss1_advsimd_aarch64_instrs_vector_crypto_sm3_sm3ss1_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_crypto_sm3_sm3tt1a[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_crypto_sm3_sm3tt1a d i m n)"
  by (unfold execute_aarch64_instrs_vector_crypto_sm3_sm3tt1a_def, non_mem_expI)

lemma non_mem_exp_decode_sm3tt1a_advsimd_aarch64_instrs_vector_crypto_sm3_sm3tt1a[non_mem_expI]:
  "non_mem_exp (decode_sm3tt1a_advsimd_aarch64_instrs_vector_crypto_sm3_sm3tt1a Rd Rn imm2 Rm)"
  by (unfold decode_sm3tt1a_advsimd_aarch64_instrs_vector_crypto_sm3_sm3tt1a_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_crypto_sm3_sm3tt1b[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_crypto_sm3_sm3tt1b d i m n)"
  by (unfold execute_aarch64_instrs_vector_crypto_sm3_sm3tt1b_def, non_mem_expI)

lemma non_mem_exp_decode_sm3tt1b_advsimd_aarch64_instrs_vector_crypto_sm3_sm3tt1b[non_mem_expI]:
  "non_mem_exp (decode_sm3tt1b_advsimd_aarch64_instrs_vector_crypto_sm3_sm3tt1b Rd Rn imm2 Rm)"
  by (unfold decode_sm3tt1b_advsimd_aarch64_instrs_vector_crypto_sm3_sm3tt1b_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_crypto_sm3_sm3tt2a[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_crypto_sm3_sm3tt2a d i m n)"
  by (unfold execute_aarch64_instrs_vector_crypto_sm3_sm3tt2a_def, non_mem_expI)

lemma non_mem_exp_decode_sm3tt2a_advsimd_aarch64_instrs_vector_crypto_sm3_sm3tt2a[non_mem_expI]:
  "non_mem_exp (decode_sm3tt2a_advsimd_aarch64_instrs_vector_crypto_sm3_sm3tt2a Rd Rn imm2 Rm)"
  by (unfold decode_sm3tt2a_advsimd_aarch64_instrs_vector_crypto_sm3_sm3tt2a_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_crypto_sm3_sm3tt2b[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_crypto_sm3_sm3tt2b d i m n)"
  by (unfold execute_aarch64_instrs_vector_crypto_sm3_sm3tt2b_def, non_mem_expI)

lemma non_mem_exp_decode_sm3tt2b_advsimd_aarch64_instrs_vector_crypto_sm3_sm3tt2b[non_mem_expI]:
  "non_mem_exp (decode_sm3tt2b_advsimd_aarch64_instrs_vector_crypto_sm3_sm3tt2b Rd Rn imm2 Rm)"
  by (unfold decode_sm3tt2b_advsimd_aarch64_instrs_vector_crypto_sm3_sm3tt2b_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_crypto_sm4_sm4enc[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_crypto_sm4_sm4enc d n)"
  by (unfold execute_aarch64_instrs_vector_crypto_sm4_sm4enc_def, non_mem_expI)

lemma non_mem_exp_decode_sm4e_advsimd_aarch64_instrs_vector_crypto_sm4_sm4enc[non_mem_expI]:
  "non_mem_exp (decode_sm4e_advsimd_aarch64_instrs_vector_crypto_sm4_sm4enc Rd Rn)"
  by (unfold decode_sm4e_advsimd_aarch64_instrs_vector_crypto_sm4_sm4enc_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_crypto_sm4_sm4enckey[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_crypto_sm4_sm4enckey d m n)"
  by (unfold execute_aarch64_instrs_vector_crypto_sm4_sm4enckey_def, non_mem_expI)

lemma non_mem_exp_decode_sm4ekey_advsimd_aarch64_instrs_vector_crypto_sm4_sm4enckey[non_mem_expI]:
  "non_mem_exp (decode_sm4ekey_advsimd_aarch64_instrs_vector_crypto_sm4_sm4enckey Rd Rn Rm)"
  by (unfold decode_sm4ekey_advsimd_aarch64_instrs_vector_crypto_sm4_sm4enckey_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_integer_arithmetic_mul_widening_32_64[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_integer_arithmetic_mul_widening_32_64 a d datasize destsize m n sub_op is_unsigned)"
  by (unfold execute_aarch64_instrs_integer_arithmetic_mul_widening_32_64_def, non_mem_expI)

lemma non_mem_exp_decode_smaddl_aarch64_instrs_integer_arithmetic_mul_widening_32_64[non_mem_expI]:
  "non_mem_exp (decode_smaddl_aarch64_instrs_integer_arithmetic_mul_widening_32_64 Rd Rn Ra o0 Rm U)"
  by (unfold decode_smaddl_aarch64_instrs_integer_arithmetic_mul_widening_32_64_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_single[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_single d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) m minimum n is_unsigned)"
  by (unfold execute_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_single_def, non_mem_expI)

lemma non_mem_exp_decode_smax_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_single[non_mem_expI]:
  "non_mem_exp (decode_smax_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_single Rd Rn o1 Rm b__0 U b__1)"
  by (unfold decode_smax_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_single_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_pair[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_pair d l__193 elements (esize :: 'esize::len itself) m minimum n is_unsigned)"
  by (unfold execute_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_pair_def, non_mem_expI)

lemma non_mem_exp_decode_smaxp_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_pair[non_mem_expI]:
  "non_mem_exp (decode_smaxp_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_pair Rd Rn o1 Rm b__0 U b__1)"
  by (unfold decode_smaxp_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_pair_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_reduce_int_max[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_reduce_int_max d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) min__arg n is_unsigned)"
  by (unfold execute_aarch64_instrs_vector_reduce_int_max_def, non_mem_expI)

lemma non_mem_exp_decode_smaxv_advsimd_aarch64_instrs_vector_reduce_int_max[non_mem_expI]:
  "non_mem_exp (decode_smaxv_advsimd_aarch64_instrs_vector_reduce_int_max Rd Rn op b__0 U b__1)"
  by (unfold decode_smaxv_advsimd_aarch64_instrs_vector_reduce_int_max_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_system_exceptions_runtime_smc[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_system_exceptions_runtime_smc imm)"
  by (unfold execute_aarch64_instrs_system_exceptions_runtime_smc_def, non_mem_expI)

lemma non_mem_exp_decode_smc_aarch64_instrs_system_exceptions_runtime_smc[non_mem_expI]:
  "non_mem_exp (decode_smc_aarch64_instrs_system_exceptions_runtime_smc imm16)"
  by (unfold decode_smc_aarch64_instrs_system_exceptions_runtime_smc_def, non_mem_expI)

lemma non_mem_exp_decode_smin_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_single[non_mem_expI]:
  "non_mem_exp (decode_smin_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_single Rd Rn o1 Rm b__0 U b__1)"
  by (unfold decode_smin_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_single_def, non_mem_expI)

lemma non_mem_exp_decode_sminp_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_pair[non_mem_expI]:
  "non_mem_exp (decode_sminp_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_pair Rd Rn o1 Rm b__0 U b__1)"
  by (unfold decode_sminp_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_pair_def, non_mem_expI)

lemma non_mem_exp_decode_sminv_advsimd_aarch64_instrs_vector_reduce_int_max[non_mem_expI]:
  "non_mem_exp (decode_sminv_advsimd_aarch64_instrs_vector_reduce_int_max Rd Rn op b__0 U b__1)"
  by (unfold decode_sminv_advsimd_aarch64_instrs_vector_reduce_int_max_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_long[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_long d datasize elements l__185 (idxdsize :: 'idxdsize::len itself) index__arg m n part sub_op is_unsigned)"
  by (unfold execute_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_long_def, non_mem_expI)

lemma non_mem_exp_decode_smlal_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_long[non_mem_expI]:
  "non_mem_exp (decode_smlal_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_long Rd Rn b__0 o2 Rm M L b__1 U Q)"
  by (unfold decode_smlal_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_long_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_arithmetic_binary_disparate_mul_accum[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_arithmetic_binary_disparate_mul_accum d datasize elements l__537 m n part sub_op is_unsigned)"
  by (unfold execute_aarch64_instrs_vector_arithmetic_binary_disparate_mul_accum_def, non_mem_expI)

lemma non_mem_exp_decode_smlal_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_accum[non_mem_expI]:
  "non_mem_exp (decode_smlal_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_accum Rd Rn o1 Rm b__0 U Q)"
  by (unfold decode_smlal_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_accum_def, non_mem_expI)

lemma non_mem_exp_decode_smlsl_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_long[non_mem_expI]:
  "non_mem_exp (decode_smlsl_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_long Rd Rn b__0 o2 Rm M L b__1 U Q)"
  by (unfold decode_smlsl_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_long_def, non_mem_expI)

lemma non_mem_exp_decode_smlsl_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_accum[non_mem_expI]:
  "non_mem_exp (decode_smlsl_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_accum Rd Rn o1 Rm b__0 U Q)"
  by (unfold decode_smlsl_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_accum_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_transfer_integer_move_signed[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_transfer_integer_move_signed d (datasize :: 'datasize::len itself) (esize :: 'esize::len itself) (idxdsize :: 'idxdsize::len itself) index__arg n)"
  by (unfold execute_aarch64_instrs_vector_transfer_integer_move_signed_def, non_mem_expI)

lemma non_mem_exp_decode_smov_advsimd_aarch64_instrs_vector_transfer_integer_move_signed[non_mem_expI]:
  "non_mem_exp (decode_smov_advsimd_aarch64_instrs_vector_transfer_integer_move_signed Rd Rn b__0 b__1)"
  by (unfold decode_smov_advsimd_aarch64_instrs_vector_transfer_integer_move_signed_def, non_mem_expI)

lemma non_mem_exp_decode_smsubl_aarch64_instrs_integer_arithmetic_mul_widening_32_64[non_mem_expI]:
  "non_mem_exp (decode_smsubl_aarch64_instrs_integer_arithmetic_mul_widening_32_64 Rd Rn Ra o0 Rm U)"
  by (unfold decode_smsubl_aarch64_instrs_integer_arithmetic_mul_widening_32_64_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_integer_arithmetic_mul_widening_64_128hi[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_integer_arithmetic_mul_widening_64_128hi d datasize m n is_unsigned)"
  by (unfold execute_aarch64_instrs_integer_arithmetic_mul_widening_64_128hi_def, non_mem_expI)

lemma non_mem_exp_decode_smulh_aarch64_instrs_integer_arithmetic_mul_widening_64_128hi[non_mem_expI]:
  "non_mem_exp (decode_smulh_aarch64_instrs_integer_arithmetic_mul_widening_64_128hi Rd Rn Ra Rm U)"
  by (unfold decode_smulh_aarch64_instrs_integer_arithmetic_mul_widening_64_128hi_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_arithmetic_binary_element_mul_long[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_long d datasize elements l__173 (idxdsize :: 'idxdsize::len itself) index__arg m n part is_unsigned)"
  by (unfold execute_aarch64_instrs_vector_arithmetic_binary_element_mul_long_def, non_mem_expI)

lemma non_mem_exp_decode_smull_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_long[non_mem_expI]:
  "non_mem_exp (decode_smull_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_long Rd Rn b__0 Rm M L b__1 U Q)"
  by (unfold decode_smull_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_long_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_arithmetic_binary_disparate_mul_product[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_arithmetic_binary_disparate_mul_product d datasize elements l__189 m n part is_unsigned)"
  by (unfold execute_aarch64_instrs_vector_arithmetic_binary_disparate_mul_product_def, non_mem_expI)

lemma non_mem_exp_decode_smull_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_product[non_mem_expI]:
  "non_mem_exp (decode_smull_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_product Rd Rn Rm b__0 U Q)"
  by (unfold decode_smull_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_product_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_arithmetic_unary_diff_neg_sat_sisd[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_arithmetic_unary_diff_neg_sat_sisd d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) n neg)"
  by (unfold execute_aarch64_instrs_vector_arithmetic_unary_diff_neg_sat_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_sqabs_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_sat_simd[non_mem_expI]:
  "non_mem_exp (decode_sqabs_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_sat_simd Rd Rn b__0 U b__1)"
  by (unfold decode_sqabs_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_sat_simd_def, non_mem_expI)

lemma non_mem_exp_decode_sqabs_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_sat_sisd[non_mem_expI]:
  "non_mem_exp (decode_sqabs_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_sat_sisd Rd Rn b__0 U)"
  by (unfold decode_sqabs_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_sat_sisd_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_arithmetic_binary_uniform_add_saturating_sisd[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_arithmetic_binary_uniform_add_saturating_sisd d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) m n is_unsigned)"
  by (unfold execute_aarch64_instrs_vector_arithmetic_binary_uniform_add_saturating_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_sqadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_saturating_simd[non_mem_expI]:
  "non_mem_exp (decode_sqadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_saturating_simd Rd Rn Rm b__0 U b__1)"
  by (unfold decode_sqadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_saturating_simd_def, non_mem_expI)

lemma non_mem_exp_decode_sqadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_saturating_sisd[non_mem_expI]:
  "non_mem_exp (decode_sqadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_saturating_sisd Rd Rn Rm b__0 U)"
  by (unfold decode_sqadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_saturating_sisd_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_double_sisd[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_double_sisd d l__403 elements l__404 (idxdsize :: 'idxdsize::len itself) index__arg m n part sub_op)"
  by (unfold execute_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_double_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_sqdmlal_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_double_simd[non_mem_expI]:
  "non_mem_exp (decode_sqdmlal_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_double_simd Rd Rn b__0 o2 Rm M L b__1 Q)"
  by (unfold decode_sqdmlal_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_double_simd_def, non_mem_expI)

lemma non_mem_exp_decode_sqdmlal_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_double_sisd[non_mem_expI]:
  "non_mem_exp (decode_sqdmlal_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_double_sisd Rd Rn b__0 o2 Rm M L b__1)"
  by (unfold decode_sqdmlal_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_double_sisd_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_arithmetic_binary_disparate_mul_dmacc_sisd[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_arithmetic_binary_disparate_mul_dmacc_sisd d l__437 elements l__438 m n part sub_op)"
  by (unfold execute_aarch64_instrs_vector_arithmetic_binary_disparate_mul_dmacc_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_sqdmlal_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_dmacc_simd[non_mem_expI]:
  "non_mem_exp (decode_sqdmlal_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_dmacc_simd Rd Rn o1 Rm b__0 Q)"
  by (unfold decode_sqdmlal_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_dmacc_simd_def, non_mem_expI)

lemma non_mem_exp_decode_sqdmlal_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_dmacc_sisd[non_mem_expI]:
  "non_mem_exp (decode_sqdmlal_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_dmacc_sisd Rd Rn o1 Rm b__0)"
  by (unfold decode_sqdmlal_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_dmacc_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_sqdmlsl_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_double_simd[non_mem_expI]:
  "non_mem_exp (decode_sqdmlsl_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_double_simd Rd Rn b__0 o2 Rm M L b__1 Q)"
  by (unfold decode_sqdmlsl_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_double_simd_def, non_mem_expI)

lemma non_mem_exp_decode_sqdmlsl_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_double_sisd[non_mem_expI]:
  "non_mem_exp (decode_sqdmlsl_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_double_sisd Rd Rn b__0 o2 Rm M L b__1)"
  by (unfold decode_sqdmlsl_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_double_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_sqdmlsl_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_dmacc_simd[non_mem_expI]:
  "non_mem_exp (decode_sqdmlsl_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_dmacc_simd Rd Rn o1 Rm b__0 Q)"
  by (unfold decode_sqdmlsl_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_dmacc_simd_def, non_mem_expI)

lemma non_mem_exp_decode_sqdmlsl_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_dmacc_sisd[non_mem_expI]:
  "non_mem_exp (decode_sqdmlsl_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_dmacc_sisd Rd Rn o1 Rm b__0)"
  by (unfold decode_sqdmlsl_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_dmacc_sisd_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_arithmetic_binary_element_mul_high_sisd[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_high_sisd d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) (idxdsize :: 'idxdsize::len itself) index__arg m n round__arg)"
  by (unfold execute_aarch64_instrs_vector_arithmetic_binary_element_mul_high_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_sqdmulh_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_high_simd[non_mem_expI]:
  "non_mem_exp (decode_sqdmulh_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_high_simd Rd Rn b__0 op Rm M L b__1 b__2)"
  by (unfold decode_sqdmulh_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_high_simd_def, non_mem_expI)

lemma non_mem_exp_decode_sqdmulh_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_high_sisd[non_mem_expI]:
  "non_mem_exp (decode_sqdmulh_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_high_sisd Rd Rn b__0 op Rm M L b__1)"
  by (unfold decode_sqdmulh_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_high_sisd_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_sisd[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_sisd d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) m n rounding)"
  by (unfold execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_sqdmulh_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_simd[non_mem_expI]:
  "non_mem_exp (decode_sqdmulh_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_simd Rd Rn Rm b__0 U b__1)"
  by (unfold decode_sqdmulh_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_simd_def, non_mem_expI)

lemma non_mem_exp_decode_sqdmulh_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_sisd[non_mem_expI]:
  "non_mem_exp (decode_sqdmulh_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_sisd Rd Rn Rm b__0 U)"
  by (unfold decode_sqdmulh_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_sisd_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_arithmetic_binary_element_mul_double_sisd[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_double_sisd d l__123 elements l__124 (idxdsize :: 'idxdsize::len itself) index__arg m n part)"
  by (unfold execute_aarch64_instrs_vector_arithmetic_binary_element_mul_double_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_sqdmull_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_double_simd[non_mem_expI]:
  "non_mem_exp (decode_sqdmull_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_double_simd Rd Rn b__0 Rm M L b__1 Q)"
  by (unfold decode_sqdmull_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_double_simd_def, non_mem_expI)

lemma non_mem_exp_decode_sqdmull_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_double_sisd[non_mem_expI]:
  "non_mem_exp (decode_sqdmull_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_double_sisd Rd Rn b__0 Rm M L b__1)"
  by (unfold decode_sqdmull_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_double_sisd_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_arithmetic_binary_disparate_mul_double_sisd[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_arithmetic_binary_disparate_mul_double_sisd d l__59 elements l__60 m n part)"
  by (unfold execute_aarch64_instrs_vector_arithmetic_binary_disparate_mul_double_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_sqdmull_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_double_simd[non_mem_expI]:
  "non_mem_exp (decode_sqdmull_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_double_simd Rd Rn Rm b__0 Q)"
  by (unfold decode_sqdmull_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_double_simd_def, non_mem_expI)

lemma non_mem_exp_decode_sqdmull_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_double_sisd[non_mem_expI]:
  "non_mem_exp (decode_sqdmull_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_double_sisd Rd Rn Rm b__0)"
  by (unfold decode_sqdmull_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_double_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_sqneg_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_sat_simd[non_mem_expI]:
  "non_mem_exp (decode_sqneg_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_sat_simd Rd Rn b__0 U b__1)"
  by (unfold decode_sqneg_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_sat_simd_def, non_mem_expI)

lemma non_mem_exp_decode_sqneg_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_sat_sisd[non_mem_expI]:
  "non_mem_exp (decode_sqneg_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_sat_sisd Rd Rn b__0 U)"
  by (unfold decode_sqneg_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_sat_sisd_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_high_sisd[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_high_sisd d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) (idxdsize :: 'idxdsize::len itself) index__arg m n rounding sub_op)"
  by (unfold execute_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_high_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_sqrdmlah_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_high_simd[non_mem_expI]:
  "non_mem_exp (decode_sqrdmlah_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_high_simd Rd Rn b__0 S Rm M L b__1 b__2)"
  by (unfold decode_sqrdmlah_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_high_simd_def, non_mem_expI)

lemma non_mem_exp_decode_sqrdmlah_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_high_sisd[non_mem_expI]:
  "non_mem_exp (decode_sqrdmlah_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_high_sisd Rd Rn b__0 S Rm M L b__1)"
  by (unfold decode_sqrdmlah_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_high_sisd_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_accum_sisd[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_accum_sisd d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) m n rounding sub_op)"
  by (unfold execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_accum_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_sqrdmlah_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_accum_simd[non_mem_expI]:
  "non_mem_exp (decode_sqrdmlah_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_accum_simd Rd Rn S Rm b__0 b__1)"
  by (unfold decode_sqrdmlah_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_accum_simd_def, non_mem_expI)

lemma non_mem_exp_decode_sqrdmlah_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_accum_sisd[non_mem_expI]:
  "non_mem_exp (decode_sqrdmlah_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_accum_sisd Rd Rn S Rm b__0)"
  by (unfold decode_sqrdmlah_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_accum_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_sqrdmlsh_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_high_simd[non_mem_expI]:
  "non_mem_exp (decode_sqrdmlsh_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_high_simd Rd Rn b__0 S Rm M L b__1 b__2)"
  by (unfold decode_sqrdmlsh_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_high_simd_def, non_mem_expI)

lemma non_mem_exp_decode_sqrdmlsh_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_high_sisd[non_mem_expI]:
  "non_mem_exp (decode_sqrdmlsh_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_high_sisd Rd Rn b__0 S Rm M L b__1)"
  by (unfold decode_sqrdmlsh_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_high_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_sqrdmlsh_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_accum_simd[non_mem_expI]:
  "non_mem_exp (decode_sqrdmlsh_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_accum_simd Rd Rn S Rm b__0 b__1)"
  by (unfold decode_sqrdmlsh_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_accum_simd_def, non_mem_expI)

lemma non_mem_exp_decode_sqrdmlsh_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_accum_sisd[non_mem_expI]:
  "non_mem_exp (decode_sqrdmlsh_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_accum_sisd Rd Rn S Rm b__0)"
  by (unfold decode_sqrdmlsh_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_accum_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_sqrdmulh_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_high_simd[non_mem_expI]:
  "non_mem_exp (decode_sqrdmulh_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_high_simd Rd Rn b__0 op Rm M L b__1 b__2)"
  by (unfold decode_sqrdmulh_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_high_simd_def, non_mem_expI)

lemma non_mem_exp_decode_sqrdmulh_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_high_sisd[non_mem_expI]:
  "non_mem_exp (decode_sqrdmulh_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_high_sisd Rd Rn b__0 op Rm M L b__1)"
  by (unfold decode_sqrdmulh_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_high_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_sqrdmulh_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_simd[non_mem_expI]:
  "non_mem_exp (decode_sqrdmulh_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_simd Rd Rn Rm b__0 U b__1)"
  by (unfold decode_sqrdmulh_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_simd_def, non_mem_expI)

lemma non_mem_exp_decode_sqrdmulh_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_sisd[non_mem_expI]:
  "non_mem_exp (decode_sqrdmulh_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_sisd Rd Rn Rm b__0 U)"
  by (unfold decode_sqrdmulh_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_sisd_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) m n rounding saturating is_unsigned)"
  by (unfold execute_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_sqrshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd[non_mem_expI]:
  "non_mem_exp (decode_sqrshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd Rd Rn S R Rm b__0 U b__1)"
  by (unfold decode_sqrshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd_def, non_mem_expI)

lemma non_mem_exp_decode_sqrshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd[non_mem_expI]:
  "non_mem_exp (decode_sqrshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd Rd Rn S R Rm b__0 U)"
  by (unfold decode_sqrshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_shift_right_narrow_uniform_sisd[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_shift_right_narrow_uniform_sisd d l__325 elements l__326 n part round__arg shift is_unsigned)"
  by (unfold execute_aarch64_instrs_vector_shift_right_narrow_uniform_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_sqrshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_simd[non_mem_expI]:
  "non_mem_exp (decode_sqrshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_simd Rd Rn op immb b__0 U Q)"
  by (unfold decode_sqrshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_simd_def, non_mem_expI)

lemma non_mem_exp_decode_sqrshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_sisd[non_mem_expI]:
  "non_mem_exp (decode_sqrshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_sisd Rd Rn op immb b__0 U)"
  by (unfold decode_sqrshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_sisd_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_shift_right_narrow_nonuniform_sisd[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_shift_right_narrow_nonuniform_sisd d l__482 elements l__483 n part round__arg shift)"
  by (unfold execute_aarch64_instrs_vector_shift_right_narrow_nonuniform_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_sqrshrun_advsimd_aarch64_instrs_vector_shift_right_narrow_nonuniform_simd[non_mem_expI]:
  "non_mem_exp (decode_sqrshrun_advsimd_aarch64_instrs_vector_shift_right_narrow_nonuniform_simd Rd Rn op immb b__0 Q)"
  by (unfold decode_sqrshrun_advsimd_aarch64_instrs_vector_shift_right_narrow_nonuniform_simd_def, non_mem_expI)

lemma non_mem_exp_decode_sqrshrun_advsimd_aarch64_instrs_vector_shift_right_narrow_nonuniform_sisd[non_mem_expI]:
  "non_mem_exp (decode_sqrshrun_advsimd_aarch64_instrs_vector_shift_right_narrow_nonuniform_sisd Rd Rn op immb b__0)"
  by (unfold decode_sqrshrun_advsimd_aarch64_instrs_vector_shift_right_narrow_nonuniform_sisd_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_shift_left_sat_sisd[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_shift_left_sat_sisd d (datasize :: 'datasize::len itself) dst_unsigned elements (esize :: 'esize::len itself) n shift src_unsigned)"
  by (unfold execute_aarch64_instrs_vector_shift_left_sat_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_sqshl_advsimd_imm_aarch64_instrs_vector_shift_left_sat_simd[non_mem_expI]:
  "non_mem_exp (decode_sqshl_advsimd_imm_aarch64_instrs_vector_shift_left_sat_simd Rd Rn op immb b__0 U b__1)"
  by (unfold decode_sqshl_advsimd_imm_aarch64_instrs_vector_shift_left_sat_simd_def, non_mem_expI)

lemma non_mem_exp_decode_sqshl_advsimd_imm_aarch64_instrs_vector_shift_left_sat_sisd[non_mem_expI]:
  "non_mem_exp (decode_sqshl_advsimd_imm_aarch64_instrs_vector_shift_left_sat_sisd Rd Rn op immb b__0 U)"
  by (unfold decode_sqshl_advsimd_imm_aarch64_instrs_vector_shift_left_sat_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_sqshl_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd[non_mem_expI]:
  "non_mem_exp (decode_sqshl_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd Rd Rn S R Rm b__0 U b__1)"
  by (unfold decode_sqshl_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd_def, non_mem_expI)

lemma non_mem_exp_decode_sqshl_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd[non_mem_expI]:
  "non_mem_exp (decode_sqshl_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd Rd Rn S R Rm b__0 U)"
  by (unfold decode_sqshl_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_sqshlu_advsimd_aarch64_instrs_vector_shift_left_sat_simd[non_mem_expI]:
  "non_mem_exp (decode_sqshlu_advsimd_aarch64_instrs_vector_shift_left_sat_simd Rd Rn op immb b__0 U b__1)"
  by (unfold decode_sqshlu_advsimd_aarch64_instrs_vector_shift_left_sat_simd_def, non_mem_expI)

lemma non_mem_exp_decode_sqshlu_advsimd_aarch64_instrs_vector_shift_left_sat_sisd[non_mem_expI]:
  "non_mem_exp (decode_sqshlu_advsimd_aarch64_instrs_vector_shift_left_sat_sisd Rd Rn op immb b__0 U)"
  by (unfold decode_sqshlu_advsimd_aarch64_instrs_vector_shift_left_sat_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_sqshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_simd[non_mem_expI]:
  "non_mem_exp (decode_sqshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_simd Rd Rn op immb b__0 U Q)"
  by (unfold decode_sqshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_simd_def, non_mem_expI)

lemma non_mem_exp_decode_sqshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_sisd[non_mem_expI]:
  "non_mem_exp (decode_sqshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_sisd Rd Rn op immb b__0 U)"
  by (unfold decode_sqshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_sqshrun_advsimd_aarch64_instrs_vector_shift_right_narrow_nonuniform_simd[non_mem_expI]:
  "non_mem_exp (decode_sqshrun_advsimd_aarch64_instrs_vector_shift_right_narrow_nonuniform_simd Rd Rn op immb b__0 Q)"
  by (unfold decode_sqshrun_advsimd_aarch64_instrs_vector_shift_right_narrow_nonuniform_simd_def, non_mem_expI)

lemma non_mem_exp_decode_sqshrun_advsimd_aarch64_instrs_vector_shift_right_narrow_nonuniform_sisd[non_mem_expI]:
  "non_mem_exp (decode_sqshrun_advsimd_aarch64_instrs_vector_shift_right_narrow_nonuniform_sisd Rd Rn op immb b__0)"
  by (unfold decode_sqshrun_advsimd_aarch64_instrs_vector_shift_right_narrow_nonuniform_sisd_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_arithmetic_binary_uniform_sub_saturating_sisd[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_arithmetic_binary_uniform_sub_saturating_sisd d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) m n is_unsigned)"
  by (unfold execute_aarch64_instrs_vector_arithmetic_binary_uniform_sub_saturating_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_sqsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_saturating_simd[non_mem_expI]:
  "non_mem_exp (decode_sqsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_saturating_simd Rd Rn Rm b__0 U b__1)"
  by (unfold decode_sqsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_saturating_simd_def, non_mem_expI)

lemma non_mem_exp_decode_sqsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_saturating_sisd[non_mem_expI]:
  "non_mem_exp (decode_sqsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_saturating_sisd Rd Rn Rm b__0 U)"
  by (unfold decode_sqsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_saturating_sisd_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_arithmetic_unary_extract_sat_sisd[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_arithmetic_unary_extract_sat_sisd d l__91 elements l__92 n part is_unsigned)"
  by (unfold execute_aarch64_instrs_vector_arithmetic_unary_extract_sat_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_sqxtn_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_sat_simd[non_mem_expI]:
  "non_mem_exp (decode_sqxtn_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_sat_simd Rd Rn b__0 U Q)"
  by (unfold decode_sqxtn_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_sat_simd_def, non_mem_expI)

lemma non_mem_exp_decode_sqxtn_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_sat_sisd[non_mem_expI]:
  "non_mem_exp (decode_sqxtn_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_sat_sisd Rd Rn b__0 U)"
  by (unfold decode_sqxtn_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_sat_sisd_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_arithmetic_unary_extract_sqxtun_sisd[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_arithmetic_unary_extract_sqxtun_sisd d l__4 elements l__5 n part)"
  by (unfold execute_aarch64_instrs_vector_arithmetic_unary_extract_sqxtun_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_sqxtun_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_sqxtun_simd[non_mem_expI]:
  "non_mem_exp (decode_sqxtun_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_sqxtun_simd Rd Rn b__0 Q)"
  by (unfold decode_sqxtun_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_sqxtun_simd_def, non_mem_expI)

lemma non_mem_exp_decode_sqxtun_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_sqxtun_sisd[non_mem_expI]:
  "non_mem_exp (decode_sqxtun_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_sqxtun_sisd Rd Rn b__0)"
  by (unfold decode_sqxtun_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_sqxtun_sisd_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_arithmetic_binary_uniform_add_halving_rounding[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_arithmetic_binary_uniform_add_halving_rounding d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) m n is_unsigned)"
  by (unfold execute_aarch64_instrs_vector_arithmetic_binary_uniform_add_halving_rounding_def, non_mem_expI)

lemma non_mem_exp_decode_srhadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_halving_rounding[non_mem_expI]:
  "non_mem_exp (decode_srhadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_halving_rounding Rd Rn Rm b__0 U b__1)"
  by (unfold decode_srhadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_halving_rounding_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_shift_right_insert_sisd[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_shift_right_insert_sisd d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) n shift)"
  by (unfold execute_aarch64_instrs_vector_shift_right_insert_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_sri_advsimd_aarch64_instrs_vector_shift_right_insert_simd[non_mem_expI]:
  "non_mem_exp (decode_sri_advsimd_aarch64_instrs_vector_shift_right_insert_simd Rd Rn immb b__0 b__1)"
  by (unfold decode_sri_advsimd_aarch64_instrs_vector_shift_right_insert_simd_def, non_mem_expI)

lemma non_mem_exp_decode_sri_advsimd_aarch64_instrs_vector_shift_right_insert_sisd[non_mem_expI]:
  "non_mem_exp (decode_sri_advsimd_aarch64_instrs_vector_shift_right_insert_sisd Rd Rn immb immh)"
  by (unfold decode_sri_advsimd_aarch64_instrs_vector_shift_right_insert_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_srshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd[non_mem_expI]:
  "non_mem_exp (decode_srshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd Rd Rn S R Rm b__0 U b__1)"
  by (unfold decode_srshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd_def, non_mem_expI)

lemma non_mem_exp_decode_srshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd[non_mem_expI]:
  "non_mem_exp (decode_srshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd Rd Rn S R Rm b__0 U)"
  by (unfold decode_srshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_shift_right_sisd[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_shift_right_sisd accumulate d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) n round__arg shift is_unsigned)"
  by (unfold execute_aarch64_instrs_vector_shift_right_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_srshr_advsimd_aarch64_instrs_vector_shift_right_simd[non_mem_expI]:
  "non_mem_exp (decode_srshr_advsimd_aarch64_instrs_vector_shift_right_simd Rd Rn o0 o1 immb b__0 U b__1)"
  by (unfold decode_srshr_advsimd_aarch64_instrs_vector_shift_right_simd_def, non_mem_expI)

lemma non_mem_exp_decode_srshr_advsimd_aarch64_instrs_vector_shift_right_sisd[non_mem_expI]:
  "non_mem_exp (decode_srshr_advsimd_aarch64_instrs_vector_shift_right_sisd Rd Rn o0 o1 immb immh U)"
  by (unfold decode_srshr_advsimd_aarch64_instrs_vector_shift_right_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_srsra_advsimd_aarch64_instrs_vector_shift_right_simd[non_mem_expI]:
  "non_mem_exp (decode_srsra_advsimd_aarch64_instrs_vector_shift_right_simd Rd Rn o0 o1 immb b__0 U b__1)"
  by (unfold decode_srsra_advsimd_aarch64_instrs_vector_shift_right_simd_def, non_mem_expI)

lemma non_mem_exp_decode_srsra_advsimd_aarch64_instrs_vector_shift_right_sisd[non_mem_expI]:
  "non_mem_exp (decode_srsra_advsimd_aarch64_instrs_vector_shift_right_sisd Rd Rn o0 o1 immb immh U)"
  by (unfold decode_srsra_advsimd_aarch64_instrs_vector_shift_right_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_sshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd[non_mem_expI]:
  "non_mem_exp (decode_sshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd Rd Rn S R Rm b__0 U b__1)"
  by (unfold decode_sshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd_def, non_mem_expI)

lemma non_mem_exp_decode_sshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd[non_mem_expI]:
  "non_mem_exp (decode_sshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd Rd Rn S R Rm b__0 U)"
  by (unfold decode_sshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_shift_left_long[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_shift_left_long d datasize elements l__320 n part shift is_unsigned)"
  by (unfold execute_aarch64_instrs_vector_shift_left_long_def, non_mem_expI)

lemma non_mem_exp_decode_sshll_advsimd_aarch64_instrs_vector_shift_left_long[non_mem_expI]:
  "non_mem_exp (decode_sshll_advsimd_aarch64_instrs_vector_shift_left_long Rd Rn immb b__0 U Q)"
  by (unfold decode_sshll_advsimd_aarch64_instrs_vector_shift_left_long_def, non_mem_expI)

lemma non_mem_exp_decode_sshr_advsimd_aarch64_instrs_vector_shift_right_simd[non_mem_expI]:
  "non_mem_exp (decode_sshr_advsimd_aarch64_instrs_vector_shift_right_simd Rd Rn o0 o1 immb b__0 U b__1)"
  by (unfold decode_sshr_advsimd_aarch64_instrs_vector_shift_right_simd_def, non_mem_expI)

lemma non_mem_exp_decode_sshr_advsimd_aarch64_instrs_vector_shift_right_sisd[non_mem_expI]:
  "non_mem_exp (decode_sshr_advsimd_aarch64_instrs_vector_shift_right_sisd Rd Rn o0 o1 immb immh U)"
  by (unfold decode_sshr_advsimd_aarch64_instrs_vector_shift_right_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_ssra_advsimd_aarch64_instrs_vector_shift_right_simd[non_mem_expI]:
  "non_mem_exp (decode_ssra_advsimd_aarch64_instrs_vector_shift_right_simd Rd Rn o0 o1 immb b__0 U b__1)"
  by (unfold decode_ssra_advsimd_aarch64_instrs_vector_shift_right_simd_def, non_mem_expI)

lemma non_mem_exp_decode_ssra_advsimd_aarch64_instrs_vector_shift_right_sisd[non_mem_expI]:
  "non_mem_exp (decode_ssra_advsimd_aarch64_instrs_vector_shift_right_sisd Rd Rn o0 o1 immb immh U)"
  by (unfold decode_ssra_advsimd_aarch64_instrs_vector_shift_right_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_ssubl_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_long[non_mem_expI]:
  "non_mem_exp (decode_ssubl_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_long Rd Rn o1 Rm b__0 U Q)"
  by (unfold decode_ssubl_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_long_def, non_mem_expI)

lemma non_mem_exp_decode_ssubw_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_wide[non_mem_expI]:
  "non_mem_exp (decode_ssubw_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_wide Rd Rn o1 Rm b__0 U Q)"
  by (unfold decode_ssubw_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_wide_def, non_mem_expI)

lemma non_mem_exp_decode_sub_addsub_ext_aarch64_instrs_integer_arithmetic_add_sub_extendedreg[non_mem_expI]:
  "non_mem_exp (decode_sub_addsub_ext_aarch64_instrs_integer_arithmetic_add_sub_extendedreg Rd Rn imm3 option_name Rm S op b__0)"
  by (unfold decode_sub_addsub_ext_aarch64_instrs_integer_arithmetic_add_sub_extendedreg_def, non_mem_expI)

lemma non_mem_exp_decode_sub_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate[non_mem_expI]:
  "non_mem_exp (decode_sub_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate Rd Rn imm12 sh S op b__0)"
  by (unfold decode_sub_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate_def, non_mem_expI)

lemma non_mem_exp_decode_sub_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg[non_mem_expI]:
  "non_mem_exp (decode_sub_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg Rd Rn imm6 Rm shift S op b__0)"
  by (unfold decode_sub_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg_def, non_mem_expI)

lemma non_mem_exp_decode_sub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_wrapping_single_simd[non_mem_expI]:
  "non_mem_exp (decode_sub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_wrapping_single_simd Rd Rn Rm b__0 U b__1)"
  by (unfold decode_sub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_wrapping_single_simd_def, non_mem_expI)

lemma non_mem_exp_decode_sub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_wrapping_single_sisd[non_mem_expI]:
  "non_mem_exp (decode_sub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_wrapping_single_sisd Rd Rn Rm b__0 U)"
  by (unfold decode_sub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_wrapping_single_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_subhn_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_narrow[non_mem_expI]:
  "non_mem_exp (decode_subhn_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_narrow Rd Rn o1 Rm b__0 U Q)"
  by (unfold decode_subhn_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_narrow_def, non_mem_expI)

lemma non_mem_exp_decode_subs_addsub_ext_aarch64_instrs_integer_arithmetic_add_sub_extendedreg[non_mem_expI]:
  "non_mem_exp (decode_subs_addsub_ext_aarch64_instrs_integer_arithmetic_add_sub_extendedreg Rd Rn imm3 option_name Rm S op b__0)"
  by (unfold decode_subs_addsub_ext_aarch64_instrs_integer_arithmetic_add_sub_extendedreg_def, non_mem_expI)

lemma non_mem_exp_decode_subs_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate[non_mem_expI]:
  "non_mem_exp (decode_subs_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate Rd Rn imm12 sh S op b__0)"
  by (unfold decode_subs_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate_def, non_mem_expI)

lemma non_mem_exp_decode_subs_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg[non_mem_expI]:
  "non_mem_exp (decode_subs_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg Rd Rn imm6 Rm shift S op b__0)"
  by (unfold decode_subs_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_arithmetic_unary_add_saturating_sisd[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_arithmetic_unary_add_saturating_sisd d (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) n is_unsigned)"
  by (unfold execute_aarch64_instrs_vector_arithmetic_unary_add_saturating_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_suqadd_advsimd_aarch64_instrs_vector_arithmetic_unary_add_saturating_simd[non_mem_expI]:
  "non_mem_exp (decode_suqadd_advsimd_aarch64_instrs_vector_arithmetic_unary_add_saturating_simd Rd Rn b__0 U b__1)"
  by (unfold decode_suqadd_advsimd_aarch64_instrs_vector_arithmetic_unary_add_saturating_simd_def, non_mem_expI)

lemma non_mem_exp_decode_suqadd_advsimd_aarch64_instrs_vector_arithmetic_unary_add_saturating_sisd[non_mem_expI]:
  "non_mem_exp (decode_suqadd_advsimd_aarch64_instrs_vector_arithmetic_unary_add_saturating_sisd Rd Rn b__0 U)"
  by (unfold decode_suqadd_advsimd_aarch64_instrs_vector_arithmetic_unary_add_saturating_sisd_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_system_exceptions_runtime_svc[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_system_exceptions_runtime_svc imm)"
  by (unfold execute_aarch64_instrs_system_exceptions_runtime_svc_def, non_mem_expI)

lemma non_mem_exp_decode_svc_aarch64_instrs_system_exceptions_runtime_svc[non_mem_expI]:
  "non_mem_exp (decode_svc_aarch64_instrs_system_exceptions_runtime_svc imm16)"
  by (unfold decode_svc_aarch64_instrs_system_exceptions_runtime_svc_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_transfer_vector_table[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_transfer_vector_table d (datasize :: 'datasize::len itself) elements is_tbl m n__arg l__181)"
  by (unfold execute_aarch64_instrs_vector_transfer_vector_table_def, non_mem_expI)

lemma non_mem_exp_decode_tbl_advsimd_aarch64_instrs_vector_transfer_vector_table[non_mem_expI]:
  "non_mem_exp (decode_tbl_advsimd_aarch64_instrs_vector_transfer_vector_table Rd Rn op len Rm b__0)"
  by (unfold decode_tbl_advsimd_aarch64_instrs_vector_transfer_vector_table_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_branch_conditional_test[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_branch_conditional_test bit_pos bit_val (datasize :: 'datasize::len itself) offset t__arg)"
  by (unfold execute_aarch64_instrs_branch_conditional_test_def, non_mem_expI)

lemma non_mem_exp_decode_tbnz_aarch64_instrs_branch_conditional_test[non_mem_expI]:
  "non_mem_exp (decode_tbnz_aarch64_instrs_branch_conditional_test Rt imm14 b40 op b__0)"
  by (unfold decode_tbnz_aarch64_instrs_branch_conditional_test_def, non_mem_expI)

lemma non_mem_exp_decode_tbx_advsimd_aarch64_instrs_vector_transfer_vector_table[non_mem_expI]:
  "non_mem_exp (decode_tbx_advsimd_aarch64_instrs_vector_transfer_vector_table Rd Rn op len Rm b__0)"
  by (unfold decode_tbx_advsimd_aarch64_instrs_vector_transfer_vector_table_def, non_mem_expI)

lemma non_mem_exp_decode_tbz_aarch64_instrs_branch_conditional_test[non_mem_expI]:
  "non_mem_exp (decode_tbz_aarch64_instrs_branch_conditional_test Rt imm14 b40 op b__0)"
  by (unfold decode_tbz_aarch64_instrs_branch_conditional_test_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_transfer_vector_permute_transpose[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_transfer_vector_permute_transpose d (datasize :: 'datasize::len itself) (esize :: 'esize::len itself) m n pairs part)"
  by (unfold execute_aarch64_instrs_vector_transfer_vector_permute_transpose_def, non_mem_expI)

lemma non_mem_exp_decode_trn1_advsimd_aarch64_instrs_vector_transfer_vector_permute_transpose[non_mem_expI]:
  "non_mem_exp (decode_trn1_advsimd_aarch64_instrs_vector_transfer_vector_permute_transpose Rd Rn op Rm b__0 b__1)"
  by (unfold decode_trn1_advsimd_aarch64_instrs_vector_transfer_vector_permute_transpose_def, non_mem_expI)

lemma non_mem_exp_decode_trn2_advsimd_aarch64_instrs_vector_transfer_vector_permute_transpose[non_mem_expI]:
  "non_mem_exp (decode_trn2_advsimd_aarch64_instrs_vector_transfer_vector_permute_transpose Rd Rn op Rm b__0 b__1)"
  by (unfold decode_trn2_advsimd_aarch64_instrs_vector_transfer_vector_permute_transpose_def, non_mem_expI)

lemma non_mem_exp_decode_uaba_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_diff[non_mem_expI]:
  "non_mem_exp (decode_uaba_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_diff Rd Rn ac Rm b__0 U b__1)"
  by (unfold decode_uaba_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_diff_def, non_mem_expI)

lemma non_mem_exp_decode_uabal_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_diff[non_mem_expI]:
  "non_mem_exp (decode_uabal_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_diff Rd Rn op Rm b__0 U Q)"
  by (unfold decode_uabal_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_diff_def, non_mem_expI)

lemma non_mem_exp_decode_uabd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_diff[non_mem_expI]:
  "non_mem_exp (decode_uabd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_diff Rd Rn ac Rm b__0 U b__1)"
  by (unfold decode_uabd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_diff_def, non_mem_expI)

lemma non_mem_exp_decode_uabdl_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_diff[non_mem_expI]:
  "non_mem_exp (decode_uabdl_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_diff Rd Rn op Rm b__0 U Q)"
  by (unfold decode_uabdl_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_diff_def, non_mem_expI)

lemma non_mem_exp_decode_uadalp_advsimd_aarch64_instrs_vector_arithmetic_unary_add_pairwise[non_mem_expI]:
  "non_mem_exp (decode_uadalp_advsimd_aarch64_instrs_vector_arithmetic_unary_add_pairwise Rd Rn op b__0 U b__1)"
  by (unfold decode_uadalp_advsimd_aarch64_instrs_vector_arithmetic_unary_add_pairwise_def, non_mem_expI)

lemma non_mem_exp_decode_uaddl_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_long[non_mem_expI]:
  "non_mem_exp (decode_uaddl_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_long Rd Rn o1 Rm b__0 U Q)"
  by (unfold decode_uaddl_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_long_def, non_mem_expI)

lemma non_mem_exp_decode_uaddlp_advsimd_aarch64_instrs_vector_arithmetic_unary_add_pairwise[non_mem_expI]:
  "non_mem_exp (decode_uaddlp_advsimd_aarch64_instrs_vector_arithmetic_unary_add_pairwise Rd Rn op b__0 U b__1)"
  by (unfold decode_uaddlp_advsimd_aarch64_instrs_vector_arithmetic_unary_add_pairwise_def, non_mem_expI)

lemma non_mem_exp_decode_uaddlv_advsimd_aarch64_instrs_vector_reduce_add_long[non_mem_expI]:
  "non_mem_exp (decode_uaddlv_advsimd_aarch64_instrs_vector_reduce_add_long Rd Rn b__0 U b__1)"
  by (unfold decode_uaddlv_advsimd_aarch64_instrs_vector_reduce_add_long_def, non_mem_expI)

lemma non_mem_exp_decode_uaddw_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_wide[non_mem_expI]:
  "non_mem_exp (decode_uaddw_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_wide Rd Rn o1 Rm b__0 U Q)"
  by (unfold decode_uaddw_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_wide_def, non_mem_expI)

lemma non_mem_exp_decode_ubfm_aarch64_instrs_integer_bitfield[non_mem_expI]:
  "non_mem_exp (decode_ubfm_aarch64_instrs_integer_bitfield Rd Rn imms immr N opc b__0)"
  by (unfold decode_ubfm_aarch64_instrs_integer_bitfield_def, non_mem_expI)

lemma non_mem_exp_decode_ucvtf_advsimd_fix_aarch64_instrs_vector_shift_conv_int_simd[non_mem_expI]:
  "non_mem_exp (decode_ucvtf_advsimd_fix_aarch64_instrs_vector_shift_conv_int_simd Rd Rn immb b__0 U b__1)"
  by (unfold decode_ucvtf_advsimd_fix_aarch64_instrs_vector_shift_conv_int_simd_def, non_mem_expI)

lemma non_mem_exp_decode_ucvtf_advsimd_fix_aarch64_instrs_vector_shift_conv_int_sisd[non_mem_expI]:
  "non_mem_exp (decode_ucvtf_advsimd_fix_aarch64_instrs_vector_shift_conv_int_sisd Rd Rn immb b__0 U)"
  by (unfold decode_ucvtf_advsimd_fix_aarch64_instrs_vector_shift_conv_int_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_ucvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_int_simd[non_mem_expI]:
  "non_mem_exp (decode_ucvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_int_simd Rd Rn b__0 U b__1)"
  by (unfold decode_ucvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_int_simd_def, non_mem_expI)

lemma non_mem_exp_decode_ucvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_int_sisd[non_mem_expI]:
  "non_mem_exp (decode_ucvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_int_sisd Rd Rn b__0 U)"
  by (unfold decode_ucvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_int_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_ucvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_int_simd[non_mem_expI]:
  "non_mem_exp (decode_ucvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_int_simd Rd Rn U b__0)"
  by (unfold decode_ucvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_int_simd_def, non_mem_expI)

lemma non_mem_exp_decode_ucvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_int_sisd[non_mem_expI]:
  "non_mem_exp (decode_ucvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_int_sisd Rd Rn U)"
  by (unfold decode_ucvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_int_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_ucvtf_float_fix_aarch64_instrs_float_convert_fix[non_mem_expI]:
  "non_mem_exp (decode_ucvtf_float_fix_aarch64_instrs_float_convert_fix Rd Rn scale opcode rmode b__0 b__1)"
  by (unfold decode_ucvtf_float_fix_aarch64_instrs_float_convert_fix_def, non_mem_expI)

lemma non_mem_exp_decode_ucvtf_float_int_aarch64_instrs_float_convert_int[non_mem_expI]:
  "non_mem_exp (decode_ucvtf_float_int_aarch64_instrs_float_convert_int Rd Rn opcode rmode ftype b__0)"
  by (unfold decode_ucvtf_float_int_aarch64_instrs_float_convert_int_def, non_mem_expI)

lemma non_mem_exp_decode_udiv_aarch64_instrs_integer_arithmetic_div[non_mem_expI]:
  "non_mem_exp (decode_udiv_aarch64_instrs_integer_arithmetic_div Rd Rn o1 Rm b__0)"
  by (unfold decode_udiv_aarch64_instrs_integer_arithmetic_div_def, non_mem_expI)

lemma non_mem_exp_decode_udot_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_dotp[non_mem_expI]:
  "non_mem_exp (decode_udot_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_dotp Rd Rn H Rm M L b__0 U b__1)"
  by (unfold decode_udot_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_dotp_def, non_mem_expI)

lemma non_mem_exp_decode_udot_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_dotp[non_mem_expI]:
  "non_mem_exp (decode_udot_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_dotp Rd Rn Rm b__0 U b__1)"
  by (unfold decode_udot_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_dotp_def, non_mem_expI)

lemma non_mem_exp_decode_uhadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_halving_truncating[non_mem_expI]:
  "non_mem_exp (decode_uhadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_halving_truncating Rd Rn Rm b__0 U b__1)"
  by (unfold decode_uhadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_halving_truncating_def, non_mem_expI)

lemma non_mem_exp_decode_uhsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_int[non_mem_expI]:
  "non_mem_exp (decode_uhsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_int Rd Rn Rm b__0 U b__1)"
  by (unfold decode_uhsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_int_def, non_mem_expI)

lemma non_mem_exp_decode_umaddl_aarch64_instrs_integer_arithmetic_mul_widening_32_64[non_mem_expI]:
  "non_mem_exp (decode_umaddl_aarch64_instrs_integer_arithmetic_mul_widening_32_64 Rd Rn Ra o0 Rm U)"
  by (unfold decode_umaddl_aarch64_instrs_integer_arithmetic_mul_widening_32_64_def, non_mem_expI)

lemma non_mem_exp_decode_umax_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_single[non_mem_expI]:
  "non_mem_exp (decode_umax_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_single Rd Rn o1 Rm b__0 U b__1)"
  by (unfold decode_umax_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_single_def, non_mem_expI)

lemma non_mem_exp_decode_umaxp_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_pair[non_mem_expI]:
  "non_mem_exp (decode_umaxp_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_pair Rd Rn o1 Rm b__0 U b__1)"
  by (unfold decode_umaxp_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_pair_def, non_mem_expI)

lemma non_mem_exp_decode_umaxv_advsimd_aarch64_instrs_vector_reduce_int_max[non_mem_expI]:
  "non_mem_exp (decode_umaxv_advsimd_aarch64_instrs_vector_reduce_int_max Rd Rn op b__0 U b__1)"
  by (unfold decode_umaxv_advsimd_aarch64_instrs_vector_reduce_int_max_def, non_mem_expI)

lemma non_mem_exp_decode_umin_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_single[non_mem_expI]:
  "non_mem_exp (decode_umin_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_single Rd Rn o1 Rm b__0 U b__1)"
  by (unfold decode_umin_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_single_def, non_mem_expI)

lemma non_mem_exp_decode_uminp_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_pair[non_mem_expI]:
  "non_mem_exp (decode_uminp_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_pair Rd Rn o1 Rm b__0 U b__1)"
  by (unfold decode_uminp_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_pair_def, non_mem_expI)

lemma non_mem_exp_decode_uminv_advsimd_aarch64_instrs_vector_reduce_int_max[non_mem_expI]:
  "non_mem_exp (decode_uminv_advsimd_aarch64_instrs_vector_reduce_int_max Rd Rn op b__0 U b__1)"
  by (unfold decode_uminv_advsimd_aarch64_instrs_vector_reduce_int_max_def, non_mem_expI)

lemma non_mem_exp_decode_umlal_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_long[non_mem_expI]:
  "non_mem_exp (decode_umlal_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_long Rd Rn b__0 o2 Rm M L b__1 U Q)"
  by (unfold decode_umlal_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_long_def, non_mem_expI)

lemma non_mem_exp_decode_umlal_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_accum[non_mem_expI]:
  "non_mem_exp (decode_umlal_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_accum Rd Rn o1 Rm b__0 U Q)"
  by (unfold decode_umlal_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_accum_def, non_mem_expI)

lemma non_mem_exp_decode_umlsl_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_long[non_mem_expI]:
  "non_mem_exp (decode_umlsl_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_long Rd Rn b__0 o2 Rm M L b__1 U Q)"
  by (unfold decode_umlsl_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_long_def, non_mem_expI)

lemma non_mem_exp_decode_umlsl_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_accum[non_mem_expI]:
  "non_mem_exp (decode_umlsl_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_accum Rd Rn o1 Rm b__0 U Q)"
  by (unfold decode_umlsl_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_accum_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_transfer_integer_move_unsigned[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_transfer_integer_move_unsigned d (datasize :: 'datasize::len itself) (esize :: 'esize::len itself) (idxdsize :: 'idxdsize::len itself) index__arg n)"
  by (unfold execute_aarch64_instrs_vector_transfer_integer_move_unsigned_def, non_mem_expI)

lemma non_mem_exp_decode_umov_advsimd_aarch64_instrs_vector_transfer_integer_move_unsigned[non_mem_expI]:
  "non_mem_exp (decode_umov_advsimd_aarch64_instrs_vector_transfer_integer_move_unsigned Rd Rn b__0 b__1)"
  by (unfold decode_umov_advsimd_aarch64_instrs_vector_transfer_integer_move_unsigned_def, non_mem_expI)

lemma non_mem_exp_decode_umsubl_aarch64_instrs_integer_arithmetic_mul_widening_32_64[non_mem_expI]:
  "non_mem_exp (decode_umsubl_aarch64_instrs_integer_arithmetic_mul_widening_32_64 Rd Rn Ra o0 Rm U)"
  by (unfold decode_umsubl_aarch64_instrs_integer_arithmetic_mul_widening_32_64_def, non_mem_expI)

lemma non_mem_exp_decode_umulh_aarch64_instrs_integer_arithmetic_mul_widening_64_128hi[non_mem_expI]:
  "non_mem_exp (decode_umulh_aarch64_instrs_integer_arithmetic_mul_widening_64_128hi Rd Rn Ra Rm U)"
  by (unfold decode_umulh_aarch64_instrs_integer_arithmetic_mul_widening_64_128hi_def, non_mem_expI)

lemma non_mem_exp_decode_umull_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_long[non_mem_expI]:
  "non_mem_exp (decode_umull_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_long Rd Rn b__0 Rm M L b__1 U Q)"
  by (unfold decode_umull_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_long_def, non_mem_expI)

lemma non_mem_exp_decode_umull_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_product[non_mem_expI]:
  "non_mem_exp (decode_umull_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_product Rd Rn Rm b__0 U Q)"
  by (unfold decode_umull_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_product_def, non_mem_expI)

lemma non_mem_exp_decode_uqadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_saturating_simd[non_mem_expI]:
  "non_mem_exp (decode_uqadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_saturating_simd Rd Rn Rm b__0 U b__1)"
  by (unfold decode_uqadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_saturating_simd_def, non_mem_expI)

lemma non_mem_exp_decode_uqadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_saturating_sisd[non_mem_expI]:
  "non_mem_exp (decode_uqadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_saturating_sisd Rd Rn Rm b__0 U)"
  by (unfold decode_uqadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_saturating_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_uqrshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd[non_mem_expI]:
  "non_mem_exp (decode_uqrshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd Rd Rn S R Rm b__0 U b__1)"
  by (unfold decode_uqrshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd_def, non_mem_expI)

lemma non_mem_exp_decode_uqrshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd[non_mem_expI]:
  "non_mem_exp (decode_uqrshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd Rd Rn S R Rm b__0 U)"
  by (unfold decode_uqrshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_uqrshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_simd[non_mem_expI]:
  "non_mem_exp (decode_uqrshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_simd Rd Rn op immb b__0 U Q)"
  by (unfold decode_uqrshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_simd_def, non_mem_expI)

lemma non_mem_exp_decode_uqrshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_sisd[non_mem_expI]:
  "non_mem_exp (decode_uqrshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_sisd Rd Rn op immb b__0 U)"
  by (unfold decode_uqrshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_uqshl_advsimd_imm_aarch64_instrs_vector_shift_left_sat_simd[non_mem_expI]:
  "non_mem_exp (decode_uqshl_advsimd_imm_aarch64_instrs_vector_shift_left_sat_simd Rd Rn op immb b__0 U b__1)"
  by (unfold decode_uqshl_advsimd_imm_aarch64_instrs_vector_shift_left_sat_simd_def, non_mem_expI)

lemma non_mem_exp_decode_uqshl_advsimd_imm_aarch64_instrs_vector_shift_left_sat_sisd[non_mem_expI]:
  "non_mem_exp (decode_uqshl_advsimd_imm_aarch64_instrs_vector_shift_left_sat_sisd Rd Rn op immb b__0 U)"
  by (unfold decode_uqshl_advsimd_imm_aarch64_instrs_vector_shift_left_sat_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_uqshl_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd[non_mem_expI]:
  "non_mem_exp (decode_uqshl_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd Rd Rn S R Rm b__0 U b__1)"
  by (unfold decode_uqshl_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd_def, non_mem_expI)

lemma non_mem_exp_decode_uqshl_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd[non_mem_expI]:
  "non_mem_exp (decode_uqshl_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd Rd Rn S R Rm b__0 U)"
  by (unfold decode_uqshl_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_uqshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_simd[non_mem_expI]:
  "non_mem_exp (decode_uqshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_simd Rd Rn op immb b__0 U Q)"
  by (unfold decode_uqshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_simd_def, non_mem_expI)

lemma non_mem_exp_decode_uqshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_sisd[non_mem_expI]:
  "non_mem_exp (decode_uqshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_sisd Rd Rn op immb b__0 U)"
  by (unfold decode_uqshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_uqsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_saturating_simd[non_mem_expI]:
  "non_mem_exp (decode_uqsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_saturating_simd Rd Rn Rm b__0 U b__1)"
  by (unfold decode_uqsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_saturating_simd_def, non_mem_expI)

lemma non_mem_exp_decode_uqsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_saturating_sisd[non_mem_expI]:
  "non_mem_exp (decode_uqsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_saturating_sisd Rd Rn Rm b__0 U)"
  by (unfold decode_uqsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_saturating_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_uqxtn_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_sat_simd[non_mem_expI]:
  "non_mem_exp (decode_uqxtn_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_sat_simd Rd Rn b__0 U Q)"
  by (unfold decode_uqxtn_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_sat_simd_def, non_mem_expI)

lemma non_mem_exp_decode_uqxtn_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_sat_sisd[non_mem_expI]:
  "non_mem_exp (decode_uqxtn_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_sat_sisd Rd Rn b__0 U)"
  by (unfold decode_uqxtn_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_sat_sisd_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_arithmetic_unary_special_recip_int[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_arithmetic_unary_special_recip_int d (datasize :: 'datasize::len itself) elements n)"
  by (unfold execute_aarch64_instrs_vector_arithmetic_unary_special_recip_int_def, non_mem_expI)

lemma non_mem_exp_decode_urecpe_advsimd_aarch64_instrs_vector_arithmetic_unary_special_recip_int[non_mem_expI]:
  "non_mem_exp (decode_urecpe_advsimd_aarch64_instrs_vector_arithmetic_unary_special_recip_int Rd Rn sz b__0)"
  by (unfold decode_urecpe_advsimd_aarch64_instrs_vector_arithmetic_unary_special_recip_int_def, non_mem_expI)

lemma non_mem_exp_decode_urhadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_halving_rounding[non_mem_expI]:
  "non_mem_exp (decode_urhadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_halving_rounding Rd Rn Rm b__0 U b__1)"
  by (unfold decode_urhadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_halving_rounding_def, non_mem_expI)

lemma non_mem_exp_decode_urshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd[non_mem_expI]:
  "non_mem_exp (decode_urshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd Rd Rn S R Rm b__0 U b__1)"
  by (unfold decode_urshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd_def, non_mem_expI)

lemma non_mem_exp_decode_urshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd[non_mem_expI]:
  "non_mem_exp (decode_urshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd Rd Rn S R Rm b__0 U)"
  by (unfold decode_urshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_urshr_advsimd_aarch64_instrs_vector_shift_right_simd[non_mem_expI]:
  "non_mem_exp (decode_urshr_advsimd_aarch64_instrs_vector_shift_right_simd Rd Rn o0 o1 immb b__0 U b__1)"
  by (unfold decode_urshr_advsimd_aarch64_instrs_vector_shift_right_simd_def, non_mem_expI)

lemma non_mem_exp_decode_urshr_advsimd_aarch64_instrs_vector_shift_right_sisd[non_mem_expI]:
  "non_mem_exp (decode_urshr_advsimd_aarch64_instrs_vector_shift_right_sisd Rd Rn o0 o1 immb immh U)"
  by (unfold decode_urshr_advsimd_aarch64_instrs_vector_shift_right_sisd_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_arithmetic_unary_special_sqrt_est_int[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_arithmetic_unary_special_sqrt_est_int d (datasize :: 'datasize::len itself) elements n)"
  by (unfold execute_aarch64_instrs_vector_arithmetic_unary_special_sqrt_est_int_def, non_mem_expI)

lemma non_mem_exp_decode_ursqrte_advsimd_aarch64_instrs_vector_arithmetic_unary_special_sqrt_est_int[non_mem_expI]:
  "non_mem_exp (decode_ursqrte_advsimd_aarch64_instrs_vector_arithmetic_unary_special_sqrt_est_int Rd Rn sz b__0)"
  by (unfold decode_ursqrte_advsimd_aarch64_instrs_vector_arithmetic_unary_special_sqrt_est_int_def, non_mem_expI)

lemma non_mem_exp_decode_ursra_advsimd_aarch64_instrs_vector_shift_right_simd[non_mem_expI]:
  "non_mem_exp (decode_ursra_advsimd_aarch64_instrs_vector_shift_right_simd Rd Rn o0 o1 immb b__0 U b__1)"
  by (unfold decode_ursra_advsimd_aarch64_instrs_vector_shift_right_simd_def, non_mem_expI)

lemma non_mem_exp_decode_ursra_advsimd_aarch64_instrs_vector_shift_right_sisd[non_mem_expI]:
  "non_mem_exp (decode_ursra_advsimd_aarch64_instrs_vector_shift_right_sisd Rd Rn o0 o1 immb immh U)"
  by (unfold decode_ursra_advsimd_aarch64_instrs_vector_shift_right_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_ushl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd[non_mem_expI]:
  "non_mem_exp (decode_ushl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd Rd Rn S R Rm b__0 U b__1)"
  by (unfold decode_ushl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd_def, non_mem_expI)

lemma non_mem_exp_decode_ushl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd[non_mem_expI]:
  "non_mem_exp (decode_ushl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd Rd Rn S R Rm b__0 U)"
  by (unfold decode_ushl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_ushll_advsimd_aarch64_instrs_vector_shift_left_long[non_mem_expI]:
  "non_mem_exp (decode_ushll_advsimd_aarch64_instrs_vector_shift_left_long Rd Rn immb b__0 U Q)"
  by (unfold decode_ushll_advsimd_aarch64_instrs_vector_shift_left_long_def, non_mem_expI)

lemma non_mem_exp_decode_ushr_advsimd_aarch64_instrs_vector_shift_right_simd[non_mem_expI]:
  "non_mem_exp (decode_ushr_advsimd_aarch64_instrs_vector_shift_right_simd Rd Rn o0 o1 immb b__0 U b__1)"
  by (unfold decode_ushr_advsimd_aarch64_instrs_vector_shift_right_simd_def, non_mem_expI)

lemma non_mem_exp_decode_ushr_advsimd_aarch64_instrs_vector_shift_right_sisd[non_mem_expI]:
  "non_mem_exp (decode_ushr_advsimd_aarch64_instrs_vector_shift_right_sisd Rd Rn o0 o1 immb immh U)"
  by (unfold decode_ushr_advsimd_aarch64_instrs_vector_shift_right_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_usqadd_advsimd_aarch64_instrs_vector_arithmetic_unary_add_saturating_simd[non_mem_expI]:
  "non_mem_exp (decode_usqadd_advsimd_aarch64_instrs_vector_arithmetic_unary_add_saturating_simd Rd Rn b__0 U b__1)"
  by (unfold decode_usqadd_advsimd_aarch64_instrs_vector_arithmetic_unary_add_saturating_simd_def, non_mem_expI)

lemma non_mem_exp_decode_usqadd_advsimd_aarch64_instrs_vector_arithmetic_unary_add_saturating_sisd[non_mem_expI]:
  "non_mem_exp (decode_usqadd_advsimd_aarch64_instrs_vector_arithmetic_unary_add_saturating_sisd Rd Rn b__0 U)"
  by (unfold decode_usqadd_advsimd_aarch64_instrs_vector_arithmetic_unary_add_saturating_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_usra_advsimd_aarch64_instrs_vector_shift_right_simd[non_mem_expI]:
  "non_mem_exp (decode_usra_advsimd_aarch64_instrs_vector_shift_right_simd Rd Rn o0 o1 immb b__0 U b__1)"
  by (unfold decode_usra_advsimd_aarch64_instrs_vector_shift_right_simd_def, non_mem_expI)

lemma non_mem_exp_decode_usra_advsimd_aarch64_instrs_vector_shift_right_sisd[non_mem_expI]:
  "non_mem_exp (decode_usra_advsimd_aarch64_instrs_vector_shift_right_sisd Rd Rn o0 o1 immb immh U)"
  by (unfold decode_usra_advsimd_aarch64_instrs_vector_shift_right_sisd_def, non_mem_expI)

lemma non_mem_exp_decode_usubl_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_long[non_mem_expI]:
  "non_mem_exp (decode_usubl_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_long Rd Rn o1 Rm b__0 U Q)"
  by (unfold decode_usubl_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_long_def, non_mem_expI)

lemma non_mem_exp_decode_usubw_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_wide[non_mem_expI]:
  "non_mem_exp (decode_usubw_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_wide Rd Rn o1 Rm b__0 U Q)"
  by (unfold decode_usubw_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_wide_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_transfer_vector_permute_unzip[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_transfer_vector_permute_unzip d l__195 elements (esize :: 'esize::len itself) m n part)"
  by (unfold execute_aarch64_instrs_vector_transfer_vector_permute_unzip_def, non_mem_expI)

lemma non_mem_exp_decode_uzp1_advsimd_aarch64_instrs_vector_transfer_vector_permute_unzip[non_mem_expI]:
  "non_mem_exp (decode_uzp1_advsimd_aarch64_instrs_vector_transfer_vector_permute_unzip Rd Rn op Rm b__0 b__1)"
  by (unfold decode_uzp1_advsimd_aarch64_instrs_vector_transfer_vector_permute_unzip_def, non_mem_expI)

lemma non_mem_exp_decode_uzp2_advsimd_aarch64_instrs_vector_transfer_vector_permute_unzip[non_mem_expI]:
  "non_mem_exp (decode_uzp2_advsimd_aarch64_instrs_vector_transfer_vector_permute_unzip Rd Rn op Rm b__0 b__1)"
  by (unfold decode_uzp2_advsimd_aarch64_instrs_vector_transfer_vector_permute_unzip_def, non_mem_expI)

lemma non_mem_exp_decode_wfe_aarch64_instrs_system_hints[non_mem_expI]:
  "non_mem_exp (decode_wfe_aarch64_instrs_system_hints op2 CRm)"
  by (unfold decode_wfe_aarch64_instrs_system_hints_def, non_mem_expI)

lemma non_mem_exp_decode_wfi_aarch64_instrs_system_hints[non_mem_expI]:
  "non_mem_exp (decode_wfi_aarch64_instrs_system_hints op2 CRm)"
  by (unfold decode_wfi_aarch64_instrs_system_hints_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_crypto_sha3_xar[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_crypto_sha3_xar d imm6 m n)"
  by (unfold execute_aarch64_instrs_vector_crypto_sha3_xar_def, non_mem_expI)

lemma non_mem_exp_decode_xar_advsimd_aarch64_instrs_vector_crypto_sha3_xar[non_mem_expI]:
  "non_mem_exp (decode_xar_advsimd_aarch64_instrs_vector_crypto_sha3_xar Rd Rn imm6 Rm)"
  by (unfold decode_xar_advsimd_aarch64_instrs_vector_crypto_sha3_xar_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_arithmetic_unary_extract_nosat[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_arithmetic_unary_extract_nosat d datasize elements l__0 n part)"
  by (unfold execute_aarch64_instrs_vector_arithmetic_unary_extract_nosat_def, non_mem_expI)

lemma non_mem_exp_decode_xtn_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_nosat[non_mem_expI]:
  "non_mem_exp (decode_xtn_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_nosat Rd Rn b__0 Q)"
  by (unfold decode_xtn_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_nosat_def, non_mem_expI)

lemma non_mem_exp_decode_yield_aarch64_instrs_system_hints[non_mem_expI]:
  "non_mem_exp (decode_yield_aarch64_instrs_system_hints op2 CRm)"
  by (unfold decode_yield_aarch64_instrs_system_hints_def, non_mem_expI)

lemma non_mem_exp_execute_aarch64_instrs_vector_transfer_vector_permute_zip[non_mem_expI]:
  "non_mem_exp (execute_aarch64_instrs_vector_transfer_vector_permute_zip d (datasize :: 'datasize::len itself) (esize :: 'esize::len itself) m n pairs part)"
  by (unfold execute_aarch64_instrs_vector_transfer_vector_permute_zip_def, non_mem_expI)

lemma non_mem_exp_decode_zip1_advsimd_aarch64_instrs_vector_transfer_vector_permute_zip[non_mem_expI]:
  "non_mem_exp (decode_zip1_advsimd_aarch64_instrs_vector_transfer_vector_permute_zip Rd Rn op Rm b__0 b__1)"
  by (unfold decode_zip1_advsimd_aarch64_instrs_vector_transfer_vector_permute_zip_def, non_mem_expI)

lemma non_mem_exp_decode_zip2_advsimd_aarch64_instrs_vector_transfer_vector_permute_zip[non_mem_expI]:
  "non_mem_exp (decode_zip2_advsimd_aarch64_instrs_vector_transfer_vector_permute_zip Rd Rn op Rm b__0 b__1)"
  by (unfold decode_zip2_advsimd_aarch64_instrs_vector_transfer_vector_permute_zip_def, non_mem_expI)

end

context Morello_Instr_Mem_Automaton
begin

lemmas non_cap_exp_traces_enabled[traces_enabledI] = non_cap_expI[THEN non_cap_exp_traces_enabledI]

lemmas non_mem_exp_traces_enabled[traces_enabledI] = non_mem_expI[THEN non_mem_exp_traces_enabledI]


lemma traces_enabled_DC_ZVA[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "store_enabled s AccType_DCZVA (unat (Align val_name 64)) 64 (0 :: 512 word) False"
  shows "traces_enabled (DC_ZVA val_name) s"
  unfolding DC_ZVA_def bind_assoc
  by (traces_enabledI assms: assms intro: traces_enabled_foreachM_index_list_inv2[where Inv = "\<lambda>idx _ memaddrdesc s. {''PCC''} \<subseteq> accessible_regs s \<and> FullAddress_address (AddressDescriptor_paddress memaddrdesc) = FullAddress_address (AddressDescriptor_paddress memaddrdesc0) + word_of_int idx" and var_b = memaddrdesc0 for memaddrdesc0] store_enabled_data_paccess_enabled_subset[OF assms(2)] simp: DCZID_EL0_assm exp_fails_if_then_else aligned_unat_plus_distrib[where sz = 64] AArch64_FullTranslate_translate_address[THEN translate_address_aligned_iff] wi_hom_syms elim: Run_bindE)

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

lemma traces_enabled_AArch64_MemSingle_read[traces_enabledI]:
  assumes "translate_address (unat address) \<noteq> None \<longrightarrow> load_enabled s acctype (unat address) size__arg False"
  shows "traces_enabled (AArch64_MemSingle_read address size__arg acctype wasaligned :: 'size_times_p8::len word M) s"
  unfolding AArch64_MemSingle_read_def bind_assoc
  by (traces_enabledI assms: assms simp: exp_fails_if_then_else)

lemma traces_enabled_AArch64_MemSingle_set[traces_enabledI]:
  assumes "translate_address (unat address) \<noteq> None \<longrightarrow> store_enabled s acctype (unat address) size__arg value_name False" and "LENGTH('a) = 8 * nat size__arg"
  shows "traces_enabled (AArch64_MemSingle_set address size__arg acctype wasaligned (value_name :: 'a::len word)) s"
  unfolding AArch64_MemSingle_set_def bind_assoc
  by (traces_enabledI assms: assms simp: exp_fails_if_then_else translate_address_aligned32_plus16)

lemma traces_enabled_AArch64_TaggedMemSingle[traces_enabledI]:
  assumes "aligned (unat address) (nat size__arg)" and "load_enabled s acctype (unat address) 16 True" and "size__arg = 32 \<Longrightarrow> load_enabled s acctype (unat address + 16) 16 True" and "size__arg = 32 \<Longrightarrow> load_enabled s acctype (unat address) 32 False"
  shows "traces_enabled (AArch64_TaggedMemSingle address size__arg acctype wasaligned) s"
  unfolding AArch64_TaggedMemSingle_def bind_assoc
  by (traces_enabledI assms: assms simp: exp_fails_if_then_else translate_address_aligned32_plus16)

lemma traces_enabled_AArch64_TaggedMemSingle__1[traces_enabledI]:
  assumes "aligned (unat addr) (nat sz)" and "store_enabled s acctype (unat addr) 16 (ucast data :: 128 word) (tags !! 0)" and "sz = 32 \<Longrightarrow> store_enabled s acctype (unat addr + 16) 16 (Word.slice 128 data :: 128 word) (tags !! 1)" and "LENGTH('t) = nat sz div 16" and "LENGTH('d) = 8 * nat sz"
  shows "traces_enabled (AArch64_TaggedMemSingle__1 addr sz acctype wasaligned (tags :: 't::len word) (data :: 'd::len word)) s"
  unfolding AArch64_TaggedMemSingle__1_def bind_assoc
  by (traces_enabledI assms: assms intro: access_enabled_runI simp: exp_fails_if_then_else translate_address_aligned32_plus16)

lemma traces_enabled_AArch64_CapabilityTag[traces_enabledI]:
  assumes "aligned (unat address) 16 \<longrightarrow> load_enabled s acctype (unat address) 16 True"
  shows "traces_enabled (AArch64_CapabilityTag address acctype) s"
  unfolding AArch64_CapabilityTag_def bind_assoc
  by (traces_enabledI assms: assms simp: exp_fails_if_then_else)

lemma traces_enabled_AArch64_CapabilityTag_set[traces_enabledI]:
  assumes "\<And>data :: 128 word. aligned (unat vaddr) 16 \<Longrightarrow> store_enabled s acctype (unat vaddr) 16 data False" and "tag = 0"
  shows "traces_enabled (AArch64_CapabilityTag_set vaddr acctype tag) s"
  unfolding AArch64_CapabilityTag_set_def AArch64_TranslateAddress_def bind_assoc
  by (traces_enabledI assms: assms simp: exp_fails_if_then_else intro: paccess_enabled_runI store_enabled_access_enabled[OF assms(1)])

lemma traces_enabled_Mem_read0[traces_enabledI]:
  assumes "load_enabled s acctype (unat vaddr) sz False"
  shows "traces_enabled (Mem_read0 vaddr sz acctype) s"
  unfolding Mem_read0_def bind_assoc
  by (traces_enabledI assms: assms simp: AArch64_MemSingle_read_translate_address_Some)

lemma traces_enabled_Mem_set0[traces_enabledI]:
  assumes "store_enabled s acctype (unat vaddr) sz data False" and "LENGTH('a) = 8 * nat sz" and "sz \<le> 16"
  shows "traces_enabled (Mem_set0 vaddr sz acctype (data :: 'a::len word)) s"
  unfolding Mem_set0_def bind_assoc
  by (traces_enabledI assms: assms simp: AArch64_MemSingle_set_translate_address_Some)

lemma traces_enabled_MemC_read[traces_enabledI]:
  assumes "aligned (unat address) 16 \<longrightarrow> load_enabled s acctype (unat address) 16 True"
  shows "traces_enabled (MemC_read address acctype) s"
  unfolding MemC_read_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_MemC_set[traces_enabledI]:
  assumes "aligned (unat address) 16 \<longrightarrow> store_enabled s acctype (unat address) 16 (ucast value_name :: 128 word) (CapIsTagSet value_name)"
  shows "traces_enabled (MemC_set address acctype value_name) s"
  unfolding MemC_set_def bind_assoc
  by (traces_enabledI assms: assms simp: update_subrange_vec_dec_test_bit)

lemma traces_enabled_MemCP__1[traces_enabledI]:
  assumes "aligned (unat address) 32" and "store_enabled s acctype (unat address) 16 (ucast value1_name :: 128 word) (CapIsTagSet value1_name)" and "store_enabled s acctype (unat address + 16) 16 (ucast value2_name :: 128 word) (CapIsTagSet value2_name)"
  shows "traces_enabled (MemCP__1 address acctype value1_name value2_name) s"
  unfolding MemCP__1_def bind_assoc
  by (traces_enabledI assms: assms simp: DataFromCapability_def update_subrange_vec_dec_test_bit update_subrange_vec_dec_word_cat_cap_pair slice_128_cat_cap_pair)

lemma traces_enabled_MemAtomicCompareAndSwap[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "VA_derivable base s" and "8 dvd LENGTH('a)"
  shows "traces_enabled (MemAtomicCompareAndSwap base expval (newval :: 'a::len word) ldacctype stacctype) s"
  unfolding MemAtomicCompareAndSwap_def AArch64_TranslateAddressForAtomicAccess_def Let_def bind_assoc
  by (traces_enabledI assms: assms simp: exp_fails_if_then_else)

lemma traces_enabled_MemAtomic[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "VA_derivable base s" and "8 dvd LENGTH('a)"
  shows "traces_enabled (MemAtomic base op (data :: 'a::len word) ldacctype stacctype) s"
  unfolding MemAtomic_def AArch64_TranslateAddressForAtomicAccess_def Let_def bind_assoc
  by (traces_enabledI assms: assms simp: exp_fails_if_then_else)

lemma traces_enabled_MemAtomicCompareAndSwapC[traces_enabledI]:
  assumes "aligned (unat addr) 16 \<longrightarrow> load_enabled s ldacctype (unat addr) 16 True" and "aligned (unat addr) 16 \<longrightarrow> store_enabled s stacctype (unat addr) 16 (ucast newcap :: 128 word) (CapIsTagSet newcap)" and "newcap \<in> derivable_caps s"
  shows "traces_enabled (MemAtomicCompareAndSwapC va addr expcap newcap ldacctype stacctype) s"
  unfolding MemAtomicCompareAndSwapC_def AArch64_TranslateAddressForAtomicAccess_def Let_def bind_assoc
  by (traces_enabledI assms: assms simp: exp_fails_if_then_else update_subrange_vec_dec_test_bit)

lemma traces_enabled_MemAtomicC[traces_enabledI]:
  assumes "aligned (unat address) 16 \<longrightarrow> load_enabled s ldacctype (unat address) 16 True" and "aligned (unat address) 16 \<longrightarrow> store_enabled s stacctype (unat address) 16 (ucast value_name :: 128 word) (CapIsTagSet value_name)" and "value_name \<in> derivable_caps s"
  shows "traces_enabled (MemAtomicC address op value_name ldacctype stacctype) s"
  unfolding MemAtomicC_def AArch64_TranslateAddressForAtomicAccess_def Let_def bind_assoc
  by (traces_enabledI assms: assms simp: DataFromCapability_def update_subrange_vec_dec_test_bit test_bit_of_bl exp_fails_if_then_else)

lemma traces_enabled_CAP_DC_ZVA[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "cval \<in> derivable_caps s"
  shows "traces_enabled (CAP_DC_ZVA cval) s"
  unfolding CAP_DC_ZVA_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_AArch64_SysInstrWithCapability[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "val_name \<in> derivable_caps s"
  shows "traces_enabled (AArch64_SysInstrWithCapability op0 op1 crn crm op2 val_name) s"
  unfolding AArch64_SysInstrWithCapability_def bind_assoc
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

lemma traces_enabled_execute_BLR_CI_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "n = 29 \<longrightarrow> 29 \<in> invoked_indirect_regs" and "RegAuth n \<in> load_auths" and "is_indirect_branch"
  shows "traces_enabled (execute_BLR_CI_C branch_type n offset) s"
  unfolding execute_BLR_CI_C_def bind_assoc
  by (traces_enabledI assms: assms elim: VADeref_load_enabled)

lemma traces_enabled_decode_BLR_CI_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "uint Cn = 29 \<longrightarrow> 29 \<in> invoked_indirect_regs" and "RegAuth (uint Cn) \<in> load_auths" and "is_indirect_branch"
  shows "traces_enabled (decode_BLR_CI_C imm7 Cn) s"
  unfolding decode_BLR_CI_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_BR_CI_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> n" and "n \<le> 31" and "n = 29 \<longrightarrow> 29 \<in> invoked_indirect_regs" and "RegAuth n \<in> load_auths" and "is_indirect_branch"
  shows "traces_enabled (execute_BR_CI_C branch_type n offset) s"
  unfolding execute_BR_CI_C_def bind_assoc
  by (traces_enabledI assms: assms elim: VADeref_load_enabled)

lemma traces_enabled_decode_BR_CI_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "uint Cn = 29 \<longrightarrow> 29 \<in> invoked_indirect_regs" and "RegAuth (uint Cn) \<in> load_auths" and "is_indirect_branch"
  shows "traces_enabled (decode_BR_CI_C imm7 Cn) s"
  unfolding decode_BR_CI_C_def bind_assoc
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
  by (traces_enabledI assms: assms intro: traces_enabled_foreachM_index_list_inv2[where Inv = "\<lambda>idx addr _ s. addr = addr0 + word_of_int (idx * 16) \<and> {''PCC'', ''_R29''} \<subseteq> accessible_regs s \<and> (idx = 0 \<or> valid_address AccType_NORMAL (unat addr0))" and var_a = addr0 for addr0] elim: VADeref_load_enabled AArch64_CapabilityTag_valid_address simp: wi_hom_syms)

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
  by (traces_enabledI assms: assms elim: VADeref_load_enabled)

lemma traces_enabled_decode_LDPBLR_C_C_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "uint Ct = 29 \<longrightarrow> uint Cn \<in> invoked_indirect_regs" and "RegAuth (uint Cn) \<in> load_auths" and "uint Ct \<noteq> 29 \<longrightarrow> \<not>invokes_indirect_caps" and "is_indirect_branch"
  shows "traces_enabled (decode_LDPBLR_C_C_C opc Cn Ct) s"
  unfolding decode_LDPBLR_C_C_C_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_LDPBR_C_C_C[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "0 \<le> n" and "n \<le> 31" and "t__arg = 29 \<longrightarrow> n \<in> invoked_indirect_regs" and "RegAuth n \<in> load_auths" and "t__arg \<noteq> 29 \<longrightarrow> \<not>invokes_indirect_caps" and "is_indirect_branch"
  shows "traces_enabled (execute_LDPBR_C_C_C branch_type n t__arg) s"
  unfolding execute_LDPBR_C_C_C_def bind_assoc
  by (traces_enabledI assms: assms elim: VADeref_load_enabled)

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

lemma traces_enabled_execute_STCT_R_R[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "0 \<le> n" and "n \<le> 31"
  shows "traces_enabled (execute_STCT_R_R n t__arg) s"
  unfolding execute_STCT_R_R_def bind_assoc
  by (traces_enabledI assms: assms elim: VADeref_store_enabled and_SystemAccessEnabled_TagSettingEnabledE[where thesis = "(if a then x else y) = z" and a = a for a x y z])

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

lemma traces_enabled_execute_aarch64_instrs_memory_vector_multiple_no_wb[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "LENGTH('esize) \<in> {8, 16, 32, 64}" and "LENGTH('datasize) \<in> {64, 128}" and "elements = int LENGTH('datasize) div int LENGTH('esize)" and "rpt \<in> {1, 2, 3, 4}" and "selem \<in> {1, 2, 3, 4}"
  shows "traces_enabled (execute_aarch64_instrs_memory_vector_multiple_no_wb (datasize :: 'datasize::len itself) elements (esize :: 'esize::len itself) m memop n rpt selem t__arg wback) s"
  unfolding execute_aarch64_instrs_memory_vector_multiple_no_wb_def bind_assoc Let_def case_prod_beta
  by (traces_enabledI assms: assms intro: traces_enabled_triple_foreachM_index_list_inv[where Inv = "Inv_vector_multiple_no_wb (LENGTH('esize) div 8) elements selem base" and body = "\<lambda>idx_a idx_b idx_c (vars :: (64 word * 'datasize word * int)). (V_read _ (snd (snd vars)) :: 'datasize word M) \<bind> (\<lambda>w. (if memop = MemOp_LOAD then Mem_read0 (add_vec base (fst vars)) _ _ \<bind> (_ w idx_b vars :: 'esize word \<Rightarrow> 'datasize word M) else _ w base idx_b vars) \<bind> (_ vars :: 'datasize word \<Rightarrow> (64 word * 'datasize word * int) M))" for base :: "64 word"] elim: Run_bindE[where thesis = "Inv_vector_multiple_no_wb _ _ _ _ _ _ (_ + 1) _ _"] Run_ifE[where thesis = "Inv_vector_multiple_no_wb _ _ _ _ _ _ (_ + 1) _ _"] Inv_vector_multiple_no_wb_step Mem_read0_valid_address Mem_set0_valid_address simp: unat_0_iff)

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
  unfolding execute_aarch64_instrs_memory_vector_single_no_wb_def bind_assoc Let_def case_prod_beta
  by (traces_enabledI assms: assms intro: traces_enabled_foreachM_index_list_inv[where Inv = "\<lambda>idx vars s. Inv_vector_single_no_wb ebytes idx address (fst (snd vars))" and body = "\<lambda>s (vars :: ('esize word * 64 word * int)). (Mem_read0 (add_vec address (fst (snd vars))) ebytes _ :: 'esize word M) \<bind> (\<lambda>w. _ w vars :: ('esize word * 64 word * int) M)" for address :: "64 word" and ebytes] traces_enabled_foreachM_index_list_inv[where Inv = "\<lambda>idx vars s. Inv_vector_single_no_wb ebytes idx address (fst vars)" and body = "\<lambda>s (vars :: 64 word * 128 word * int). (V_read 128 (snd (snd vars)) :: 128 word M) \<bind> (\<lambda>w. (if memop = MemOp_LOAD then Mem_read0 (add_vec address (fst vars)) ebytes _ \<bind> (\<lambda>w'. _ w' w vars :: 128 word M) else (_ w vars :: 128 word M)) \<bind> (\<lambda>w'. _ w' w vars :: (64 word * 128 word * int) M))" for address :: "64 word" and ebytes] elim: Run_bindE[where thesis = "Inv_vector_single_no_wb _ (_ + 1) _ _"] Run_ifE[where thesis = "Inv_vector_single_no_wb _ (_ + 1) _ _"] Mem_read0_valid_address Mem_set0_valid_address simp: unat_0_iff)

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
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "LENGTH('regsize) \<in> {32, 64} \<and> elsize \<in> {32, 64} \<and> datasize = 2 * elsize"
  shows "traces_enabled (execute_aarch64_instrs_memory_exclusive_pair acctype datasize elsize memop n True (regsize :: 'regsize::len itself) s__arg t__arg t2) s"
  unfolding execute_aarch64_instrs_memory_exclusive_pair_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldaxp_aarch64_instrs_memory_exclusive_pair[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldaxp_aarch64_instrs_memory_exclusive_pair Rt Rn Rt2 o0 Rs L b__0) s"
  unfolding decode_ldaxp_aarch64_instrs_memory_exclusive_pair_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_memory_exclusive_single[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "LENGTH('regsize) \<in> {32, 64} \<and> elsize \<in> {8, 16, 32, 64} \<and> datasize = elsize"
  shows "traces_enabled (execute_aarch64_instrs_memory_exclusive_single acctype datasize elsize memop n False (regsize :: 'regsize::len itself) s__arg t__arg t2) s"
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
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t2" and "t2 \<le> 31" and "0 \<le> t__arg" and "t__arg \<le> 31" and "0 \<le> n" and "n \<le> 31" and "int LENGTH('datasize) \<in> {32, 64, 128, 256}"
  shows "traces_enabled (execute_aarch64_instrs_memory_pair_simdfp_no_alloc acctype (datasize :: 'datasize::len itself) memop n offset postindex t__arg t2 wback) s"
  unfolding execute_aarch64_instrs_memory_pair_simdfp_no_alloc_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldnp_fpsimd_aarch64_instrs_memory_pair_simdfp_no_alloc[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldnp_fpsimd_aarch64_instrs_memory_pair_simdfp_no_alloc Rt Rn Rt2 imm7 L b__0) s"
  unfolding decode_ldnp_fpsimd_aarch64_instrs_memory_pair_simdfp_no_alloc_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_memory_pair_general_no_alloc[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t2" and "t2 \<le> 31" and "0 \<le> t__arg" and "t__arg \<le> 31" and "0 \<le> n" and "n \<le> 31" and "int LENGTH('datasize) \<in> {32, 64}"
  shows "traces_enabled (execute_aarch64_instrs_memory_pair_general_no_alloc acctype (datasize :: 'datasize::len itself) memop n offset postindex t__arg t2 wback) s"
  unfolding execute_aarch64_instrs_memory_pair_general_no_alloc_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldnp_gen_aarch64_instrs_memory_pair_general_no_alloc[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldnp_gen_aarch64_instrs_memory_pair_general_no_alloc Rt Rn Rt2 imm7 L b__0) s"
  unfolding decode_ldnp_gen_aarch64_instrs_memory_pair_general_no_alloc_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_memory_pair_simdfp_post_idx[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t2" and "t2 \<le> 31" and "0 \<le> t__arg" and "t__arg \<le> 31" and "0 \<le> n" and "n \<le> 31" and "int LENGTH('datasize) \<in> {32, 64, 128, 256}"
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
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t2" and "t2 \<le> 31" and "0 \<le> t__arg" and "t__arg \<le> 31" and "0 \<le> n" and "n \<le> 31" and "int LENGTH('datasize) \<in> {32, 64}"
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
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "0 \<le> n" and "n \<le> 31" and "int LENGTH('datasize) \<in> {8, 16, 32, 64, 128, 256, 512, 1024}"
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
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "int LENGTH('regsize) \<in> {32, 64}" and "0 \<le> n" and "n \<le> 31" and "int LENGTH('datasize) \<in> {8, 16, 32, 64}"
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
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_aarch64_instrs_memory_single_simdfp_register acctype (datasize :: 'datasize::len itself) extend_type m memop n postindex shift t__arg wback) s"
  unfolding execute_aarch64_instrs_memory_single_simdfp_register_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldr_reg_fpsimd_aarch64_instrs_memory_single_simdfp_register[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldr_reg_fpsimd_aarch64_instrs_memory_single_simdfp_register Rt Rn S option_name Rm b__0 b__1) s"
  unfolding decode_ldr_reg_fpsimd_aarch64_instrs_memory_single_simdfp_register_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_memory_single_general_register[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "shift \<in> {0, 1, 2, 3}" and "int LENGTH('regsize) \<in> {32, 64}" and "0 \<le> n" and "n \<le> 31" and "0 \<le> m" and "m \<le> 31" and "int LENGTH('datasize) \<in> {8, 16, 32, 64}"
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
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "int LENGTH('regsize) \<in> {32, 64}" and "0 \<le> n" and "n \<le> 31" and "int LENGTH('datasize) \<in> {8, 16, 32, 64}"
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
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "0 \<le> n" and "n \<le> 31" and "int LENGTH('datasize) \<in> {8, 16, 32, 64, 128, 256, 512, 1024}"
  shows "traces_enabled (execute_aarch64_instrs_memory_single_simdfp_immediate_signed_offset_normal acctype (datasize :: 'datasize::len itself) memop n offset postindex t__arg wback) s"
  unfolding execute_aarch64_instrs_memory_single_simdfp_immediate_signed_offset_normal_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_decode_ldur_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_offset_normal[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s"
  shows "traces_enabled (decode_ldur_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_offset_normal Rt Rn imm9 b__0 b__1) s"
  unfolding decode_ldur_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_offset_normal_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_aarch64_instrs_memory_single_general_immediate_signed_offset_normal[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "int LENGTH('regsize) \<in> {32, 64}" and "0 \<le> n" and "n \<le> 31" and "int LENGTH('datasize) \<in> {8, 16, 32, 64}"
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

lemma traces_enabled_execute_aarch64_instrs_memory_single_general_immediate_unsigned[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "0 \<le> t__arg" and "t__arg \<le> 31" and "int LENGTH('regsize) \<in> {32, 64}" and "0 \<le> n" and "n \<le> 31" and "int LENGTH('datasize) \<in> {8, 16, 32, 64}"
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

lemma traces_enabled_DecodeA64[traces_enabledI]:
  assumes "{''PCC'', ''_R29''} \<subseteq> accessible_regs s" and "instr_exp_assms (DecodeA64 pc opcode)" and "no_system_reg_access"
  shows "traces_enabled (DecodeA64 pc opcode) s"
  using assms(2)
  by (unfold DecodeA64_def, elim instr_exp_assms_traces_enabled_ifE instr_exp_assms_traces_enabled_letE) (solves \<open>traces_enabledI assms: assms(1) intro: assms(3) simp: instr_exp_assms_def invocation_instr_exp_assms_write_ThisInstrAbstract_iff load_instr_exp_assms_write_ThisInstrAbstract_iff\<close>)+

end

end
