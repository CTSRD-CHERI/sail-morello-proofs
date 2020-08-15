theory CHERI_Lemmas
  imports CHERI_Gen_Lemmas
begin

context Morello_Axiom_Automaton
begin

lemma MemCP_fst_derivable[derivable_capsE]:
  "Run (MemCP address acctype) t a \<Longrightarrow> use_mem_caps \<Longrightarrow> fst a \<in> derivable_caps (run s t)"
  by (unfold MemCP_def, derivable_capsI)

lemma MemCP_snd_derivable[derivable_capsE]:
  "Run (MemCP address acctype) t a \<Longrightarrow> use_mem_caps \<Longrightarrow> snd a \<in> derivable_caps (run s t)"
  by (unfold MemCP_def, derivable_capsI)

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
  assumes "Run (VADeref va sz perms acctype) t vaddr"
  shows "VAIsSealedCap va \<longleftrightarrow> False"
  using assms
  unfolding VADeref_def
  by (auto simp: VAIsSealedCap_def VAIsCapability_def CheckCapability_CapIsSealed_False elim!: Run_bindE Run_ifE)

lemma VADeref_not_sealed[derivable_capsE]:
  assumes "Run (VADeref va sz perms acctype) t vaddr"
  shows "\<not>VAIsSealedCap va"
  using assms
  by auto

lemma if_VADerefs_VAIsSealedCap_False[derivable_capsE]:
  assumes "Run (if b then VADeref va sz perms acctype else VADeref va sz' perms' acctype') t vaddr"
  shows "\<not>VAIsSealedCap va"
  using assms
  by (auto split: if_splits)

lemma Run_case_MemOp_LOAD_STORE_not_VAIsSealedCap[derivable_capsE]:
  assumes "Run (case memop of MemOp_LOAD \<Rightarrow> VADeref va sz perms acctype \<bind> m | MemOp_STORE \<Rightarrow> VADeref va sz' perms' acctype' \<bind> m' | MemOp_PREFETCH \<Rightarrow> return ()) t a"
    and "memop \<noteq> MemOp_PREFETCH"
  shows "\<not>VAIsSealedCap va"
  using assms
  by (cases memop) (auto elim!: Run_bindE)

lemma Run_case_MemOp_LOAD_STORE_not_VAIsSealedCap_pre_idx[derivable_capsE]:
  assumes "Run (case memop of MemOp_LOAD \<Rightarrow> VADeref va sz perms acctype \<bind> m | MemOp_STORE \<Rightarrow> VADeref va sz' perms' acctype' \<bind> m' | MemOp_PREFETCH \<Rightarrow> return ()) t a"
    and "memop \<noteq> MemOp_PREFETCH"
    and "VAIsSealedCap va = VAIsSealedCap va'"
  shows "\<not>VAIsSealedCap va'"
  using assms
  by (cases memop) (auto elim!: Run_bindE)

lemma Run_case_MemOp_LOAD_STORE_not_VAIsSealedCap_generic:
  assumes "Run (case memop of MemOp_LOAD \<Rightarrow> VADeref va sz perms acctype \<bind> m | MemOp_STORE \<Rightarrow> VADeref va sz' perms' acctype' \<bind> m' | MemOp_PREFETCH \<Rightarrow> m'') t a"
    and "memop \<noteq> MemOp_PREFETCH"
    and "VAIsSealedCap va = VAIsSealedCap va'"
  shows "\<not>VAIsSealedCap va'"
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

lemma CSP_read_derivable_caps[derivable_capsE]:
  "Run (CSP_read u) t c \<Longrightarrow> c \<in> derivable_caps (run s t)"
  using EL_exhaust_disj
  by (fastforce simp: CSP_read_def Let_def register_defs derivable_caps_def accessible_regs_def accessed_caps_def
                elim!: Run_bindE Run_ifE Run_read_regE intro!: derivable.Copy)

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
    by - (derivable_capsI elim: CSP_read_derivable_caps VAFromCapability_base_derivable_run)
  then show ?thesis
    using VA_Capability
    by (auto simp: VA_derivable_def)
qed

declare BaseReg_read_VA_derivable[where is_prefetch = False, folded BaseReg_read__1_def, derivable_capsE]

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
    by - (derivable_capsI elim: CSP_read_derivable_caps VAFromCapability_base_derivable_run)
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

lemma traces_enabled_WriteTags[traces_enabledI]:
  assumes "tags = 0" and "LENGTH('a) = nat sz"
  shows "traces_enabled (WriteTags addrdesc sz (tags :: 'a::len word) accdesc) s"
  unfolding WriteTags_def
  by (traces_enabledI assms: assms intro: traces_enabled_return
                      simp: cap_of_mem_bytes_of_word_Capability_of_tag_word[where tag = False, simplified])

text \<open>Capability invocation\<close>

definition enabled_pcc :: "Capability \<Rightarrow> (Capability, register_value) axiom_state \<Rightarrow> bool" where
  "enabled_pcc c s \<equiv>
     c \<in> derivable_caps s \<or>
     (c \<in> invoked_caps \<and>
      ((\<exists>c' \<in> derivable_caps s.
          CapIsTagSet c' \<and> CapGetObjectType c' = CAP_SEAL_TYPE_RB \<and>
          leq_cap CC c (CapUnseal c')) \<or>
       (\<exists>cc cd.
          cc \<in> derivable_caps s \<and> cd \<in> derivable_caps s \<and>
          invokable CC cc cd \<and>
          leq_cap CC c (CapUnseal cc))))"

lemma traces_enabled_PCC_set:
  assumes "enabled_pcc c s"
  shows "traces_enabled (PCC_set c) s"
  using assms
  unfolding PCC_set_def enabled_pcc_def derivable_caps_def
  by (intro traces_enabled_write_reg) (auto simp: register_defs is_sentry_def invokable_def CapIsSealed_def)

definition enabled_branch_target :: "Capability \<Rightarrow> (Capability, register_value) axiom_state \<Rightarrow> bool" where
  "enabled_branch_target c s \<equiv>
     (CapIsTagSet c \<and> \<not>CapIsSealed c) \<longrightarrow> (\<forall>c' \<in> branch_caps c. enabled_pcc c' s)"

declare Run_ifE[where thesis = "enabled_branch_target c s" and a = c for c s, derivable_caps_combinators]
declare Run_letE[where thesis = "enabled_branch_target c s" and a = c for c s, derivable_caps_combinators]
declare Run_return_resultE[where P = "\<lambda>c. enabled_branch_target c s" for s, derivable_caps_combinators]

declare Run_bindE'[where P = "\<lambda>t. enabled_branch_target c (run s t)" for c s, simplified, derivable_caps_combinators]
declare Run_bindE[where thesis = "enabled_branch_target c s" and a = c for c s, derivable_caps_combinators]
declare if_split[where P = "\<lambda>c. enabled_branch_target c s" for s, THEN iffD2, derivable_capsI]
declare if_split[where P = "\<lambda>c. enabled_branch_target (CapUnseal c) s" for s, THEN iffD2, derivable_capsI]

lemma enabled_branch_targetI:
  assumes "CapIsTagSet c \<and> \<not>CapIsSealed c \<longrightarrow> (\<forall>c' \<in> branch_caps c. enabled_pcc c' s)"
  shows "enabled_branch_target c s"
  using assms
  by (auto simp: enabled_branch_target_def)

lemma enabled_pcc_run_imp:
  assumes "enabled_pcc c s"
  shows "enabled_pcc c (run s t)"
  using assms
  by (auto simp: enabled_pcc_def intro: derivable_caps_run_imp)

lemma enabled_branch_target_run_imp[derivable_caps_runI]:
  assumes "enabled_branch_target c s"
  shows "enabled_branch_target c (run s t)"
  using assms
  by (auto simp: enabled_branch_target_def intro: derivable_caps_run_imp enabled_pcc_run_imp)

lemma enabled_branch_target_CapUnseal[derivable_capsI]:
  assumes "c \<in> derivable_caps s"
    and "CapIsTagSet c \<longrightarrow> CapGetObjectType c = CAP_SEAL_TYPE_RB \<and> branch_caps (CapUnseal c) \<subseteq> invoked_caps"
  shows "enabled_branch_target (CapUnseal c) s"
  using assms
  unfolding enabled_branch_target_def enabled_pcc_def
  by (fastforce intro: branch_caps_leq)

lemma enabled_branch_target_CapWithTagClear[derivable_capsI]:
  "enabled_branch_target (CapWithTagClear c) s"
  by (auto simp: enabled_branch_target_def enabled_pcc_def derivable_caps_def branch_caps_128th_iff)

lemma derivable_enabled_branch_target:
  assumes "c \<in> derivable_caps s"
  shows "enabled_branch_target c s"
  using branch_caps_derivable_caps[OF _ assms]
  by (auto simp: enabled_branch_target_def enabled_pcc_def)

declare C_read_derivable[THEN derivable_enabled_branch_target, derivable_capsE]

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

lemma branch_sealed_pair_enabled_pcc:
  assumes "CapGetObjectType cc = CapGetObjectType cd"
    and "CapIsTagSet cc" and "CapIsTagSet cd"
    and "cap_permits CAP_PERM_EXECUTE cc" and "\<not>cap_permits CAP_PERM_EXECUTE cd"
    and "cap_permits CAP_PERM_BRANCH_SEALED_PAIR cc" and "cap_permits CAP_PERM_BRANCH_SEALED_PAIR cd"
    and "CAP_MAX_FIXED_SEAL_TYPE < uint (CapGetObjectType cc)"
    and "cc \<in> derivable_caps s" and "cd \<in> derivable_caps s"
    and "branch_caps (CapUnseal cc) \<subseteq> invoked_caps"
  shows "\<forall>c' \<in> branch_caps (CapUnseal cc). enabled_pcc c' s"
  using assms
  unfolding enabled_pcc_def
  by (fastforce simp: invokable_def CapIsSealed_def is_sentry_def intro: branch_caps_leq)

lemma (in Write_Cap_Assm_Automaton) traces_enabled_write_IDC_CCall:
  assumes "c \<in> invoked_caps" and "invokable CC cc cd"
    and "isa.caps_of_regval ISA (regval_of r v) = {c}"
    and "cc \<in> derivable (accessed_caps (\<not>invokes_mem_caps) s)"
    and "cd \<in> derivable (accessed_caps (\<not>invokes_mem_caps) s)"
    and "name r \<in> isa.IDC ISA"
    and "leq_cap CC c (unseal_method CC cd)"
  shows "traces_enabled (write_reg r v) s"
  using assms
  by (intro traces_enabled_write_reg) auto

lemma branch_sealed_pair_C_set_29:
  assumes "CapGetObjectType cc = CapGetObjectType cd"
    and "CapIsTagSet cc" and "CapIsTagSet cd"
    and "cap_permits CAP_PERM_EXECUTE cc" and "\<not>cap_permits CAP_PERM_EXECUTE cd"
    and "cap_permits CAP_PERM_BRANCH_SEALED_PAIR cc" and "cap_permits CAP_PERM_BRANCH_SEALED_PAIR cd"
    and "CAP_MAX_FIXED_SEAL_TYPE < uint (CapGetObjectType cc)"
    and "cc \<in> derivable_caps s" and "cd \<in> derivable_caps s"
    and "CapUnseal cd \<in> invoked_caps"
  shows "traces_enabled (C_set 29 (CapUnseal cd)) s"
  using assms
  by (fastforce simp: C_set_def R_set_def  derivable_caps_def invokable_def CapIsSealed_def is_sentry_def register_defs
                intro: traces_enabled_write_IDC_CCall[of "CapUnseal cd" cc cd])

lemma traces_enabled_BranchToCapability[traces_enabledI]:
  assumes "enabled_branch_target c s"
  shows "traces_enabled (BranchToCapability c branch_type) s"
  unfolding BranchToCapability_def
  by (traces_enabledI assms: assms intro: traces_enabled_PCC_set non_cap_expI[THEN non_cap_exp_traces_enabledI])

lemma enabled_branch_target_set_0th[derivable_capsI]:
  assumes "enabled_branch_target c s"
  shows "enabled_branch_target (update_vec_dec c 0 (Morello.Bit 0)) s"
  using assms
  by (auto simp: enabled_branch_target_def branch_caps_def CapGetValue_def nth_ucast test_bit_set_gen)

lemma traces_enabled_BranchXToCapability[traces_enabledI]:
  assumes "enabled_branch_target c s"
  shows "traces_enabled (BranchXToCapability c branch_type) s"
  unfolding BranchXToCapability_def
  by (traces_enabledI assms: assms intro: non_cap_expI[THEN non_cap_exp_traces_enabledI])

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
  then have "seal_method CC c (get_cursor_method CC c') \<in> derivable (accessed_caps (\<not>invokes_mem_caps) s)"
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
  have "seal_method CC c (unat otype) \<in> derivable (accessed_caps (\<not>invokes_mem_caps) s)"
    if "CapIsTagSet c"
    using that assms
    by (intro derivable.SealEntry)
       (auto simp: is_sentry_def seal_def derivable_caps_def simps and_mask_bintr)
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
  then have "clear_global_unless CC (is_global_method CC auth) (unseal_method CC c) \<in> derivable (accessed_caps (\<not>invokes_mem_caps) s)"
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

lemma CapIsSubSetOf_CapUnseal_derivable:
  assumes "Run (CapIsSubSetOf c c') t a" and "a" and "trace_assms t"
    and "c \<in> derivable_caps s"
    and "c' \<in> derivable_caps s"
    and "CapIsTagSet c'" and "\<not>CapIsSealed c'"
  shows "CapUnseal c \<in> derivable_caps s"
proof cases
  assume tag: "CapIsTagSet c"
  (* TODO: Lemma as stated here requires global assumption that (base \<le> limit) holds for
     derivable capabilities *)
  then have "get_base (CapUnseal c) \<le> get_limit (CapUnseal c)"
    using \<open>c \<in> derivable_caps s\<close> and \<open>trace_assms t\<close>
    unfolding get_bounds_CapUnseal_eq
    sorry
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

(*lemma CapIsInternalExponent_CapSetObjectType_iff[simp]:
  "CapIsInternalExponent (CapSetObjectType c otype) = CapIsInternalExponent c"
  unfolding CapIsInternalExponent_def CapSetObjectType_def CAP_OTYPE_LO_BIT_def CAP_OTYPE_HI_BIT_def CAP_IE_BIT_def
  by (auto simp: update_subrange_vec_dec_test_bit)*)

text \<open>Some instructions have constrained UNPREDICTABLE behaviour that allows
  using UNKNOWN values for Capabilities and VirtualAddresses.  However, rules
  TRWTV and TSNJF in the Morello architecture document (DDI0606 A.c) say that
  these values must "not increase the Capability defined rights available to
  software".  Here, we assume that UNKNOWN capabilities are derivable.\<close>

lemma UNKNOWN_Capability_derivable[derivable_capsE]:
  assumes "Run (UNKNOWN_bits 129) t c" and "trace_assms t"
  shows "c \<in> derivable_caps s"
  (* TODO: Formulate suitable trace_assms.  Tweaking the Choose constructor of the prompt monad
     to allow arbitrary register_value's instead of just Booleans might make this easier. *)
  sorry

lemma UNKNOWN_VirtualAddress_derivable[derivable_capsE]:
  assumes "Run (UNKNOWN_VirtualAddress u) t va" and "trace_assms t"
  shows "VA_derivable va s"
  sorry

text \<open>AArch32 is unsupported on Morello\<close>

lemma UsingAArch32_False[simp]:
  assumes "trace_assms t"
  shows "\<not>Run (UsingAArch32 ()) t True"
  sorry

text \<open>Assume that tag setting is disabled\<close>

lemma IsTagSettingDisabled_not_False:
  assumes "trace_assms t"
  shows "Run (IsTagSettingDisabled ()) t False \<longleftrightarrow> False"
  sorry

text \<open>Assume that PCC is not sealed\<close>

lemma PCC_read_not_sealed[intro, simp, derivable_capsE]:
  assumes "Run (PCC_read u) t c" and "trace_assms t"
  shows "\<not>CapIsSealed c"
  sorry

lemma read_PCC_not_sealed[intro, simp, derivable_capsE]:
  assumes "Run (read_reg PCC_ref) t c" and "trace_assms t"
  shows "\<not>CapIsSealed c"
  sorry

end

context Morello_Mem_Automaton
begin

lemma access_enabled_runI[derivable_caps_runI]:
  assumes "access_enabled s acctype vaddr paddr sz v tag"
  shows "access_enabled (run s t) acctype vaddr paddr sz v tag"
  using assms derivable_mono[OF accessed_caps_run_mono]
  by (auto simp: access_enabled_def)

abbreviation paccess_enabled where
  "paccess_enabled s acctype paddr sz v tag
   \<equiv> \<exists>vaddr. access_enabled s acctype vaddr paddr sz v tag"

lemma paccess_enabled_runI[derivable_caps_runI]:
  assumes "paccess_enabled s acctype paddr sz v tag"
  shows "paccess_enabled (run s t) acctype paddr sz v tag"
  using assms
  by (auto intro: derivable_caps_runI)

lemma traces_enabled_ReadMemory:
  assumes "\<And>v. paccess_enabled s Load (unat paddr) sz v B0"
  shows "traces_enabled (ReadMemory sz paddr) s"
  using assms
  unfolding ReadMemory_def
  by (intro traces_enabled_read_mem) (auto)

lemma traces_enabled_Mem_read[traces_enabledI]:
  assumes "\<And>v. paccess_enabled s Load (unat (FullAddress_address (AddressDescriptor_paddress desc))) (nat sz) v B0"
  shows "traces_enabled (Mem_read desc sz accdesc) s"
  unfolding Mem_read_def bind_assoc
  by (traces_enabledI intro: traces_enabled_read_mem assms: assms)

lemma traces_enabled_ReadMem[traces_enabledI]:
  assumes "\<And>v. paccess_enabled s Load (unat (FullAddress_address (AddressDescriptor_paddress desc))) (nat sz) v B0"
  shows "traces_enabled (ReadMem desc sz accdesc) s"
  unfolding ReadMem_def bind_assoc
  by (traces_enabledI intro: traces_enabled_read_mem assms: assms)

lemma traces_enabled_ReadTaggedMem[traces_enabledI]:
  assumes "\<And>v tag. paccess_enabled s Load (unat (FullAddress_address (AddressDescriptor_paddress desc))) 16 v tag"
    and "\<And>v tag. sz = 32 \<Longrightarrow> paccess_enabled s Load (unat (FullAddress_address (AddressDescriptor_paddress desc)) + 16) 16 v tag"
    and "sz = 16 \<or> sz = 32"
  shows "traces_enabled (ReadTaggedMem desc sz accdesc) s"
  unfolding ReadTaggedMem_def bind_assoc
  by (traces_enabledI intro: traces_enabled_read_memt non_cap_expI[THEN non_cap_exp_traces_enabledI] paccess_enabled_runI assms: assms)

lemma traces_enabled_ReadTags[traces_enabledI]:
  assumes "\<And>v tag. paccess_enabled s Load (unat (FullAddress_address (AddressDescriptor_paddress desc))) 16 v tag"
  shows "traces_enabled (ReadTags desc 1 accdesc) s"
  unfolding ReadTags_def bind_assoc
  by (traces_enabledI intro: traces_enabled_read_memt non_cap_expI[THEN non_cap_exp_traces_enabledI] paccess_enabled_runI
                      assms: assms)

lemma traces_enabled_Write_mem:
  assumes "\<And>r. traces_enabled (m r) (axiom_step s (E_write_mem wk paddr sz v r))"
    and "\<And>r. enabled s (E_write_mem wk paddr sz v r)"
  shows "traces_enabled (Write_mem wk paddr sz v m) s"
  using assms
  by (fastforce simp: traces_enabled_def elim!: Traces_cases[where m = "Write_mem wk paddr sz v m"])

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
  by (auto intro!: traces_enabled_Write_mem non_cap_expI[THEN non_cap_exp_traces_enabledI]
           split: option.splits simp: legal_store_def length_mem_bytes_of_word)

lemma traces_enabled_Mem_set[traces_enabledI]:
  fixes data :: "'a::len word"
  assumes "paccess_enabled s Store (unat (FullAddress_address (AddressDescriptor_paddress desc))) (nat sz) (mem_bytes_of_word data) B0"
    and "LENGTH('a) = nat sz * 8" and "sz > 0"
  shows "traces_enabled (Mem_set desc sz accdesc data) s"
  using assms
  unfolding Mem_set_def
  by (auto intro!: traces_enabled_bind traces_enabled_write_mem non_cap_expI[THEN non_cap_exp_traces_enabledI])

lemma traces_enabled_Write_memt:
  assumes "\<And>r. traces_enabled (m r) (axiom_step s (E_write_memt wk paddr sz v tag r))"
    and "\<And>r. enabled s (E_write_memt wk paddr sz v tag r)"
  shows "traces_enabled (Write_memt wk paddr sz v tag m) s"
  using assms
  by (fastforce simp: traces_enabled_def elim!: Traces_cases[where m = "Write_memt wk paddr sz v tag m"])

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
  by (auto intro!: traces_enabled_Write_memt non_cap_expI[THEN non_cap_exp_traces_enabledI]
           split: option.splits simp: legal_store_def length_mem_bytes_of_word)

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
  "store_enabled s vaddr sz data tag \<equiv>
     sz > 0 \<and> vaddr + nat sz \<le> 2^64 \<and>
     (\<forall>paddr.
        translate_address vaddr = Some paddr \<longrightarrow>
        access_enabled s Store vaddr paddr (nat sz) (mem_bytes_of_word data) (bitU_of_bool tag))"

definition load_enabled where
  "load_enabled s vaddr sz tagged \<equiv>
     sz > 0 \<and> vaddr + nat sz \<le> 2^64 \<and>
     (\<forall>paddr data tag.
        translate_address vaddr = Some paddr \<longrightarrow>
        access_enabled s Load vaddr paddr (nat sz) data (if tagged then tag else B0))"

lemma store_enabled_runI[derivable_caps_runI]:
  assumes "store_enabled s vaddr sz data tag"
  shows "store_enabled (run s t) vaddr sz data tag"
  using assms
  by (auto simp: store_enabled_def intro: access_enabled_runI)

lemma load_enabled_runI[derivable_caps_runI]:
  assumes "load_enabled s vaddr sz tagged"
  shows "load_enabled (run s t) vaddr sz tagged"
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

lemma access_enabled_data_load_subset:
  assumes "access_enabled s Load vaddr paddr sz data tag"
    and "vaddr \<le> vaddr'" and "vaddr' + sz' \<le> vaddr + sz"
    and "translate_address vaddr' = Some paddr'"
  shows "access_enabled s Load vaddr' paddr' sz' data' B0"
  using assms
  unfolding access_enabled_def authorises_access_def has_access_permission_def
  by (auto intro: addrs_in_mem_region_subset)

lemma load_enabled_data_subset[intro]:
  assumes "load_enabled s vaddr sz False"
    and "vaddr + nat sz \<le> 2^64 \<longrightarrow> vaddr \<le> vaddr' \<and> vaddr' + nat sz' \<le> vaddr + nat sz"
    and "sz' > 0"
    and "translate_address vaddr \<noteq> None"
  shows "load_enabled s vaddr' sz' False"
  using assms
  by (auto simp: load_enabled_def intro: access_enabled_data_load_subset)

lemma load_enabled_access_enabled[intro]:
  assumes "load_enabled s vaddr sz tagged"
    and "sz' = nat sz"
    and "translate_address vaddr = Some paddr"
    and "tagged \<or> tag = B0"
  shows "\<exists>vaddr. access_enabled s Load vaddr paddr sz' data tag"
  using assms
  unfolding load_enabled_def
  by (cases tagged) auto

lemma access_enabled_data_store_subset:
  assumes "access_enabled s Store vaddr paddr sz data tag"
    and "vaddr \<le> vaddr'" and "vaddr' + sz' \<le> vaddr + sz"
    and "translate_address vaddr' = Some paddr'"
  shows "access_enabled s Store vaddr' paddr' sz' data' B0"
  using assms
  unfolding access_enabled_def authorises_access_def has_access_permission_def
  by (auto intro: addrs_in_mem_region_subset)

lemma store_enabled_data_subset[intro]:
  assumes "store_enabled s vaddr sz data tag"
    and "vaddr + nat sz \<le> 2^64 \<longrightarrow> vaddr \<le> vaddr' \<and> vaddr' + nat sz' \<le> vaddr + nat sz"
    and "sz' > 0"
    and "translate_address vaddr \<noteq> None"
  shows "store_enabled s vaddr' sz' data' False"
  using assms
  by (auto simp: store_enabled_def intro: access_enabled_data_store_subset)

lemma store_enabled_access_enabled[intro]:
  assumes "store_enabled s vaddr sz data tag"
    and "sz' = nat sz" and "data' = mem_bytes_of_word data" and "tag' = bitU_of_bool tag"
    and "translate_address vaddr = Some paddr"
  shows "\<exists>vaddr. access_enabled s Store vaddr paddr sz' data' tag'"
  using assms
  unfolding store_enabled_def
  by auto

lemma store_enabled_reverse_endianness[simp]:
  "store_enabled s vaddr sz (reverse_endianness0 data) False = store_enabled s vaddr sz data False"
  by (auto simp: store_enabled_def access_enabled_def)

lemma trace_assms_translation_trace_assms[intro, simp]:
  "trace_assms t \<Longrightarrow> translation_assms_trace t"
  by auto

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

lemma translate_address_aligned32_plus16:
  assumes "translate_address vaddr = Some paddr"
    and "aligned vaddr 32"
  shows "translate_address (vaddr + 16) = Some (paddr + 16)"
  using assms
  apply (auto simp: translate_address_def aligned_def dvd_def)
  find_theorems aligned "(_ + _)"
  find_theorems (70) "(_ + _) mod _"
  find_theorems (80) "(mod)" "(*)" "(+)"
  thm div_mult_mod_eq
  sorry

lemma AArch64_MemSingle_read_translate_address_Some:
  assumes "Run (AArch64_MemSingle_read vaddr sz acctype wasaligned) t a"
    and "trace_assms t"
  shows "\<exists>paddr. translate_address (unat vaddr) = Some paddr"
  using assms
  unfolding AArch64_MemSingle_read_def AArch64_TranslateAddress_def
  by (auto elim!: Run_bindE simp: exp_fails_if_then_else IsFault_def translate_correct)

lemma AArch64_MemSingle_set_translate_address_Some:
  assumes "Run (AArch64_MemSingle_set vaddr sz acctype wasaligned data) t a"
    and "trace_assms t"
  shows "\<exists>paddr. translate_address (unat vaddr) = Some paddr"
  using assms
  unfolding AArch64_MemSingle_set_def AArch64_TranslateAddress_def
  by (auto elim!: Run_bindE simp: exp_fails_if_then_else IsFault_def translate_correct)

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

lemma tag_granule_16[simp]: "tag_granule ISA = 16"
  by (auto simp: ISA_def)

lemma address_tag_aligned_iff_aligned_16[simp]:
  "address_tag_aligned ISA addr \<longleftrightarrow> aligned addr 16"
  by (auto simp: address_tag_aligned_def aligned_def)

lemma translate_address_aligned_iff[simp]:
  assumes "translate_address vaddr = Some paddr"
    and "sz dvd 2^48"
  shows "aligned paddr sz \<longleftrightarrow> aligned vaddr sz"
  using assms
  by (auto simp: translate_address_def dvd_mod_iff aligned_def)

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
    and "FaultRecord_statuscode (AddressDescriptor_fault addrdesc) = Fault_None"
    and "aligned (unat vaddr) sz" and "sz dvd 2^48"
    and "trace_assms t"
  shows "aligned (unat (FullAddress_address (AddressDescriptor_paddress addrdesc))) sz"
    (is "aligned ?paddr sz")
proof -
  have *: "translate_address (unat vaddr) = Some ?paddr"
    using assms
    by (auto simp: translate_correct trace_assms_def ev_assms_def)
  show ?thesis
    using \<open>aligned (unat vaddr) sz\<close>
    unfolding translate_address_aligned_iff[OF * \<open>sz dvd 2^48\<close>] .
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
  assumes "Run (CapIsRangeInBounds c addr sz) t True" and "trace_assms t"
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

lemma CheckCapability_load_enabled:
  assumes t: "Run (CheckCapability c addr sz req_perms acctype) t vaddr" "trace_assms t"
    and sz: "sz > 0" "unat vaddr + nat sz \<le> 2^64"
    and sz': "sz' > 0" "unat vaddr \<le> vaddr'" "vaddr' + nat sz' \<le> unat vaddr + nat sz"
    and "perm_bits_included CAP_PERM_LOAD req_perms"
    and "tagged \<longrightarrow> perm_bits_included CAP_PERM_LOAD_CAP req_perms"
    and "tagged \<longrightarrow> nat sz' = 16 \<and> aligned vaddr' 16"
    and "\<not>CapIsSealed c \<longrightarrow> c \<in> derivable_caps (run s t)"
  shows "load_enabled (run s t) vaddr' sz' tagged"
proof (unfold load_enabled_def, intro allI impI conjI)
  show "sz' > 0" and "vaddr' + nat sz' \<le> 2 ^ 64"
    using sz sz'
    by auto
next
  fix paddr data tag
  assume paddr: "translate_address vaddr' = Some paddr"
  let ?tag = "if tagged then tag else B0"
  let ?is_cap = "?tag \<noteq> B0"
  let ?is_local_cap = "mem_val_is_local_cap CC ISA data ?tag \<and> tag = B1"
  have tagged: "CapIsTagSet c" and not_sealed: "\<not>CapIsSealed c"
    using assms
    by (auto elim!: Run_bindE split: if_splits simp: CheckCapability_def)
  then have c: "c \<in> derivable (accessed_caps (\<not>invokes_mem_caps) (run s t))"
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
  then show "access_enabled (run s t) Load vaddr' paddr (nat sz') data ?tag"
    using c aligned
    by (fastforce simp: access_enabled_def)
qed

lemma CheckCapability_store_enabled:
  fixes data :: "'a::len word"
  assumes t: "Run (CheckCapability c addr sz req_perms acctype) t vaddr" "trace_assms t"
    and sz: "sz > 0" "unat vaddr + nat sz \<le> 2^64"
    and sz': "sz' > 0" "unat vaddr \<le> vaddr'" "vaddr' + nat sz' \<le> unat vaddr + nat sz"
    and store_perm: "perm_bits_included CAP_PERM_STORE req_perms"
    and store_cap_perm: "tag \<longrightarrow> perm_bits_included CAP_PERM_STORE_CAP req_perms"
    and local_perm: "tag \<and> CapIsLocal (Capability_of_tag_word tag (ucast data)) \<longrightarrow> perm_bits_included CAP_PERM_STORE_LOCAL req_perms"
    and aligned: "tag \<longrightarrow> nat sz' = 16 \<and> aligned vaddr' 16 \<and> LENGTH('a) = 128"
    and "\<not>CapIsSealed c \<longrightarrow> c \<in> derivable_caps (run s t)"
  shows "store_enabled (run s t) vaddr' sz' data tag"
proof (unfold store_enabled_def, intro allI impI conjI)
  show "sz' > 0" and "vaddr' + nat sz' \<le> 2 ^ 64"
    using sz sz'
    by auto
next
  fix paddr
  assume paddr: "translate_address vaddr' = Some paddr"
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
  then have c: "c \<in> derivable (accessed_caps (\<not>invokes_mem_caps) (run s t))"
    using \<open>\<not>CapIsSealed c \<longrightarrow> c \<in> derivable_caps (run s t)\<close>
    by (auto simp: derivable_caps_def)
  have aligned': "nat sz' = 16 \<and> aligned paddr 16" if "tag"
    using aligned paddr that
    by auto
  obtain t' where "Run (CapIsRangeInBounds c vaddr (word_of_int sz)) t' True" and "trace_assms t'"
    using t
    by (auto elim!: Run_bindE simp: CheckCapability_def split: if_splits)
  from CapIsRangeInBounds_in_get_mem_region[OF this]
  have "addrs_in_mem_region c Store vaddr' paddr (nat sz')"
    using paddr sz sz'
    unfolding addrs_in_mem_region_def
    by (auto simp: unat_def uint_word_of_int subset_eq)
  thm store_enabled_def access_enabled_def
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
  ultimately have "authorises_access c Store tag ?is_local_cap vaddr' paddr (nat sz')"
    using tagged not_sealed
    by (auto simp: authorises_access_def)
  then show "access_enabled (run s t) Store vaddr' paddr (nat sz') ?bytes ?tagbit"
    using aligned' c
    by (cases tag) (auto simp: access_enabled_def)
qed

lemma VADeref_addr_l2p64[intro, simp, derivable_capsE]:
  assumes "Run (VADeref va sz perms acctype) t vaddr" "trace_assms t"
  shows "uint vaddr + sz \<le> 2^64"
  (* TODO: Add capability validness assumption to trace_assms, and prove
     that it is an invariant of the derivable caps *)
  sorry

lemma VADeref_addr_l2p64_nat[intro, simp, derivable_capsE]:
  assumes "Run (VADeref va sz perms acctype) t vaddr" "trace_assms t"
    and "0 \<le> sz"
  shows "unat vaddr + nat sz \<le> 2^64"
  using VADeref_addr_l2p64[OF assms(1,2)] assms(3)
  by (auto simp add: unat_def simp flip: nat_add_distrib)

text \<open>Loads enabled by VADeref\<close>

lemmas load_enabled_combinators[derivable_caps_combinators] =
  Run_bindE'[where P = "\<lambda>t. load_enabled (run s t) addr sz tagged" for s addr sz tagged, simplified]
  Run_ifE[where thesis = "load_enabled (run s t) addr sz tagged" and t = t for s addr sz tagged t]
  Run_letE[where thesis = "load_enabled (run s t) addr sz tagged" and t = t for s addr sz tagged t]
  Run_case_prodE[where thesis = "load_enabled (run s t) addr sz tagged" and t = t for s addr sz tagged t]

lemma Run_VAToCapability_iff:
  "Run (VAToCapability va) t c \<longleftrightarrow> VAIsCapability va \<and> c = VirtualAddress_base va \<and> t = []"
  unfolding VAToCapability_def
  by auto

lemma VADeref_load_enabled:
  assumes "Run (VADeref va sz perms acctype) t vaddr" "trace_assms t"
    and "sz > 0 \<and> sz' > 0"
    and "unat vaddr + nat sz \<le> 2^64 \<longrightarrow> unat vaddr \<le> vaddr' \<and> vaddr' + nat sz' \<le> unat vaddr + nat sz"
    and "perm_bits_included CAP_PERM_LOAD perms"
    and "tagged \<longrightarrow> perm_bits_included CAP_PERM_LOAD_CAP perms"
    and "tagged \<longrightarrow> nat sz' = 16 \<and> aligned vaddr' 16"
    and "\<not>VAIsSealedCap va \<longrightarrow> VA_derivable va s"
    and "{''PCC''} \<subseteq> accessible_regs s"
  shows "load_enabled (run s t) vaddr' sz' tagged"
proof (cases "VAIsPCCRelative va \<or> VAIsBits64 va")
  case True
  then show ?thesis
    using assms(1,2)
    unfolding VADeref_def
    by - (derivable_capsI assms: assms(3-) VADeref_addr_l2p64_nat[OF assms(1,2)]
                          elim: CheckCapability_load_enabled)
next
  case False
  let ?c = "VirtualAddress_base va"
  obtain t' t''
    where "Run (CheckCapability ?c (CapGetValue ?c) sz perms acctype) t'' vaddr"
      and "trace_assms t''"
      and "VirtualAddress_vatype va = VA_Capability"
      and "t = t' @ t''"
    using False assms(1,2)
    unfolding VADeref_def
    by (auto elim!: Run_bindE Run_ifE)
  then show ?thesis
    using assms(3-) VADeref_addr_l2p64_nat[OF assms(1,2)]
    unfolding \<open>t = t' @ t''\<close> foldl_append
    by (elim CheckCapability_load_enabled)
       (auto simp: VA_derivable_def VAIsSealedCap_def intro: derivable_caps_run_imp)
qed

text \<open>Common patterns\<close>

lemma VADeref_data_load_enabled[derivable_capsE]:
  assumes "Run (VADeref va sz CAP_PERM_LOAD acctype) t vaddr" "trace_assms t"
    and "sz > 0 \<and> sz' > 0"
    and "unat vaddr + nat sz \<le> 2^64 \<longrightarrow> unat vaddr \<le> vaddr' \<and> vaddr' + nat sz' \<le> unat vaddr + nat sz"
    and "\<not>VAIsSealedCap va \<longrightarrow> VA_derivable va s"
    and "{''PCC''} \<subseteq> accessible_regs s"
  shows "load_enabled (run s t) vaddr' sz' False"
  using assms
  by (elim VADeref_load_enabled) auto

lemma VADeref_data_load_enabled'[derivable_capsE]:
  assumes "Run (VADeref va sz (CAP_PERM_LOAD OR perms) acctype) t vaddr" "trace_assms t"
    and "sz > 0 \<and> sz' > 0"
    and "unat vaddr + nat sz \<le> 2^64 \<longrightarrow> unat vaddr \<le> vaddr' \<and> vaddr' + nat sz' \<le> unat vaddr + nat sz"
    and "\<not>VAIsSealedCap va \<longrightarrow> VA_derivable va s"
    and "{''PCC''} \<subseteq> accessible_regs s"
  shows "load_enabled (run s t) vaddr' sz' False"
  using assms
  by (elim VADeref_load_enabled) auto

lemma VADeref_cap_load_enabled[derivable_capsE]:
  assumes "Run (VADeref va sz (or_vec CAP_PERM_LOAD CAP_PERM_LOAD_CAP) acctype) t vaddr" "trace_assms t"
    and "sz > 0 \<and> sz' > 0"
    and "unat vaddr + nat sz \<le> 2^64 \<longrightarrow> unat vaddr \<le> vaddr' \<and> vaddr' + nat sz' \<le> unat vaddr + nat sz"
    and "nat sz' = 16 \<and> aligned vaddr' 16"
    and "\<not>VAIsSealedCap va \<longrightarrow> VA_derivable va s"
    and "{''PCC''} \<subseteq> accessible_regs s"
  shows "load_enabled (run s t) vaddr' sz' True"
  using assms
  by (elim VADeref_load_enabled) auto

lemma VADeref_cap_load_enabled'[derivable_capsE]:
  assumes "Run (VADeref va sz (or_vec CAP_PERM_LOAD CAP_PERM_LOAD_CAP OR perms) acctype) t vaddr" "trace_assms t"
    and "sz > 0 \<and> sz' > 0"
    and "unat vaddr + nat sz \<le> 2^64 \<longrightarrow> unat vaddr \<le> vaddr' \<and> vaddr' + nat sz' \<le> unat vaddr + nat sz"
    and "nat sz' = 16 \<and> aligned vaddr' 16"
    and "\<not>VAIsSealedCap va \<longrightarrow> VA_derivable va s"
    and "{''PCC''} \<subseteq> accessible_regs s"
  shows "load_enabled (run s t) vaddr' sz' True"
  using assms
  by (elim VADeref_load_enabled) auto

lemma VADeref_load_data_access_enabled'[derivable_capsE]:
  assumes "Run (VADeref va sz (CAP_PERM_LOAD OR perms) acctype) t vaddr" "trace_assms t"
    and "sz > 0 \<and> sz' > 0"
    and "translate_address (unat vaddr) = Some paddr"
    and "\<not>VAIsSealedCap va \<longrightarrow> VA_derivable va s"
    and "{''PCC''} \<subseteq> accessible_regs s"
  shows "\<exists>vaddr. access_enabled (run s t) Load vaddr paddr (nat sz) data B0"
  using assms
  by (auto intro: VADeref_data_load_enabled')

text \<open>Stores enabled by VADeref\<close>

lemmas store_enabled_combinators[derivable_caps_combinators] =
  Run_bindE'[where P = "\<lambda>t. store_enabled (run s t) addr sz data tag" for s addr sz data tag, simplified]
  Run_ifE[where thesis = "store_enabled (run s t) addr sz data tag" and t = t for s addr sz data tag t]
  Run_letE[where thesis = "store_enabled (run s t) addr sz data tag" and t = t for s addr sz data tag t]
  Run_case_prodE[where thesis = "store_enabled (run s t) addr sz data tag" and t = t for s addr sz data tag t]

lemma VADeref_store_enabled:
  assumes "Run (VADeref va sz perms acctype) t vaddr" "trace_assms t"
    and "sz > 0 \<and> sz' > 0"
    and "unat vaddr + nat sz \<le> 2^64 \<longrightarrow> unat vaddr \<le> vaddr' \<and> vaddr' + nat sz' \<le> unat vaddr + nat sz"
    and "perm_bits_included CAP_PERM_STORE perms"
    and "tag \<longrightarrow> perm_bits_included CAP_PERM_STORE_CAP perms"
    and "tag \<and> CapIsLocal (Capability_of_tag_word tag (ucast data)) \<longrightarrow> perm_bits_included CAP_PERM_STORE_LOCAL perms"
    and "tag \<longrightarrow> LENGTH('a) = 128 \<and> nat sz' = 16 \<and> aligned vaddr' 16"
    and "\<not>VAIsSealedCap va \<longrightarrow> VA_derivable va s"
    and "{''PCC''} \<subseteq> accessible_regs s"
  shows "store_enabled (run s t) vaddr' sz' (data :: 'a::len word) tag"
proof (cases "VAIsPCCRelative va \<or> VAIsBits64 va")
  case True
  then show ?thesis
    using assms(1,2)
    unfolding VADeref_def
    by - (derivable_capsI assms: assms(3-) VADeref_addr_l2p64_nat[OF assms(1,2)]
                          elim: CheckCapability_store_enabled)
next
  case False
  let ?c = "VirtualAddress_base va"
  obtain t' t''
    where "Run (CheckCapability ?c (CapGetValue ?c) sz perms acctype) t'' vaddr"
      and "trace_assms t''"
      and "VirtualAddress_vatype va = VA_Capability"
      and "t = t' @ t''"
    using False assms(1,2)
    unfolding VADeref_def
    by (auto elim!: Run_bindE Run_ifE)
  then show ?thesis
    using assms(3-) VADeref_addr_l2p64_nat[OF assms(1,2)]
    unfolding \<open>t = t' @ t''\<close> foldl_append
    by (elim CheckCapability_store_enabled)
       (auto simp: VA_derivable_def VAIsSealedCap_def intro: derivable_caps_run_imp)
qed

text \<open>Common patterns\<close>

lemma VADeref_store_data_enabled[derivable_capsE]:
  assumes "Run (VADeref va sz CAP_PERM_STORE acctype) t vaddr" "trace_assms t"
    and "sz > 0 \<and> sz' > 0"
    and "unat vaddr + nat sz \<le> 2^64 \<longrightarrow> unat vaddr \<le> vaddr' \<and> vaddr' + nat sz' \<le> unat vaddr + nat sz"
    and "\<not>VAIsSealedCap va \<longrightarrow> VA_derivable va s"
    and "{''PCC''} \<subseteq> accessible_regs s"
  shows "store_enabled (run s t) vaddr' sz' (data :: 'a::len word) False"
  using assms
  by (elim VADeref_store_enabled) auto

lemma VADeref_store_data_enabled'[derivable_capsE]:
  assumes "Run (VADeref va sz (perms OR CAP_PERM_STORE) acctype) t vaddr" "trace_assms t"
    and "sz > 0 \<and> sz' > 0"
    and "unat vaddr + nat sz \<le> 2^64 \<longrightarrow> unat vaddr \<le> vaddr' \<and> vaddr' + nat sz' \<le> unat vaddr + nat sz"
    and "\<not>VAIsSealedCap va \<longrightarrow> VA_derivable va s"
    and "{''PCC''} \<subseteq> accessible_regs s"
  shows "store_enabled (run s t) vaddr' sz' (data :: 'a::len word) False"
  using assms
  by (elim VADeref_store_enabled) auto

abbreviation cap_store_perms where
  "cap_store_perms c \<equiv>
     (if CapIsLocal c \<and> CapIsTagSet c then
        or_vec (or_vec CAP_PERM_STORE CAP_PERM_STORE_CAP) CAP_PERM_STORE_LOCAL
      else
        or_vec CAP_PERM_STORE CAP_PERM_STORE_CAP)"

lemma VADeref_store_cap_enabled[derivable_capsE]:
  assumes "Run (VADeref va CAPABILITY_DBYTES (cap_store_perms c) acctype) t vaddr" "trace_assms t"
    and "aligned (unat vaddr) 16"
    and "Capability_of_tag_word tag data = c"
    and "\<not>VAIsSealedCap va \<longrightarrow> VA_derivable va s"
    and "{''PCC''} \<subseteq> accessible_regs s"
  shows "store_enabled (run s t) (unat vaddr) 16 (data :: 128 word) tag"
  using assms
  by (elim VADeref_store_enabled) (auto split: if_splits)

lemma VADeref_store_cap_enabled'[derivable_capsE]:
  assumes "Run (VADeref va CAPABILITY_DBYTES (perms OR cap_store_perms c) acctype) t vaddr" "trace_assms t"
    and "aligned (unat vaddr) 16"
    and "Capability_of_tag_word tag data = c"
    and "\<not>VAIsSealedCap va \<longrightarrow> VA_derivable va s"
    and "{''PCC''} \<subseteq> accessible_regs s"
  shows "store_enabled (run s t) (unat vaddr) 16 (data :: 128 word) tag"
  using assms
  by (elim VADeref_store_enabled) (auto split: if_splits)

lemma VADeref_store_data_access_enabled[derivable_capsE]:
  assumes "Run (VADeref va sz CAP_PERM_STORE acctype) t vaddr" "trace_assms t"
    and "sz > 0"
    and "translate_address (unat vaddr) = Some paddr"
    and "\<not>VAIsSealedCap va \<longrightarrow> VA_derivable va s"
    and "{''PCC''} \<subseteq> accessible_regs s"
  shows "\<exists>vaddr. access_enabled (run s t) Store vaddr paddr (nat sz) (mem_bytes_of_word data) B0"
  using assms
  by (auto intro: VADeref_store_data_enabled)

lemma VADeref_store_data_access_enabled'[derivable_capsE]:
  assumes "Run (VADeref va sz (perms OR CAP_PERM_STORE) acctype) t vaddr" "trace_assms t"
    and "sz > 0"
    and "translate_address (unat vaddr) = Some paddr"
    and "\<not>VAIsSealedCap va \<longrightarrow> VA_derivable va s"
    and "{''PCC''} \<subseteq> accessible_regs s"
  shows "\<exists>vaddr. access_enabled (run s t) Store vaddr paddr (nat sz) (mem_bytes_of_word data) B0"
  using assms
  by (auto intro: VADeref_store_data_enabled')

lemma traces_enabled_bind_VADeref_Let[traces_enabled_combinatorI]:
  assumes "traces_enabled (VADeref va sz perms acctype \<bind> (\<lambda>addr. f addr y)) s"
  shows "traces_enabled (VADeref va sz perms acctype \<bind> (\<lambda>addr. let x = y in f addr x)) s"
  using assms
  by auto

text \<open>Work around a problem with a common pattern of VirtualAddress dereference
  in the ASL, where there are two calls to VADeref with the same address and size,
  but requesting different permissions.  This is used to get the priority of faults
  right for instructions that both load and store data.  The ASL assumes that the
  virtual address returned by the two calls is the same, and ignores the second.
  This does not hold for arbitrary traces, because the returned value depends on
  register reads, so we'll have to add an assumption on traces that consecutive
  reads from the same register (without writes in between) read the same values.\<close>

lemma traces_enabled_bind_VADeref_pair_ignore_second[traces_enabled_combinatorI]:
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
  sorry

text \<open>Some instructions have constrained UNPREDICTABLE behaviour that allows
  using UNKNOWN values for Capabilities and VirtualAddresses.  However, rules
  TRWTV and TSNJF in the Morello architecture document (DDI0606 A.c) say that
  these values must "not increase the Capability defined rights available to
  software".\<close>

lemma UNKNOWN_Capability_derivable[derivable_capsE]:
  assumes "Run (UNKNOWN_bits 129) t c" and "trace_assms t"
  shows "c \<in> derivable_caps s"
  (* TODO: Formulate suitable trace_assms.  Tweaking the Choose constructor of the prompt monad
     to allow arbitrary register_value's instead of just Booleans might make this easier. *)
  sorry

lemma UNKNOWN_VirtualAddress_derivable[derivable_capsE]:
  assumes "Run (UNKNOWN_VirtualAddress u) t va" and "trace_assms t"
  shows "VA_derivable va s"
  sorry

text \<open>AArch32 is unsupported on Morello\<close>

lemma UsingAArch32_False[simp]:
  assumes "trace_assms t"
  shows "\<not>Run (UsingAArch32 ()) t True"
  sorry

text \<open>Assume that tag setting is disabled\<close>

lemma IsTagSettingDisabled_not_False:
  assumes "trace_assms t"
  shows "Run (IsTagSettingDisabled ()) t False \<longleftrightarrow> False"
  sorry

end

end
