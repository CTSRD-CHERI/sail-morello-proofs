theory VM_No_Translation

imports CHERI_Instantiation
    "Sail-T-CHERI.No_Exception"
    "Sail-T-CHERI.Trace_Subset"

begin

text \<open>
Proofs that the translation system behaves nicely when
disabled. When system registers are set to
ensure S1 and S2 translation are disabled, the function
AArch64_FullTranslateWithTag produces simple predictable
results.
\<close>

text \<open>
Non-translation assumptions. The exception level is 0,
translation of el-0 is disabled by SCTLR_EL1, and this is
not overruled by HCR_EL2.E2H and HCR_EL2.TGE, whatever that
means. We also need the second stage translation to be
disabled by clearing both HCR_EL2.VM and HCR_EL2.DC.

FIXME: this just disallows HCR_EL2.E2H. To permit that
(in the absence of HCR_EL2.TGE), we'd need to ensure that
the two reads of HCR_EL2 in ELIsInHost read the same thing.
\<close>

fun(sequential)
  sctlr_no_translation :: "register_value event \<Rightarrow> bool"
where
    "sctlr_no_translation (E_read_reg nm rv) = (
        (nm = name PSTATE_ref \<longrightarrow> ProcState_EL (the (of_regval PSTATE_ref rv)) = EL0) \<and>
        (nm = name SCTLR_EL1_ref \<longrightarrow> \<not> lsb (the (of_regval SCTLR_EL1_ref rv))) \<and>
        (nm = name HCR_EL2_ref \<longrightarrow> (let reg = (the (of_regval HCR_EL2_ref rv))
            in \<not> (test_bit reg 34) \<and> \<not> (test_bit reg 12) \<and> \<not> (test_bit reg 0)))
    )"
  | "sctlr_no_translation ev = True"

text \<open>
Yet another Hoare logic, this one for the pure monad rather than
the state monad.
\<close>
definition
  hoare_pure :: "('regv event \<Rightarrow> bool) \<Rightarrow> bool \<Rightarrow> ('regv, 'a, 'e) monad \<Rightarrow>
    ('a \<Rightarrow> bool) \<Rightarrow> ('e \<Rightarrow> bool) \<Rightarrow> ('regv event \<Rightarrow> bool) \<Rightarrow> bool"
  where
  "hoare_pure T_P P m Q E T_Q = (\<forall> t r. (m, t, r) \<in> Traces \<and> (\<forall>ev \<in> set t. T_P ev) \<and> P \<longrightarrow>
    (case r of
        Done x \<Rightarrow> Q x
      | Exception e \<Rightarrow> E e
      | _ \<Rightarrow> True
    ) \<and>
    (\<forall>ev \<in> set t. T_Q ev))"

lemmas hoare_pureD = hoare_pure_def[THEN iffD1, rule_format, OF _ conjI]

lemma hoare_pure_RunD:
  "hoare_pure assms P m Q E T_Q \<Longrightarrow>
    Run m t x \<Longrightarrow>
    (\<forall>ev \<in> set t. assms ev) \<Longrightarrow>
    P \<Longrightarrow>
    Q x"
  by (fastforce simp add: hoare_pure_def)

lemma hoare_pure_bind:
  "(\<forall>x. hoare_pure assms (Q x) (g x) R E tr) \<Longrightarrow>
    hoare_pure assms P f Q E tr \<Longrightarrow>
    hoare_pure assms P (Sail2_prompt_monad.bind f (\<lambda>x. g x)) R E tr"
  apply (subst hoare_pure_def, clarsimp)
  apply (erule bind_Traces_cases)
   apply (drule(1) hoare_pureD, simp)
   apply (case_tac m''; clarsimp)
   apply (simp split: monad.split)
   apply (fastforce simp: ball_Un dest: hoare_pureD)
  apply (clarsimp simp: ball_Un)
  apply (auto dest!: hoare_pureD)
  done

lemma hoare_pure_meta:
  "hoare_pure assms P f Q E tr \<Longrightarrow>
    hoare_pure assms (P \<and> (\<forall>x. Q x \<longrightarrow> Q' x)) f Q' E tr"
  apply (subst hoare_pure_def, clarsimp)
  apply (drule(1) hoare_pureD, simp+)
  apply (auto split: monad.split)
  done

lemma hoare_pure_triv1:
  "hoare_pure assms True f (\<lambda>_. True) (\<lambda>_. True) (\<lambda>_. True)"
  by (simp add: hoare_pure_def split: monad.split)

lemmas hoare_pure_triv = hoare_pure_triv1[THEN hoare_pure_meta, simplified]

lemma hoare_pure_triv_no_exception1:
  "monad_no_exception S f \<Longrightarrow> monad_trace_subset S' f \<Longrightarrow>
    hoare_pure assms (S \<subseteq> {e. E e} \<and> S' \<subseteq> {ev. tr ev}) f (\<lambda>_. True) E tr"
  apply (clarsimp simp: hoare_pure_def)
  apply (drule(1) monad_no_exceptionD)
  apply (drule(1) monad_trace_subsetD)
  apply (auto split: monad.split)
  done

lemmas hoare_pure_triv_no_exception =
    hoare_pure_triv_no_exception1[THEN hoare_pure_meta, simplified]

lemma HaveEL_simp:
  "HaveEL el = return True"
  using EL_exhaust_disj[of el]
  by (clarsimp simp: HaveEL_def CFG_ID_AA64PFR0_EL1_EL2_def CFG_ID_AA64PFR0_EL1_EL3_def)

lemma hoare_pure_return:
  "hoare_pure assms (Q x) (return x) Q E tr"
  by (simp add: hoare_pure_def return_def)

lemma hoare_pure_weaken:
  "hoare_pure assms P f Q E tr \<Longrightarrow> (P' \<longrightarrow> P) \<Longrightarrow>
    hoare_pure assms P' f Q E tr"
  by (clarsimp simp add: hoare_pure_def)

lemma read_reg_hoare_pure1:
  "hoare_pure assms (\<forall>regv. tr (E_read_reg (name ref) regv))
    (read_reg ref)
    (\<lambda>x. \<exists>regv. assms (E_read_reg (name ref) regv) \<and>
        of_regval ref regv = Some x) E tr"
  apply (clarsimp simp: hoare_pure_def read_reg_def)
  apply (erule Traces.cases; auto elim!: T.cases split: option.split_asm)
  done

lemmas read_reg_hoare_pure = read_reg_hoare_pure1[THEN hoare_pure_meta]

lemma read_PSTATE_no_translation:
  "hoare_pure sctlr_no_translation
    ((\<forall>regv. tr (E_read_reg (name PSTATE_ref) regv)) \<and> (\<forall>ps. ProcState_EL ps = EL0 \<longrightarrow> Q ps))
    (read_reg PSTATE_ref) Q E tr"
  apply (rule hoare_pure_weaken, rule read_reg_hoare_pure)
  apply (clarsimp simp: PSTATE_ref_def SCTLR_EL1_ref_def)
  done

lemma read_SCTLR_no_translation:
  "hoare_pure sctlr_no_translation
    ((\<forall>regv. tr (E_read_reg (name SCTLR_EL1_ref) regv)) \<and> (\<forall>sreg. \<not> lsb sreg \<longrightarrow> Q sreg))
    (read_reg SCTLR_EL1_ref) Q E tr"
  apply (rule hoare_pure_weaken, rule read_reg_hoare_pure)
  apply (clarsimp simp: PSTATE_ref_def SCTLR_EL1_ref_def)
  done

lemma hoare_pure_If:
  "hoare_pure assms P f Q E tr \<Longrightarrow>
    hoare_pure assms P' g Q E tr \<Longrightarrow>
    hoare_pure assms (if x then P else P') (if x then f else g) Q E tr"
  by simp

lemma hoare_pure_Fail:
  "hoare_pure assms True (exit0 ()) Q E tr"
  "hoare_pure assms True (Fail str) Q E tr"
  by (simp add: exit0_def hoare_pure_def)+

lemma hoare_pure_assert_exp:
  "hoare_pure assms (P \<longrightarrow> Q ()) (assert_exp P str) Q E tr"
  apply (simp add: assert_exp_def hoare_pure_Fail)
  apply (simp add: hoare_pure_def)
  done

setup \<open>Monad_Trace_Subset_Exploration.install_recs
  ["Morello", "Morello_types"]
  @{thms undefined_bitvector_def undefined_int_def
    IsSecureBelowEL3_def[simplified HaveEL_simp bind_return if_simps]
    HasS2Translation_def UNKNOWN_bits_def undefined_FaultRecord_def
    UNKNOWN_integer_def ELUsingAArch32_def
}\<close>
setup \<open>Monad_No_Exception_Exploration.install_recs
  ["Morello", "Morello_types"]
  @{thms undefined_bitvector_def undefined_int_def
    IsSecureBelowEL3_def[simplified HaveEL_simp bind_return if_simps]
    HasS2Translation_def UNKNOWN_bits_def undefined_FaultRecord_def
    UNKNOWN_integer_def ELUsingAArch32_def
}\<close>

lemma range_subset_iff:
  "range f \<le> S \<longleftrightarrow> (\<forall>x. f x \<in> S)"
  by auto

abbreviation(input)
  "nmem_event \<equiv> (\<lambda>ev. \<not> (is_mem_event ev))"

lemma ELIsInHost_no_translation:
  "hoare_pure sctlr_no_translation True
    (ELIsInHost el) (\<lambda>rv. el = EL0 \<longrightarrow> rv = False) E nmem_event"
  apply (simp only: ELIsInHost_def)
  apply (simp only: and_boolM_def or_boolM_def)
  apply (rule hoare_pure_weaken)
   apply (rule hoare_pure_bind allI hoare_pure_If
        hoare_pure_return
        read_reg_hoare_pure
        hoare_pure_triv_no_exception[where f="ELUsingAArch32 _"]
        hoare_pure_triv_no_exception[where f="IsSecureBelowEL3 _"]
        monad_no_exception monad_trace_subset
  )+
  apply (clarsimp simp add: EL0_def EL2_def HCR_EL2_ref_def
        word_eq_iff[where 'a=1] nth_slice range_subset_iff)
  done

lemma S1TranslationRegime__1_no_translation:
  "hoare_pure sctlr_no_translation True
    (S1TranslationRegime__1 ()) (\<lambda>el. el = EL1) E nmem_event"
  apply (simp add: S1TranslationRegime__1_def S1TranslationRegime_def)
  apply (rule hoare_pure_weaken)
   apply (rule hoare_pure_If hoare_pure_bind allI hoare_pure_return
        ELIsInHost_no_translation[THEN hoare_pure_meta]
        read_PSTATE_no_translation
    | simp only: and_boolM_def)+
  apply clarsimp
  done

lemma SCTLR_read__1_no_translation:
  "hoare_pure sctlr_no_translation True
    (SCTLR_read__1 ()) (\<lambda>sreg. \<not> lsb sreg) E nmem_event"
  apply (simp add: SCTLR_read__1_def SCTLR_read_def)
  apply (rule hoare_pure_weaken)
   apply (rule hoare_pure_If hoare_pure_bind allI
        hoare_pure_return
        read_SCTLR_no_translation
        read_reg_hoare_pure
        hoare_pure_Fail hoare_pure_assert_exp
        hoare_pure_triv_no_exception[where f="undefined_bitvector _"]
        S1TranslationRegime__1_no_translation[THEN hoare_pure_meta]
        monad_no_exception monad_trace_subset
    | simp only: Unreachable_def
  )+
  apply clarsimp
  done

lemma AArch64_IsStageOneEnabled_no_translation:
  "hoare_pure sctlr_no_translation True
    (AArch64_IsStageOneEnabled acc_type)
    (\<lambda>x. \<not> x) E nmem_event"
  apply (simp add: AArch64_IsStageOneEnabled_def)
  apply (rule hoare_pure_weaken)
   apply (rule hoare_pure_bind allI hoare_pure_If
        hoare_pure_return read_SCTLR_no_translation
        SCTLR_read__1_no_translation[THEN hoare_pure_meta]
        read_reg_hoare_pure[where ref="HCR_EL2_ref"]
        hoare_pure_triv_no_exception[where f="HasS2Translation _"]
        hoare_pure_triv_no_exception[where f="undefined_bool _"]
        monad_no_exception monad_trace_subset
    | simp split del: if_split cong: if_cong
        add: and_boolM_def)+
  apply (clarsimp simp: word_lsb_alt word_eq_iff[where 'a=1] nth_ucast
                        range_subset_iff)
  done

lemma hoare_pure_pair_case:
  "(\<And>x y. hoare_pure assms (P x y) (f x y) Q E tr) \<Longrightarrow>
    hoare_pure assms (case t of (x, y) \<Rightarrow> P x y) (case t of (x, y) \<Rightarrow> f x y) Q E tr"
  by (cases t; simp)

lemma hoare_pure_fetch_asm:
  "(P \<Longrightarrow> hoare_pure assms P' f Q E tr) \<Longrightarrow>
    hoare_pure assms (P \<and> P') f Q E tr"
  by (clarsimp simp add: hoare_pure_def)

lemma hoare_pure_pre_cont:
  "hoare_pure assms False f Q E tr"
  by (clarsimp simp add: hoare_pure_def)

lemma AArch64_AddressSizeFault_no_translation:
  "hoare_pure sctlr_no_translation True
    (AArch64_AddressSizeFault addr lvl acctype iswrite snd_stage s2fs)
    (\<lambda>desc. FaultRecord_statuscode desc \<noteq> Fault_None) E nmem_event"
  apply (simp add: AArch64_AddressSizeFault_def AArch64_CreateFaultRecord_def)
  apply (rule hoare_pure_weaken)
   apply (rule hoare_pure_bind allI hoare_pure_If
        hoare_pure_return monad_trace_subset
    | (rule hoare_pure_triv_no_exception, rule monad_no_exception)
   )+
  apply (clarsimp simp: range_subset_iff)
  done

lemma AArch64_AlignmentFault_no_translation:
  "hoare_pure sctlr_no_translation True
    (AArch64_AlignmentFault acctype iswrite snd_stage)
    (\<lambda>desc. FaultRecord_statuscode desc \<noteq> Fault_None) E nmem_event"
  apply (simp add: AArch64_AlignmentFault_def AArch64_CreateFaultRecord_def)
  apply (rule hoare_pure_weaken)
   apply (rule hoare_pure_bind allI hoare_pure_If
        hoare_pure_return monad_trace_subset
    | (rule hoare_pure_triv_no_exception, rule monad_no_exception)
   )+
  apply (clarsimp simp: range_subset_iff)
  done

lemma AArch64_NoFault_no_translation:
  "hoare_pure sctlr_no_translation True
    (AArch64_NoFault uu)
    (\<lambda>desc. FaultRecord_statuscode desc = Fault_None) E nmem_event"
  apply (simp add: AArch64_NoFault_def AArch64_CreateFaultRecord_def)
  apply (rule hoare_pure_weaken)
   apply (rule hoare_pure_bind allI hoare_pure_If
        hoare_pure_return monad_trace_subset
    | (rule hoare_pure_triv_no_exception, rule monad_no_exception)
   )+
  apply (clarsimp simp: range_subset_iff)
  done

lemma PAMax_simp:
  "PAMax uu = return 48"
  by (simp add: PAMax_def IMPDEF_integer_def IMPDEF_integer_map_def)

setup \<open>Monad_Trace_Subset_Exploration.install_recs
  ["Morello", "Morello_types"]
  @{thms MemAttrDefaults_def IsSecure_def
    undefined_MemAttrHints_def AddrTop_def undefined_TLBRecord_def
    ELUsingAArch32_def undefined_AccessDescriptor_def
    AArch64_CheckPermission_def
}\<close>
setup \<open>Monad_No_Exception_Exploration.install_recs
  ["Morello", "Morello_types"]
  @{thms MemAttrDefaults_def IsSecure_def
    undefined_MemAttrHints_def AddrTop_def undefined_TLBRecord_def
    ELUsingAArch32_def undefined_AccessDescriptor_def
    AArch64_CheckPermission_def
}\<close>

lemma AArch64_TranslateAddressS1Off_no_translation:
  "hoare_pure sctlr_no_translation True
    (AArch64_TranslateAddressS1Off vaddress acctype iswrite)
    (\<lambda>rec. \<not> IsFault (TLBRecord_addrdesc rec) \<longrightarrow>
        FullAddress_address (AddressDescriptor_paddress (TLBRecord_addrdesc rec)) = (ucast vaddress))
    E nmem_event"
  apply (simp add: AArch64_TranslateAddressS1Off_def)
  apply (rule hoare_pure_weaken)
   apply (rule hoare_pure_bind allI hoare_pure_If
        hoare_pure_pair_case hoare_pure_return
    | simp add: IsFault_def split del: if_split
    | rule
        AArch64_AddressSizeFault_no_translation[THEN hoare_pure_meta]
        AArch64_NoFault_no_translation[THEN hoare_pure_meta]
        SCTLR_read__1_no_translation[THEN hoare_pure_meta]
        read_PSTATE_no_translation
        hoare_pure_assert_exp
        S1TranslationRegime__1_no_translation[THEN hoare_pure_meta]
        monad_trace_subset
    | simp only: Let_def simp_thms and_boolM_def if_simps PAMax_simp
    | (rule hoare_pure_triv_no_exception, rule monad_no_exception)
  )+
  apply (clarsimp simp: range_subset_iff)
  done

lemma hoare_pure_throw:
  "hoare_pure assms (E ex) (throw ex) P E tr"
  by (simp add: hoare_pure_def throw_def)

lemma hoare_pure_try_catch:
  "(\<forall>x. hoare_pure assms (Q x) (g x) R E tr) \<Longrightarrow>
    hoare_pure assms P f R Q tr \<Longrightarrow>
    hoare_pure assms P (try_catch f (\<lambda>x. g x)) R E tr"
  apply (subst hoare_pure_def, clarsimp)
  apply (erule try_catch_Traces_cases)
   apply (drule(1) hoare_pureD, simp+)
   apply (case_tac m', simp_all)[1]
   apply (fastforce dest: hoare_pureD)
  apply (clarsimp simp: ball_Un)
  apply (auto dest!: hoare_pureD)
  done

lemma hoare_pure_catch_early_return:
  "hoare_pure assms P f Q (case_sum Q E) tr \<Longrightarrow>
    hoare_pure assms P (catch_early_return f) Q E tr"
  apply (simp add: catch_early_return_def)
  apply (erule hoare_pure_try_catch[rotated])
  apply (clarsimp simp: hoare_pure_return hoare_pure_throw split: sum.split)
  done

lemma hoare_pure_liftR:
  "hoare_pure assms P f Q (E o Inr) tr \<Longrightarrow>
    hoare_pure assms P (liftR f) Q E tr"
  apply (simp add: liftR_def)
  apply (erule hoare_pure_try_catch[rotated])
  apply (clarsimp simp: hoare_pure_return hoare_pure_throw split: sum.split)
  done

lemma AArch64_CheckAndUpdateDescriptor_no_translation1:
  "hoare_pure sctlr_no_translation
    ((\<not> DescriptorUpdate_AF result \<and> \<not> DescriptorUpdate_AP result \<and> \<not> DescriptorUpdate_SC result) \<and> True)
    (AArch64_CheckAndUpdateDescriptor result fault snd_stage vaddress acctype is_w s2 hwup iswritevalidcap)
    (\<lambda>flt. FaultRecord_statuscode flt = Fault_None \<longrightarrow> FaultRecord_statuscode fault = Fault_None)
    E nmem_event"
  apply (rule hoare_pure_fetch_asm)
  apply (simp add: AArch64_CheckAndUpdateDescriptor_def split del: if_split)
  apply (rule hoare_pure_weaken)
   apply (rule hoare_pure_bind allI hoare_pure_If
        hoare_pure_return
        hoare_pure_catch_early_return hoare_pure_liftR
        hoare_pure_triv_no_exception[where f="undefined_bool _"]
        hoare_pure_triv_no_exception[where f="undefined_bitvector _"]
        hoare_pure_triv_no_exception[where f="undefined_AddressDescriptor _"]
        hoare_pure_triv_no_exception[where f="undefined_AccessDescriptor _"]
        monad_no_exception monad_trace_subset)+
  apply (clarsimp simp: range_subset_iff)
  done

lemma AArch64_CheckAndUpdateDescriptor_no_translation:
  "hoare_pure sctlr_no_translation
    True
    (AArch64_CheckAndUpdateDescriptor result fault snd_stage vaddress acctype is_w s2 hwup iswritevalidcap)
    (\<lambda>flt. FaultRecord_statuscode flt = Fault_None \<longrightarrow> FaultRecord_statuscode fault = Fault_None)
    E nmem_event"
  (* cheated at this point. there is a semantic disagreement issue
     about whether the AF/AP/SC update flags really get initialised
     or not, so we cheat to hide those assumptions from the previous.
  *)
  sorry

lemma AArch64_InstructionDevice_no_translation:
  "hoare_pure sctlr_no_translation True
    (AArch64_InstructionDevice addrdesc vaddress ipaddress level acctype iswrite snd_stage s2fs)
    (\<lambda> desc. (\<not> IsFault desc \<longrightarrow> \<not> IsFault addrdesc) \<and>
        AddressDescriptor_paddress desc = AddressDescriptor_paddress addrdesc)
    E nmem_event"
  apply (simp add: AArch64_InstructionDevice_def)
  apply (rule hoare_pure_weaken)
   apply (rule hoare_pure_bind allI hoare_pure_return monad_trace_subset
    | (rule hoare_pure_triv_no_exception, rule monad_no_exception)
  )+
  apply (simp add: IsFault_def range_subset_iff)
  done

lemma AArch64_FirstStageTranslateWithTag_no_translation:
  "hoare_pure sctlr_no_translation True
    (AArch64_FirstStageTranslateWithTag vaddress acctype iswrite wasaligned sz isw_v_cap)
    (\<lambda> desc. \<not> IsFault desc \<longrightarrow>
        FullAddress_address (AddressDescriptor_paddress desc) = (ucast vaddress))
    E nmem_event"
  apply (simp add: AArch64_FirstStageTranslateWithTag_def)
  apply (rule hoare_pure_weaken)
   apply (rule hoare_pure_bind allI hoare_pure_If
        hoare_pure_pair_case hoare_pure_return
        AArch64_CheckAndUpdateDescriptor_no_translation[THEN hoare_pure_meta]
        AArch64_InstructionDevice_no_translation[THEN hoare_pure_meta]
        hoare_pure_triv_no_exception[where f="AArch64_CheckPermission _ _ _ _ _ _"]
        AArch64_AlignmentFault_no_translation[THEN hoare_pure_meta]
        monad_no_exception monad_trace_subset
        hoare_pure_pre_cont[where f="AArch64_TranslationTableWalk _ _ _ _ _ _ _"]
        AArch64_TranslateAddressS1Off_no_translation[THEN hoare_pure_meta]
        hoare_pure_triv_no_exception[where f="UNKNOWN_bits _"]
        AArch64_IsStageOneEnabled_no_translation[THEN hoare_pure_meta]
        hoare_pure_triv_no_exception[where f="undefined_bool _"]
        hoare_pure_triv_no_exception[where f="undefined_TLBRecord _"]
    | simp add: IsFault_def split del: if_split
  )+
  apply (clarsimp simp: IsFault_def range_subset_iff)
  done

lemma AArch64_SecondStageTranslate_no_translation:
  "hoare_pure sctlr_no_translation True
    (AArch64_SecondStageTranslate S1 vaddress acctype iswrite wasaligned s2fs sz hwup isw_v_cap)
    (\<lambda> desc. desc = S1)
    E nmem_event"
  apply (simp add: AArch64_SecondStageTranslate_def)
  apply (rule hoare_pure_weaken)
   apply (rule hoare_pure_bind allI hoare_pure_If
        hoare_pure_return hoare_pure_assert_exp
        read_reg_hoare_pure
        hoare_pure_triv_no_exception[where f="HasS2Translation _"]
        monad_no_exception monad_trace_subset
        AArch64_InstructionDevice_no_translation[THEN hoare_pure_meta]
        AArch64_AlignmentFault_no_translation[THEN hoare_pure_meta]
        hoare_pure_pre_cont[where f="AArch64_CheckS2Permission _ _ _ _ _ _ _ _"]
        hoare_pure_pre_cont[where f="AArch64_PermissionFault _ _ _ _ _ _"]
        hoare_pure_pre_cont[where f="AArch64_CombineS1S2Desc _ _"]
        hoare_pure_pre_cont[where f="AArch64_TranslationTableWalk_mutrec_vvvvTvv _ _ _ _ _ _"]
        hoare_pure_pre_cont[where f="AArch64_CheckAndUpdateDescriptor_mutrec_vvTvvvvvv _ _ _ _ _ _ _ _"]
    | simp only: and_boolM_def or_boolM_def Let_def simp_thms if_simps
    | (rule hoare_pure_triv_no_exception, rule monad_no_exception)
  )+
  apply (clarsimp simp: range_subset_iff)
  apply (clarsimp simp add: Let_def HCR_EL2_ref_def
        word_eq_iff[where 'a=1] nth_slice nth_ucast)
  done

lemma AArch64_FullTranslateWithTag_no_translation:
  "hoare_pure sctlr_no_translation True
    (AArch64_FullTranslateWithTag vaddress acctype iswrite wasaligned sz isw_v_cap)
    (\<lambda> desc. \<not> IsFault desc \<longrightarrow>
        FullAddress_address (AddressDescriptor_paddress desc) = (ucast vaddress))
    E nmem_event"
  apply (simp add: AArch64_FullTranslateWithTag_def)
  apply (rule hoare_pure_weaken)
   apply (rule hoare_pure_bind allI hoare_pure_If
        hoare_pure_return
        AArch64_FirstStageTranslateWithTag_no_translation[THEN hoare_pure_meta]
        AArch64_SecondStageTranslate_no_translation[THEN hoare_pure_meta]
        hoare_pure_triv_no_exception[where f="HasS2Translation _"]
        monad_no_exception monad_trace_subset
    | simp only: and_boolM_def
    | (rule hoare_pure_triv_no_exception, rule monad_no_exception)
  )+
  apply (clarsimp simp: range_subset_iff)
  done

lemma translate_correct:
  "Run (AArch64_FullTranslateWithTag vaddress acctype iswrite algnd sz is_wvc) t addrdesc \<Longrightarrow>
    \<not>IsFault addrdesc \<Longrightarrow>
    \<forall>e \<in> set t. sctlr_no_translation e \<Longrightarrow>
    translate_address (unat vaddress) =
    Some (unat (FullAddress_address (AddressDescriptor_paddress addrdesc)))"
  apply (drule AArch64_FullTranslateWithTag_no_translation[THEN hoare_pure_RunD], simp_all)
  apply (simp add: CHERI_Instantiation.translate_address_def unat_and_mask)
  done

lemma mod_div_cong:
  "(x :: ('a :: semiring_modulo)) mod d = y mod d \<Longrightarrow> x div d = y div d \<Longrightarrow> x = y"
  by (metis mod_mult_div_eq)

interpretation fixed_no_translate:
  Morello_Fixed_Address_Translation
  where translate_address = CHERI_Instantiation.translate_address
    and is_translation_event = "\<lambda>_. False"
    and translation_assms = "sctlr_no_translation"
    and s1_enabled = "\<lambda>_. False"
  apply unfold_locales
defer (* what is tbi_enabled ? *)
  apply (simp add: translate_correct)
apply (drule AArch64_FullTranslateWithTag_no_translation[THEN hoare_pureD], simp_all)[1]
  apply simp
defer (* what is translation_el ? *)
  apply (drule AArch64_IsStageOneEnabled_no_translation[THEN hoare_pure_RunD], simp_all)[1]
defer (* more tbi_enabled *)
defer (* in_host *)
apply (subst Morello_Bounds_Address_Calculation.valid_address_def)
defer (* more tbi_enabled *)
apply (simp add: CHERI_Instantiation.translate_address_def)
(* I don't think this is true ... translation doesn't fail just because
   you're out of bounds, does it? *)
defer
apply (subst Morello_Bounds_Address_Calculation.bounds_address_def)
defer (* more tbi_enabled *)
apply (simp add: CHERI_Instantiation.translate_address_def mod_mod_cancel)
apply (simp add: CHERI_Instantiation.translate_address_def)
apply clarsimp
apply (rule mod_div_cong[where d="2 ^ 12"]; simp)
apply (simp add: mod_mod_cancel)
apply (simp add: div_exp_mod_exp_eq[where n=12 and m=36, simplified, symmetric])
(* that's all we can do without figuring out tbi_enabled *)
oops

end