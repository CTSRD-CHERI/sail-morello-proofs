theory VM_Inst
  imports
    "CHERI_Instantiation"
begin

ML \<open>
val let_atom_simproc = Simplifier.make_simproc @{context} "let_atom"
  {lhss = [@{term "Let f x"}], proc = fn _ => fn _ => fn ct => let
    val t = Thm.term_of ct
    val (_, xs) = strip_comb t
    fun is_atom t = is_Bound t orelse is_Const t orelse is_Var t orelse is_Free t
  in
    if length xs = 2 andalso is_atom (hd xs)
    then SOME (@{thm Let_def})
    else NONE
  end}

fun let_atom_tac ctxt = simp_tac (put_simpset HOL_basic_ss ctxt addsimprocs [let_atom_simproc])
\<close>

method_setup let_atom = \<open>Scan.succeed (fn ctxt => Method.SIMPLE_METHOD (CHANGED (let_atom_tac ctxt 1)))\<close>

fun(sequential)
  read_const_regs :: "(string set \<times> (string \<Rightarrow> register_value option)) \<Rightarrow> register_value event \<Rightarrow> bool"
where
    "read_const_regs cfg (E_read_reg nm rv) = (if nm \<in> fst cfg 
        then (snd cfg nm = Some rv) else True)"
  | "read_const_regs el ev = True"

definition
  "const_regs_translate cfg = read_const_regs
    ({''PSTATE'', ''SCR_EL3'', ''HCR_EL2'', ''TCR_EL1'', ''TCR_EL2'', ''TCR_EL3'',
        ''SCTLR_EL1'', ''SCTLR_EL2'', ''SCTLR_EL3'', ''TTBR0_EL3''
}, cfg)"

definition
  "translate_address_concrete cfg vaddr =
    (if vaddr < 2 ^ 64
    then let res = monad_result_of (const_regs_translate cfg)
        (AArch64_FullTranslateWithTag (of_nat vaddr) AccType_NORMAL False True 1 False)
     in (if IsFault res then None else Some (unat (AddressDescriptor_vaddress res)))
    else None)"

abbreviation(input)
  "no_exception m \<equiv> (\<forall>tr e. (m, tr, Exception e) \<notin> Traces)"

named_theorems no_exception

declare undefined_bitvector_exception[no_exception]

named_theorems monad_return_rel

named_theorems monad_return_rel_unfold

datatype two = Two_A | Two_B

definition
  eq_merge_rel :: "((two list \<Rightarrow> 'a) \<Rightarrow> (two list \<Rightarrow> 'a) \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
where
  "eq_merge_rel f x y = (\<exists>known unknown_l unknown_r. x = f known unknown_l \<and> y = f known unknown_r)"

lemmas eq_merge_relD = eq_merge_rel_def[THEN iffD1]
lemmas eq_merge_relI = eq_merge_rel_def[THEN iffD2, OF exI, OF exI, OF exI]

lemma monad_return_rel_unknown:
  "no_exception f \<Longrightarrow> monad_return_rel assms f f (eq_merge_rel (\<lambda>k u. u [])) E"
  apply (rule monad_return_rel_rel_weaken[where E=E], rule monad_return_rel_triv, simp_all)
  apply (auto simp add: eq_merge_rel_def)
  done

lemma undefined_bool_exception[no_exception]:
  "no_exception (undefined_bool s)"
  by (clarsimp simp: undefined_bool_def choose_bool_def dest!: Choose_exception)

lemmas monad_return_rel_undefined_bool[monad_return_rel] =
    monad_return_rel_unknown[where f="undefined_bool _",
        simplified undefined_bool_exception, simplified]

lemma undefined_int_exception[no_exception]:
  "no_exception (undefined_int s)"
  by (auto simp: undefined_int_def Let_def no_exception
          dest!: bind_Traces_final_cases)

lemmas monad_return_rel_undefined_int[monad_return_rel] =
    monad_return_rel_unknown[where f="undefined_int _",
        simplified undefined_int_exception, simplified]

lemma genlistM_exception:
  "(\<And>i. i < n \<Longrightarrow> no_exception (f i)) \<Longrightarrow> no_exception (genlistM f n)"
  apply (clarsimp simp add: genlistM_def genlist_def)
  apply (subst(asm) foreachM_no_exception, simp_all)
  apply (auto dest!: bind_Traces_final_cases)
  done

lemma choose_bool_exception[no_exception]:
  "no_exception (choose_bool s)"
  by (auto simp: choose_bool_def dest!: Choose_exception)

lemma choose_bools_exception[no_exception]:
  "no_exception (choose_bools s n)"
  by (auto simp: choose_bools_def simp: no_exception intro!: genlistM_exception)

lemma internal_pick_exception[no_exception]:
  "no_exception (internal_pick xs)"
  by (auto simp: internal_pick_def chooseM_def no_exception
    dest!: bind_Traces_final_cases
    split: option.split_asm)

lemma undefined_AccType_exception[no_exception]:
  "no_exception (undefined_AccType s)"
  by (auto simp: undefined_AccType_def no_exception)

lemma undefined_Fault_exception[no_exception]:
  "no_exception (undefined_Fault s)"
  by (auto simp: undefined_Fault_def no_exception)

lemma undefined_FaultRecord_exception[no_exception]:
  "no_exception (undefined_FaultRecord s)"
  by (auto simp: undefined_FaultRecord_def no_exception
          dest!: bind_Traces_final_cases)

lemmas monad_return_rel_undefined_FaultRecord[monad_return_rel] =
    monad_return_rel_unknown[where f="undefined_FaultRecord s", simplified no_exception, simplified]

lemma bind_no_exception_right:
  "no_exception f \<Longrightarrow> ((bind f g, tr, Exception e) \<in> Traces) =
    (\<exists>tra trb x. tr = tra @ trb \<and> Run f tra x \<and> (g x, trb, Exception e) \<in> Traces)"
  by (auto elim: Traces_bindI dest!: bind_Traces_final_cases)

lemmas def_to_exception = ssubst[where P="no_exception"]

lemmas undefined_MemType_exception[no_exception] =
    undefined_MemType_def[THEN def_to_exception, simplified no_exception, simplified]

lemmas undefined_DeviceType_exception[no_exception] =
    undefined_DeviceType_def[THEN def_to_exception, simplified no_exception, simplified]

lemmas undefined_MemAttrHints_exception[no_exception] =
    undefined_MemAttrHints_def[THEN def_to_exception, simplified no_exception bind_no_exception_right simp_thms, simplified]

lemmas monad_return_rel_undefined_MemAttrHints[monad_return_rel] =
    undefined_MemAttrHints_exception[THEN monad_return_rel_unknown]

lemmas undefined_FullAddress_exception[no_exception] =
    undefined_FullAddress_def[THEN def_to_exception, simplified no_exception bind_no_exception_right simp_thms, simplified]

lemmas undefined_MemoryAttributes_exception[no_exception] =
    undefined_MemoryAttributes_def[THEN def_to_exception, simplified no_exception bind_no_exception_right simp_thms, simplified]

lemmas monad_return_rel_undefined_MemoryAttributes[monad_return_rel] =
    undefined_MemoryAttributes_exception[THEN monad_return_rel_unknown]

lemmas undefined_MPAMinfo_exception[no_exception] =
    undefined_MPAMinfo_def[THEN def_to_exception, simplified no_exception bind_no_exception_right simp_thms, simplified]

lemmas undefined_AccessDescriptor_exception[no_exception] =
    undefined_AccessDescriptor_def[THEN def_to_exception, simplified no_exception bind_no_exception_right simp_thms, simplified]

lemmas monad_return_rel_undefined_AccessDescriptor[monad_return_rel] =
    undefined_AccessDescriptor_exception[THEN monad_return_rel_unknown]

lemmas undefined_AddressDescriptor_exception[no_exception] =
    undefined_AddressDescriptor_def[THEN def_to_exception, simplified no_exception bind_no_exception_right simp_thms, simplified]

lemmas monad_return_rel_undefined_AddressDescriptor[monad_return_rel] =
    undefined_AddressDescriptor_exception[THEN monad_return_rel_unknown]

lemmas undefined_Permissions_exception[no_exception] =
    undefined_Permissions_def[THEN def_to_exception, simplified no_exception bind_no_exception_right simp_thms, simplified]

lemmas undefined_DescriptorUpdate_exception[no_exception] =
    undefined_DescriptorUpdate_def[THEN def_to_exception, simplified no_exception bind_no_exception_right simp_thms, simplified]

lemmas undefined_TLBRecord_exception[no_exception] =
    undefined_TLBRecord_def[THEN def_to_exception, simplified no_exception bind_no_exception_right simp_thms, simplified]

lemmas monad_return_rel_undefined_TLBRecord[monad_return_rel] =
    undefined_TLBRecord_exception[THEN monad_return_rel_unknown]

lemmas undefined_Constraint_exception[no_exception] =
    undefined_Constraint_def[THEN def_to_exception, simplified no_exception bind_no_exception_right simp_thms, simplified]

lemmas monad_return_rel_undefined_Constraint[monad_return_rel] =
    undefined_Constraint_exception[THEN monad_return_rel_unknown]

(*
template for the above

lemmas _exception[no_exception] =
    _def[THEN def_to_exception, simplified no_exception bind_no_exception_right simp_thms, simplified]

lemmas monad_return_rel_ [monad_return_rel] =
    _exception[THEN monad_return_rel_unknown]
*)

lemma read_reg_exception[no_exception, simp]:
  "no_exception (read_reg r)"
  apply (auto simp: read_reg_def)
  apply (erule Traces.cases; auto elim!: T.cases split: option.split_asm)
  done

lemma read_reg_monad_return_rel:
  "name r \<in> fst cfg \<Longrightarrow> monad_determ (read_const_regs cfg) (read_reg r)"
  by (auto simp add: monad_return_rel_def elim!: Run_read_regE split: monad.split)

lemma monad_return_rel_throw:
  "E x y \<Longrightarrow> monad_return_rel assms (throw x) (throw y) R E"
  by (simp add: monad_return_rel_def)

definition
  rel_min :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
where
  "rel_min P Q x y = (P x y \<or> Q x y)"

lemma rel_min_simp[simp]:
  "rel_min P P = P"
  "rel_min P (rel_min P Q) = rel_min P Q"
  "rel_min P (rel_min Q R) = rel_min Q (rel_min P R)"
  "rel_min P (\<lambda>_ _. False) = P"
  "rel_min (\<lambda>_ _. False) P = P"
  by (auto simp add: fun_eq_iff rel_min_def)

lemma monad_return_rel_if_P:
  "G = G' \<Longrightarrow> (G \<Longrightarrow> monad_return_rel assms f f' P1 E)
    \<Longrightarrow> (\<not> G \<Longrightarrow> monad_return_rel assms g g' P2 E)
    \<Longrightarrow> monad_return_rel assms (If G f g) (If G' f' g') (If G' P1 P2) E"
  by simp

lemma monad_return_rel_if_rel_min[monad_return_rel]:
  "G = G' \<Longrightarrow> (G \<Longrightarrow> monad_return_rel assms f f' P1 E)
    \<Longrightarrow> (\<not> G \<Longrightarrow> monad_return_rel assms g g' P2 E)
    \<Longrightarrow> monad_return_rel assms (If G f g) (If G' f' g') (rel_min P1 P2) E"
  by (auto simp: rel_min_def elim!: monad_return_rel_rel_weaken)

lemma monad_return_rel_and_boolM[monad_return_rel]:
  "monad_return_rel assms x x' P E \<Longrightarrow>
    (\<And>sw sw'. Abbrev and_boolM x x = and_boolM x x \<Longrightarrow> P sw sw' \<longrightarrow> sw = sw') \<Longrightarrow>
    monad_return_rel assms y y' Q E \<Longrightarrow>
    monad_return_rel assms (and_boolM x y) (and_boolM x' y') (rel_min Q (=)) E"
  apply (simp add: and_boolM_def Abbrev_def)
  apply (erule monad_return_rel_bind)
  apply (auto simp: rel_min_def intro: monad_return_rel_return elim: monad_return_rel_rel_weaken)
  done

lemma monad_return_rel_or_boolM[monad_return_rel]:
  "monad_return_rel assms x x' P E \<Longrightarrow>
    (\<And>sw sw'. Abbrev or_boolM x x = or_boolM x x \<Longrightarrow> P sw sw' \<longrightarrow> sw = sw') \<Longrightarrow>
    monad_return_rel assms y y' Q E \<Longrightarrow>
    monad_return_rel assms (or_boolM x y) (or_boolM x' y') (rel_min Q (=)) E"
  apply (simp add: or_boolM_def Abbrev_def)
  apply (erule monad_return_rel_bind)
  apply (auto simp: rel_min_def intro: monad_return_rel_return elim: monad_return_rel_rel_weaken)
  done

lemma try_catch_Traces_final_cases:
  "(try_catch f (\<lambda>x. g x), t, r) \<in> Traces \<Longrightarrow>
    (case r of Done _ \<Rightarrow> False | Exception _ \<Rightarrow> False | _ \<Rightarrow> True) \<or>
    (\<exists>e ta tb. t = ta @ tb \<and> (f, ta, Exception e) \<in> Traces \<and> (
        (\<exists>y. r = Done y \<and> Run (g e) tb y) \<or>
        (\<exists>e'. r = Exception e' \<and> (g e, tb, Exception e') \<in> Traces))) \<or>
    (\<exists>x. r = Done x \<and> Run f t x)"
  apply (erule try_catch_Traces_cases)
   apply (case_tac m', simp_all)[1]
   apply (simp split: monad.split)
   apply (fastforce intro: exI[where x=Nil])
  apply (simp split: monad.split)
  apply auto[1]
  done

lemma monad_return_rel_try_catch:
  "monad_return_rel assms f f' P C \<Longrightarrow> (\<And>x x'. C x x' \<Longrightarrow> monad_return_rel assms (g x) (g' x') P E)
    \<Longrightarrow> monad_return_rel assms (try_catch f g) (try_catch f' (\<lambda>x'. g' x')) P E"
  apply (subst monad_return_rel_def, clarsimp)
  apply (simp split: monad.split)
  apply (erule try_catch_Traces_final_cases[THEN disjE], fastforce)
  apply (erule try_catch_Traces_final_cases[THEN disjE], fastforce)
  apply (elim disjE; clarsimp; drule(2) monad_return_relD; clarsimp?)
  apply (elim meta_allE, drule(1) meta_mp)
  apply (clarsimp simp: ball_Un)
  apply (auto dest: monad_return_relD)
  done

lemma monad_return_rel_liftR:
  "monad_return_rel assms f g P E
    \<Longrightarrow> monad_return_rel assms (liftR f) (liftR g) P (rel_sum C E)"
  apply (simp add: liftR_def)
  apply (erule monad_return_rel_try_catch)
  apply (rule monad_return_rel_throw)
  apply simp
  done

lemma monad_return_rel_catch_early_return:
  "monad_return_rel assms f g P (rel_sum P E)
    \<Longrightarrow> monad_return_rel assms (catch_early_return f) (catch_early_return g) P E"
  apply (simp add: catch_early_return_def)
  apply (erule monad_return_rel_try_catch)
  apply (erule rel_sum.cases, simp_all)
   apply (rule monad_return_rel_return, simp)
  apply (rule monad_return_rel_throw, simp)
  done

lemma monad_return_rel_return_same:
  "monad_return_rel assms (return x) (return x) (\<lambda>a b. a = b \<and> Abbrev (a = x)) E"
  apply (rule monad_return_rel_return)
  apply (simp add: Abbrev_def)
  done

lemma monad_return_rel_return_same_weak:
  "monad_return_rel assms (return x) (return x) (=) E"
  by (rule monad_return_rel_return, simp)

lemma monad_return_rel_weaken_P:
  "monad_return_rel assms f g P E \<Longrightarrow> (\<And>x y. P x y \<longrightarrow> P' x y) \<Longrightarrow>
    monad_return_rel assms f g P' E"
  by (erule monad_return_rel_rel_weaken, simp_all)

lemma rel_min_imp:
  "P x y \<longrightarrow> R \<Longrightarrow> Q x y \<longrightarrow> R \<Longrightarrow> rel_min P Q x y \<longrightarrow> R"
  by (simp add: rel_min_def)

lemmas monad_return_rel_impossible =
    FalseE[where P="monad_return_rel assms f g (\<lambda>x y. False) E" for assms f g E]

lemmas init_monad_return_rel[monad_return_rel] =
    monad_return_rel_assert_exp_P
    monad_return_rel_if_rel_min
    monad_return_rel_and_boolM
    monad_return_rel_or_boolM
    monad_return_rel_catch_early_return
    monad_return_rel_return_same_weak
    monad_return_rel_undefined_bitvector

declare bind_assoc[monad_return_rel_unfold]

lemmas monad_return_rel_comb = rel_min_imp conjI impI refl
        monad_return_rel_bind monad_return_rel_liftR

method read_reg_monad_return_rel =
    ((simp(no_asm) only: const_regs_translate_def)?,
        rule read_reg_monad_return_rel,
        (solves \<open>simp add: register_defs\<close>)?)

method monad_return_rel_step = (determ \<open>intro monad_return_rel monad_return_rel_comb
    | rule monad_return_rel
    | (rule monad_return_rel_impossible, solves \<open>simp only: monad_return_rel_unfold rel_min_simp
            | let_atom\<close>)
    | simp only: monad_return_rel_unfold rel_min_simp
    | let_atom
    | (rule monad_return_rel_weaken_P, rule monad_return_rel)
    | read_reg_monad_return_rel\<close>
    | (rule monad_return_rel_impossible, solves \<open>clarsimp; simp\<close>))

method monad_return_rel = monad_return_rel_step+

lemma AArch64_AccessUsesEL_monad_return_rel[monad_return_rel]:
  "monad_determ (const_regs_translate cfg) (AArch64_AccessUsesEL acctype)"
  apply (simp add: AArch64_AccessUsesEL_def split del: if_split)
  apply monad_return_rel
  done

lemma HaveEL_monad_return_rel[monad_return_rel]:
  "monad_determ assms (HaveEL el)"
  apply (simp add: HaveEL_def)
  apply monad_return_rel
  done

lemma IMPDEF_boolean_monad_return_rel[monad_return_rel]:
  "monad_determ assms (IMPDEF_boolean nm)"
  unfolding IMPDEF_boolean_def IMPDEF_boolean_map_def
  by (intro monad_return_rel_if refl monad_return_rel_return monad_return_rel_throw TrueI)

lemma IsSecureBelowEL3_monad_return_rel[monad_return_rel]:
  "monad_determ (const_regs_translate cfg) (IsSecureBelowEL3 x)"
  apply (simp add: IsSecureBelowEL3_def SCR_GEN_read_def const_regs_translate_def
             cong: if_cong)
  apply monad_return_rel
  done

lemma HighestEL_monad_return_rel[monad_return_rel]:
  "monad_determ assms (HighestEL ())"
  apply (simp add: HighestEL_def)
  apply monad_return_rel
  done

lemma HaveAArch32EL_monad_return_rel[monad_return_rel]:
  "monad_determ assms (HaveAArch32EL el)"
  using EL_exhaust_disj[of el] monad_return_rel_if_P[monad_return_rel]
  apply (simp add: HaveAArch32EL_def)
  apply (rule
        monad_return_rel_if_rel_min[where ?P1.0="(=)" and ?P2.0="(=)", simplified]
    | monad_return_rel_step
  )+
  apply simp
  done

lemma ELStateUsingAArch32K_monad_return_rel[monad_return_rel]:
  "monad_return_rel (const_regs_translate cfg)
    (ELStateUsingAArch32K el x) (ELStateUsingAArch32K el x)
    (\<lambda>(known, x) (known', y). known = known' \<and> (known \<longrightarrow> x = y)) (=)"
  (is "monad_return_rel _ _ _ ?R _")
  apply (simp add: ELStateUsingAArch32K_def)
  apply (
    clarsimp simp: UNKNOWN_boolean_def
    | rule monad_return_rel_return[where P="?R"]
    | monad_return_rel_step
  )+
  sorry

lemma ELStateUsingAArch32_monad_return_rel[monad_return_rel]:
  "monad_determ (const_regs_translate cfg) (ELStateUsingAArch32 el x)"
  apply (simp add: ELStateUsingAArch32_def)
  apply (monad_return_rel | clarsimp)+
  done

lemma monad_return_rel_assms_weaken:
  "monad_return_rel assms' x y R E \<Longrightarrow> (\<forall>ev. assms ev \<longrightarrow> assms' ev) \<Longrightarrow>
    monad_return_rel assms x y R E"
  apply (subst monad_return_rel_def, clarsimp)
  apply (drule(2) monad_return_relD, simp_all)
  done

declare ELUsingAArch32_def[monad_return_rel_unfold]

lemma S1TranslationRegime_monad_return_rel[monad_return_rel]:
  "monad_return_rel (const_regs_translate cfg)
    (S1TranslationRegime x) (S1TranslationRegime x)
    (\<lambda>rg rg'. rg = rg' \<and> rg \<in> {EL1, EL2, EL3}) (=)"
  (is "monad_return_rel _ _ _ ?R _")
  using EL_exhaust_disj[of x]
  apply (simp add: S1TranslationRegime_def HaveVirtHostExt_def HasArchVersion_def ELIsInHost_def
                   monad_return_rel_return
        split del: if_split cong: if_cong)
  apply (rule monad_return_rel_return[where P="?R"]
    | monad_return_rel_step
    | clarsimp)+
  done

lemma unat_ELs:
  "map unat [EL0, EL1, EL2, EL3] = [0, 1, 2, 3]"
  by (simp add: EL0_def EL1_def EL2_def EL3_def)

lemma ELIsInHost_monad_return_rel[monad_return_rel]:
  "monad_determ (const_regs_translate cfg) (ELIsInHost el)"
  apply (simp add: ELIsInHost_def)
  apply monad_return_rel
  done

lemma AddrTop_monad_return_rel[monad_return_rel]:
  "monad_determ (const_regs_translate cfg) (AddrTop vaddr el)"
  using unat_ELs
  apply (clarsimp simp add: AddrTop_def split del: if_split)
  apply (monad_return_rel_step
    | simp only: Let_def
    | (rule monad_return_rel_return[where P="(=)"], clarsimp)
  )+
  done

lemma HasS2Translation_monad_return_rel[monad_return_rel]:
  "monad_determ (const_regs_translate cfg) (HasS2Translation ())"
  apply (simp add: HasS2Translation_def EL2Enabled_def IsInHost_def)
  apply monad_return_rel
  done

declare SCTLR_read__1_def[monad_return_rel_unfold]
    S1TranslationRegime__1_def[monad_return_rel_unfold]

lemma SCTLR_read_monad_return_rel[monad_return_rel]:
  "el \<in> {EL1, EL2, EL3} \<Longrightarrow> monad_determ (const_regs_translate cfg) (SCTLR_read el)"
  apply (simp add: SCTLR_read_def)
  apply (monad_return_rel | simp)+
  done

lemma AArch64_IsStageOneEnabled_monad_return_rel[monad_return_rel]:
  "monad_determ (const_regs_translate cfg) (AArch64_IsStageOneEnabled acc_type)"
  apply (simp add: AArch64_IsStageOneEnabled_def)
  apply (monad_return_rel | clarsimp)+
  done

lemma liftR_bind_split:
  "liftR (bind f (\<lambda>x. g x)) = bind (liftR f) (\<lambda>x. liftR (g x))"
  apply (simp add: liftR_def)
  apply (induct f, simp_all)
  apply (simp add: throw_def)
  done

lemma UsingAArch32_monad_return_rel[monad_return_rel]:
  "monad_determ (const_regs_translate cfg) (UsingAArch32 x)"
  apply (simp add: UsingAArch32_def Let_def)
  apply (monad_return_rel | simp)+
  done

lemma IsSecure_monad_return_rel[monad_return_rel]:
  "monad_determ (const_regs_translate cfg) (IsSecure x)"
  apply (simp add: IsSecure_def
             cong: if_cong)
  apply (monad_return_rel)
  done

(* possibly a lie, it seems the configuration is wrong somewhere *)
lemma tlb_disabled:
  "\<not> tlb_enabled"
  sorry

lemma monad_return_rel_acc_disagree:
  "(\<And>x y. Abbrev (x = acc a) \<Longrightarrow> Abbrev (y = acc b) \<Longrightarrow> monad_return_rel assms (f x) (g y) P E) \<Longrightarrow>
    monad_return_rel assms (let x = acc a in f x) (let y = acc b in g y) P E"
  by (simp add: Abbrev_def)

lemma ConstrainUnpredictable_monad_return_rel[monad_return_rel]:
  "monad_determ assms (ConstrainUnpredictable X)"
  by (cases X, simp_all, monad_return_rel)

declare HasArchVersion_def[monad_return_rel_unfold]

lemma Have52BitVAExt_monad_return_rel[monad_return_rel]:
  "monad_determ assms (Have52BitVAExt ())"
  apply (simp add: Have52BitVAExt_def)
  apply monad_return_rel
  done

lemma S1CacheDisabled_monad_return_rel[monad_return_rel]:
  "monad_determ (const_regs_translate cfg) (S1CacheDisabled acctype)"
  apply (simp add: S1CacheDisabled_def)
  apply (monad_return_rel | clarsimp)+
  done

lemma S2CacheDisabled_monad_return_rel[monad_return_rel]:
  "monad_determ (const_regs_translate cfg) (S2CacheDisabled acctype)"
  apply (simp add: S2CacheDisabled_def)
  apply (monad_return_rel | clarsimp)+
  done

lemma eq_merge_rel_apply_update:
  "(\<forall>r x. acc (f x r) = x) \<Longrightarrow>
    eq_merge_rel g_r r r' \<Longrightarrow>
    eq_merge_rel g_x x x' \<Longrightarrow>
    eq_merge_rel (\<lambda>k u. f (g_x (acc o k o Cons Two_A) (acc o u o Cons Two_A)) (g_r (k o Cons Two_B) (u o Cons Two_B)))
        (f x r) (f x' r')"
  apply (clarsimp dest!: eq_merge_relD)
  apply (rule_tac known="\<lambda>xs. case xs of Two_A # ys \<Rightarrow> f (knowna ys) undefined | Two_B # ys \<Rightarrow> known ys" and
        unknown_l="\<lambda>xs. case xs of Two_A # ys \<Rightarrow> f (unknown_la ys) undefined | Two_B # ys \<Rightarrow> unknown_l ys" and
        unknown_r="\<lambda>xs. case xs of Two_A # ys \<Rightarrow> f (unknown_ra ys) undefined | Two_B # ys \<Rightarrow> unknown_r ys" in
    eq_merge_relI)
  apply (simp add: o_def)
  done

lemmas monad_return_rel_return_merge = monad_return_rel_return[where P="eq_merge_rel f" for f]

lemma monad_return_rel_let_eq_merge:
  "eq_merge_rel f_x x y \<Longrightarrow>
    (\<And>a b. Abbrev (a = x) \<Longrightarrow> Abbrev (b = y) \<Longrightarrow> eq_merge_rel f_x x y \<Longrightarrow>
        monad_return_rel assms (f a) (g b) P E) \<Longrightarrow>
    monad_return_rel assms (let a = x in f a) (let b = y in g b) P E"
  by (simp add: Abbrev_def)

lemmas MemAttrs_merge =
    eq_merge_rel_apply_update[where acc="MemAttrHints_hints" and
        f="\<lambda>x. MemAttrHints_hints_update (\<lambda>_. x)", simplified]
    eq_merge_rel_apply_update[where acc="MemAttrHints_attrs" and
        f="\<lambda>x. MemAttrHints_attrs_update (\<lambda>_. x)", simplified]

lemma eq_merge_rel_refl:
  "eq_merge_rel (\<lambda>k u. k []) x x"
  by (auto simp add: eq_merge_rel_def)

lemma eq_merge_rel_knownD[dest!]:
  "(eq_merge_rel (\<lambda>k u. f k) x y) \<Longrightarrow> (x = y)"
  by (auto simp add: eq_merge_rel_def)

lemma ShortConvertAttrsHints_monad_return_rel[monad_return_rel]:
  "monad_return_rel (const_regs_translate cfg)
     (ShortConvertAttrsHints RGN acctype sndstage)
     (ShortConvertAttrsHints RGN acctype sndstage)
     (eq_merge_rel
        (\<lambda>k u. u [] \<lparr>MemAttrHints_attrs := MemAttrHints_attrs (k []),
               MemAttrHints_hints := MemAttrHints_hints (k [Two_A]),
               MemAttrHints_transient := MemAttrHints_transient (k [Two_B])\<rparr>)) (=)"
  (is "monad_return_rel _ _ _ ?R _")
  using word_unat.univ[THEN eqset_imp_iff, where x=RGN, simplified]
  apply (simp add: ShortConvertAttrsHints_def unats_def lessThan_def[symmetric]
        lessThan_nat_numeral lessThan_Suc Let_def[where s=RGN]
        cong: if_cong)
  apply (monad_return_rel
    | rule MemAttrs_merge eq_merge_rel_refl monad_return_rel_return_merge
    | assumption)+
  apply simp
thm MemAttrs_merge

  apply monad_return_rel
apply (rule monad_return_rel_return_merge, (rule MemAttrs_merge eq_merge_rel_refl | assumption)+)

  apply (monad_return_rel
    | rule to_eq_merge_rel
    | ((rule
    return_eq_after_update
[where acc="MemAttrHints_hints" and f="\<lambda>x. MemAttrHints_hints_update (\<lambda>_. x)", simplified]
    return_eq_after_update[where acc="MemAttrHints_attrs" and f="\<lambda>x. MemAttrHints_attrs_update (\<lambda>_. x)", simplified]
)+, rule
    monad_return_rel_return[where P="\<lambda>_ _. True", OF TrueI]
)
)+

apply (rule to_eq_merge_rel)
apply (rule to_eq_merge_rel)
apply (monad_return_rel)

apply ((rule
    return_eq_after_update[where acc="MemAttrHints_hints" and f="\<lambda>x. MemAttrHints_hints_update (\<lambda>_. x)", simplified]
    return_eq_after_update[where acc="MemAttrHints_attrs" and f="\<lambda>x. MemAttrHints_attrs_update (\<lambda>_. x)", simplified]
)+, rule
    monad_return_rel_return[where P="\<lambda>_ _. True", OF TrueI]
)


  apply (monad_return_rel
| rule
    monad_return_rel_let_via_bind
    to_eq_merge_rel
  )+

apply ((rule
    return_eq_after_update[where acc="MemAttrHints_hints" and f="\<lambda>x. MemAttrHints_hints_update (\<lambda>_. x)", simplified]
    return_eq_after_update[where acc="MemAttrHints_attrs" and f="\<lambda>x. MemAttrHints_attrs_update (\<lambda>_. x)", simplified]
)+, rule
    monad_return_rel_return[where P="\<lambda>_ _. True", OF TrueI]
)

  apply (monad_return_rel
| rule
    monad_return_rel_let_via_bind
    to_eq_merge_rel
  )+

apply ((rule
    return_eq_after_update[where acc="MemAttrHints_hints" and f="\<lambda>x. MemAttrHints_hints_update (\<lambda>_. x)", simplified]
    return_eq_after_update[where acc="MemAttrHints_attrs" and f="\<lambda>x. MemAttrHints_attrs_update (\<lambda>_. x)", simplified]
)+, rule
    monad_return_rel_return[where P="\<lambda>_ _. True", OF TrueI]
)

  apply (monad_return_rel
| rule
    monad_return_rel_let_via_bind
    to_eq_merge_rel
  )+

apply ((rule
    return_eq_after_update[where acc="MemAttrHints_hints" and f="\<lambda>x. MemAttrHints_hints_update (\<lambda>_. x)", simplified]
    return_eq_after_update[where acc="MemAttrHints_attrs" and f="\<lambda>x. MemAttrHints_attrs_update (\<lambda>_. x)", simplified]
)+, rule
    monad_return_rel_return[where P="\<lambda>_ _. True", OF TrueI]
)


  apply (
 rule
    monad_return_rel_let_via_bind
    to_eq_merge_rel
  )+

apply (monad_return_rel_step)
apply (monad_return_rel_step)

apply (rule
    monad_return_rel_return[where P="\<lambda>_ _. True", OF TrueI]
)

apply ( monad_return_rel
  | rule
    return_eq_after_update[where acc="MemAttrHints_attrs" and f="\<lambda>x. MemAttrHints_attrs_update (\<lambda>_. x)", simplified]
    return_eq_after_update[where acc="MemAttrHints_hints" and f="\<lambda>x. MemAttrHints_hints_update (\<lambda>_. x)", simplified]

    monad_return_rel_let_via_bind
    to_eq_merge_rel
  | simp only:
  | rule monad_return_rel_return[where P="\<lambda>_ _. True", OF TrueI]
)+


apply (monad_return_rel)
apply ( rule
    return_eq_after_update[where acc="MemAttrHints_attrs" and f="\<lambda>x. MemAttrHints_attrs_update (\<lambda>_. x)", simplified]
    return_eq_after_update[where acc="MemAttrHints_hints" and f="\<lambda>x. MemAttrHints_hints_update (\<lambda>_. x)", simplified]

    monad_return_rel_let_via_bind
    to_eq_merge_rel
  | simp only:
)+
apply (monad_return_rel)

apply ( rule
    return_eq_after_update[where acc="MemAttrHints_attrs" and f="\<lambda>x. MemAttrHints_attrs_update (\<lambda>_. x)", simplified]
    return_eq_after_update[where acc="MemAttrHints_hints" and f="\<lambda>x. MemAttrHints_hints_update (\<lambda>_. x)", simplified]

    monad_return_rel_let_via_bind
    to_eq_merge_rel
  | simp only:
)+


apply (rule
    monad_return_rel_return[where P="\<lambda>_ _. True", OF TrueI]
)

apply ( rule
    return_eq_after_update[where acc="MemAttrHints_attrs" and f="\<lambda>x. MemAttrHints_attrs_update (\<lambda>_. x)", simplified]
    return_eq_after_update[where acc="MemAttrHints_hints" and f="\<lambda>x. MemAttrHints_hints_update (\<lambda>_. x)", simplified]

    monad_return_rel_let_via_bind
    to_eq_merge_rel
  | simp only:
)+


thm let_double_refold

apply simp
apply simp
  done

lemma WalkAttrDecode_monad_return_rel[monad_return_rel]:
  "monad_determ (const_regs_translate cfg)
  (WalkAttrDecode SH ORGN IRGN sndstage)"
  apply (simp add: WalkAttrDecode_def)
  apply monad_return_rel


text {*
lemma AArch64_NoFault_monad_return_rel[monad_return_rel]:
  "monad_return_rel assms (AArch64_NoFault x) (AArch64_NoFault y)
    (\<lambda>ft ft'. FaultRecord_statuscode ft = Fault_None \<and> FaultRecord_statuscode ft' = Fault_None) (=)"
  apply (simp add: AArch64_NoFault_def AArch64_CreateFaultRecord_def
                   UNKNOWN_bits_def UNKNOWN_integer_def UNKNOWN_boolean_def)
  apply (monad_return_rel
    | rule monad_return_rel_bind[OF monad_return_rel_undefined_FaultRecord]
    | simp)+
  done

lemma monad_return_rel_let_binop_shuffle:
  "monad_return_rel assms (let x = x; y = y in g (f x y)) (let x = x'; y = y' in g' (f x y)) Q E \<Longrightarrow>
    monad_return_rel assms (let z = f x y in g z) (let z = f x' y' in g' z) Q E"
  by simp



lemma AArch64_TranslationTableWalk_monad_return_rel[monad_return_rel]:
  "monad_determ (const_regs_translate cfg)
    (AArch64_TranslationTableWalk ipaddress vaddr acctype iswrite sndstage s2fs sz)"
  using [[simproc del: let_simp]]
  apply (simp only: AArch64_TranslationTableWalk_def tlb_disabled)
  apply (monad_return_rel
    | rule
        monad_return_rel_let_Abbrev
        monad_return_rel_if_P
        monad_return_rel_bind[where P="\<lambda>_ (_ :: unit). True"]
    | simp only: liftR_bind_split
  )+

  apply (monad_return_rel
    | rule
        monad_return_rel_assert_exp
        monad_return_rel_bind[where P="(=) :: bool \<Rightarrow> _"]
        monad_return_rel_bind[where P="(=)", where f="if tlb_enabled then _ else _"]
        monad_return_rel_let_Abbrev
    | simp only: if_simps bind_return
  )+


apply (let_atom
  | rule
    monad_return_rel_let_binop_shuffle[where f="\<lambda>x y. y \<lparr> AddressDescriptor_memattrs := x \<rparr>"]
    monad_return_rel_let_binop_shuffle[where f="\<lambda>x y. y \<lparr> MemoryAttributes_memtype := x \<rparr>"]
        monad_return_rel_let_Abbrev
monad_return_rel_acc_disagree[where acc="AddressDescriptor_memattrs"]
   monad_return_rel_if_P[where G="\<not> sndstage", THEN monad_return_rel_bind_eq]
)+



  apply (monad_return_rel
    | rule
   monad_return_rel_if_P[where G="_ = EL3", THEN monad_return_rel_bind_eq]
   monad_return_rel_if_P[where G="_ < _", THEN monad_return_rel_bind_eq]
        monad_return_rel_let_Abbrev
        monad_return_rel_bind[where P="(=) :: bool \<Rightarrow> _"]
    | clarify elim!: TrueE
)+
apply (
thm TrueE
apply (rule monad_return_rel_bind_eq)
apply monad_return_rel[1]


thm ConstrainUnpredictable.simps
thm simp_thms
thm if_simps
  apply (
        monad_return_rel_bind[where P="(=) :: bool \<Rightarrow> _"]
)
thm bind_return
thm tlb_enabled_def


thm monad.split
thm TLBLookup_def
thm monad_return_rel_assert_exp
thm 
        monad_return_rel_and_boolM
thm 
monad_return_rel_undefined_AccessDescriptor[THEN monad_return_rel_liftR, THEN monad_return_rel_bind]

text {*
lemma AArch64_FirstStageTranslateWithTag_monad_return_rel[monad_return_rel]:
  "monad_return_rel (const_regs_translate cfg)
    (AArch64_FirstStageTranslateWithTag vaddr acctype iswrite wasaligned sz iswritevalidcap)
    (AArch64_FirstStageTranslateWithTag vaddr acctype iswrite wasaligned sz iswritevalidcap)
    (\<lambda>res res'. IsFault res = IsFault res' \<and> (\<not> IsFault res \<longrightarrow>
        AddressDescriptor_vaddress res = AddressDescriptor_vaddress res'))"
  apply (simp add: AArch64_FirstStageTranslateWithTag_def)
  apply (monad_return_rel
    | rule
        monad_return_rel_and_boolM[THEN monad_return_rel_bind]
        monad_return_rel_bind[OF monad_return_rel_triv[where f="undefined_FaultRecord _"]]
        monad_return_rel_bind[OF monad_return_rel_triv[where f="undefined_TLBRecord _"]]
    | simp add:
        AArch64_AddressSizeFault_def UNKNOWN_bits_def AArch64_CreateFaultRecord_def
    | solves \<open>simp add: IsFault_def\<close>)+
  done

lemma AArch64_FullTranslateWithTag_monad_return_rel:
  "monad_return_rel (const_regs_translate cfg)
    (AArch64_FullTranslateWithTag vaddr acctype iswrite wasaligned sz iswritevalidcap)
    (AArch64_FullTranslateWithTag vaddr acctype iswrite wasaligned sz iswritevalidcap)
    (\<lambda>res res'. IsFault res = IsFault res' \<and> (\<not> IsFault res \<longrightarrow>
        AddressDescriptor_vaddress res = AddressDescriptor_vaddress res'))"
  apply (simp add: AArch64_FullTranslateWithTag_def)
  apply (monad_return_rel
    | rule
        monad_return_rel_and_boolM[THEN monad_return_rel_bind]
    | simp add: AArch64_SecondStageTranslate_def
  )+
  apply (clarsimp simp: AArch64_SecondStageTranslate_def split: if_split_asm)
  done

thm AArch64_SecondStageTranslate_def

locale Morello_Fixed_Address_Translation =
  Morello_Bounds_Address_Calculation +
  fixes translate_address :: "nat \<Rightarrow> nat option"
    and is_translation_event :: "register_value event \<Rightarrow> bool"
    (* TODO: Let assumptions refer to a trace (and possibly a state) instead of just events,
       allowing us to make assumptions about register values/fields that might change over time,
       e.g. PSTATE.EL *)
    and translation_assms :: "register_value event \<Rightarrow> bool"
  assumes translate_correct[simp]:
      "\<And>vaddress acctype iswrite wasaligned size iswritevalidcap addrdesc.
          Run (AArch64_FullTranslateWithTag vaddress acctype iswrite wasaligned size iswritevalidcap) t addrdesc \<Longrightarrow>
          \<not>IsFault addrdesc \<Longrightarrow>
          \<forall>e \<in> set t. translation_assms e \<Longrightarrow>
          translate_address (unat vaddress) = Some (unat (FullAddress_address (AddressDescriptor_paddress addrdesc)))"
    and no_cap_load_translation_events: "\<And>rk addr sz data. \<not>is_translation_event (E_read_memt rk addr sz data)"
    and translation_el: "\<And>t acctype el. Run (AArch64_AccessUsesEL acctype) t el \<Longrightarrow> \<forall>e \<in> set t. translation_assms e \<Longrightarrow> translation_el acctype = el"
    and s1_enabled: "\<And>t acctype s1e. Run (AArch64_IsStageOneEnabled acctype) t s1e \<Longrightarrow> \<forall>e \<in> set t. translation_assms e \<Longrightarrow> s1_enabled acctype = s1e"
    and tbi_enabled: "\<And>t acctype addr top. Run (AddrTop addr (translation_el acctype)) t top \<Longrightarrow> \<forall>e \<in> set t. translation_assms e \<Longrightarrow> tbi_enabled acctype (unat addr) = (top \<noteq> 63)"
    and in_host: "\<And>t acctype ih. Run (ELIsInHost (translation_el acctype)) t ih \<Longrightarrow> \<forall>e \<in> set t. translation_assms e \<Longrightarrow> in_host acctype = ih"
    and translate_address_valid: "\<And>vaddr acctype paddr. translate_address vaddr = Some paddr \<Longrightarrow> valid_address acctype vaddr"
    and translate_bounds_address: "\<And>vaddr acctype. valid_address acctype vaddr \<Longrightarrow> translate_address (bounds_address acctype vaddr) = translate_address vaddr"
    (* Memory pages are at least 4KB in AArch64 *)
    and translate_address_paged: "\<And>vaddr vaddr' paddr. translate_address vaddr = Some paddr \<Longrightarrow> vaddr' div 2^12 = vaddr div 2^12 \<Longrightarrow> translate_address vaddr' = Some (2^12 * (paddr div 2^12) + vaddr' mod 2^12)"
    (*and translate_address_paged: "\<And>vaddr vaddr' acctype paddr paddr'. translate_address vaddr acctype = Some paddr \<Longrightarrow> translate_address vaddr' acctype = Some paddr' \<Longrightarrow> vaddr div 2^12 = vaddr' div 2^12 \<Longrightarrow> paddr div 2^12 = paddr' div 2^12"
    and translate_address_page_offset: "\<And>vaddr acctype paddr. translate_address vaddr acctype = Some paddr \<Longrightarrow> paddr mod 2^12 = vaddr mod 2^12"*)
begin

end
