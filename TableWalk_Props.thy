theory TableWalk_Props

  imports
    "Sail-Morello.Morello_lemmas"
    "Sail-T-CHERI.Bound_UntilM"
    "Sail-T-CHERI.Trace_Subset"

begin

text \<open>
Proof that the page table walk is guaranteed to terminate, and
calculation of the set of registers it is sensitive to.
\<close>

ML \<open>
structure TableWalk_Coerce_Bound = struct

val t = @{thm coerce_inv_bound_untilM[where
    bound="\<lambda>(_, _, _, _, _, _, _, _, _, _, lv :: int, _). nat (5 - lv)" and
    I="\<lambda>(_, _, _, _, _, _, _, _, _, _, lv :: int, _). 0 \<le> lv \<and> lv \<le> 4"]}

val t_pair = Thm.concl_of t |> HOLogic.dest_Trueprop |> HOLogic.dest_eq

val (reg_lhs, reg_rhs) = @{thm AArch64_TranslationTableWalk_def[abs_def]}
    |> Thm.concl_of |> Logic.dest_equals

val reg_rhs_rew = reg_rhs
    |> Pattern.rewrite_term @{theory} [t_pair] []

val t2 = @{thm coerce_inv_bound_untilM[where
    bound="\<lambda>(_, _, _, _, _, _, _, _, lv :: int, _). nat (5 - lv)" and
    I="\<lambda>(_, _, _, _, _, _, _, _, lv :: int, _). 0 \<le> lv \<and> lv \<le> 4"]}

val t_pair2 = Thm.concl_of t2 |> HOLogic.dest_Trueprop |> HOLogic.dest_eq

val (mut_lhs, mut_rhs) = @{thm AArch64_TranslationTableWalk_mutrec_vvvvTvv_def[abs_def]}
    |> Thm.concl_of |> Logic.dest_equals

val mut_rhs_rew = mut_rhs
    |> Pattern.rewrite_term @{theory} [t_pair2] []

val checks = [reg_rhs_rew <> reg_rhs, mut_rhs_rew <> mut_rhs]

fun setup b1 b2 = 
  Sign.add_abbrev Print_Mode.input (b1, reg_rhs_rew)
  #> snd
  #> Sign.add_abbrev Print_Mode.input (b2, mut_rhs_rew)
  #> snd
end

val checks = TableWalk_Coerce_Bound.checks
\<close>

setup \<open>TableWalk_Coerce_Bound.setup @{binding VMWalk_body_bound} @{binding VMWalk_mutrec_body_bound}\<close>

(* possibly a lie, it seems the configuration is wrong somewhere
lemma tlb_disabled:
  "\<not> tlb_enabled"
  sorry
*)

lemma Run_return_eq:
  "(Run (return x) t y) = (t = [] \<and> y = x)"
  by (simp add: return_def)

lemma t_eq_helper:
  "inputsize \<ge> 24 \<Longrightarrow> grainsize \<le> 20 \<Longrightarrow> stride \<ge> 1 \<Longrightarrow>
    (0 :: int) \<le> (inputsize - grainsize - 1) div stride"
  by (simp add: pos_imp_zdiv_nonneg_iff[THEN iffD2])

lemma AArch64_TranslationTableWalk_def_bound:
  "AArch64_TranslationTableWalk ipaddress vaddress acctype isw sndstage s2fs1walk sz =
    VMWalk_body_bound  ipaddress vaddress acctype isw sndstage s2fs1walk sz"
  using [[goals_limit = 1]]
  apply (simp only: AArch64_TranslationTableWalk_def Let_def[where s="numeral _"])
  apply (intro bind_cong arg_cong[where f=catch_early_return] refl
    let_cong prod.case_cong if_cong)
  apply (rule coerce_inv_bound_untilM[where
    bound="\<lambda>(_, _, _, _, _, _, _, _, _, _, lv :: int, _). nat (5 - lv)" and
    I="\<lambda>(_, _, _, _, _, _, _, _, _, _, lv :: int, _). lv \<le> 3", rotated])
   apply (thin_tac "PROP P" for P)+
   apply (clarsimp simp: Let_def Run_return_eq split: if_split_asm
    elim!: Run_bindE Run_early_returnE Run_returnE)
  (* the difficult part is to prove that initially level \<le> 3 *)
  apply (clarify elim!: Run_bindE Run_letE)
  apply (split if_split_asm[where Q="\<not> sndstage"])
   (* standard mode, awkward division at the end *)
   apply (clarsimp elim!: Run_bindE Run_letE Run_early_returnE Run_returnE)
   apply ((erule notE)?, rule t_eq_helper)
     (* basically clarsimp but specialise the strategy *)
     apply ((clarify elim!: Run_bindE Run_letE Run_early_returnE Run_returnE
        | simp(no_asm_use) | simp(no_asm_simp)
        | erule Run_ifE)+)[1]
    apply (simp(no_asm_use) split: if_split_asm[where x="(numeral _, _)"]; simp(no_asm_simp))
   apply (simp(no_asm_use) split: if_split_asm[where x="(numeral _, _)"]; simp(no_asm_simp))
  (* second stage mode, basically just a case division *)
  apply (simp only: Let_def)
  apply ((clarify elim!: Run_bindE Run_letE Run_returnE Run_early_returnE
    | simp(no_asm_use) add: uint_ge_0[THEN order_trans[rotated]]
    | simp(no_asm_simp)
    | split if_split_asm[where x="(numeral _, _)"]
    | erule Run_ifE)+)[1]
  done

text \<open>One down, one to go.\<close>

lemma AArch64_TranslationTableWalk_mutrec_vvvvTvv_def_bound:
  "AArch64_TranslationTableWalk_mutrec_vvvvTvv ipaddress vaddress acctype isw s2fs1walk sz =
    VMWalk_mutrec_body_bound ipaddress vaddress acctype isw s2fs1walk sz"
  apply (simp only: AArch64_TranslationTableWalk_mutrec_vvvvTvv_def Let_def[where s="numeral _"])
  apply (intro bind_cong arg_cong[where f=catch_early_return] refl
    let_cong prod.case_cong if_cong)
  apply (rule coerce_inv_bound_untilM[where
    bound="\<lambda>(_, _, _, _, _, _, _, _, lv :: int, _). nat (5 - lv)" and
    I="\<lambda>(_, _, _, _, _, _, _, _, lv :: int, _). lv \<le> 3", rotated])
   apply (thin_tac "PROP P" for P)+
   apply (clarsimp simp: Let_def split: if_split_asm
        elim!: Run_bindE Run_returnE Run_early_returnE)
  (* the difficult part is to prove that initially level \<le> 3 *)
  apply (clarify elim!: Run_bindE Run_letE)
  (* second stage mode, basically just a case division *)
  apply (simp only: Let_def)
  apply ((clarify elim!: Run_bindE Run_letE Run_returnE Run_early_returnE
    | simp(no_asm_use) add: uint_ge_0[THEN order_trans[rotated]]
    | simp(no_asm_simp)
    | split if_split_asm[where x="(numeral _, _)"]
    | erule Run_ifE)+)[1]
  done

text \<open>Trace overapproximation.\<close>

lemma ConstrainUnpredictable_monad_trace_subset[monad_trace_subset]:
  "monad_trace_subset {} (ConstrainUnpredictable k)"
  by (cases k, simp_all, monad_trace_subsetI)

lemmas walk_datatype_splits =
  Constraint.split

lemmas split_subset_intros[monad_trace_subset_intro] =
    walk_datatype_splits[where P="monad_trace_subset _", THEN iffD2]

setup \<open>Monad_Trace_Subset_Exploration.install_recs
  ["Morello", "Prelude"]
  @{thms AArch64_TranslationTableWalk_mutrec_vvvvTvv_def_bound}
\<close>

setup \<open>Monad_Trace_Subset_Exploration.install_recs
  ["Morello", "Prelude"]
  @{thms AArch64_TranslationTableWalk_def_bound}
\<close>

end