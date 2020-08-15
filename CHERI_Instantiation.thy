theory CHERI_Instantiation
  imports
    "Sail-Morello.Morello_lemmas"
    "Sail-T-CHERI.Cheri_axioms_lemmas"
    "Sail.Sail2_operators_mwords_lemmas"
    "Sail.Sail2_values_lemmas"
    "HOL-Library.Monad_Syntax"
    "Sail-T-CHERI.Word_Extra"
    "Sail-T-CHERI.Recognising_Automata"
begin

no_notation Sail2_prompt_monad.bind (infixr "\<bind>" 54)
no_notation Sail2_prompt_monad_lemmas.seq (infixr "\<then>" 54)
adhoc_overloading bind Sail2_prompt_monad.bind

section \<open>General lemmas\<close>

lemma un_ui_lt:
  "(unat x < unat y) \<longleftrightarrow> (uint x < uint y)"
  unfolding unat_def nat_less_eq_zless[OF uint_ge_0] ..

declare unat_add_lem[THEN iffD1, simp]
declare unat_mult_lem[THEN iffD1, simp]

lemma bitU_of_bool_simps[simp]:
  "bitU_of_bool True = B1"
  "bitU_of_bool False = B0"
  by (auto simp: bitU_of_bool_def)

lemma of_bits_method_vec_of_bits_maybe[simp]:
  "of_bits_method BC_mword = vec_of_bits_maybe"
  by (auto simp: BC_mword_defs vec_of_bits_maybe_def)

lemma or_boolM_return_True[simp]: "or_boolM (return True) m = return True"
  by (auto simp: or_boolM_def)

lemma if_then_let_unfold[simp]:
  "(if c then let x = y in f x else z) = (if c then f y else z)"
  by auto

lemma Run_if_then_return[simp]:
  "Run (if c then return x else m) t a \<longleftrightarrow> (c \<and> t = [] \<and> a = x \<or> \<not>c \<and> Run m t a)"
  by auto

lemma Run_bind_return[simp]:
  "Run (m \<bind> (\<lambda>a. return (f a))) t a \<longleftrightarrow> (\<exists>a'. Run m t a' \<and> a = f a')"
  by (auto elim!: Run_bindE intro: Traces_bindI[of m t _ _ "[]", simplified])

lemma Run_bind_iff:
  "Run (m \<bind> f) t a \<longleftrightarrow> (\<exists>t1 t2 a1. t = t1 @ t2 \<and> Run m t1 a1 \<and> Run (f a1) t2 a)"
  by (auto elim!: Run_bindE intro: Traces_bindI)

lemma Run_and_boolM_True_iff:
  "Run (and_boolM m1 m2) t True \<longleftrightarrow> (\<exists>t1 t2. t = t1 @ t2 \<and> Run m1 t1 True \<and> Run m2 t2 True)"
  by (auto simp: and_boolM_def Run_bind_iff)

lemma Run_if_iff:
  "Run (if c then m1 else m2) t a \<longleftrightarrow> (c \<and> Run m1 t a \<or> \<not>c \<and> Run m2 t a)"
  by auto

lemma Run_if_then_throw_iff[simp]:
  "Run (if c then throw e else m) t a \<longleftrightarrow> \<not>c \<and> Run m t a"
  by auto

lemma Run_bind_assert_exp_iff[simp]:
  "Run (assert_exp c msg \<bind> f) t a \<longleftrightarrow> c \<and> Run (f ()) t a"
  by (auto elim: Run_bindE)

lemma concat_take_chunks_eq:
  "n > 0 \<Longrightarrow> List.concat (take_chunks n xs) = xs"
  by (induction n xs rule: take_chunks.induct) auto

lemma leq_bounds_trans:
  assumes "leq_bounds CC c c'" and "leq_bounds CC c' c''"
  shows "leq_bounds CC c c''"
  using assms
  by (auto simp: leq_bounds_def)

lemma leq_perms_trans:
  assumes "leq_perms p p'" and "leq_perms p' p''"
  shows "leq_perms p p''"
  using assms
  by (auto simp: leq_perms_def leq_bools_iff)

lemma leq_cap_trans:
  assumes "leq_cap CC c c'" and "leq_cap CC c' c''"
  shows "leq_cap CC c c''"
  using assms
  by (auto simp: leq_cap_def elim: leq_bounds_trans leq_perms_trans)

lemma bits_of_mem_bytes_of_word_to_bl:
  "bits_of_mem_bytes (mem_bytes_of_word w) = map bitU_of_bool (to_bl w)"
  unfolding bits_of_mem_bytes_def mem_bytes_of_word_def bits_of_bytes_def
  by (auto simp add: concat_take_chunks_eq simp del: take_chunks.simps)

lemma uint_leq2pm1[intro]:
  fixes w :: "'a::len word"
  assumes "n \<ge> 2^LENGTH('a) - 1"
  shows "uint w \<le> n"
  using assms dual_order.trans zle_diff1_eq by blast

lemma test_bit_of_bl_append:
  fixes x y :: "bool list"
  defines "w \<equiv> of_bl (x @ y) :: 'a::len word"
  shows "w !! n =
           (if n \<ge> LENGTH('a) \<or> n \<ge> length x + length y then False else
            if n < length y then rev y ! n else
            rev x ! (n - length y))"
  unfolding w_def
  by (auto simp: test_bit_of_bl nth_append)

lemma update_subrange_vec_dec_test_bit:
  fixes w :: "'a::len word" and w' :: "'b::len word"
  assumes "0 \<le> j" and "j \<le> i" and "nat i < LENGTH('a)" and "LENGTH('b) = nat (i - j + 1)"
  shows "update_subrange_vec_dec w i j w' !! n =
         (if nat j > n \<or> n > nat i then w !! n else w' !! (n - nat j))"
    (is "?lhs = ?rhs")
proof -
  note [simp] = update_subrange_vec_dec_update_subrange_list_dec
                update_subrange_list_dec_drop_take
                nat_add_distrib nat_diff_distrib
  consider (Low) "nat j > n" | (Mid) "nat j \<le> n \<and> n \<le> nat i" | (High) "n > nat i"
    by linarith
  then show ?thesis
  proof cases
    case Low
    then show ?thesis
      using assms
      by (auto simp: test_bit_of_bl nth_append rev_nth test_bit_bl)
  next
    case Mid
    then show ?thesis
      using assms
      by (auto simp: test_bit_of_bl_append nth_append less_diff_conv2 test_bit_bl[of w' "n - nat j"])
  next
    case High
    then show ?thesis
      using assms
      by (auto simp: test_bit_of_bl_append nth_rev test_bit_bl[of w n])
  qed
qed

lemma slice_update_subrange_vec_dec_above:
  fixes w :: "'a::len word" and w' :: "'b::len word"
  assumes "0 \<le> j" and "j \<le> i" and "nat i < LENGTH('a)" and "LENGTH('b) = nat (i - j + 1)"
    and "nat j \<ge> n + LENGTH('c)"
  shows "Word.slice n (update_subrange_vec_dec w i j w') = (Word.slice n w :: 'c::len word)"
  using assms
  by (intro word_eqI)
     (auto simp: update_subrange_vec_dec_update_subrange_list_dec update_subrange_list_dec_drop_take
                 nth_slice test_bit_of_bl nat_add_distrib nat_diff_distrib nth_append rev_nth to_bl_nth)

lemma slice_update_subrange_vec_dec_below:
  fixes w :: "'a::len word" and w' :: "'b::len word"
  assumes "0 \<le> j" and "j \<le> i" and "nat i < LENGTH('a)" and "LENGTH('b) = nat (i - j + 1)"
    and "n > nat i"
  shows "Word.slice n (update_subrange_vec_dec w i j w') = (Word.slice n w :: 'c::len word)"
  using assms
  by (intro word_eqI)
     (auto simp: update_subrange_vec_dec_update_subrange_list_dec update_subrange_list_dec_drop_take
                 nth_slice test_bit_of_bl_append nth_rev nat_add_distrib nat_diff_distrib test_bit_bl[of w "n' + n" for n'])

lemma update_subrange_vec_dec_word_cat_cap_pair:
  fixes tmp :: "256 word" and c1 c2 :: "128 word"
  shows "update_subrange_vec_dec (update_subrange_vec_dec tmp 127 0 c2) 255 128 c1 = (word_cat c1 c2 :: 256 word)"
  by (intro word_eqI) (auto simp: test_bit_cat update_subrange_vec_dec_test_bit)

lemmas slice_128_cat_cap_pair = slice_cat1[where a = c1 and b = c2 for c1 c2 :: "128 word", simplified]

lemma slice_set_bit_above:
  assumes "n' \<ge> n + LENGTH('a)"
  shows "Word.slice n (set_bit w n' b) = (Word.slice n w :: 'a::len word)"
  using assms
  by (intro word_eqI) (auto simp: nth_slice test_bit_set_gen)

lemma of_bl_0th[simp]: "(of_bl [b] :: 1 word) !! 0 = b"
  by (auto simp: test_bit_of_bl)

definition aligned :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "aligned addr sz \<equiv> sz dvd addr"

lemma aligned_dvd_trans:
  assumes "aligned addr sz" and "sz' dvd sz"
  shows "aligned addr sz'"
  using assms
  by (auto simp: aligned_def)

lemma aligned32_16[intro, simp]:
  "aligned addr 32 \<Longrightarrow> aligned addr 16"
  by (simp add: aligned_dvd_trans)

lemma aligned_add_size_iff[simp]:
  "aligned (addr + sz) sz \<longleftrightarrow> aligned addr sz"
  by (auto simp: aligned_def)

lemma unat_le_unat_add_iff:
  fixes x y :: "'a::len word"
  shows "unat x \<le> unat (x + y) \<longleftrightarrow> unat x + unat y < 2^LENGTH('a)"
  using no_olen_add_nat word_le_nat_alt by blast

lemma aligned_unat_plus_distrib:
  fixes addr offset :: "'a::len word"
  assumes "aligned (unat addr) sz" and "unat offset < sz" and "sz dvd 2^LENGTH('a)"
  shows "unat (addr + offset) = unat addr + unat offset"
proof -
  obtain k k' where k: "unat addr = sz * k" and k': "2^LENGTH('a) = sz * k'"
    using assms
    by (auto simp: dvd_def aligned_def)
  then have "k < k'" and "k' > 0"
    using unat_lt2p[of addr]
    by auto
  have "sz * k + unat offset < sz * (Suc k)"
    using \<open>unat offset < sz\<close>
    by auto
  also have "\<dots> \<le> sz * k'"
    using \<open>k < k'\<close>
    unfolding less_eq_Suc_le
    by (intro mult_le_mono2)
  finally show ?thesis
    unfolding unat_plus_if' k k'
    by auto
qed

lemma integer_subrange_word_of_int[simp]:
  assumes "sz \<ge> 0" and "LENGTH('a) = Suc (nat sz)"
  shows "(integer_subrange i sz 0 :: 'a::len word) = word_of_int i"
  using assms
  by (auto simp: integer_subrange_def of_bl_bin_word_of_int)

lemma unat_word_of_int[simp]:
  "unat (word_of_int i :: 'a::len word) = nat (i mod 2^LENGTH('a))"
  by (auto simp: unat_def uint_word_of_int)

lemma unat_add_word_of_int_l2p_distrib:
  fixes w :: "'a::len word"
  assumes "uint w + i < 2^LENGTH('a)" and "i \<ge> 0"
  shows "unat (w + word_of_int i) = unat w + nat i"
  using assms
  by (metis add_increasing nat_add_distrib uint_ge_0 unat_def wi_hom_add word_of_int_inverse word_uint.Rep_inverse)

lemma unat_add_l2p_distrib:
  fixes w :: "'a::len word"
  assumes "uint w + uint i < 2^LENGTH('a)"
  shows "unat (w + i) = unat w + unat i"
  using assms
  using no_olen_add unat_plus_simple
  by auto

lemma leq_perms_to_bl_iff:
  fixes x y :: "'a::len word"
  shows "leq_perms (to_bl x) (to_bl y) \<longleftrightarrow> (\<forall>n. x !! n \<longrightarrow> y !! n)"
proof
  assume leq: "leq_perms (to_bl x) (to_bl y)"
  show "\<forall>n. x !! n \<longrightarrow> y !! n"
  proof
    fix n
    have "to_bl x ! (size x - Suc n) \<longrightarrow> to_bl y ! (size y - Suc n)"
      using leq
      unfolding leq_perms_def leq_bools_iff
      by auto
    then show "x !! n \<longrightarrow> y !! n"
      by (cases "n < LENGTH('a)") (auto simp: to_bl_nth dest: test_bit_len)
  qed
next
  assume "\<forall>n. x !! n \<longrightarrow> y !! n"
  then show "leq_perms (to_bl x) (to_bl y)"
    unfolding leq_perms_def leq_bools_iff
    by (auto simp: to_bl_nth)
qed

lemma AND_NOT_eq_0_iff:
  fixes x y :: "'a::len word"
  shows "(x AND NOT y = 0) \<longleftrightarrow> (\<forall>n. x !! n \<longrightarrow> y !! n)"
  by (auto simp: word_eq_iff word_ops_nth_size intro: test_bit_len)

context Cap_Axiom_Automaton
begin

lemma (in Cap_Axiom_Automaton) read_memt_bytes_derivable:
  assumes "Run (read_memt_bytes BCa BCb rk addr sz) t (bytes, tag)"
    and "cap_of_mem_bytes_method CC bytes tag = Some c"
    and "\<forall>addr'. nat_of_bv BCa addr = Some addr' \<longrightarrow> \<not>is_translation_event ISA (E_read_memt rk addr' (nat sz) (bytes, tag))"
  shows "c \<in> derivable_caps (run s t)"
  using assms
  unfolding read_memt_bytes_def
  by (auto simp: derivable_caps_def maybe_fail_def split: option.splits intro: derivable.Copy
           elim!: Run_bindE Traces_cases[of "Read_memt _ _ _ _"])

lemma Run_bindE':
  fixes m :: "('rv, 'b, 'e) monad" and a :: 'a
  assumes "Run (bind m f) t a"
    and "\<And>tm am tf. t = tm @ tf \<Longrightarrow> Run m tm am \<Longrightarrow> Run (f am) tf a \<Longrightarrow> P (tm @ tf)"
  shows "P t"
  using assms
  by (auto elim: Run_bindE)

lemmas Run_case_prodE = case_prodE2[where Q = "\<lambda>m. Run m t a" and R = thesis for t a thesis]

declare Run_case_prodE[where thesis = "c \<in> derivable_caps s" and a = c for c s, derivable_caps_combinators]
declare Run_case_prodE[where thesis = "fst a \<in> derivable_caps s" and a = a for a s, derivable_caps_combinators]
declare Run_case_prodE[where thesis = "snd a \<in> derivable_caps s" and a = a for a s, derivable_caps_combinators]

lemma prod_snd_derivable_caps[derivable_capsE]:
  assumes "a = (x, y)"
    and "snd a \<in> derivable_caps s"
  shows "y \<in> derivable_caps s"
  using assms
  by auto

lemma prod_fst_derivable_caps[derivable_capsE]:
  assumes "a = (x, y)"
    and "fst a \<in> derivable_caps s"
  shows "x \<in> derivable_caps s"
  using assms
  by auto

lemma return_prod_snd_derivable_caps[derivable_capsE]:
  assumes "Run (return (x, y)) t a"
    and "y \<in> derivable_caps s"
  shows "snd a \<in> derivable_caps s"
  using assms
  by auto

lemma return_prod_fst_derivable_caps[derivable_capsE]:
  assumes "Run (return (x, y)) t a"
    and "x \<in> derivable_caps s"
  shows "fst a \<in> derivable_caps s"
  using assms
  by auto

text \<open>For the proofs of some of the decode clauses, some fairly simple side conditions need to be
  proved, but the auto proof method struggles in some cases due to the nesting of blocks and use
  of mutable variables, so we declare some custom proof rules so that these conditions can be
  handled efficiently by the derivable_capsI proof method.\<close>

lemma member_fst_snd_prod_elims[derivable_capsE]:
  "\<And>a x y xs. a = (x, y) \<Longrightarrow> fst a \<in> xs \<Longrightarrow> x \<in> xs"
  "\<And>a x y xs. a = (x, y) \<Longrightarrow> snd a \<in> xs \<Longrightarrow> y \<in> xs"
  "\<And>a x y xs. a = (x, y) \<Longrightarrow> fst (snd a) \<in> xs \<Longrightarrow> fst y \<in> xs"
  "\<And>a x y xs. a = (x, y) \<Longrightarrow> fst (snd (snd a)) \<in> xs \<Longrightarrow> fst (snd y) \<in> xs"
  "\<And>a x y xs. a = (x, y) \<Longrightarrow> fst (snd (snd (snd a))) \<in> xs \<Longrightarrow> fst (snd (snd y)) \<in> xs"
  "\<And>a x y xs. a = (x, y) \<Longrightarrow> snd (snd a) \<in> xs \<Longrightarrow> snd y \<in> xs"
  "\<And>a x y xs. a = (x, y) \<Longrightarrow> snd (snd (snd a)) \<in> xs \<Longrightarrow> snd (snd y) \<in> xs"
  "\<And>a x y xs. a = (x, y) \<Longrightarrow> snd (snd (snd (snd a))) \<in> xs \<Longrightarrow> snd (snd (snd y)) \<in> xs"
  by auto

lemma return_prods_derivable[derivable_capsE]:
  "\<And>a b x xs. Run (return (a, b)) t x \<Longrightarrow> a \<in> xs \<Longrightarrow> fst x \<in> xs"
  "\<And>a b x xs. Run (return (a, b)) t x \<Longrightarrow> b \<in> xs \<Longrightarrow> snd x \<in> xs"
  "\<And>a b c x xs. Run (return (a, b, c)) t x \<Longrightarrow> b \<in> xs \<Longrightarrow> fst (snd x) \<in> xs"
  "\<And>a b c x xs. Run (return (a, b, c)) t x \<Longrightarrow> c \<in> xs \<Longrightarrow> snd (snd x) \<in> xs"
  "\<And>a b c d e x xs. Run (return (a, b, c, d, e)) t x \<Longrightarrow> d \<in> xs \<Longrightarrow> fst (snd (snd (snd x))) \<in> xs"
  by auto

declare Run_bindE[where thesis = "fst (snd (snd (snd a))) \<in> xs" and a = a for a xs, derivable_caps_combinators]
declare Run_bindE[where thesis = "snd (snd a) \<in> xs" and a = a for a xs, derivable_caps_combinators]
declare Run_ifE[where thesis = "fst (snd (snd (snd a))) \<in> xs" and a = a for a xs, derivable_caps_combinators]
declare Run_ifE[where thesis = "snd (snd a) \<in> xs" and a = a for a xs, derivable_caps_combinators]
declare Run_letE[where thesis = "fst (snd (snd (snd a))) \<in> xs" and a = a for a xs, derivable_caps_combinators]
declare Run_letE[where thesis = "snd (snd a) \<in> xs" and a = a for a xs, derivable_caps_combinators]
declare Run_case_prodE[where thesis = "fst (snd (snd (snd a))) \<in> xs" and a = a for a xs, derivable_caps_combinators]
declare Run_case_prodE[where thesis = "snd (snd a) \<in> xs" and a = a for a xs, derivable_caps_combinators]

declare Run_bindE[where thesis = "a \<in> xs" and a = a for a xs, derivable_caps_combinators]
declare Run_ifE[where thesis = "a \<in> xs" and a = a for a xs, derivable_caps_combinators]
declare Run_letE[where thesis = "a \<in> xs" and a = a for a xs, derivable_caps_combinators]

lemma Run_return_resultE:
  assumes "Run (return x) t a"
    and "P x"
  shows "P a"
  using assms
  by auto

declare Run_return_resultE[where P = "\<lambda>a. a \<in> xs" for xs, derivable_capsE]

end

section \<open>Simplification rules\<close>

lemma Zeros_0[simp]:
  "Zeros n = 0"
  by (auto simp: Zeros_def zeros_def)

lemma Ones_max_word[simp]:
  "Ones n = max_word"
  by (auto simp: Ones_def sail_ones_def zeros_def)

declare id0_def[simp]
declare eq_bits_int_def[simp]
declare CAPABILITY_DBITS_def[simp]
declare CAPABILITY_DBYTES_def[simp]
declare zero_extend_def[simp]

lemmas cap_bit_index_defs[simp] =
  CAP_TAG_BIT_def CAP_IE_BIT_def
  CAP_VALUE_HI_BIT_def CAP_VALUE_LO_BIT_def
  CAP_PERMS_LO_BIT_def CAP_PERMS_HI_BIT_def
  CAP_OTYPE_LO_BIT_def CAP_OTYPE_HI_BIT_def
  CAP_BASE_LO_BIT_def CAP_BASE_HI_BIT_def
  CAP_LIMIT_LO_BIT_def CAP_LIMIT_HI_BIT_def
  CAP_BASE_MANTISSA_LO_BIT_def CAP_LIMIT_MANTISSA_LO_BIT_def
  CAP_FLAGS_HI_BIT_def CAP_FLAGS_LO_BIT_def

lemmas special_otype_defs[simp] =
  CAP_SEAL_TYPE_RB_def CAP_SEAL_TYPE_LPB_def CAP_SEAL_TYPE_LB_def
  CAP_MAX_FIXED_SEAL_TYPE_def

lemma ZeroExtend1_ucast[simp]:
  "ZeroExtend1 n w = ucast w"
  by (auto simp: ZeroExtend1_def)

lemma DataFromCapability_tag_ucast[simp]:
  "DataFromCapability 128 c = (of_bl [c !! 128], ucast c)"
  by (auto simp: DataFromCapability_def)

definition Capability_of_tag_word :: "bool \<Rightarrow> 128 word \<Rightarrow> Capability" where
  "Capability_of_tag_word tag word =
     (let tag = (of_bl [tag] :: 1 word) in
      word_cat tag word)"

lemma Capability_of_tag_word_id[simp]:
  fixes c :: Capability
  shows "Capability_of_tag_word (c !! 128) (ucast c) = c" (is "?c' = c")
proof (intro word_eqI impI)
  fix n
  assume "n < size ?c'"
  then show "?c' !! n = c !! n"
    unfolding Capability_of_tag_word_def
    by (cases "n = 128") (auto simp: nth_word_cat nth_ucast test_bit_of_bl)
qed

lemma Capability_of_tag_word_128th[simp]:
  "Capability_of_tag_word tag data !! 128 = tag"
  by (auto simp: Capability_of_tag_word_def nth_word_cat test_bit_of_bl)

lemma update_bits_tag_Capability_from_tag_word[simp]:
  "update_vec_dec (update_subrange_vec_dec c 127 0 cap_bits) 128 (bitU_of_bool tag)
   = Capability_of_tag_word tag cap_bits"
  unfolding Capability_of_tag_word_def
  by (cases tag; intro word_eqI)
     (auto simp: test_bit_set_gen update_subrange_vec_dec_test_bit nth_word_cat nth_ucast
           dest: test_bit_len)

lemma nat_of_bv_mword_unat[simp]: "nat_of_bv BC_mword w = Some (unat w)"
  by (auto simp: nat_of_bv_def unat_def)

lemma Bit_bitU_of_bool[simp]: "Morello.Bit w = bitU_of_bool (w !! 0)"
  by (auto simp: Morello.Bit_def)

lemma CapIsTagSet_128th[simp]:
  "CapIsTagSet c \<longleftrightarrow> c !! 128"
  by (auto simp: CapIsTagSet_def CapGetTag_def nth_ucast test_bit_of_bl)

lemma CapSetTag_set_128th[simp]:
  "CapSetTag c t = set_bit c 128 (t !! 0)"
  by (cases "t !! 0") (auto simp: CapSetTag_def)

lemma CapIsTagSet_CapSetTag_iff[simp]:
  "CapIsTagSet (CapSetTag c t) \<longleftrightarrow> (t !! 0)"
  by (auto simp: test_bit_set)

lemma CapWithTagClear_128th[simp]:
  "CapWithTagClear c !! 128 = False"
  by (auto simp: CapWithTagClear_def test_bit_set)

lemma CapIsTagSet_CapWithTagSet_eq:
  assumes "CapIsTagSet c"
  shows "CapWithTagSet c = c"
  using assms
  by (intro word_eqI) (auto simp: CapWithTagSet_def test_bit_set_gen)

lemma CapIsTagClear_iff_not_128th[simp]:
  "CapIsTagClear c \<longleftrightarrow> \<not>CapIsTagSet c"
  by (auto simp: CapIsTagClear_def CapGetTag_def nth_ucast test_bit_of_bl)

lemma CapGetPermissions_set_0th[simp]:
  "CapGetPermissions (set_bit c 0 b) = CapGetPermissions c"
  by (intro word_eqI) (auto simp: CapGetPermissions_def nth_slice test_bit_set_gen)

lemma CapGetPermissions_CapSetFlags_eq[simp]:
  "CapGetPermissions (CapSetFlags c flags) = CapGetPermissions c"
  by (intro word_eqI)
     (auto simp: CapGetPermissions_def CapSetFlags_def nth_slice slice_update_subrange_vec_dec_below)

lemma CapGetObjectType_CapSetObjectType_and_mask:
  "CapGetObjectType (CapSetObjectType c otype) = (otype AND mask (nat CAP_OTYPE_HI_BIT - nat CAP_OTYPE_LO_BIT + 1))"
  unfolding CapGetObjectType_def CapSetObjectType_def
  by (intro word_eqI)
     (auto simp: word_ao_nth nth_slice nth_ucast update_subrange_vec_dec_test_bit)

lemma CapGetObjectType_CapUnseal_0[simp]:
  "CapGetObjectType (CapUnseal c) = 0"
  by (auto simp: CapUnseal_def CapGetObjectType_CapSetObjectType_and_mask)

lemma CapSetObjectType_128th_iff[simp]:
  "CapSetObjectType c otype !! 128 \<longleftrightarrow> c !! 128"
  unfolding CapSetObjectType_def
  by (auto simp: update_subrange_vec_dec_test_bit)

lemma CapUnseal_128th_iff[simp]:
  "CapUnseal c !! 128 = c !! 128"
  by (auto simp: CapUnseal_def)

lemma clear_perms_128th_iff[simp]:
  "CapClearPerms c perms !! 128 \<longleftrightarrow> c !! 128"
  by (auto simp: CapClearPerms_def update_subrange_vec_dec_test_bit)

lemma CapSetFlags_128th_iff[simp]:
  "CapSetFlags c flags !! 128 = c !! 128"
  by (auto simp: CapSetFlags_def update_subrange_vec_dec_test_bit)

lemma CapUnseal_not_sealed[simp]:
  "\<not>CapIsSealed (CapUnseal c)"
  by (auto simp: CapIsSealed_def CapUnseal_def CapGetObjectType_CapSetObjectType_and_mask)

lemma CapUnsignedGreaterThan_iff_unat_gt[simp]:
  "CapUnsignedGreaterThan x y \<longleftrightarrow> unat x > unat y"
  unfolding unat_def nat_less_eq_zless[OF uint_ge_0]
  by (auto simp: CapUnsignedGreaterThan_def)

lemma CapUnsignedGreaterThanOrEqual_iff_unat_geq[simp]:
  "CapUnsignedGreaterThanOrEqual x y \<longleftrightarrow> unat x \<ge> unat y"
  by (auto simp: CapUnsignedGreaterThanOrEqual_def unat_def nat_le_eq_zle)

lemma CapUnsignedLessThan_iff_unat_lt[simp]:
  "CapUnsignedLessThan x y \<longleftrightarrow> unat x < unat y"
  unfolding unat_def nat_less_eq_zless[OF uint_ge_0]
  by (auto simp: CapUnsignedLessThan_def)

lemma CapUnsignedLessThanOrEqual_iff_unat_leq[simp]:
  "CapUnsignedLessThanOrEqual x y \<longleftrightarrow> unat x \<le> unat y"
  by (auto simp: CapUnsignedLessThanOrEqual_def unat_def nat_le_eq_zle)

lemma CapGetObjectType_set_bit_128_eq[simp]:
  "CapGetObjectType (set_bit c 128 tag) = CapGetObjectType c"
  unfolding CapGetObjectType_def CAP_OTYPE_LO_BIT_def
  by (intro word_eqI) (auto simp: word_ao_nth nth_slice test_bit_set_gen)

lemma CapGetObjectType_update_address[simp]:
  fixes addr :: "64 word"
  shows "CapGetObjectType (update_subrange_vec_dec c 63 0 addr) = CapGetObjectType c"
  unfolding CapGetObjectType_def
  by (intro word_eqI) (auto simp: word_ao_nth nth_slice update_subrange_vec_dec_test_bit)

lemma CapAdd_GetObjectType_eq:
  assumes "Run (CapAdd c increment) t c'"
  shows "CapGetObjectType c' = CapGetObjectType c"
  using assms
  unfolding CapAdd_def
  by (auto elim!: Run_letE Run_bindE)

lemma CapAdd_CapIsSealed_iff[simp]:
  assumes "Run (CapAdd c increment) t c'"
  shows "CapIsSealed c' \<longleftrightarrow> CapIsSealed c"
  using assms
  by (auto simp: CapIsSealed_def CapAdd_GetObjectType_eq)

lemma CapAdd__1_CapIsSealed_iff[simp]:
  assumes "Run (CapAdd__1 c increment) t c'"
  shows "CapIsSealed c' \<longleftrightarrow> CapIsSealed c"
  using assms
  by (auto simp: CapAdd__1_def)

lemma Run_CapAdd_tag_imp:
  assumes "Run (CapAdd c offset) t c'"
    and "c' !! 128"
  shows "c !! 128"
  using assms
  unfolding CapAdd_def CAP_VALUE_HI_BIT_def CAP_VALUE_LO_BIT_def
  by (auto simp: test_bit_set update_subrange_vec_dec_test_bit
           elim!: Run_bindE Run_letE split: if_splits)

(*lemma no_Run_EndOfInstruction[simp]:
  "Run (EndOfInstruction u) t a \<longleftrightarrow> False"
  by (auto simp: EndOfInstruction_def)

lemma no_Run_AArch64_TakeException[simp]:
  "Run (AArch64_TakeException target_el exception preferred_exception_return vect_offset) t a \<longleftrightarrow> False"
  unfolding AArch64_TakeException_def bind_assoc
  by (auto elim!: Run_bindE)

lemma no_Run_AArch64_DataAbort[simp]:
  "Run (AArch64_DataAbort vaddress fault) t a \<longleftrightarrow> False"
  by (auto simp: AArch64_DataAbort_def elim!: Run_bindE Run_ifE)

lemma no_Run_AArch64_InstructionAbort[simp]:
  "Run (AArch64_InstructionAbort vaddress fault) t a \<longleftrightarrow> False"
  by (auto simp: AArch64_InstructionAbort_def elim!: Run_bindE Run_ifE)

lemma no_Run_AArch64_WatchpointException[simp]:
  "Run (AArch64_WatchpointException vaddress fault) t a \<longleftrightarrow> False"
  by (auto simp: AArch64_WatchpointException_def elim!: Run_bindE Run_ifE)

lemma no_Run_AArch64_BreakpointException[simp]:
  "Run (AArch64_BreakpointException fault) t a \<longleftrightarrow> False"
  by (auto simp: AArch64_BreakpointException_def elim!: Run_bindE Run_ifE)

lemma no_Run_AArch64_Abort[simp]:
  "Run (AArch64_Abort vaddress fault) t a \<longleftrightarrow> False"
  by (auto simp: AArch64_Abort_def elim!: Run_bindE Run_ifE)

lemma no_Run_AArch64_SystemAccessTrap[simp]:
  "Run (AArch64_SystemAccessTrap target_el ec) t a \<longleftrightarrow> False"
  by (auto simp: AArch64_SystemAccessTrap_def elim!: Run_bindE Run_ifE)

lemma no_Run_CapabilityAccessTrap[simp]:
  "Run (CapabilityAccessTrap target_el) t a \<longleftrightarrow> False"
  by (auto simp: CapabilityAccessTrap_def elim!: Run_bindE Run_ifE)

lemma no_Run_Unreachable[simp]:
  "Run (Unreachable u) t a \<longleftrightarrow> False"
  by (auto simp: Unreachable_def elim!: Run_bindE)*)

lemma EL_exhaust_disj:
  fixes el :: "2 word"
  shows "el = EL0 \<or> el = EL1 \<or> el = EL2 \<or> el = EL3"
  by (cases el rule: exhaustive_2_word) (auto simp: EL0_def EL1_def EL2_def EL3_def)

lemma unat_paddress_plus_distrib[simp]:
  fixes w :: "48 word"
  assumes offset: "unat offset < 2^63"
  shows "unat (ucast w + offset :: 64 word) = unat w + unat offset"
proof -
  have "unat w + unat offset < 2^64"
    using add_strict_mono[OF unat_lt2p[of w] offset]
    by auto
  then show ?thesis
    by (auto simp: unat_plus_if_size)
qed

lemmas datatype_splits =
  ArchVersion.split Constraint.split Unpredictable.split Exception.split InstrEnc.split
  BranchType.split Fault.split AccType.split DeviceType.split MemType.split InstrSet.split
  GTEParamType.split PrivilegeLevel.split MBReqDomain.split MBReqTypes.split PrefetchHint.split
  FPExc.split FPRounding.split FPType.split SysRegAccess.split OpType.split TimeStamp.split
  CountOp.split ExtendType.split FPMaxMinOp.split FPUnaryOp.split FPConvOp.split
  MoveWideOp.split ShiftType.split LogicalOp.split MemOp.split MemAtomicOp.split
  MemBarrierOp.split SystemHintOp.split PSTATEField.split SystemOp.split VBitOp.split
  CompareOp.split ImmediateOp.split ReduceOp.split AsyncErrorType.split

section \<open>Capabilities\<close>

definition is_sentry :: "Capability \<Rightarrow> bool" where
  "is_sentry c \<equiv> CapGetObjectType c \<in> {CAP_SEAL_TYPE_RB, CAP_SEAL_TYPE_LPB, CAP_SEAL_TYPE_LB}"

definition get_base :: "Capability \<Rightarrow> nat" where
  "get_base c \<equiv> unat (THE b. \<exists>t. Run (CapGetBase c) t b)"

definition get_limit :: "Capability \<Rightarrow> nat" where
  "get_limit c \<equiv> unat (THE l. \<exists>t b v. Run (CapGetBounds c) t (l, b, v))"

definition get_perms :: "Capability \<Rightarrow> perms" where
  "get_perms c = to_bl (CapGetPermissions c)"

definition set_tag :: "Capability \<Rightarrow> bool \<Rightarrow> Capability" where
  "set_tag c tag = CapSetTag c (if tag then 1 else 0)"

definition seal :: "Capability \<Rightarrow> nat \<Rightarrow> Capability" where
  "seal c obj_type = CapSetObjectType c (of_nat obj_type)"

definition cap_of_mem_bytes :: "memory_byte list \<Rightarrow> bitU \<Rightarrow> Capability option" where
  "cap_of_mem_bytes bytes tag =
     do {
       (bytes' :: 128 word) \<leftarrow> vec_of_bits_maybe (bits_of_mem_bytes bytes);
       (tag' :: bool) \<leftarrow> bool_of_bitU tag;
       let (tag'' :: 1 word) = of_bl [tag'];
       Some (word_cat tag'' bytes')
     }"

abbreviation "cap_permits p c \<equiv> CapCheckPermissions c p"

abbreviation "clear_perm p c \<equiv> CapClearPerms c p"

definition "CC \<equiv>
  \<lparr>is_tagged_method = CapIsTagSet,
   is_sealed_method = CapIsSealed,
   is_sentry_method = is_sentry,
   get_base_method = get_base,
   get_top_method = get_limit,
   get_obj_type_method = (\<lambda>c. unat (CapGetObjectType c)),
   get_perms_method = get_perms,
   get_cursor_method = (\<lambda>c. unat (CapGetValue c)),
   is_global_method = (\<lambda>c. \<not>(CapIsLocal c)),
   set_tag_method = set_tag,
   seal_method = seal,
   unseal_method = CapUnseal,
   clear_global_method = (clear_perm CAP_PERM_GLOBAL),
   cap_of_mem_bytes_method = cap_of_mem_bytes,
   permits_execute_method = CapIsExecutePermitted,
   permits_ccall_method = (cap_permits CAP_PERM_BRANCH_SEALED_PAIR),
   permits_load_method = (cap_permits CAP_PERM_LOAD),
   permits_load_cap_method = (cap_permits CAP_PERM_LOAD_CAP),
   permits_seal_method = (cap_permits CAP_PERM_SEAL),
   permits_store_method = (cap_permits CAP_PERM_STORE),
   permits_store_cap_method = (cap_permits CAP_PERM_STORE_CAP),
   permits_store_local_cap_method = (cap_permits CAP_PERM_STORE_LOCAL),
   permits_system_access_method = CapIsSystemAccessPermitted,
   permits_unseal_method = (cap_permits CAP_PERM_UNSEAL)\<rparr>"

interpretation Capabilities CC
proof
  fix c tag
  show "is_tagged_method CC (set_tag_method CC c tag) = tag"
    by (auto simp: CC_def set_tag_def test_bit_set)
next
  fix c obj_type
  show "is_tagged_method CC (seal_method CC c obj_type) = is_tagged_method CC c"
    by (auto simp: CC_def seal_def)
next
  fix c bytes tag
  have test_128_128: "w !! 128 \<longleftrightarrow> False" for w :: "128 word"
    by (auto dest: test_bit_len)
  assume "cap_of_mem_bytes_method CC bytes tag = Some c"
  then show "is_tagged_method CC c = (tag = B1)"
    by (cases tag)
       (auto simp: CC_def cap_of_mem_bytes_def bind_eq_Some_conv nth_ucast test_bit_cat test_128_128)
qed

lemma CC_simps[simp]:
  "is_tagged_method CC c = CapIsTagSet c"
  "is_sealed_method CC c = CapIsSealed c"
  "is_sentry_method CC c = is_sentry c"
  "seal_method CC c otype = seal c otype"
  "unseal_method CC c = CapUnseal c"
  "get_cursor_method CC c = unat (CapGetValue c)"
  "get_base_method CC c = get_base c"
  "get_top_method CC c = get_limit c"
  "get_obj_type_method CC c = unat (CapGetObjectType c)"
  "cap_of_mem_bytes_method CC = cap_of_mem_bytes"
  "permits_execute_method CC c = cap_permits CAP_PERM_EXECUTE c"
  "permits_unseal_method CC c = cap_permits CAP_PERM_UNSEAL c"
  "permits_ccall_method CC c = cap_permits CAP_PERM_BRANCH_SEALED_PAIR c"
  "get_perms_method CC c = to_bl (CapGetPermissions c)"
  "is_global_method CC c = cap_permits CAP_PERM_GLOBAL c"
  "clear_global_method CC c = clear_perm CAP_PERM_GLOBAL c"
  by (auto simp: CC_def CapIsExecutePermitted_def get_perms_def CapIsLocal_def)

lemma cap_of_mem_bytes_of_word_Capability_of_tag_word:
  fixes data :: "'a::len word"
  assumes "LENGTH('a) = 128"
  shows "cap_of_mem_bytes (mem_bytes_of_word data) (bitU_of_bool tag) = Some (Capability_of_tag_word tag (ucast data))"
  unfolding Capability_of_tag_word_def cap_of_mem_bytes_def
  by (auto simp: bind_eq_Some_conv bits_of_mem_bytes_of_word_to_bl ucast_bl)

lemma cap_of_mem_bytes_of_word_B1_Capability_of_tag_word:
  fixes data :: "'a::len word"
  assumes "LENGTH('a) = 128"
  shows "cap_of_mem_bytes (mem_bytes_of_word data) B1 = Some (Capability_of_tag_word True (ucast data))"
  using cap_of_mem_bytes_of_word_Capability_of_tag_word[of data True, OF assms]
  by (auto simp: CC_def)

lemma CapGetBounds_get_base:
  assumes "Run (CapGetBounds c) t (base, limit, valid)"
  shows "get_base c = unat base"
  using assms
  apply (auto simp: CC_def get_base_def)
  apply (rule theI2) thm theI2
    apply auto
  thm CapGetBounds_def CapGetTop_def
  sorry

lemma CapGetBounds_get_limit:
  assumes "Run (CapGetBounds c) t (base, limit, valid)"
  shows "get_limit c = unat limit"
  sorry

lemma CapIsBaseAboveLimit_get_base_leq_get_limit:
  assumes "Run (CapIsBaseAboveLimit c) t a"
  shows "get_base c \<le> get_limit c \<longleftrightarrow> \<not>a"
  using assms
  unfolding CapIsBaseAboveLimit_def
  by (auto simp: CapGetBounds_get_base CapGetBounds_get_limit un_ui_le un_ui_lt elim!: Run_bindE)

lemma CapUnseal_get_bounds_helpers_eq:
  "CapGetExponent (CapUnseal c) = CapGetExponent c"
  "CapGetBottom (CapUnseal c) = CapGetBottom c"
  "CapGetTop (CapUnseal c) = CapGetTop c"
  "CapGetValue (CapUnseal c) = CapGetValue c"
  unfolding CapGetExponent_def CapGetBottom_def CapGetTop_def CapGetValue_def
  unfolding CapUnseal_def CapIsInternalExponent_def CapSetObjectType_def
  by (auto simp add: update_subrange_vec_dec_test_bit slice_update_subrange_vec_dec_above
           simp del: slice_zero)

lemma CapGetBounds_CapUnseal_eq:
  shows "CapGetBounds (CapUnseal c) = CapGetBounds c"
  unfolding CapGetBounds_def CapIsExponentOutOfRange_def CapUnseal_get_bounds_helpers_eq
  ..

lemma CapGetPermissions_CapUnseal_eq:
  "CapGetPermissions (CapUnseal c) = CapGetPermissions c"
  unfolding CapGetPermissions_def CapUnseal_def CapSetObjectType_def
  unfolding CAP_OTYPE_LO_BIT_def CAP_OTYPE_HI_BIT_def CAP_PERMS_LO_BIT_def
  by (auto simp: slice_update_subrange_vec_dec_below)

lemma CapIsSubSetOf_CapUnseal_eq:
  "CapIsSubSetOf (CapUnseal c) c' = CapIsSubSetOf c c'"
  "CapIsSubSetOf c (CapUnseal c') = CapIsSubSetOf c c'"
  unfolding CapIsSubSetOf_def CapGetBounds_CapUnseal_eq CapGetPermissions_CapUnseal_eq
  by blast+

lemma get_bounds_CapUnseal_eq:
  "get_base (CapUnseal c) = get_base c"
  "get_limit (CapUnseal c) = get_limit c"
  unfolding get_base_def CapGetBase_def get_limit_def CapGetBounds_CapUnseal_eq
  by auto

lemma CapWithTagSet_get_bounds_helpers_eq:
  "CapGetExponent (CapWithTagSet c) = CapGetExponent c"
  "CapGetBottom (CapWithTagSet c) = CapGetBottom c"
  "CapGetTop (CapWithTagSet c) = CapGetTop c"
  "CapGetValue (CapWithTagSet c) = CapGetValue c"
  unfolding CapGetExponent_def CapGetBottom_def CapGetTop_def CapGetValue_def
  unfolding CapWithTagSet_def CapIsInternalExponent_def CapSetObjectType_def
  by (auto simp add: test_bit_set_gen slice_set_bit_above simp del: slice_zero)

lemma CapGetBounds_CapWithTagSet_eq:
  shows "CapGetBounds (CapWithTagSet c) = CapGetBounds c"
  unfolding CapGetBounds_def CapIsExponentOutOfRange_def CapWithTagSet_get_bounds_helpers_eq
  ..

lemma get_bounds_CapWithTagSet_eq:
  "get_base (CapWithTagSet c) = get_base c"
  "get_limit (CapWithTagSet c) = get_limit c"
  unfolding get_base_def CapGetBase_def get_limit_def CapGetBounds_CapWithTagSet_eq
  by auto

lemma CapClearPerms_get_bounds_helpers_eq:
  "CapGetExponent (CapClearPerms c perms) = CapGetExponent c"
  "CapGetBottom (CapClearPerms c perms) = CapGetBottom c"
  "CapGetTop (CapClearPerms c perms) = CapGetTop c"
  "CapGetValue (CapClearPerms c perms) = CapGetValue c"
  unfolding CapGetExponent_def CapGetBottom_def CapGetTop_def CapGetValue_def
  unfolding CapClearPerms_def CapIsInternalExponent_def CapSetObjectType_def
  by (auto simp add: update_subrange_vec_dec_test_bit slice_update_subrange_vec_dec_above
           simp del: slice_zero)

lemma CapGetBounds_CapClearPerms_eq:
  shows "CapGetBounds (CapClearPerms c perms) = CapGetBounds c"
  unfolding CapGetBounds_def CapIsExponentOutOfRange_def CapClearPerms_get_bounds_helpers_eq
  ..

lemma get_bounds_CapClearPerms_eq:
  "get_base (CapClearPerms c perms) = get_base c"
  "get_limit (CapClearPerms c perms) = get_limit c"
  unfolding get_base_def CapGetBase_def get_limit_def CapGetBounds_CapClearPerms_eq
  by auto

section \<open>Architecture abstraction\<close>

type_synonym instr = "(InstrEnc * 32 word)"

text \<open>TODO: Split up toplevel fetch-decode-execute function and use here.\<close>

definition instr_sem :: "instr \<Rightarrow> unit M" where
  "instr_sem instr = (case instr of (enc, opcode) \<Rightarrow> DecodeExecute enc opcode)"

definition instr_fetch :: "instr M" where
  "instr_fetch \<equiv> do {
     (pc :: 64 word) \<leftarrow> ThisInstrAddr 64;
     FetchInstr pc
   }"

fun caps_of_regval :: "register_value \<Rightarrow> Capability set" where
  "caps_of_regval (Regval_bitvector_129_dec c) = {c}"
| "caps_of_regval _ = {}"

text \<open>Over-approximation of invoked caps: all capabilities written to PCC.
TODO: Restrict to branching instructions and caps that result from unsealing caps in source registers.\<close>

definition invokes_caps :: "instr \<Rightarrow> register_value trace \<Rightarrow> Capability set" where
  "invokes_caps instr t = {c. E_write_reg ''PCC'' (Regval_bitvector_129_dec c) \<in> set t}"

definition instr_raises_ex :: "instr \<Rightarrow> register_value trace \<Rightarrow> bool" where
  "instr_raises_ex instr t \<equiv> hasException t (instr_sem instr)"

definition fetch_raises_ex :: "register_value trace \<Rightarrow> bool" where
  "fetch_raises_ex t \<equiv> hasException t instr_fetch"

definition exception_targets :: "register_value set \<Rightarrow> Capability set" where
  "exception_targets rvs \<equiv> \<Union>(caps_of_regval ` rvs)"

fun acctype_of_AccType :: "AccType \<Rightarrow> bool \<Rightarrow> acctype" where
  "acctype_of_AccType AccType_PTW _ = PTW"
| "acctype_of_AccType AccType_IFETCH _ = Fetch"
| "acctype_of_AccType _ True = Store"
| "acctype_of_AccType _ False = Load"

fun atomic_AccType :: "AccType \<Rightarrow> bool" where
  "atomic_AccType AccType_ATOMIC = True"
| "atomic_AccType AccType_ATOMICRW = True"
| "atomic_AccType AccType_ORDEREDATOMIC = True"
| "atomic_AccType AccType_ORDEREDATOMICRW = True"
| "atomic_AccType _ = False"

fun is_mem_event :: "'regval event \<Rightarrow> bool" where
  "is_mem_event (E_read_memt _ _ _ _) = True"
| "is_mem_event (E_read_mem _ _ _ _) = True"
| "is_mem_event (E_write_memt _ _ _ _ _ _) = True"
| "is_mem_event (E_write_mem _ _ _ _ _) = True"
| "is_mem_event _ = False"

locale Morello_ISA =
  fixes translate_address :: "nat \<Rightarrow> acctype \<Rightarrow> register_value trace \<Rightarrow> nat option"
    and is_translation_event :: "register_value event \<Rightarrow> bool"
  assumes no_cap_load_translation_events: "\<And>rk addr sz data. \<not>is_translation_event (E_read_memt rk addr sz data)"
begin

definition "ISA \<equiv>
  \<lparr>isa.instr_sem = instr_sem,
   isa.instr_fetch = instr_fetch,
   tag_granule = 16,
   PCC = {''PCC''},
   KCC = {''VBAR_EL1'', ''VBAR_EL2'', ''VBAR_EL3''},
   IDC = {''_R29''},
   isa.caps_of_regval = caps_of_regval,
   isa.invokes_caps = invokes_caps,
   isa.instr_raises_ex = instr_raises_ex,
   isa.fetch_raises_ex = fetch_raises_ex,
   isa.exception_targets = exception_targets,
   privileged_regs = {''VBAR_EL1'', ''VBAR_EL2'', ''VBAR_EL3''}, \<comment> \<open>TODO\<close>
   isa.is_translation_event = is_translation_event,
   isa.translate_address = translate_address\<rparr>"

sublocale Capability_ISA CC ISA ..

lemma ISA_simps[simp]:
  "PCC ISA = {''PCC''}"
  "KCC ISA = {''VBAR_EL1'', ''VBAR_EL2'', ''VBAR_EL3''}"
  "IDC ISA = {''_R29''}"
  "privileged_regs ISA = {''VBAR_EL1'', ''VBAR_EL2'', ''VBAR_EL3''}"
  "isa.instr_sem ISA = instr_sem"
  "isa.instr_fetch ISA = instr_fetch"
  "isa.caps_of_regval ISA = caps_of_regval"
  "isa.is_translation_event ISA = is_translation_event"
  by (auto simp: ISA_def)

lemma no_cap_regvals[simp]:
  "\<And>v. GTEParamType_of_regval rv = Some v \<Longrightarrow> caps_of_regval rv = {}"
  "\<And>v. PCSample_of_regval rv = Some v \<Longrightarrow> caps_of_regval rv = {}"
  "\<And>v. ProcState_of_regval rv = Some v \<Longrightarrow> caps_of_regval rv = {}"
  "\<And>v. TLBLine_of_regval rv = Some v \<Longrightarrow> caps_of_regval rv = {}"
  "\<And>v. InstrEnc_of_regval rv = Some v \<Longrightarrow> caps_of_regval rv = {}"
  "\<And>v. bit_of_regval rv = Some v \<Longrightarrow> caps_of_regval rv = {}"
  "\<And>v. bitvector_11_dec_of_regval rv = Some v \<Longrightarrow> caps_of_regval rv = {}"
  "\<And>v. bitvector_128_dec_of_regval rv = Some v \<Longrightarrow> caps_of_regval rv = {}"
  "\<And>v. bitvector_16_dec_of_regval rv = Some v \<Longrightarrow> caps_of_regval rv = {}"
  "\<And>v. bitvector_1_dec_of_regval rv = Some v \<Longrightarrow> caps_of_regval rv = {}"
  "\<And>v. bitvector_2_dec_of_regval rv = Some v \<Longrightarrow> caps_of_regval rv = {}"
  "\<And>v. bitvector_32_dec_of_regval rv = Some v \<Longrightarrow> caps_of_regval rv = {}"
  "\<And>v. bitvector_4_dec_of_regval rv = Some v \<Longrightarrow> caps_of_regval rv = {}"
  "\<And>v. bitvector_48_dec_of_regval rv = Some v \<Longrightarrow> caps_of_regval rv = {}"
  "\<And>v. bitvector_63_dec_of_regval rv = Some v \<Longrightarrow> caps_of_regval rv = {}"
  "\<And>v. bitvector_64_dec_of_regval rv = Some v \<Longrightarrow> caps_of_regval rv = {}"
  "\<And>v. bool_of_regval rv = Some v \<Longrightarrow> caps_of_regval rv = {}"
  "\<And>v. int_of_regval rv = Some v \<Longrightarrow> caps_of_regval rv = {}"
  "\<And>v. signal_of_regval rv = Some v \<Longrightarrow> caps_of_regval rv = {}"
  "\<And>xs. vector_of_regval of_rv rv = Some xs \<Longrightarrow> caps_of_regval rv = {}"
  "\<And>xs. caps_of_regval (regval_of_vector rv_of xs) = {}"
  "\<And>v. option_of_regval of_rv rv = Some v \<Longrightarrow> caps_of_regval rv = {}"
  "\<And>v. caps_of_regval (regval_of_option rv_of v) = {}"
  by (cases rv; auto simp: vector_of_regval_def regval_of_vector_def option_of_regval_def regval_of_option_def)+

lemma caps_of_regval_of_bitvector_129[simp]:
  "caps_of_regval (regval_of_bitvector_129_dec c) = {c}"
  by (auto simp: regval_of_bitvector_129_dec_def)

lemma bitvector_129_Some_iff[simp]:
  "bitvector_129_dec_of_regval rv = Some c \<longleftrightarrow> rv = Regval_bitvector_129_dec c"
  by (cases rv) auto

end

locale Morello_Fixed_Address_Translation =
  fixes translate_address :: "nat \<Rightarrow> nat option"
    and is_translation_event :: "register_value event \<Rightarrow> bool"
    and translation_assms :: "register_value event \<Rightarrow> bool"
  assumes translate_correct:
      "\<And>vaddress acctype iswrite wasaligned size iswritevalidcap addrdesc.
          Run (AArch64_TranslateAddressWithTag vaddress acctype iswrite wasaligned size iswritevalidcap) t addrdesc \<Longrightarrow>
          FaultRecord_statuscode (AddressDescriptor_fault addrdesc) = Fault_None \<Longrightarrow>
          \<forall>e \<in> set t. translation_assms e \<Longrightarrow>
          translate_address (unat vaddress) =
            Some (unat (FullAddress_address (AddressDescriptor_paddress addrdesc)))"
    and is_translation_event_correct:
      "\<And>vaddress acctype iswrite wasaligned size iswritevalidcap addrdesc e.
          Run (AArch64_TranslateAddressWithTag vaddress acctype iswrite wasaligned size iswritevalidcap) t addrdesc \<Longrightarrow>
          \<forall>e' \<in> set t. translation_assms e' \<Longrightarrow>
          e \<in> set t \<Longrightarrow> is_mem_event e \<Longrightarrow>
          is_translation_event e"
    and no_cap_load_translation_events: "\<And>rk addr sz data. \<not>is_translation_event (E_read_memt rk addr sz data)"
begin

sublocale Morello_ISA where translate_address = "\<lambda>addr _ _. translate_address addr"
  using no_cap_load_translation_events
  by unfold_locales auto

sublocale Capability_ISA_Fixed_Translation CC ISA translation_assms
  by unfold_locales (auto simp: ISA_def)

end

text \<open>Instantiation of translate_address for version of spec with translation stubs\<close>

definition translate_address :: "nat \<Rightarrow> nat option" where
  "translate_address addr \<equiv> Some (addr mod 2^48)"

lemmas TranslateAddress_defs =
  AArch64_TranslateAddress_def AArch64_TranslateAddressWithTag_def AArch64_FullTranslateWithTag_def
  AArch64_FirstStageTranslateWithTag_def AArch64_SecondStageTranslate_def
  translate_address_def

(*lemma unat64_and_mask52_mod: "unat ((w :: 64 word) AND mask 52) = unat w mod 2^52"
  by (auto simp: and_mask_bintr unat_def uint_word_of_int bintrunc_mod2p nat_mod_distrib)

lemma unat32_and_mask52_eq: "unat (w :: 32 word) mod 4503599627370496 = unat w"
  using unat_lt2p[of w]
  by auto*)


interpretation Morello_Fixed_Address_Translation
  where translate_address = translate_address
    and is_translation_event = "\<lambda>_. False"
    and translation_assms = "\<lambda>_. True"
  apply unfold_locales
     (* apply (auto simp: TranslateAddress_defs return_def unat64_and_mask52_mod elim!: Run_bindE Run_ifE)[] *)
  (* apply (auto simp: TranslateAddress_defs return_def unat32_and_mask52_eq elim!: Run_bindE Run_ifE)[] *)
  (* TODO: Show that translation stubs are non_mem_exp's *)
  oops

section \<open>Verification framework\<close>

locale Morello_Axiom_Automaton = Morello_ISA + Cap_Axiom_Automaton CC ISA enabled
  for enabled :: "(Capability, register_value) axiom_state \<Rightarrow> register_value event \<Rightarrow> bool"
begin

lemmas privilegeds_accessible_system_reg_access[intro] =
  privileged_accessible_system_reg_access[where r = "''VBAR_EL1''", simplified]
  privileged_accessible_system_reg_access[where r = "''VBAR_EL2''", simplified]
  privileged_accessible_system_reg_access[where r = "''VBAR_EL3''", simplified]

lemma non_cap_exp_undefined_bitvector[non_cap_expI]:
  "non_cap_exp (undefined_bitvector n)"
  by (auto simp add: undefined_bitvector_def simp del: repeat.simps intro: non_cap_expI)

lemma non_cap_exp_undefined_bits[non_cap_expI]:
  "non_cap_exp (undefined_bits n)"
  by (unfold undefined_bits_def, non_cap_expI)

lemma non_cap_exp_undefined_bit[non_cap_expI]:
  "non_cap_exp (undefined_bit u)"
  by (unfold undefined_bit_def, non_cap_expI)

lemma non_cap_exp_undefined_string[non_cap_expI]:
  "non_cap_exp (undefined_string u)"
  by (unfold undefined_string_def, non_cap_expI)

lemma non_cap_exp_undefined_unit[non_cap_expI]:
  "non_cap_exp (undefined_unit u)"
  by (unfold undefined_unit_def, non_cap_expI)

lemma non_cap_exp_undefined_vector[non_cap_expI]:
  "non_cap_exp (undefined_vector len v)"
  by (auto simp add: undefined_vector_def simp del: repeat.simps intro: non_cap_expI)

lemma non_cap_exp_undefined_int[non_cap_expI]:
  "non_cap_exp (undefined_int u)"
  by (unfold undefined_int_def, non_cap_expI)

lemma non_cap_exp_undefined_nat[non_cap_expI]:
  "non_cap_exp (undefined_nat u)"
  by (unfold undefined_nat_def, non_cap_expI)

lemma non_cap_exp_undefined_real[non_cap_expI]:
  "non_cap_exp (undefined_real u)"
  by (unfold undefined_real_def, non_cap_expI)

lemma non_cap_exp_undefined_range[non_cap_expI]:
  "non_cap_exp (undefined_range i j)"
  by (unfold undefined_range_def, non_cap_expI)

lemma non_cap_exp_undefined_atom[non_cap_expI]:
  "non_cap_exp (undefined_atom i)"
  by (unfold undefined_atom_def, non_cap_expI)

lemma no_reg_writes_to_undefined_bitvector[no_reg_writes_toI, simp]:
  "no_reg_writes_to Rs (undefined_bitvector n)"
  by (unfold undefined_bitvector_def, no_reg_writes_toI)

lemma no_reg_writes_to_undefined_bits[no_reg_writes_toI, simp]:
  "no_reg_writes_to Rs (undefined_bits n)"
  by (unfold undefined_bits_def, no_reg_writes_toI)

lemma no_reg_writes_to_undefined_bit[no_reg_writes_toI, simp]:
  "no_reg_writes_to Rs (undefined_bit u)"
  by (unfold undefined_bit_def, no_reg_writes_toI)

lemma no_reg_writes_to_undefined_string[no_reg_writes_toI, simp]:
  "no_reg_writes_to Rs (undefined_string u)"
  by (unfold undefined_string_def, no_reg_writes_toI)

lemma no_reg_writes_to_undefined_unit[no_reg_writes_toI, simp]:
  "no_reg_writes_to Rs (undefined_unit u)"
  by (unfold undefined_unit_def, no_reg_writes_toI)

lemma no_reg_writes_to_undefined_vector[no_reg_writes_toI, simp]:
  "no_reg_writes_to Rs (undefined_vector len v)"
  by (unfold undefined_vector_def, no_reg_writes_toI)

lemma no_reg_writes_to_undefined_int[no_reg_writes_toI, simp]:
  "no_reg_writes_to Rs (undefined_int u)"
  by (unfold undefined_int_def, no_reg_writes_toI)

lemma no_reg_writes_to_undefined_nat[no_reg_writes_toI, simp]:
  "no_reg_writes_to Rs (undefined_nat u)"
  by (unfold undefined_nat_def, no_reg_writes_toI)

lemma no_reg_writes_to_undefined_real[no_reg_writes_toI, simp]:
  "no_reg_writes_to Rs (undefined_real u)"
  by (unfold undefined_real_def, no_reg_writes_toI)

lemma no_reg_writes_to_undefined_range[no_reg_writes_toI, simp]:
  "no_reg_writes_to Rs (undefined_range i j)"
  by (unfold undefined_range_def, no_reg_writes_toI)

lemma no_reg_writes_to_undefined_atom[no_reg_writes_toI, simp]:
  "no_reg_writes_to Rs (undefined_atom n)"
  by (unfold undefined_atom_def, no_reg_writes_toI)

declare datatype_splits[split]
declare datatype_splits[where P = "non_cap_exp", non_cap_exp_split]
declare datatype_splits[where P = "non_mem_exp", non_mem_exp_split]
declare datatype_splits[where P = "no_reg_writes_to Rs" for Rs, THEN iffD2, no_reg_writes_toI]
declare datatype_splits[where P = "runs_no_reg_writes_to Rs" for Rs, THEN iffD2, runs_no_reg_writes_toI]

lemma CapNull_derivable[simp, intro, derivable_capsI]:
  "CapNull u \<in> derivable_caps s"
  by (auto simp: derivable_caps_def CapNull_def Zeros_def zeros_def)

lemma CapWithTagClear_derivable[intro, simp, derivable_capsI]:
  "CapWithTagClear c \<in> derivable_caps s"
  by (auto simp: derivable_caps_def)

lemma CapWithTagSet_bounds_eq[simp]:
  "get_base (CapWithTagSet c) = get_base c"
  "get_limit (CapWithTagSet c) = get_limit c"
  unfolding get_base_def get_limit_def CapGetBase_def CapGetBounds_CapWithTagSet_eq
  by auto

lemma CapGetPermissions_CapWithTagSet_eq[simp]:
  "CapGetPermissions (CapWithTagSet c) = CapGetPermissions c"
  unfolding CapGetPermissions_def CapWithTagSet_def
  by (intro word_eqI) (auto simp: nth_slice test_bit_set_gen)

lemma cap_permits_CapWithTagSet_iff[simp]:
  "cap_permits perms (CapWithTagSet c) \<longleftrightarrow> cap_permits perms c"
  by (auto simp: CapCheckPermissions_def)

lemma CapGetObjectType_CapWithTagSet_eq[simp]:
  "CapGetObjectType (CapWithTagSet c) = CapGetObjectType c"
  unfolding CapGetObjectType_def CapWithTagSet_def CapGetObjectType_def
  by (intro word_eqI) (auto simp: word_ao_nth nth_slice test_bit_set_gen)

lemma CapIsSealed_CapWithTagSet_iff[simp]:
  "CapIsSealed (CapWithTagSet c) \<longleftrightarrow> CapIsSealed c"
  unfolding CapIsSealed_def
  by auto

lemma CapGetObjectType_CapSetFlags_eq[simp]:
  "CapGetObjectType (CapSetFlags c flags) = CapGetObjectType c"
  by (intro word_eqI)
     (auto simp: CapGetObjectType_def CapSetFlags_def word_ao_nth slice_update_subrange_vec_dec_below)

lemma CapIsSealed_CapSetFlags_iff[simp]:
  "CapIsSealed (CapSetFlags c flags) = CapIsSealed c"
  by (auto simp: CapIsSealed_def)

lemma Run_BranchAddr_not_CapIsSealed_if:
  assumes "Run (BranchAddr c el) t c'"
    and "CapIsTagSet c'" and "CapIsTagSet c \<longrightarrow> \<not>CapIsSealed c"
  shows "\<not>CapIsSealed c'"
  using assms
  unfolding BranchAddr_def
  by (auto elim!: Run_bindE Run_letE Run_ifE split: if_splits)

lemma CapGetObjectType_set_bit_0_eq[simp]:
  "CapGetObjectType (set_bit c 0 b) = CapGetObjectType c"
  by (intro word_eqI)
     (auto simp: CapGetObjectType_def word_ao_nth nth_slice test_bit_set_gen)

lemma CapIsSealed_set_bit_0_iff[simp]:
  "CapIsSealed (set_bit c 0 b) = CapIsSealed c"
  by (auto simp: CapIsSealed_def)

lemma leq_perms_cap_permits_imp:
  assumes "leq_perms (to_bl (CapGetPermissions c)) (to_bl (CapGetPermissions c'))"
    and "cap_permits perms c"
  shows "cap_permits perms c'"
  using assms
  by (auto simp: CapCheckPermissions_def word_eq_iff word_ops_nth_size nth_ucast leq_perms_to_bl_iff)

lemma leq_bounds_set_0th:
  "leq_bounds CC (set_bit c 0 b) c"
  sorry

lemma leq_bounds_CapSetFlags:
  "leq_bounds CC (CapSetFlags c flags) c"
  sorry

lemma leq_cap_set_0th:
  "CapIsTagSet c \<longrightarrow> \<not>CapIsSealed c \<Longrightarrow> leq_cap CC (set_bit c 0 b) c"
  using leq_perms_cap_permits_imp[rotated]
  by (auto simp: leq_cap_def test_bit_set_gen leq_bounds_set_0th)

lemma leq_cap_CapSetFlags:
  "CapIsTagSet c \<longrightarrow> \<not>CapIsSealed c \<Longrightarrow> leq_cap CC (CapSetFlags c flags) c"
  using leq_perms_cap_permits_imp[rotated]
  by (auto simp: leq_cap_def leq_bounds_CapSetFlags)

lemma Capability_of_tag_word_False_derivable[intro, simp, derivable_capsI]:
  "Capability_of_tag_word False data \<in> derivable_caps s"
  by (auto simp: derivable_caps_def)

lemma CapSetFlags_derivable[derivable_capsI]:
  assumes "c \<in> derivable_caps s" and "CapIsTagSet c \<longrightarrow> \<not>CapIsSealed c"
  shows "CapSetFlags c flags \<in> derivable_caps s"
  thm CapSetFlags_def
  sorry

lemma clear_perm_derivable[derivable_capsI]:
  assumes "c \<in> derivable_caps s" and "CapIsTagSet c \<longrightarrow> \<not>CapIsSealed c"
  shows "clear_perm perms c \<in> derivable_caps s"
    (is "?c' \<in> derivable_caps s")
proof -
  have perms: "leq_perms (to_bl (CapGetPermissions (clear_perm perms c))) (to_bl (CapGetPermissions c))"
    unfolding leq_perms_def leq_bools_iff CapGetPermissions_def CapClearPerms_def
    by (auto simp: to_bl_nth nth_slice update_subrange_vec_dec_test_bit word_ops_nth_size)
  moreover have "cap_permits CAP_PERM_GLOBAL ?c' \<longrightarrow> cap_permits CAP_PERM_GLOBAL c"
    using perms
    by (auto simp: leq_perms_to_bl_iff CapCheckPermissions_def word_eq_iff word_ops_nth_size)
  moreover have tag: "CapIsTagSet ?c' \<longleftrightarrow> CapIsTagSet c"
    and "CapIsSealed ?c' \<longleftrightarrow> CapIsSealed c"
    unfolding CapClearPerms_def CapIsSealed_def CapGetObjectType_def
    by (auto simp: update_subrange_vec_dec_test_bit slice_update_subrange_vec_dec_above)
  ultimately have "leq_cap CC (clear_perm perms c) c"
    using assms(2)
    by (auto simp: leq_cap_def leq_bounds_def get_bounds_CapClearPerms_eq)
  from derivable.Restrict[OF _ this]
  show ?thesis
    using assms(1) tag
    by (auto simp: derivable_caps_def)
qed

lemma set_bit_0_derivable[derivable_capsI]:
  assumes "c \<in> derivable_caps s" and "CapIsTagSet c \<longrightarrow> \<not>CapIsSealed c"
  shows "update_vec_dec c 0 b \<in> derivable_caps s"
  (* TODO Changing the LSB should always be representable *)
  sorry

lemma subrange_vec_dec_128_derivable[derivable_capsI]:
  "c \<in> derivable_caps s \<Longrightarrow> subrange_vec_dec c 128 0 \<in> derivable_caps s"
  by auto

lemma update_subrange_addr_CapWithTagClear_derivable:
  fixes addr :: "64 word"
  shows "update_subrange_vec_dec (CapWithTagClear c) CAP_VALUE_HI_BIT CAP_VALUE_LO_BIT addr \<in> derivable_caps s"
  by (auto simp: derivable_caps_def update_subrange_vec_dec_test_bit)

lemma update_subrange_addr_CapIsRepresentable_derivable:
  assumes "Run (CapIsRepresentable c addr) t a" and "a"
    and "c \<in> derivable_caps s"
    and "CapIsTagSet c \<longrightarrow> \<not>CapIsSealed c"
  shows "update_subrange_vec_dec c CAP_VALUE_HI_BIT CAP_VALUE_LO_BIT addr \<in> derivable_caps s"
    (is "?c' \<in> derivable_caps s")
proof -
  have "get_base ?c' = get_base c" and "get_limit ?c' = get_limit c"
    using assms(1-2)
    unfolding CapIsRepresentable_def CapBoundsEqual_def
    by (auto simp: CapGetBounds_get_base CapGetBounds_get_limit elim!: Run_bindE)
  then have "leq_bounds CC ?c' c"
    by (auto simp: leq_bounds_def)
  moreover have tag: "CapIsTagSet ?c' \<longleftrightarrow> CapIsTagSet c"
    and perms: "CapGetPermissions ?c' = CapGetPermissions c"
    and "CapIsSealed ?c' \<longleftrightarrow> CapIsSealed c"
    unfolding CapIsSealed_def CapGetObjectType_def CapGetPermissions_def
    by (auto simp: update_subrange_vec_dec_test_bit slice_update_subrange_vec_dec_below)
  moreover have "cap_permits CAP_PERM_GLOBAL ?c' \<longleftrightarrow> cap_permits CAP_PERM_GLOBAL c"
    using perms
    by (auto simp: CapCheckPermissions_def)
  ultimately have "leq_cap CC ?c' c"
    using assms(4)
    unfolding derivable_caps_def
    by (auto simp: leq_cap_def)
  from derivable.Restrict[OF _ this]
  show ?thesis
    using assms(3) tag
    by (auto simp: derivable_caps_def)
qed

lemmas update_subrange_if_derivable =
  if_split[where P = "\<lambda>c. update_subrange_vec_dec c hi lo v \<in> derivable_caps s" for hi lo v s, THEN iffD2]

lemma update_subrange_addr_CapIsRepresentableFast_derivable:
  assumes "Run (CapIsRepresentableFast c incr) t a" and "a"
    and "c \<in> derivable_caps s"
    and "CapIsTagSet c \<longrightarrow> \<not>CapIsSealed c"
  shows "update_subrange_vec_dec c CAP_VALUE_HI_BIT CAP_VALUE_LO_BIT (add_vec (CapGetValue c) incr) \<in> derivable_caps s"
  sorry

lemma update_tag_bit_zero_derivable[derivable_capsI]:
  "update_vec_dec c CAP_TAG_BIT (Morello.Bit 0) \<in> derivable_caps s"
  by (auto simp: derivable_caps_def test_bit_set)

lemma ucast_derivable[intro, simp]:
  fixes w :: "'a::len word"
  assumes "LENGTH('a) < 128"
  shows "ucast w \<in> derivable_caps s"
  using assms
  by (auto simp: derivable_caps_def nth_ucast dest: test_bit_len)

lemma read_memt_derivable:
  assumes "Run (read_memt BC_mword BC_mword rk addr sz) t (data, tag)"
    and "tag' \<longleftrightarrow> tag = B1"
  shows "Capability_of_tag_word tag' data \<in> derivable_caps (run s t)"
proof cases
  assume "tag = B1"
  then show ?thesis
    using assms no_cap_load_translation_events
    unfolding read_memt_def maybe_fail_def Capability_of_tag_word_def
    by (auto simp: cap_of_mem_bytes_def bind_eq_Some_conv split: option.splits
             elim!: Run_bindE read_memt_bytes_derivable)
next
  assume "tag \<noteq> B1"
  then show ?thesis
    using assms
    by auto
qed

lemma ReadTaggedMem_single_derivable:
  assumes "Run (ReadTaggedMem desc 16 accdesc) t (tag, data)"
  shows "Capability_of_tag_word (tag !! 0) data \<in> derivable_caps (run s t)"
  using assms
  unfolding ReadTaggedMem_def
  by (auto simp: Bits_def elim!: Run_bindE Run_letE Run_ifE read_memt_derivable)

lemma ReadTaggedMem_lower_derivable:
  assumes "Run (ReadTaggedMem desc sz accdesc) t (tag, data :: 'a::len word)"
    and "LENGTH('a) = nat sz * 8" and "sz = 16 \<or> sz = 32"
  shows "Capability_of_tag_word (tag !! 0) (ucast data) \<in> derivable_caps (run s t)"
  using assms
  unfolding ReadTaggedMem_def
  by (auto simp add: Bits_def nth_ucast nth_word_cat
           elim!: Run_bindE Run_letE Run_ifE read_memt_derivable)

lemma ReadTaggedMem_upper_derivable:
  assumes "Run (ReadTaggedMem desc sz accdesc) t (tag :: 2 word, data :: 256 word)"
    and "sz = 32"
  shows "Capability_of_tag_word (tag !! Suc 0) (Word.slice 128 data) \<in> derivable_caps (run s t)"
  using assms
  unfolding ReadTaggedMem_def
  by (auto simp add: Bits_def nth_ucast nth_word_cat slice_128_cat_cap_pair
           elim!: Run_bindE Run_letE Run_ifE read_memt_derivable[THEN derivable_caps_run_imp])

lemma ReadTaggedMem_lower_prod_derivable[derivable_capsE]:
  assumes "Run (ReadTaggedMem desc sz accdesc) t a"
    and "LENGTH('a) = nat sz * 8" and "sz = 16 \<or> sz = 32"
  shows "Capability_of_tag_word (vec_of_bits [access_vec_dec (fst a) 0] !! 0) (slice (snd a :: 'a::len word) 0 128) \<in> derivable_caps (run s t)"
  using assms
  by (cases a) (auto simp: test_bit_of_bl elim: ReadTaggedMem_lower_derivable)

lemma AArch64_TaggedMemSingle_lower_derivable[derivable_capsE]:
  assumes "Run (AArch64_TaggedMemSingle addr sz acctype wasaligned) t a"
    and "LENGTH('a) = nat sz * 8"
    and "use_mem_caps"
  shows "Capability_of_tag_word (vec_of_bits [access_vec_dec (fst a) 0] !! 0) (slice (snd a :: 'a::len word) 0 128) \<in> derivable_caps (run s t)"
  using assms(1,2)
  unfolding AArch64_TaggedMemSingle_def
  by (auto simp: test_bit_of_bl elim!: Run_bindE Run_ifE ReadTaggedMem_lower_derivable[THEN derivable_caps_run_imp] intro: assms(3))

lemma AArch64_TaggedMemSingle_upper_derivable[derivable_capsE]:
  assumes "Run (AArch64_TaggedMemSingle addr sz acctype wasaligned) t a"
    and "sz = 32"
  shows "Capability_of_tag_word (vec_of_bits [access_vec_dec (fst a :: 2 word) 1] !! 0) (slice (snd a :: 256 word) CAPABILITY_DBITS 128) \<in> derivable_caps (run s t)"
  using assms
  unfolding AArch64_TaggedMemSingle_def
  by (auto simp: test_bit_of_bl elim!: Run_bindE Run_ifE ReadTaggedMem_upper_derivable[THEN derivable_caps_run_imp])

(* Common patterns of capability/data conversions in memory access helpers *)
lemma Capability_of_tag_word_pairE[derivable_capsE]:
  assumes "x = (tag, data)"
    and "Capability_of_tag_word ((vec_of_bits [access_vec_dec (fst x) i] :: 1 word) !! 0) (slice (snd x) j 128) \<in> derivable_caps s"
  shows "Capability_of_tag_word ((vec_of_bits [access_vec_dec tag i] :: 1 word) !! 0) (slice data j 128) \<in> derivable_caps s"
  using assms
  by auto

lemma Capability_of_tag_word_rev_pairE[derivable_capsE]:
  assumes "x = (data, tag)"
    and "Capability_of_tag_word ((vec_of_bits [access_vec_dec (snd x) i] :: 1 word) !! 0) (slice (fst x) j 128) \<in> derivable_caps s"
  shows "Capability_of_tag_word ((vec_of_bits [access_vec_dec tag i] :: 1 word) !! 0) (slice data j 128) \<in> derivable_caps s"
  using assms
  by auto

declare Run_case_prodE[where thesis = "Capability_of_tag_word tag word \<in> derivable_caps s" for tag word s, derivable_capsE]

lemma Capability_of_tag_word_return_rev_pairE[derivable_capsE]:
  assumes "Run (return (data, tag)) t x"
    and "t = [] \<longrightarrow> Capability_of_tag_word ((vec_of_bits [access_vec_dec tag i] :: 1 word) !! 0) (slice data j 128) \<in> derivable_caps s"
  shows "Capability_of_tag_word ((vec_of_bits [access_vec_dec (snd x) i] :: 1 word) !! 0) (slice (fst x) j 128) \<in> derivable_caps s"
  using assms
  by auto

(* Common patterns, e.g. in auto-generated register accessors *)
lemma if_ELs_derivable[derivable_capsE]:
  assumes "Run (if el = EL0 then m0 else if el = EL1 then m1 else if el = EL2 then m2 else if el = EL3 then m3 else mu) t a"
    and "el = EL0 \<longrightarrow> Run m0 t a \<longrightarrow> c \<in> derivable_caps (run s t)"
    and "el = EL1 \<longrightarrow> Run m1 t a \<longrightarrow> c \<in> derivable_caps (run s t)"
    and "el = EL2 \<longrightarrow> Run m2 t a \<longrightarrow> c \<in> derivable_caps (run s t)"
    and "el = EL3 \<longrightarrow> Run m3 t a \<longrightarrow> c \<in> derivable_caps (run s t)"
  shows "c \<in> derivable_caps (run s t)"
  using assms
  by (cases el rule: exhaustive_2_word; auto simp: EL0_def EL1_def EL2_def EL3_def)

lemma uint_3_word_bounded[derivable_capsI]:
  fixes w :: "3 word"
  shows "uint w \<in> {0, 1, 2, 3, 4, 5, 6, 7}"
  by (cases w rule: exhaustive_3_word) auto

lemma uint_2_word_bounded[derivable_capsI]:
  "uint (w :: 2 word) \<in> insert 0 (insert 1 (insert 2 (insert 3 xs)))"
  by (cases w rule: exhaustive_2_word) auto

lemma uint_2_word_plus_one_bounded[derivable_capsI]:
  fixes w :: "2 word"
  shows "uint w + 1 \<in> {1, 2, 3, 4}"
  by (cases w rule: exhaustive_2_word) auto

lemma uint_1_word_bounded[derivable_capsI]:
  "uint (w :: 1 word) \<in> {0, 1}"
  by (cases w rule: exhaustive_1_word, auto)

lemma uint_1_word_plus_2_bounded[derivable_capsI]:
  "2 + uint (w :: 1 word) \<in> {2, 3}"
  by (cases w rule: exhaustive_1_word, auto)

declare uint_ge_0[derivable_capsI]
thm uint_lt2p[where x = x for x :: "5 word", simplified]

lemma uint_5_word_le_31[derivable_capsI]:
  "uint (w :: 5 word) \<le> 31"
  by auto

declare insertI1[derivable_capsI]
(* declare insertI2[derivable_capsI] *)

lemma size_64_word_eq_64[derivable_capsI]:
  "int (size (w :: 64 word)) = 64"
  by auto

lemma no_reg_writes_to_Mem_read[simp, no_reg_writes_toI]:
  "no_reg_writes_to Rs (Mem_read x0 x1 x2)"
  by (unfold Mem_read_def, no_reg_writes_toI)

lemma no_reg_writes_to_Mem_set[simp, no_reg_writes_toI]:
  "no_reg_writes_to Rs (Mem_set x0 x1 x2 x3)"
  by (unfold Mem_set_def, no_reg_writes_toI)

lemma no_reg_writes_to_ReadMem[simp, no_reg_writes_toI]:
  "no_reg_writes_to Rs (ReadMem x0 x1 x2)"
  by (unfold ReadMem_def, no_reg_writes_toI)

lemma no_reg_writes_to_ReadTaggedMem[simp, no_reg_writes_toI]:
  "no_reg_writes_to Rs (ReadTaggedMem x0 x1 x2)"
  by (unfold ReadTaggedMem_def, no_reg_writes_toI)

lemma no_reg_writes_to_ReadTags[simp, no_reg_writes_toI]:
  "no_reg_writes_to Rs (ReadTags x0 x1 x2)"
  by (unfold ReadTags_def, no_reg_writes_toI)

lemma no_reg_writes_to_WriteMem[simp, no_reg_writes_toI]:
  "no_reg_writes_to Rs (WriteMem x0 x1 x2 x3)"
  by (unfold WriteMem_def, no_reg_writes_toI)

lemma no_reg_writes_to_WriteTaggedMem[simp, no_reg_writes_toI]:
  "no_reg_writes_to Rs (WriteTaggedMem x0 x1 x2 x3 x4)"
  by (unfold WriteTaggedMem_def, no_reg_writes_toI)

lemma no_reg_writes_to_WriteTags[simp, no_reg_writes_toI]:
  "no_reg_writes_to Rs (WriteTags x0 x1 x2 x3)"
  by (unfold WriteTags_def, no_reg_writes_toI)

definition VA_derivable :: "VirtualAddress \<Rightarrow> (129 word, register_value) axiom_state \<Rightarrow> bool" where
  "VA_derivable va s \<equiv>
     (case VirtualAddress_vatype va of
        VA_Capability \<Rightarrow> VirtualAddress_base va \<in> derivable_caps s
      | VA_Bits64 \<Rightarrow> True)"

lemma VAFromCapability_base[simp]:
  "Run (VAFromCapability c) t va \<Longrightarrow> VirtualAddress_base va = c"
  by (auto simp: VAFromCapability_def elim!: Run_bindE)

lemma VAFromCapability_vatype[simp]:
  "Run (VAFromCapability c) t va \<Longrightarrow> VirtualAddress_vatype va = VA_Capability"
  by (auto simp: VAFromCapability_def elim!: Run_bindE)

lemma VAFromCapability_base_derivable[derivable_capsE]:
  assumes "Run (VAFromCapability c) t va"
    and "c \<in> derivable_caps s"
  shows "VirtualAddress_base va \<in> derivable_caps s"
  using assms
  by auto

lemma VAFromCapability_derivable[derivable_capsE]:
  "Run (VAFromCapability c) t va \<Longrightarrow> c \<in> derivable_caps s \<Longrightarrow> VA_derivable va s"
  by (auto simp: VA_derivable_def)

lemma VAToCapability_vatype[simp]:
  "Run (VAToCapability va) t c \<Longrightarrow> VirtualAddress_vatype va = VA_Capability"
  by (auto simp: VAToCapability_def VAIsCapability_def elim!: Run_bindE)

lemma VAToCapability_base[simp]:
  "Run (VAToCapability va) t c \<Longrightarrow> VirtualAddress_base va = c"
  by (auto simp: VAToCapability_def)

lemma VAFromBits64_vatype[simp]:
  "Run (VAFromBits64 w) t va \<Longrightarrow> VirtualAddress_vatype va = VA_Bits64"
  by (auto simp: VAFromBits64_def elim!: Run_bindE)

lemma VAFromBits64_derivable[derivable_capsE]:
  "Run (VAFromBits64 addr) t va \<Longrightarrow> VA_derivable va s"
  by (auto simp: VA_derivable_def)

lemma VA_derivable_run_imp[derivable_caps_runI]:
  assumes "VA_derivable va s"
  shows "VA_derivable va (run s t)"
  using assms
  by (auto simp: VA_derivable_def split: VirtualAddressType.splits intro: derivable_caps_runI)

declare Run_ifE[where thesis = "VA_derivable va s" and a = va for va s, derivable_caps_combinators]
declare Run_letE[where thesis = "VA_derivable va s" and a = va for va s, derivable_caps_combinators]

thm derivable_caps_combinators

lemma Run_return_VA_derivable[derivable_caps_combinators]:
  "Run (return va') t va \<Longrightarrow> VA_derivable va' s \<Longrightarrow> VA_derivable va s"
  by auto

lemma VAFromPCC_derivable[derivable_capsE]:
  "Run (VAFromPCC offset) t va \<Longrightarrow> VA_derivable va s"
  by (auto simp: VAFromPCC_def VA_derivable_def elim: Run_bindE)

end

(*locale Morello_Axiom_Assm_Automaton = Morello_Axiom_Automaton +
  fixes ex_traces :: bool
    and ev_assms :: "register_value event \<Rightarrow> bool"
  assumes non_cap_event_enabled: "\<And>e. non_cap_event e \<Longrightarrow> enabled s e"
    and read_non_special_regs_enabled: "\<And>r v. r \<notin> PCC ISA \<union> IDC ISA \<union> KCC ISA \<union> privileged_regs ISA \<Longrightarrow> enabled s (E_read_reg r v)"
begin

sublocale Cap_Axiom_Assm_Automaton where CC = CC and ISA = ISA
  by unfold_locales (blast intro: non_cap_event_enabled read_non_special_regs_enabled)+

end*)

definition R_name :: "int \<Rightarrow> string" where
  "R_name n \<equiv>
     (if n =  0 then ''_R00'' else
      if n =  1 then ''_R01'' else
      if n =  2 then ''_R02'' else
      if n =  3 then ''_R03'' else
      if n =  4 then ''_R04'' else
      if n =  5 then ''_R05'' else
      if n =  6 then ''_R06'' else
      if n =  7 then ''_R07'' else
      if n =  8 then ''_R08'' else
      if n =  9 then ''_R09'' else
      if n = 10 then ''_R10'' else
      if n = 11 then ''_R11'' else
      if n = 12 then ''_R12'' else
      if n = 13 then ''_R13'' else
      if n = 14 then ''_R14'' else
      if n = 15 then ''_R15'' else
      if n = 16 then ''_R16'' else
      if n = 17 then ''_R17'' else
      if n = 18 then ''_R18'' else
      if n = 19 then ''_R19'' else
      if n = 20 then ''_R20'' else
      if n = 21 then ''_R21'' else
      if n = 22 then ''_R22'' else
      if n = 23 then ''_R23'' else
      if n = 24 then ''_R24'' else
      if n = 25 then ''_R25'' else
      if n = 26 then ''_R26'' else
      if n = 27 then ''_R27'' else
      if n = 28 then ''_R28'' else
      if n = 29 then ''_R29'' else
      ''_R30'')"

locale Morello_Write_Cap_Automaton = Morello_ISA +
  fixes ex_traces :: bool and invoked_caps :: "Capability set"
    and invoked_regs :: "int set" and invokes_mem_caps :: bool
begin

definition normalise_cursor_flags :: "Capability \<Rightarrow> bool \<Rightarrow> Capability" where
  "normalise_cursor_flags c top_bit \<equiv> CapSetFlags c (if top_bit then max_word else 0)"

definition branch_caps :: "Capability \<Rightarrow> Capability set" where
  "branch_caps c \<equiv>
     {c, normalise_cursor_flags c (CapGetValue c !! 55), normalise_cursor_flags c False,
      set_bit c 0 False, normalise_cursor_flags (set_bit c 0 False) (CapGetValue c !! 55),
      normalise_cursor_flags (set_bit c 0 False) False}"

(* TODO *)
fun ev_assms :: "register_value event \<Rightarrow> bool" where
  "ev_assms (E_read_reg r v) = ((r = ''PCC'' \<longrightarrow> (\<forall>c \<in> caps_of_regval v. \<not>CapIsSealed c)) \<and> (\<forall>n c. R_name n = r \<and> n \<in> invoked_regs \<and> c \<in> caps_of_regval v \<and> CapIsTagSet c \<and> CapIsSealed c \<longrightarrow> branch_caps (CapUnseal c) \<subseteq> invoked_caps))"
| "ev_assms _ = True"

sublocale Write_Cap_Assm_Automaton where CC = CC and ISA = ISA and ev_assms = ev_assms ..

sublocale Morello_Axiom_Automaton where enabled = enabled ..

declare datatype_splits[where P = "\<lambda>m. traces_enabled m s" for s, traces_enabled_split]

lemma branch_caps_leq:
  assumes "c' \<in> branch_caps c" and "CapIsTagSet c \<longrightarrow> \<not>CapIsSealed c"
  shows "leq_cap CC c' c"
proof cases
  assume "CapIsTagSet c"
  then show ?thesis
    using assms
    unfolding branch_caps_def normalise_cursor_flags_def
    by (auto intro: leq_cap_set_0th leq_cap_CapSetFlags leq_cap_CapSetFlags[THEN leq_cap_trans])
next
  assume "\<not>CapIsTagSet c"
  then have "\<not>CapIsTagSet c'"
    using assms
    by (auto simp: branch_caps_def normalise_cursor_flags_def test_bit_set_gen)
  then show ?thesis
    by (auto simp: leq_cap_def)
qed

lemma branch_caps_128th_iff:
  assumes "c' \<in> branch_caps c"
  shows "c' !! 128 \<longleftrightarrow> c !! 128"
  using assms
  by (auto simp: branch_caps_def normalise_cursor_flags_def test_bit_set_gen)

lemma branch_caps_derivable_caps:
  assumes "c' \<in> branch_caps c" and "c \<in> derivable_caps s" and "CapIsTagSet c \<longrightarrow> \<not>CapIsSealed c"
  shows "c' \<in> derivable_caps s"
  using assms(2) branch_caps_leq[OF assms(1,3)] branch_caps_128th_iff[OF assms(1)]
  by (auto simp: derivable_caps_def intro: derivable.Restrict)

lemma CapSetFlags_mask_56_normalise_cursor_flags:
  "CapSetFlags c (CapGetValue c AND mask 56) = normalise_cursor_flags c False"
  unfolding CapSetFlags_def normalise_cursor_flags_def
  by (intro word_eqI)
     (auto simp: update_subrange_vec_dec_test_bit nth_slice word_ao_nth)

lemma CapSetFlags_SignExtend_normalise_cursor_flags:
  assumes "CapGetValue c !! 55"
  shows "CapSetFlags c (SignExtend1 64 (ucast (CapGetValue c) :: 56 word)) = normalise_cursor_flags c True"
  using assms
  unfolding CapSetFlags_def normalise_cursor_flags_def SignExtend1_def sign_extend_def
  by (intro word_eqI)
     (auto simp: update_subrange_vec_dec_test_bit nth_slice nth_scast nth_ucast)

lemma leq_cap_CapWithTagClear[simp, intro]:
  "leq_cap CC (CapWithTagClear c) c'"
  by (auto simp: leq_cap_def)

lemma leq_cap_CapSetFlags:
  assumes "\<not>CapIsSealed c"
  shows "leq_cap CC (CapSetFlags c flags) c"
  using assms leq_perms_cap_permits_imp[of "CapSetFlags c flags" c]
  by (auto simp: leq_cap_def intro: leq_bounds_CapSetFlags)

lemma BranchAddr_leq_cap:
  assumes "Run (BranchAddr c el) t c'"
  shows "leq_cap CC c' c"
  using assms
  unfolding BranchAddr_def
  by (auto elim!: Run_bindE Run_letE Run_ifE Run_and_boolM_E Run_or_boolM_E intro: leq_cap_CapSetFlags)

lemma BranchAddr_in_branch_caps:
  assumes "Run (BranchAddr c el) t c'" and "CapIsTagSet c'"
  shows "c' \<in> branch_caps c"
  using assms
  unfolding BranchAddr_def branch_caps_def
  by (cases "CapIsSealed c")
     (auto elim!: Run_bindE Run_letE Run_ifE Run_and_boolM_E Run_or_boolM_E
           simp: CapSetFlags_mask_56_normalise_cursor_flags CapSetFlags_SignExtend_normalise_cursor_flags)

lemma CapAdd_CapIsSealed_imp[derivable_capsE]:
  assumes "Run (CapAdd c incr) t c'" and "\<not>CapIsSealed c"
  shows "\<not>CapIsSealed c'"
  using assms
  by auto

lemma CapAdd__1_CapIsSealed_imp[derivable_capsE]:
  assumes "Run (CapAdd__1 c incr) t c'" and "\<not>CapIsSealed c"
  shows "\<not>CapIsSealed c'"
  using assms
  by auto

lemma BranchAddr_not_sealed:
  assumes "Run (BranchAddr c el) t c'" and "CapIsTagSet c'"
  shows "\<not>CapIsSealed c" and "CapIsTagSet c"
  using assms
  unfolding BranchAddr_def
  apply (auto elim!: Run_bindE Run_letE split: if_splits)
  (* TODO: Should be fixed in the ASL *)
  sorry

lemma C_read_branch_caps_invoked_caps[derivable_capsE]:
  assumes "Run (C_read n) t c" and "trace_assms t"
    and "n \<in> invoked_regs"
    and "CapIsTagSet c" and "CapIsSealed c"
  shows "branch_caps (CapUnseal c) \<subseteq> invoked_caps"
proof -
  have "t = [E_read_reg (R_name n) (Regval_bitvector_129_dec c)]"
    using assms(1,4)
    unfolding C_read_def R_read_def
    by (auto simp: R_name_def CapNull_def register_defs elim!: Run_read_regE Run_ifE)
  with assms(2-)
  show ?thesis
    by auto
qed

lemma C_read_invoked_caps[derivable_capsE]:
  assumes "Run (C_read n) t c" and "trace_assms t"
    and "n \<in> invoked_regs"
    and "CapIsTagSet c" and "CapIsSealed c"
  shows "CapUnseal c \<in> invoked_caps"
  using C_read_branch_caps_invoked_caps[OF assms]
  by (auto simp: branch_caps_def)

end

lemma HaveAArch32EL_False[simp]:
  "Run (HaveAArch32EL el) t a \<longleftrightarrow> (t = [] \<and> a = False)"
  unfolding HaveAArch32EL_def HaveAnyAArch32_def HaveEL_def
  unfolding EL0_def EL1_def EL2_def EL3_def
  by (cases el rule: exhaustive_2_word) (auto elim: Run_bindE)

lemma ELUsingAArch32_False:
  shows "\<not>Run (ELUsingAArch32 el) t True"
  unfolding ELUsingAArch32_def ELStateUsingAArch32_def ELStateUsingAArch32K_def
  by (auto elim!: Run_bindE)

lemma AddrTop_63_or_55:
  assumes "Run (AddrTop address el) t b"
  shows "b = 63 \<or> b = 55"
  using assms
  unfolding AddrTop_def
  by (auto elim!: Run_bindE simp: ELUsingAArch32_False)


(* Assume stubbed out address translation for now *)
locale Morello_Mem_Automaton =
  Morello_Fixed_Address_Translation
  where translate_address = translate_address
    and is_translation_event = "\<lambda>_. False"
    and translation_assms = "\<lambda>_. True" +
  fixes ex_traces :: bool
begin

sublocale Mem_Assm_Automaton
  where CC = CC and ISA = ISA
    and translation_assms = "\<lambda>_. True"
    and is_fetch = "False"
    and extra_assms = "\<lambda>e. True" \<comment> \<open>TODO\<close>
  ..

sublocale Morello_Axiom_Automaton
  where translate_address = "\<lambda>addr _ _. translate_address addr"
    and enabled = enabled
    and is_translation_event = "\<lambda>_. False"
  ..

lemma translate_address_ISA[simp]:
  "isa.translate_address ISA addr acctype t = translate_address addr"
  by (auto simp: ISA_def)

declare datatype_splits[where P = "\<lambda>m. traces_enabled m s" for s, traces_enabled_split]

end

end
