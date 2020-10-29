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

lemma pow2_power[simp]: "pow2 n = 2 ^ nat n"
  by (auto simp: pow2_def pow_def)

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

lemma slice_set_bit_below:
  assumes "n' < n"
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

lemmas unat_lt2p64[simp, intro] = unat_lt2p[of w for w :: "64 word", simplified]

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

lemma read_memt_bytes_accessed_mem_cap:
  assumes "Run (read_memt_bytes BCa BCb rk addr sz) t (bytes, tag)"
    and "cap_of_mem_bytes_method CC bytes tag = Some c"
    and "\<forall>addr'. nat_of_bv BCa addr = Some addr' \<longrightarrow> \<not>is_translation_event ISA (E_read_memt rk addr' (nat sz) (bytes, tag))"
  shows "accessed_mem_cap_of_trace_if_tagged c t"
  using assms
  unfolding read_memt_bytes_def accessed_mem_cap_of_trace_if_tagged_def
  by (auto simp: derivable_caps_def maybe_fail_def accessed_caps_def
           split: option.splits intro: derivable.Copy
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

lemmas Run_int_set_member_combinators[derivable_caps_combinators] =
  Run_bindE[where thesis = "a \<in> insert x xs" and a = a for a x :: int and xs :: "int set"]
  Run_ifE[where thesis = "a \<in> insert x xs" and a = a for a x :: int and xs :: "int set"]
  Run_letE[where thesis = "a \<in> insert x xs" and a = a for a x :: int and xs :: "int set"]

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

lemma Run_if_ELs_cases:
  assumes "Run (if el = EL0 then m0 else if el = EL1 then m1 else if el = EL2 then m2 else if el = EL3 then m3 else mu) t a"
  obtains (EL0) "el = EL0" and "Run m0 t a"
  | (EL1) "el = EL1" and "Run m1 t a"
  | (EL2) "el = EL2" and "Run m2 t a"
  | (EL3) "el = EL3" and "Run m3 t a"
  using assms
  by (cases el rule: exhaustive_2_word; auto simp: EL0_def EL1_def EL2_def EL3_def)

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
  "is_sentry c \<equiv> CapGetObjectType c = CAP_SEAL_TYPE_RB"

definition is_indirect_sentry :: "Capability \<Rightarrow> bool" where
  "is_indirect_sentry c \<equiv> CapGetObjectType c \<in> {CAP_SEAL_TYPE_LB, CAP_SEAL_TYPE_LPB}"

definition get_base :: "Capability \<Rightarrow> nat" where
  "get_base c \<equiv> unat (THE b. \<exists>t. Run (CapGetBase c) t b)"

definition get_limit :: "Capability \<Rightarrow> nat" where
  "get_limit c \<equiv> unat (THE l. \<exists>t b v. Run (CapGetBounds c) t (b, l, v))"

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
   is_indirect_sentry_method = is_indirect_sentry,
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
  "is_indirect_sentry_method CC c = is_indirect_sentry c"
  "seal_method CC c otype = seal c otype"
  "unseal_method CC c = CapUnseal c"
  "get_cursor_method CC c = unat (CapGetValue c)"
  "get_base_method CC c = get_base c"
  "get_top_method CC c = get_limit c"
  "get_obj_type_method CC c = unat (CapGetObjectType c)"
  "cap_of_mem_bytes_method CC = cap_of_mem_bytes"
  "permits_store_method CC c = cap_permits CAP_PERM_STORE c"
  "permits_execute_method CC c = cap_permits CAP_PERM_EXECUTE c"
  "permits_unseal_method CC c = cap_permits CAP_PERM_UNSEAL c"
  "permits_ccall_method CC c = cap_permits CAP_PERM_BRANCH_SEALED_PAIR c"
  "permits_system_access_method CC c = CapIsSystemAccessPermitted c"
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

text \<open>Proofs that a monadic function essentially encodes a pure function\<close>

definition
  monad_return_rel :: "('rv, 'a, 'e) monad \<Rightarrow> ('rv, 'a, 'e) monad \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
where
  "monad_return_rel m m' P = (\<forall> t t' x x'. Run m t x \<and> Run m' t' x' \<longrightarrow> P x x')"

lemmas monad_return_relD = monad_return_rel_def[THEN iffD1, unfolded imp_conjL, rule_format]

definition
  monad_result_of :: "('rv, 'a, 'e) monad \<Rightarrow> 'a"
where
  "monad_result_of m = (THE v. \<exists>t. Run m t v)"

lemma monad_result_of_eq:
  "monad_return_rel m m (=) \<Longrightarrow> Run m t x \<Longrightarrow> monad_result_of m = x"
  apply (simp add: monad_result_of_def)
  apply (rule the_equality)
   apply (auto elim: monad_return_relD)
  done

lemma monad_return_rel_bind:
  "monad_return_rel f f' P \<Longrightarrow> (\<And>x x'. P x x' \<Longrightarrow> monad_return_rel (g x) (g' x') Q)
    \<Longrightarrow> monad_return_rel (bind f g) (bind f' g') Q"
  apply (subst monad_return_rel_def, clarsimp elim!: Run_bindE)
  apply (drule(2) monad_return_relD)
  apply (elim meta_allE, drule(1) meta_mp)
  apply (erule(2) monad_return_relD)
  done

lemma monad_return_rel_if:
  "G = G' \<Longrightarrow> monad_return_rel f f' P \<Longrightarrow> monad_return_rel g g' P
    \<Longrightarrow> monad_return_rel (If G f g) (If G' f' g') P"
  by simp

lemma monad_return_rel_return:
  "P x y \<Longrightarrow> monad_return_rel (return x) (return y) P"
  by (clarsimp simp: monad_return_rel_def)

lemma monad_return_rel_triv:
  "monad_return_rel f g (\<lambda> x x'. True)"
  by (clarsimp simp: monad_return_rel_def)

definition
  eq_at_bits :: "nat set \<Rightarrow> ('a :: len0) word \<Rightarrow> 'a word \<Rightarrow> bool"
where
  "eq_at_bits ns x y = (\<forall>i \<in> ns. i < size x \<longrightarrow> test_bit x i = test_bit y i)"

lemma monad_return_rel_undefined:
  "monad_return_rel (undefined_bitvector i) (undefined_bitvector j) (eq_at_bits {})"
  by (simp add: monad_return_rel_def eq_at_bits_def)

lemmas monad_return_rel_assert_exp_triv =
    monad_return_rel_triv[where f="assert_exp P str" and g="assert_exp Q str'" for str str' P Q]

lemma monad_return_rel_assert_exp_P:
  "monad_return_rel (assert_exp P str) (assert_exp P str') (\<lambda>_ _. P)"
  by (clarsimp simp: monad_return_rel_def)

lemma monad_return_rel_let_same_forget:
  "(\<And>x. monad_return_rel (g x) (g' x) Q)
    \<Longrightarrow> monad_return_rel (Let x g) (Let x g') Q"
  by simp

lemma monad_return_rel_let_rel:
  "P x x' \<Longrightarrow> (\<And>x x'. P x x' \<Longrightarrow> monad_return_rel (g x) (g' x') Q)
    \<Longrightarrow> monad_return_rel (Let x g) (Let x' g') Q"
  by simp

lemma test_bit_word_update:
  "j = i + size y - 1 \<Longrightarrow> j < size x \<Longrightarrow> 0 < size y \<Longrightarrow>
  test_bit (word_update x i j y) k = (if i \<le> k \<and> k \<le> j then test_bit y (k - i) else test_bit x k)"
  using test_bit_size[of x k] test_bit_size[of y "k - i"]
  apply (simp add: word_update_def Let_def test_bit_of_bl nth_append)
  apply (intro conjI impI iffI, simp_all add: nth_rev to_bl_nth rev_take)
  apply (simp_all add: Suc_leI le_diff_conv2)
  apply (auto simp: nth_rev to_bl_nth)
  done

lemma test_bit_slice_mask:
  "n = int (LENGTH ('a)) \<Longrightarrow> 0 \<le> i \<Longrightarrow> 0 \<le> l \<Longrightarrow>
    test_bit (slice_mask n i l :: ('a :: len) word) j = (nat i \<le> j \<and> (j - nat i) < nat l \<and> j < nat n)"
  apply (simp add: slice_mask_def word_ops_nth_size nth_shiftl sail_ones_def zeros_def)
  apply (simp add: sail_mask_def nth_shiftl mask_def[simplified, symmetric])
  apply (safe, simp_all)
  done

lemma test_bit_above_size:
  "n \<ge> size (x :: ('a :: len) word) \<Longrightarrow> \<not> test_bit x n"
  by (auto dest!: test_bit_size)

lemma test_bit_vector_update_subrange_from_subrange:
  assumes cs: "e1 \<le> s1 \<and> 0 \<le> e1 \<and> e2 \<le> s2 \<and> 0 \<le> e2"
  shows "test_bit (vector_update_subrange_from_subrange n v1 s1 e1 v2 s2 e2) i
    = (i < size v1 \<and> (nat e1 \<le> i \<and>
     v2 !! (i - nat e1 + nat e2) \<and> i - nat e1 < nat (s2 - e2 + 1) \<and> i - nat e1 + nat e2 < size v2 \<and> i - nat e1 < size v1 \<or>
     v1 !! i \<and> (nat e1 \<le> i \<longrightarrow> \<not> i - nat e1 < nat (s1 - e1 + 1))))"
  using cs
  apply (simp add: vector_update_subrange_from_subrange_def)
  apply (cases "i < size v1", simp_all add: test_bit_above_size)
  apply (simp add: word_ao_nth nth_shiftr nth_shiftl nth_ucast test_bit_slice_mask
                   word_ops_nth_size)
  done

lemma CapGetTop_monad_return_rel:
  "monad_return_rel (CapGetTop c) (CapGetTop c) (=)"
  apply (clarsimp simp add: CapGetTop_def Let_def split del: if_split)
  apply (intro monad_return_rel_if monad_return_rel_return
    monad_return_rel_bind[OF monad_return_rel_undefined])
  apply simp
  done

lemma CapGetExponent_range:
  "0 \<le> CapGetExponent c \<and> CapGetExponent c < 64"
  by (clarsimp simp add: CapGetExponent_def uint_lt2p[THEN order_less_le_trans])

lemma eq_at_bits_set_slice_zeros_lemma:
  assumes eq: "eq_at_bits S x x'"
     and imp: "\<And>y y'. eq_at_bits (S \<union> {nat i ..< nat j}) y y' \<Longrightarrow> monad_return_rel (g y) (g' y') Q"
   and extra: "n = int (size x)" "0 \<le> i" "0 \<le> j"
  shows "monad_return_rel (Let (set_slice_zeros n x i j) g) (Let (set_slice_zeros n x' i j) g') Q"
  using eq extra
  apply simp
  apply (rule imp)
  apply (clarsimp simp: eq_at_bits_def set_slice_zeros_def word_ops_nth_size
                        test_bit_slice_mask)
  apply auto
  done

lemma eq_at_bits_word_update_lemma:
  assumes eq: "eq_at_bits S x x'"
     and imp: "\<And>y y'. eq_at_bits (S \<union> {nat i ..< nat j + 1}) y y' \<Longrightarrow> monad_return_rel (g y) (g' y') Q"
   and extra: "j = i + size y - 1" "j < size x" "0 < size y"
  shows "monad_return_rel (Let (word_update x i j y) g) (Let (word_update x' i j y) g') Q"
  using eq extra
  by (auto intro!: imp simp: eq_at_bits_def test_bit_word_update)

lemma eq_at_bits_vector_update_subrange_from_subrange_lemma:
  assumes eq: "eq_at_bits S x x'"
     and imp: "\<And>y y'. eq_at_bits (S \<union> {nat e1 ..< nat (s1 + 1)}) y y' \<Longrightarrow> monad_return_rel (g y) (g' y') Q"
   and extra: "e1 \<le> s1 \<and> 0 \<le> e1 \<and> e2 \<le> s2 \<and> 0 \<le> e2"
  shows "monad_return_rel (Let (vector_update_subrange_from_subrange n x s1 e1 y s2 e2) g)
    (Let (vector_update_subrange_from_subrange n x' s1 e1 y s2 e2) g') Q"
  using eq extra
  apply (clarsimp intro!: imp conj_cong[OF refl] simp: eq_at_bits_def
    test_bit_vector_update_subrange_from_subrange)
  apply (elim disjE, simp_all)
  apply (subgoal_tac "i - nat e1 < nat (s1 - e1 + 1)", simp_all)
  apply arith
  done

lemma let_pair_to_let:
  "(Let (x, y) f) = (let a = x; b = y in f (a, b))"
  by simp

lemma monad_return_rel_let_shuffle:
  "monad_return_rel (let x = x; y = f x in g y) (let x = x'; y = f x in g' y) Q \<Longrightarrow>
    monad_return_rel (let y = f x in g y) (let y = f x' in g' y) Q"
  by simp

lemma eq_at_bits_complete:
  "eq_at_bits S x x' \<Longrightarrow> {0 ..< size x} \<subseteq> S \<Longrightarrow> x = x'"
  by (simp add: eq_at_bits_def word_eq_iff subset_iff)

lemma eq_at_bits_same:
  "eq_at_bits S x x"
  by (simp add: eq_at_bits_def)

lemma eq_at_bits_finale_lemma:
  "eq_at_bits S x x' \<Longrightarrow> {0 ..< size x} \<subseteq> S \<Longrightarrow>
    (\<And>y. x = x' \<Longrightarrow> monad_return_rel (g y) (g' y) Q) \<Longrightarrow>
    monad_return_rel (let y = f x in g y) (let y = f x' in g' y) Q"
  apply (drule(1) eq_at_bits_complete)
  apply simp
  done

lemma CapGetBounds_monad_return_rel:
  "monad_return_rel (CapGetBounds c) (CapGetBounds c) (=)"
  using CapGetExponent_range[of c] [[simproc del: let_simp]]
  apply (simp add: CapGetBounds_def
    Let_def[where s="CapGetExponent _"]
    update_subrange_vec_dec_def
    CAP_MW_def CAP_MAX_EXPONENT_def
  )
  apply (repeat_new \<open>intro conjI impI refl
    monad_return_rel_return
    monad_return_rel_bind[OF monad_return_rel_undefined]
    monad_return_rel_let_same_forget
    CapGetTop_monad_return_rel[THEN monad_return_rel_bind]
    monad_return_rel_assert_exp_P[THEN monad_return_rel_bind]
    monad_return_rel_let_shuffle[where f="Word.slice _"]
    monad_return_rel_let_shuffle[where f="ucast"]
    monad_return_rel_let_shuffle[where f="\<lambda>x. of_bl [test_bit x _]"]
  | (rule eq_at_bits_set_slice_zeros_lemma
    eq_at_bits_word_update_lemma
    eq_at_bits_vector_update_subrange_from_subrange_lemma,
    assumption)
  | simp only: let_pair_to_let prod.simps linorder_not_less
  | split if_split
  | (erule eq_at_bits_finale_lemma,
    solves \<open>clarsimp simp: CAP_MW_def nat_add_distrib\<close>)
  | (drule order_antisym[where y="CapGetExponent c"], solves \<open>simp\<close>)
  \<close>)
  apply (simp_all add: CAP_MW_def)
  done

lemma CapGetBase_monad_return_rel:
  "monad_return_rel (CapGetBase c) (CapGetBase c) (=)"
  apply (simp add: CapGetBase_def case_prod_beta)
  apply (intro
    monad_return_rel_return
    monad_return_rel_bind[OF monad_return_rel_undefined]
    CapGetBounds_monad_return_rel[THEN monad_return_rel_bind])
  apply simp
  done

lemma foreachM_witness:
  "(\<forall>x \<in> set xs. \<forall>acc. \<exists>t. Run (f x acc) t (g x acc)) \<Longrightarrow>
    v = (List.fold g xs acc) \<Longrightarrow>
    \<exists>t. Run (foreachM xs acc f) t v"
  apply (induct xs arbitrary: acc)
   apply simp
  apply (fastforce intro: Traces_bindI)
  done

lemma choose_bool_witness:
  "\<exists>t. Run (choose_bool s) t b"
  apply (simp add: choose_bool_def)
  apply (rule exI, rule Traces.Step, rule Choose)
  apply simp
  done

lemma fold_append:
  "List.fold (\<lambda>x acc. acc @ f x) xs ys = ys @ List.concat (map f xs)"
  by (induct xs arbitrary: ys, simp_all)

lemma of_bits_nondet_witness:
  "set xs \<subseteq> {BU} \<Longrightarrow>
    \<exists>t. Run (bools_of_bits_nondet xs) t (map (\<lambda>_. False) xs)"
  using choose_bool_witness[of "''bool_of_bitU''" False]
  apply (simp add: bools_of_bits_nondet_def)
  apply (rule foreachM_witness[where g="\<lambda>_ acc. acc @ [False]"])
   apply clarsimp
   apply (frule(1) subsetD)
   apply fastforce
  apply (simp add: fold_append)
  done

lemma undefined_bitvector_witness:
  "\<exists>t. Run (undefined_bitvector n) t 0"
  using of_bits_nondet_witness[of "replicate (nat n) BU"]
  apply (simp add: undefined_bitvector_def of_bits_nondet_def del: repeat.simps)
  apply fastforce
  done

lemma CapGetBounds_top_bit:
  "Run (CapGetBounds c) t (base, limit, valid) \<Longrightarrow> unat base < 2 ^ 64"
  by (auto simp add: CapGetBounds_def Let_def CAP_BOUND_MIN_def unat_and_mask elim!: Run_bindE)

lemma CapGetBounds_get_base:
  assumes "Run (CapGetBounds c) t (base, limit, valid)"
  shows "get_base c = unat base"
proof -
  have "\<exists> t2. Run (CapGetBase c) t2 (ucast base)"
    using assms undefined_bitvector_witness[where n=65]
    apply (clarsimp simp: CapGetBase_def)
    apply (rule exI)
    apply (erule Traces_bindI)
    apply (erule Traces_bindI)
    apply simp
    done

  thus ?thesis
    using CapGetBounds_top_bit[OF assms]
    apply (clarsimp simp: get_base_def)
    apply (frule monad_result_of_eq[OF CapGetBase_monad_return_rel])
    apply (simp add: monad_result_of_def less_mask_eq[unfolded word_less_nat_alt])
    done
qed

lemma CapGetBounds_get_limit:
  assumes "Run (CapGetBounds c) t (base, limit, valid)"
  shows "get_limit c = unat limit"
  using assms
  apply (simp add: get_limit_def)
  apply (rule the_equality)
   apply auto[1]
  apply clarsimp
  apply (drule(1) CapGetBounds_monad_return_rel[THEN monad_return_relD])
  apply simp
  done

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

definition invokes_indirect_caps :: "instr \<Rightarrow> register_value trace \<Rightarrow> Capability set" where
  "invokes_indirect_caps instr t = {c. \<exists>r. E_read_reg r (Regval_bitvector_129_dec c) \<in> set t \<and> CapGetObjectType c \<in> {CAP_SEAL_TYPE_LB, CAP_SEAL_TYPE_LPB}}" \<comment> \<open>TODO\<close>

definition instr_raises_ex :: "instr \<Rightarrow> register_value trace \<Rightarrow> bool" where
  "instr_raises_ex instr t \<equiv> hasException t (instr_sem instr)"

definition fetch_raises_ex :: "register_value trace \<Rightarrow> bool" where
  "fetch_raises_ex t \<equiv> hasException t instr_fetch"

text \<open>Over-approximation of allowed exception targets
TODO: Restrict to valid branch targets of KCC caps with (small) offset?\<close>

definition exception_targets :: "register_value set \<Rightarrow> Capability set" where
  "exception_targets rvs \<equiv> derivable (\<Union>(caps_of_regval ` rvs))"

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
   isa.invokes_indirect_caps = invokes_indirect_caps,
   isa.invokes_caps = invokes_caps,
   isa.instr_raises_ex = instr_raises_ex,
   isa.fetch_raises_ex = fetch_raises_ex,
   isa.exception_targets = exception_targets,
   privileged_regs = {''CDBGDTR_EL0'', ''CDLR_EL0'', ''VBAR_EL1'', ''VBAR_EL2'', ''VBAR_EL3''}, \<comment> \<open>TODO\<close>
   isa.is_translation_event = is_translation_event,
   isa.translate_address = translate_address\<rparr>"

sublocale Capability_ISA CC ISA ..

lemma ISA_simps[simp]:
  "PCC ISA = {''PCC''}"
  "KCC ISA = {''VBAR_EL1'', ''VBAR_EL2'', ''VBAR_EL3''}"
  "IDC ISA = {''_R29''}"
  "privileged_regs ISA = {''CDBGDTR_EL0'', ''CDLR_EL0'', ''VBAR_EL1'', ''VBAR_EL2'', ''VBAR_EL3''}"
  "isa.instr_sem ISA = instr_sem"
  "isa.instr_fetch ISA = instr_fetch"
  "isa.caps_of_regval ISA = caps_of_regval"
  "isa.is_translation_event ISA = is_translation_event"
  "isa.exception_targets ISA = exception_targets"
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

locale Morello_Bounds_Address_Calculation =
  fixes translation_el :: "AccType \<Rightarrow> 2 word"
    and s1_enabled :: "AccType \<Rightarrow> bool"
    and tbi_enabled :: "AccType \<Rightarrow> nat \<Rightarrow> bool"
    and in_host :: "AccType \<Rightarrow> bool"
  assumes tbi_enabled_cong: "\<And>acctype addr1 addr2. bin_nth (int addr1) 55 = bin_nth (int addr2) 55 \<Longrightarrow> tbi_enabled acctype addr1 \<longleftrightarrow> tbi_enabled acctype addr2"
begin

definition has_ttbr1 :: "AccType \<Rightarrow> bool" where
  "has_ttbr1 acctype = (translation_el acctype \<in> {EL0, EL1} \<or> in_host acctype)"

definition bounds_address :: "AccType \<Rightarrow> nat \<Rightarrow> nat" where
  "bounds_address acctype addr =
     (if tbi_enabled acctype addr then
        (if s1_enabled acctype \<and> has_ttbr1 acctype \<and> bin_nth (int addr) 55
         then addr mod 2 ^ 56 + (255 * 2 ^ 56) \<comment> \<open>sign extension of addr[55..0]\<close>
         else addr mod 2 ^ 56)                 \<comment> \<open>zero extension of addr[55..0]\<close>
      else addr)"

definition valid_address :: "AccType \<Rightarrow> nat \<Rightarrow> bool" where
  "valid_address acctype addr \<equiv>
     (if s1_enabled acctype \<and> has_ttbr1 acctype \<and> bin_nth (int addr) 55
      then (if tbi_enabled acctype addr
            then addr mod 2 ^ 56 \<ge> 15 * 2 ^ 52 \<comment> \<open>addr[55..52] = 0xF\<close>
            else addr \<ge> 4095 * 2 ^ 52)         \<comment> \<open>addr[63..52] = 0xFFF\<close>
      else (if tbi_enabled acctype addr
            then addr mod 2 ^ 56 < 2 ^ 52      \<comment> \<open>addr[55..52] = 0x0\<close>
            else addr < 2 ^ 52))"              \<comment> \<open>addr[63..52] = 0x000\<close>

lemma bin_nth_eq_mod_div:
  "bin_nth w n = odd (w mod 2 ^ (Suc n) div 2 ^ n)"
proof -
  have "bin_nth w n = odd (w div 2 ^ n)"
    by (auto simp: bin_nth_eq_mod)
  also have "\<dots> = odd ((w mod 2 ^ (Suc n) + w div 2 ^ (Suc n) * 2 ^ (Suc n)) div 2 ^ n)"
    unfolding mod_div_mult_eq
    ..
  also have "\<dots> = odd ((w mod 2 ^ (Suc n) + (2 ^ n) * (2 * (w div 2 ^ (Suc n)))) div 2 ^ n)"
    by (auto simp only: mult_ac power_Suc)
  also have "\<dots> = odd (w mod 2 ^ (Suc n) div 2 ^ n)"
    by auto
  finally show ?thesis
    .
qed

lemma bin_nth_int_eq_mod_div:
  "bin_nth (int w) n = odd (w mod 2 ^ (Suc n) div 2 ^ n)"
proof -
  have "even (nat (int w mod 2 ^ (Suc n) div 2 ^ n)) = even (int w mod 2 ^ (Suc n) div 2 ^ n)"
    by (intro even_nat_iff) (auto simp: pos_imp_zdiv_nonneg_iff)
  then show ?thesis
    unfolding bin_nth_eq_mod_div nat_mod_as_int
    by (auto simp: nat_div_distrib nat_power_eq)
qed

lemma
  assumes "addr mod 2 ^ 56 \<ge> 15 * 2 ^ 52"
    and "(addr + offset) mod 2 ^ 56 = addr mod 2 ^ 56 + offset"
    and "addr mod 2 ^ 56 + offset < 2 ^ 56"
  shows "bin_nth (int (addr + offset)) 55"
  using assms
  unfolding bin_nth_int_eq_mod_div
  by (auto dest: even_two_times_div_two)

lemma bounds_address_offset:
  assumes "valid_address acctype addr"
    and "offset < 2 ^ 52"
    and "bounds_address acctype addr + offset < 2 ^ 64"
  shows "bounds_address acctype (addr + offset) = bounds_address acctype addr + offset"
proof -
  have "bin_nth (int addr) 55 = bin_nth (int (addr + offset)) 55
        \<and> (addr + offset) mod 2 ^ 56 = addr mod 2 ^ 56 + offset"
  proof (cases "s1_enabled acctype \<and> has_ttbr1 acctype \<and> bin_nth (int addr) 55")
    case True
    let ?baddr = "bounds_address acctype addr"
    have "?baddr = (?baddr mod 2 ^ 56) + (?baddr div 2 ^ 56 * 2 ^ 56)"
      unfolding mod_div_mult_eq
      ..
    also have "\<dots> = addr mod 2 ^ 56 + 255 * 2 ^ 56"
      using True assms(1,3)
      by (intro arg_cong2[where f = "(+)"])
         (auto simp add: bounds_address_def valid_address_def simp flip: mod_add_eq)
    finally have 1: "addr mod 2 ^ 56 + offset < 2 ^ 56" and 2: "addr mod 2 ^ 56 \<ge> 15 * 2 ^ 52"
      using True assms(1,3)
      by (auto simp: bounds_address_def valid_address_def split: if_splits)
    then have 3: "(addr + offset) mod 2 ^ 56 = addr mod 2 ^ 56 + offset"
      unfolding mod_add_left_eq[of addr "2 ^ 56" offset, symmetric]
      by auto
    moreover have "bin_nth (int (addr + offset)) 55"
      using 1 2 3
      unfolding bin_nth_int_eq_mod_div
      by (auto dest: even_two_times_div_two)
    ultimately show ?thesis
      using True
      by auto
  next
    case False
    then have 1: "addr mod 2 ^ 56 < 2 ^ 52"
      using \<open>valid_address acctype addr\<close>
      by (auto simp: valid_address_def split: if_splits)
    then have 2: "addr mod 2 ^ 56 + offset < 2 ^ 53"
      using \<open>offset < 2 ^ 52\<close>
      by auto
    then have 3: "(addr + offset) mod 2 ^ 56 = addr mod 2 ^ 56 + offset"
      unfolding mod_add_left_eq[of addr "2 ^ 56" offset, symmetric]
      by auto
    moreover have "bin_nth (int addr) 55 = bin_nth (int (addr + offset)) 55"
      using 1 2 3
      unfolding bin_nth_int_eq_mod_div
      by auto
    ultimately show ?thesis
      by auto
  qed
  then show ?thesis
    using tbi_enabled_cong[of addr "addr + offset" acctype]
    unfolding bounds_address_def
    by auto
qed

end

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
    and is_translation_event_correct:
      "\<And>vaddress acctype iswrite wasaligned size iswritevalidcap addrdesc e.
          Run (AArch64_FullTranslateWithTag vaddress acctype iswrite wasaligned size iswritevalidcap) t addrdesc \<Longrightarrow>
          \<forall>e' \<in> set t. translation_assms e' \<Longrightarrow>
          e \<in> set t \<Longrightarrow> is_mem_event e \<Longrightarrow>
          is_translation_event e"
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

lemma translate_address_page_offset:
  assumes "translate_address vaddr = Some paddr"
  shows "paddr mod 2^12 = vaddr mod 2^12"
proof -
  have *: "2^12 * (paddr div 2^12) + vaddr mod 2^12 = paddr"
    using assms translate_address_paged[of vaddr paddr vaddr]
    by auto
  have "(2^12 * (paddr div 2^12) + vaddr mod 2^12) mod 2^12 = vaddr mod 2^12"
    by simp
  then show ?thesis
    unfolding *
    .
qed

lemma AArch64_FullTranslate_translate_address[simp]:
  assumes "Run (AArch64_FullTranslate vaddress acctype iswrite wasaligned sz) t addrdesc"
    and "\<not>IsFault addrdesc" and "\<forall>e \<in> set t. translation_assms e"
  shows "translate_address (unat vaddress) = Some (unat (FullAddress_address (AddressDescriptor_paddress addrdesc)))"
  using assms
  by (auto simp: AArch64_FullTranslate_def IsFault_def elim!: Run_bindE Run_ifE)

lemma AArch64_TranslateAddressWithTag_translate_address[simp]:
  assumes "Run (AArch64_TranslateAddressWithTag vaddress acctype iswrite wasaligned sz iswritevalidcap) t addrdesc"
    and "\<not>IsFault addrdesc" and "\<forall>e \<in> set t. translation_assms e"
  shows "translate_address (unat vaddress) = Some (unat (FullAddress_address (AddressDescriptor_paddress addrdesc)))"
  using assms
  by (auto simp: AArch64_TranslateAddressWithTag_def IsFault_def elim!: Run_bindE Run_ifE)

lemma AArch64_TranslateAddress_translate_address[simp]:
  assumes "Run (AArch64_TranslateAddress vaddress acctype iswrite wasaligned sz) t addrdesc"
    and "\<not>IsFault addrdesc" and "\<forall>e \<in> set t. translation_assms e"
  shows "translate_address (unat vaddress) = Some (unat (FullAddress_address (AddressDescriptor_paddress addrdesc)))"
  using assms
  by (auto simp: AArch64_TranslateAddress_def IsFault_def elim!: Run_bindE Run_ifE)

lemma AArch64_TranslateAddressForAtomicAccess_translate_address[simp]:
  assumes "Run (AArch64_TranslateAddressForAtomicAccess vaddress sz) t addrdesc"
    and "\<not>IsFault addrdesc" and "\<forall>e \<in> set t. translation_assms e"
  shows "translate_address (unat vaddress) = Some (unat (FullAddress_address (AddressDescriptor_paddress addrdesc)))"
  using assms
  by (auto simp: AArch64_TranslateAddressForAtomicAccess_def IsFault_def elim!: Run_bindE Run_ifE Run_letE)

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

locale Morello_Axiom_Automaton = Morello_ISA + Cap_Axiom_Automaton CC ISA enabled use_mem_caps
  for enabled :: "(Capability, register_value) axiom_state \<Rightarrow> register_value event \<Rightarrow> bool"
  and use_mem_caps :: bool
begin

lemmas privilegeds_accessible_system_reg_access[intro] =
  privileged_accessible_system_reg_access[where r = "''VBAR_EL1''", simplified]
  privileged_accessible_system_reg_access[where r = "''VBAR_EL2''", simplified]
  privileged_accessible_system_reg_access[where r = "''VBAR_EL3''", simplified]
  privileged_accessible_system_reg_access[where r = "''CDBGDTR_EL0''", simplified]
  privileged_accessible_system_reg_access[where r = "''CDLR_EL0''", simplified]

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

(* The following register write is used inside loops with capability effects in some instructions,
   so we need a footprint lemma for the loop tactic to work automatically. *)
lemma no_reg_writes_to_write_reg_FPSR[no_reg_writes_toI]:
  "''FPSR'' \<notin> Rs \<Longrightarrow> no_reg_writes_to Rs (write_reg FPSR_ref v)"
  by (intro no_reg_writes_to_write_reg) (auto simp: register_defs)

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

lemma set_bit_low_get_bounds_helpers_eq:
  "int i < 64 \<Longrightarrow> CapGetExponent (set_bit c i b) = CapGetExponent c"
  "int i < 64 \<Longrightarrow> CapGetBottom (set_bit c i b) = CapGetBottom c"
  "int i < 64 \<Longrightarrow> CapGetTop (set_bit c i b) = CapGetTop c"
  unfolding CapGetExponent_def CapGetBottom_def CapGetTop_def CapGetValue_def
    CapIsInternalExponent_def CapBoundsAddress_def
  by (simp_all add: CAP_MW_def slice_set_bit_above slice_set_bit_below test_bit_set_gen)

lemma shl_int[simp]:
  "shl_int x y = Bits.shiftl x (nat y)"
  sorry (* proved in sail repo, delete once propagated *)

lemma shr_int[simp]:
  "shr_int x i = Bits.shiftr x (nat i)"
  sorry (* proved in sail repo, delete once propagated *)

definition
  I_helper :: "'a \<Rightarrow> 'a"
  where
  "I_helper x = x"

definition
  mask_range :: "nat \<Rightarrow> nat \<Rightarrow> ('a :: len) word \<Rightarrow> 'a word"
  where
  "mask_range lo_eq hi_gt x = x AND (mask hi_gt AND NOT (mask lo_eq))"

lemma test_bit_mask_range:
  "test_bit (mask_range lo_eq hi_gt x) n = (lo_eq \<le> n \<and> n < hi_gt \<and> test_bit x n)"
  apply (cases "n < size x")
  apply (auto simp add: mask_range_def word_ops_nth_size dest: test_bit_size)
  done

lemma mask_range_low_first:
  "mask_range lo_eq hi_gt x = (x AND NOT (mask lo_eq)) AND mask hi_gt"
  by (simp add: mask_range_def word_bool_alg.conj_commute word_bool_alg.conj_left_commute)

lemma vector_update_subrange_from_subrange_insert_mask:
  assumes cs: "e1 \<le> s1 \<and> 0 \<le> e1 \<and> e2 \<le> s2 \<and> 0 < e2"
  shows "vector_update_subrange_from_subrange n v1 s1 e1 v2 s2 e2
    = I_helper vector_update_subrange_from_subrange n v1 s1 e1
        (mask_range (nat e2) (nat s2 + 1) v2) s2 e2"
  using cs
  apply (simp add: word_eq_iff I_helper_def test_bit_mask_range
                   test_bit_vector_update_subrange_from_subrange)
  apply (intro allI conj_cong[OF refl] impI disj_cong[OF _ refl])
  apply (rule rev_conj_cong[where P="True", simplified, OF refl])
  apply arith
  done

lemma mask_range_add_shift_insert:
  fixes x :: "('a :: len) word"
  assumes le: "l \<le> h"
  shows
  "mask_range l h (x + word_of_int (Bits.shiftl i l))
    = I_helper mask_range l h (add_vec_int (mask_range l h x) (Bits.shiftl i l))"
  (is "mask_range _ _ (_ + ?shi) = _")
proof -

  have low_pass:
    "(x + ?shi) AND NOT (mask l) = ((x AND NOT (mask l)) + ?shi) AND NOT (mask l)"
    apply (clarsimp simp: word_eq_iff word_ops_nth_size intro!: rev_conj_cong[OF refl])
    apply (rule test_bit_plus_mask_zero[where k=l], simp_all)
    apply (simp add: word_of_int_shiftl shiftl_mask_eq_0)
    done

  have low_outside:
    "(z AND NOT (mask l)) AND mask h = (z AND mask h) AND NOT (mask l)" for z :: "'a word"
    by (simp add: word_bool_alg.conj_commute word_bool_alg.conj_left_commute)

  show ?thesis
    apply (simp add: mask_range_low_first I_helper_def low_pass)
    apply (simp add: mask_eqs low_outside[where z4="_ + _"])
    done
qed

lemma let_double_refold:
  "(let x = v in body (f x) (g x))
    = (let f_x = f v; g_x = g v in body f_x g_x)"
  by simp

lemma let_name_weak_cong:
  "v = w \<Longrightarrow> (\<And>x. f x = g x) \<Longrightarrow> (let x = v in f x) = Let w g"
  by simp

(* the top/bottom values, of size CAP_MW, are used to set the bounds,
   and they are shifted up by the exponent. the bits of the cap value are
   mostly only relevant about CAP_MW + exponent bits, but there's a
   correction adjustment that takes in the top three bits. *)
lemma CapGetBounds_set_bit_low_eq:
  shows "int i < CAP_MW - 3 \<Longrightarrow> CapGetBounds (set_bit c i b) = CapGetBounds c"
  using CapGetExponent_range[of c] [[simproc del: let_simp]]
  unfolding CapGetBounds_def CapIsExponentOutOfRange_def
  apply (subgoal_tac "int i < 64")
   apply (simp add: set_bit_low_get_bounds_helpers_eq
                     Let_def[where s="CapGetExponent _"]
                     Let_def[where s="concat_vec _ (CapBoundsAddress (CapGetValue _))"]
                     vector_update_subrange_from_subrange_insert_mask
                     CAP_MW_def CAP_MAX_EXPONENT_def
                     mask_range_add_shift_insert
          split del: if_split cong: if_cong)
   apply (subst let_double_refold[where f="mask_range _ _" and g="Word.slice _"])+
   apply (intro let_name_weak_cong refl if_cong bind_cong[OF refl])
    apply (simp_all add: CAP_MW_def word_eq_iff nth_slice word_ops_nth_size
                         test_bit_mask_range CapBoundsAddress_def sign_extend_def
                         nth_scast nth_ucast CapGetValue_def
                         test_bit_set_gen)
   apply auto
  done

lemma slice_word_update_drop:
  "j < n \<Longrightarrow> j = i + size y - 1 \<Longrightarrow> j < size x \<Longrightarrow> 0 < size y \<Longrightarrow>
    Word.slice n (word_update x i j y) = Word.slice n x"
  apply (rule word_eqI)
  apply (simp add: test_bit_word_update nth_slice)
  done

lemma CapSetFlags_get_bounds_helpers_eq:
  "CapGetExponent (CapSetFlags c flags) = CapGetExponent c"
  "CapGetBottom (CapSetFlags c flags) = CapGetBottom c"
  "CapGetTop (CapSetFlags c flags) = CapGetTop c"
  "(CapBoundsAddress (CapGetValue (CapSetFlags c flags))) = (CapBoundsAddress (CapGetValue c))"
  unfolding CapGetExponent_def CapGetBottom_def CapGetTop_def CapGetValue_def
    CapSetFlags_def CapIsInternalExponent_def CapBoundsAddress_def
  apply (simp_all add: update_subrange_vec_dec_def nth_slice test_bit_word_update
                   slice_word_update_drop)
  apply (rule word_eqI)
  apply (simp add: nth_ucast test_bit_word_update nth_slice sign_extend_def
                   nth_scast)
  done

lemma CapSetFlags_CapGetBounds:
  "CapGetBounds (CapSetFlags c flags) = CapGetBounds c"
  by (simp only: CapGetBounds_def CapSetFlags_get_bounds_helpers_eq
        CapIsExponentOutOfRange_def)

lemma leq_bounds_CapSetFlags:
  "leq_bounds CC (CapSetFlags c flags) c"
  by (simp add: leq_bounds_def get_base_def get_limit_def
        CapSetFlags_CapGetBounds CapGetBase_def)

lemma leq_cap_CapSetFlags:
  "CapIsTagSet c \<longrightarrow> \<not>CapIsSealed c \<Longrightarrow> leq_cap CC (CapSetFlags c flags) c"
  using leq_perms_cap_permits_imp[rotated]
  by (auto simp: leq_cap_def leq_bounds_CapSetFlags)

lemma leq_bounds_set_0th:
  "leq_bounds CC (set_bit c 0 b) c"
  by (simp add: leq_bounds_def get_base_def get_limit_def
        CapGetBounds_set_bit_low_eq CAP_MW_def CapGetBase_def)

lemma leq_cap_set_0th:
  "CapIsTagSet c \<longrightarrow> \<not>CapIsSealed c \<Longrightarrow> leq_cap CC (set_bit c 0 b) c"
  using leq_perms_cap_permits_imp[rotated]
  by (auto simp: leq_cap_def test_bit_set_gen leq_bounds_set_0th)

lemma Capability_of_tag_word_False_derivable[intro, simp, derivable_capsI]:
  "Capability_of_tag_word False data \<in> derivable_caps s"
  by (auto simp: derivable_caps_def)

lemma CapSetFlags_derivable[derivable_capsI]:
  assumes "c \<in> derivable_caps s" and "CapIsTagSet c \<longrightarrow> \<not>CapIsSealed c"
  shows "CapSetFlags c flags \<in> derivable_caps s"
  using assms leq_cap_CapSetFlags[OF assms(2)]
  by (auto simp: derivable_caps_def elim!: Restrict)

lemma clear_perm_leq_cap:
  assumes "CapIsTagSet c \<longrightarrow> \<not>CapIsSealed c"
  shows "leq_cap CC (clear_perm perms c) c"
proof -
  have perms: "leq_perms (to_bl (CapGetPermissions (clear_perm perms c))) (to_bl (CapGetPermissions c))"
    unfolding leq_perms_def leq_bools_iff CapGetPermissions_def CapClearPerms_def
    by (auto simp: to_bl_nth nth_slice update_subrange_vec_dec_test_bit word_ops_nth_size)
  moreover have "cap_permits CAP_PERM_GLOBAL (clear_perm perms c) \<longrightarrow> cap_permits CAP_PERM_GLOBAL c"
    using perms
    by (auto simp: leq_perms_to_bl_iff CapCheckPermissions_def word_eq_iff word_ops_nth_size)
  moreover have tag: "CapIsTagSet (clear_perm perms c) \<longleftrightarrow> CapIsTagSet c"
    and "CapIsSealed (clear_perm perms c) \<longleftrightarrow> CapIsSealed c"
    unfolding CapClearPerms_def CapIsSealed_def CapGetObjectType_def
    by (auto simp: update_subrange_vec_dec_test_bit slice_update_subrange_vec_dec_above)
  ultimately show "leq_cap CC (clear_perm perms c) c"
    using assms
    by (auto simp: leq_cap_def leq_bounds_def get_bounds_CapClearPerms_eq)
qed

lemma clear_perm_derivable:
  assumes "c \<in> derivable C" and "CapIsTagSet c \<longrightarrow> \<not>CapIsSealed c"
  shows "clear_perm perms c \<in> derivable C"
  using assms
  by (blast intro: derivable.Restrict clear_perm_leq_cap)

lemma clear_perm_derivable_caps[derivable_capsI]:
  assumes "c \<in> derivable_caps s" and "CapIsTagSet c \<longrightarrow> \<not>CapIsSealed c"
  shows "clear_perm perms c \<in> derivable_caps s"
  using assms
  unfolding derivable_caps_def
  by (auto elim: clear_perm_derivable)

lemma set_bit_0_derivable1:
  assumes "c \<in> derivable_caps s" and "CapIsTagSet c \<longrightarrow> \<not>CapIsSealed c"
  shows "set_bit c 0 b \<in> derivable_caps s"
  using assms
  by (clarsimp simp: derivable_caps_def test_bit_set_gen Restrict[OF _ leq_cap_set_0th])

lemma set_bit_0_derivable[derivable_capsI]:
  assumes "c \<in> derivable_caps s" and "CapIsTagSet c \<longrightarrow> \<not>CapIsSealed c" and BU: "b \<noteq> BU"
  shows "update_vec_dec c 0 b \<in> derivable_caps s"
  using set_bit_0_derivable1[of c s] assms
  unfolding update_vec_dec_def update_vec_dec_maybe_def update_mword_dec_def
  by (simp add: update_mword_bool_dec_def bool_of_bitU_def maybe_failwith_def
        split: bitU.split)

lemma subrange_vec_dec_128_derivable[derivable_capsI]:
  "c \<in> derivable_caps s \<Longrightarrow> subrange_vec_dec c 128 0 \<in> derivable_caps s"
  by auto

lemma update_subrange_addr_CapWithTagClear_derivable:
  fixes addr :: "64 word"
  shows "update_subrange_vec_dec (CapWithTagClear c) CAP_VALUE_HI_BIT CAP_VALUE_LO_BIT addr \<in> derivable_caps s"
  by (auto simp: derivable_caps_def update_subrange_vec_dec_test_bit)

lemma update_subrange_addr_CapIsRepresentable_derivable:
  assumes "Run (CapIsRepresentable c addr) t a" and "a"
    and "c \<in> derivable C"
    and "CapIsTagSet c \<longrightarrow> \<not>CapIsSealed c"
  shows "update_subrange_vec_dec c CAP_VALUE_HI_BIT CAP_VALUE_LO_BIT addr \<in> derivable C"
    (is "?c' \<in> derivable C")
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
  from derivable.Restrict[OF assms(3) this]
  show ?thesis .
qed

lemma update_subrange_addr_CapIsRepresentable_derivable_caps:
  assumes "Run (CapIsRepresentable c addr) t a" and "a"
    and "c \<in> derivable_caps s"
    and "CapIsTagSet c \<longrightarrow> \<not>CapIsSealed c"
  shows "update_subrange_vec_dec c CAP_VALUE_HI_BIT CAP_VALUE_LO_BIT addr \<in> derivable_caps s"
  using assms update_subrange_addr_CapIsRepresentable_derivable[OF assms(1,2)]
  by (auto simp: derivable_caps_def update_subrange_vec_dec_test_bit)

lemmas update_subrange_if_derivable =
  if_split[where P = "\<lambda>c. update_subrange_vec_dec c hi lo v \<in> derivable_caps s" for hi lo v s, THEN iffD2]

lemma cap_permits_word_update_drop:
  "j = i + size y - 1 \<and> j < size x \<and> 0 < size y \<Longrightarrow>
    i + size y < 110 \<Longrightarrow>
    cap_permits perms (word_update x i j y) = cap_permits perms x"
  by (simp add: CapCheckPermissions_def CapGetPermissions_def slice_word_update_drop)

lemma word_update_low_get_bounds_helpers_eq:
  assumes "j = i + size value' - 1" "j < size c" "0 < size value'" "j < 64"
  shows
  "CapGetExponent (word_update c i j value') = CapGetExponent c"
  "CapGetBottom (word_update c i j value') = CapGetBottom c"
  "CapGetTop (word_update c i j value') = CapGetTop c"
  unfolding CapGetExponent_def CapGetBottom_def CapGetTop_def CapGetValue_def
    CapIsInternalExponent_def CapBoundsAddress_def
  using assms
  by (simp_all add: CAP_MW_def slice_set_bit_above slice_set_bit_below test_bit_set_gen test_bit_word_update
                    slice_word_update_drop)

lemma rev_disj_cong:
  "Q = Q' \<Longrightarrow> (\<not> Q' \<Longrightarrow> P = P') \<Longrightarrow> (P \<or> Q) = (P' \<or> Q')"
  by auto

lemma expand_bitwise:
  "w = of_bl (rev (map (test_bit w) [0 ..< size w]))"
  by (simp add: word_eq_iff test_bit_of_bl)

lemma update_vec_dec_bitU_of_bool:
  "update_vec_dec x i (bitU_of_bool b) = set_bit x (nat i) b"
  by (cases b, simp_all)

lemma high_exponent_update_value_bounds_unchanged:
  "CAP_MAX_EXPONENT - 2 \<le> CapGetExponent c \<Longrightarrow>
    CapGetBounds (word_update c 0 63 (value' :: 64 word)) = CapGetBounds c"
  using CapGetExponent_range[of c] [[simproc del: let_simp]]
  unfolding CapGetBounds_def CapIsExponentOutOfRange_def
  apply (simp add: word_update_low_get_bounds_helpers_eq
                   Let_def[where s="CapGetExponent _"]
                   CAP_MAX_EXPONENT_def
        split del: if_split cong: if_cong)
  apply (simp add: word_update_low_get_bounds_helpers_eq
                   Let_def[where s="CapGetExponent _"]
                   Let_def[where s="ucast (CapBoundsAddress (CapGetValue _))"]
                   vector_update_subrange_from_subrange_insert_mask
                   CAP_MW_def CAP_MAX_EXPONENT_def
                   mask_range_add_shift_insert
        split del: if_split cong: if_cong)
  apply (subst imp_refl[where P="mask_range _ _ (ucast _) = 0", rule_format, OF word_eqI],
    solves \<open>simp add: test_bit_mask_range nth_ucast test_bit_above_size\<close>)+
  apply (intro let_cong[OF refl] if_cong refl bind_cong[OF refl])
  apply (cases "CapGetExponent c \<notin> {50, 49, 48}")
   apply (simp_all split del: if_split)
  apply (elim disjE)
    apply (simp_all add: Let_def[where f="\<lambda>_. _"] split del: if_split)
   (* 49 case: only bit 65 is adjusted, and it is masked out later *)
   apply (simp add: Let_def CAP_MW_def split del: if_split)
   apply (rule arg_cong[where f=return])
   apply (simp add: word_eq_iff word_ops_nth_size nth_ucast
                    test_bit_vector_update_subrange_from_subrange
                    I_helper_def
         split del: if_split)
  (* 48 case: atop is zero, so there's only a value-1 possible variation
              at bit 64 of limit, which the final check will kill *)
  apply (simp add: Let_def CAP_MW_def I_helper_def word_of_int_shiftl
        split del: if_split
             cong: if_cong)
  apply (subst imp_refl[where P="ucast (vector_update_subrange_from_subrange _ x _ _ _ _ _) AND mask m = ucast x AND mask m" for x m],
     solves \<open>simp add: word_eq_iff nth_ucast test_bit_vector_update_subrange_from_subrange test_bit_mask_range word_ops_nth_size
         split del: if_split cong: rev_conj_cong\<close>)+
  (* unpack the 2-bit words into a pair of bits *)
  apply (simp add:
      upt_rec[where i=0] upt_rec[where i="Suc 0"]
      HOL.trans[where r="_ :: 2 word", OF slice_shiftr expand_bitwise]
      nth_slice test_bit_vector_update_subrange_from_subrange test_bit_mask_range word_of_int_shiftl nth_shiftl
      nth_ucast nth_shiftr word_ops_nth_size
                  split del: if_split cong: if_cong)
  apply (intro conjI impI arg_cong[where f=return] arg_cong2[where f=Pair] refl word_eqI)
  apply (simp add: nth_ucast if_distrib[where f=test_bit] if_distribR
                   word_ops_nth_size update_vec_dec_bitU_of_bool test_bit_set_gen
                   test_bit_vector_update_subrange_from_subrange test_bit_mask_range
                   nth_shiftl
        split del: if_split cong: if_cong)
  (* blow up into cases and solve *)
  apply (simp add: of_bl_Cons unat_def[where w="- _"] uint_word_ariths)
  done

lemma update_subrange_addr_CapIsRepresentableFast_derivable:
  assumes "Run (CapIsRepresentableFast c incr) t a" and "a"
    and "c \<in> derivable_caps s"
    and "CapIsTagSet c \<longrightarrow> \<not>CapIsSealed c"
  shows "update_subrange_vec_dec c CAP_VALUE_HI_BIT CAP_VALUE_LO_BIT (add_vec (CapGetValue c) incr) \<in> derivable_caps s"
  using assms
  apply (simp add: update_subrange_vec_dec_def CapIsRepresentableFast_def)
  apply (clarsimp elim!: Run_elims)
  apply (split if_split_asm)
   apply (clarsimp simp: derivable_caps_def test_bit_word_update)
   apply (erule Restrict)
   apply (rule leq_cap_def[THEN iffD2, OF disjI2])
   apply (simp add: test_bit_word_update cap_permits_word_update_drop)
   apply (simp add: CapIsSealed_def CapGetObjectType_def slice_word_update_drop CapGetPermissions_def)
   apply (simp add: leq_bounds_def get_base_def get_limit_def high_exponent_update_value_bounds_unchanged
                    CapGetBase_def)
  apply (simp add: Let_def arith_shiftr_def split: if_split_asm)
   (* top of incr zero case *)
   defer
  (* top of incr ones (-1) case *)

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

lemma read_memt_accessed_mem_cap:
  assumes "Run (read_memt BC_mword BC_mword rk addr sz) t (data, tag)"
    and "tag' \<longleftrightarrow> tag = B1"
  shows "accessed_mem_cap_of_trace_if_tagged (Capability_of_tag_word tag' data) t"
proof cases
  assume "tag = B1"
  then show ?thesis
    using assms(1,2) no_cap_load_translation_events
    unfolding read_memt_def maybe_fail_def Capability_of_tag_word_def
    by (auto simp: cap_of_mem_bytes_def bind_eq_Some_conv split: option.splits
             elim!: Run_bindE read_memt_bytes_accessed_mem_cap)
next
  assume "tag \<noteq> B1"
  then show ?thesis
    using assms(1,2)
    by (auto simp: accessed_mem_cap_of_trace_if_tagged_def)
qed

lemma ReadTaggedMem_single_accessed_mem_cap:
  assumes "Run (ReadTaggedMem desc 16 accdesc) t (tag, data)"
  shows "accessed_mem_cap_of_trace_if_tagged (Capability_of_tag_word (tag !! 0) data) t"
  using assms
  unfolding ReadTaggedMem_def
  by (auto simp: Bits_def elim!: Run_bindE Run_letE Run_ifE read_memt_accessed_mem_cap)

lemma ReadTaggedMem_lower_accessed_mem_cap:
  assumes t: "Run (ReadTaggedMem desc sz accdesc) t (tag, data :: 'a::len word)"
    and sz: "LENGTH('a) = nat sz * 8" "sz = 16 \<or> sz = 32"
  shows "accessed_mem_cap_of_trace_if_tagged (Capability_of_tag_word (tag !! 0) (ucast data)) t"
  using t sz
  unfolding ReadTaggedMem_def
  by (auto simp add: Bits_def nth_ucast nth_word_cat elim!: Run_bindE Run_letE Run_ifE
           intro: read_memt_accessed_mem_cap)

lemma ReadTaggedMem_upper_accessed_mem_cap:
  assumes t: "Run (ReadTaggedMem desc sz accdesc) t (tag :: 2 word, data :: 256 word)"
    and sz: "sz = 32"
  shows "accessed_mem_cap_of_trace_if_tagged (Capability_of_tag_word (tag !! Suc 0) (Word.slice 128 data)) t"
  using t sz
  unfolding ReadTaggedMem_def
  by (auto simp add: Bits_def nth_ucast nth_word_cat slice_128_cat_cap_pair
           elim!: Run_bindE Run_letE Run_ifE intro: read_memt_accessed_mem_cap)

lemma ReadTaggedMem_lower_prod_accessed_mem_cap:
  assumes t: "Run (ReadTaggedMem desc sz accdesc) t a"
    and sz: "LENGTH('a) = nat sz * 8" "sz = 16 \<or> sz = 32"
  shows "accessed_mem_cap_of_trace_if_tagged (Capability_of_tag_word (vec_of_bits [access_vec_dec (fst a) 0] !! 0) (slice (snd a :: 'a::len word) 0 128)) t"
  using t sz
  by (cases a) (auto simp: test_bit_of_bl intro: ReadTaggedMem_lower_accessed_mem_cap)

lemma AArch64_TaggedMemSingle_lower_accessed_mem_cap:
  assumes t: "Run (AArch64_TaggedMemSingle addr sz acctype wasaligned) t a"
    and sz: "LENGTH('a) = nat sz * 8"
  shows "accessed_mem_cap_of_trace_if_tagged (Capability_of_tag_word (vec_of_bits [access_vec_dec (fst a) 0] !! 0) (slice (snd a :: 'a::len word) 0 128)) t"
  using t sz
  unfolding AArch64_TaggedMemSingle_def
  by (auto simp: test_bit_of_bl elim!: Run_bindE Run_ifE ReadTaggedMem_lower_accessed_mem_cap)

lemma AArch64_TaggedMemSingle_upper_accessed_mem_cap:
  assumes t: "Run (AArch64_TaggedMemSingle addr sz acctype wasaligned) t a"
    and sz: "sz = 32"
  shows "accessed_mem_cap_of_trace_if_tagged (Capability_of_tag_word (vec_of_bits [access_vec_dec (fst a :: 2 word) 1] !! 0) (slice (snd a :: 256 word) CAPABILITY_DBITS 128)) t"
  using t sz
  unfolding AArch64_TaggedMemSingle_def
  by (auto simp: test_bit_of_bl elim!: Run_bindE Run_ifE ReadTaggedMem_upper_accessed_mem_cap)

lemma MemC_read_accessed_mem_cap:
  assumes "Run (MemC_read addr acctype) t c"
  shows "accessed_mem_cap_of_trace_if_tagged c t"
  using assms
  unfolding MemC_read_def CapabilityFromData_def
  by (auto simp: test_bit_of_bl elim!: Run_bindE dest: AArch64_TaggedMemSingle_lower_accessed_mem_cap)

lemma MemCP_fst_accessed_mem_cap:
  assumes "Run (MemCP addr acctype) t a"
  shows "accessed_mem_cap_of_trace_if_tagged (fst a) t"
  using assms
  unfolding MemCP_def CapabilityFromData_def
  by (auto simp: test_bit_of_bl elim!: Run_bindE dest: AArch64_TaggedMemSingle_lower_accessed_mem_cap)

lemma MemCP_snd_accessed_mem_cap:
  assumes "Run (MemCP addr acctype) t a"
  shows "accessed_mem_cap_of_trace_if_tagged (snd a) t"
  using assms
  unfolding MemCP_def CapabilityFromData_def
  by (auto simp: test_bit_of_bl elim!: Run_bindE dest: AArch64_TaggedMemSingle_upper_accessed_mem_cap)

lemmas tagged_mem_primitives_accessed_mem_caps =
  ReadTaggedMem_lower_prod_accessed_mem_cap
  AArch64_TaggedMemSingle_lower_accessed_mem_cap
  AArch64_TaggedMemSingle_upper_accessed_mem_cap
  MemC_read_accessed_mem_cap
  MemCP_fst_accessed_mem_cap
  MemCP_snd_accessed_mem_cap

lemmas tagged_mem_primitives_derivable_mem_caps[derivable_capsE] =
  tagged_mem_primitives_accessed_mem_caps[THEN accessed_mem_cap_of_trace_derivable_mem_cap]

lemmas tagged_mem_primitives_derivable_caps[derivable_capsE] =
  tagged_mem_primitives_derivable_mem_caps[THEN derivable_mem_caps_derivable_caps]

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
  by (cases rule: Run_if_ELs_cases) auto

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

lemmas Run_return_VA_derivable[derivable_caps_combinators] =
   Run_return_resultE[where P = "\<lambda>va. VA_derivable va s" for s]

lemma VAFromPCC_derivable[derivable_capsE]:
  "Run (VAFromPCC offset) t va \<Longrightarrow> VA_derivable va s"
  by (auto simp: VAFromPCC_def VA_derivable_def elim: Run_bindE)

(* System register access *)

fun sysreg_ev_assms :: "register_value event \<Rightarrow> bool" where
  "sysreg_ev_assms (E_read_reg r (Regval_bitvector_129_dec c)) = (r = ''PCC'' \<longrightarrow> CapIsTagSet c \<and> \<not>CapIsSealed c)"
| "sysreg_ev_assms (E_read_reg r (Regval_bitvector_32_dec v)) = (r = ''EDSCR'' \<longrightarrow> (ucast v :: 6 word) = 2)" (* Non-debug state *)
| "sysreg_ev_assms _ = True"

definition "sysreg_trace_assms t \<equiv> (\<forall>e \<in> set t. sysreg_ev_assms e)"

lemma sysreg_trace_assms_append[simp]:
  "sysreg_trace_assms (t1 @ t2) \<longleftrightarrow> sysreg_trace_assms t1 \<and> sysreg_trace_assms t2"
  by (auto simp: sysreg_trace_assms_def)

lemma bitvector_32_dec_of_regva_eq_Some_iff[simp]:
  "bitvector_32_dec_of_regval rv = Some v \<longleftrightarrow> rv = Regval_bitvector_32_dec v"
  by (cases rv) auto

(* In Debug mode, access to system registers seems to be generally enabled, so let's assume that
   we are not in Debug mode; otherwise we'd have to tweak the properties to allow for ambient
   system register access permission. *)
lemma Halted_False:
  assumes "Run (Halted u) t a" and "sysreg_trace_assms t"
  shows "\<not>a"
  using assms
  unfolding Halted_def
  by (auto simp: EDSCR_ref_def sysreg_trace_assms_def elim!: Run_bindE Run_or_boolM_E Run_read_regE)

lemma Run_Halted_True_False[simp]:
  assumes "sysreg_trace_assms t"
  shows "Run (Halted ()) t True \<longleftrightarrow> False"
  using assms
  by (auto dest: Halted_False)

lemma no_reg_writes_to_Halted[no_reg_writes_toI]:
  "no_reg_writes_to Rs (Halted u)"
  unfolding Halted_def
  by (no_reg_writes_toI)

lemma Run_Halted_accessible_regs[accessible_regsE]:
  assumes "Run (Halted u) t h" and "sysreg_trace_assms t"
    and "Rs - (if h then privileged_regs ISA else {}) \<subseteq> accessible_regs s"
  shows "Rs \<subseteq> accessible_regs (run s t)"
  using assms
  by (intro accessible_regs_no_writes_run_subset[of "Halted u" t h Rs])
     (auto intro: no_reg_writes_runs_no_reg_writes no_reg_writes_to_Halted split: if_splits)

lemma PCC_sysreg_trace_assms:
  assumes "Run (read_reg PCC_ref) t c" and "sysreg_trace_assms t"
  shows "CapIsTagSet c" and "\<not>CapIsSealed c"
  using assms
  by (auto elim!: Run_read_regE simp: PCC_ref_def sysreg_trace_assms_def)

lemma CapIsSystemAccessEnabled_trace_allows_system_reg_access:
  assumes "Run (CapIsSystemAccessEnabled u) t a" and "sysreg_trace_assms t" and "a"
    and "{''PCC''} \<subseteq> accessible_regs s"
  shows "trace_allows_system_reg_access t s"
proof -
  obtain t1 t2 c
    where t1: "Run (Halted ()) t1 False"
      and t2: "Run (read_reg PCC_ref :: Capability M) t2 c" "sysreg_trace_assms t2"
      and "CapIsSystemAccessPermitted c"
      and t: "t = t1 @ t2"
    using assms PCC_sysreg_trace_assms
    by (auto simp: CapIsSystemAccessEnabled_def PCC_read_def
             elim!: Run_bindE dest: Halted_False)
  moreover have "CapIsTagSet c" and "\<not>CapIsSealed c"
    using PCC_sysreg_trace_assms[OF t2]
    by auto
  moreover have "{''PCC''} \<subseteq> accessible_regs (run s t1)"
    using t t1 assms(2,4)
    by - accessible_regsI
  ultimately show ?thesis
    by (auto elim!: Run_read_regE simp: PCC_ref_def)
qed

lemma CapIsSystemAccessEnabled_system_reg_access:
  assumes "Run (CapIsSystemAccessEnabled u) t a" and "sysreg_trace_assms t" and "a"
    and "{''PCC''} \<subseteq> accessible_regs s"
  shows "system_reg_access (run s t)"
  using CapIsSystemAccessEnabled_trace_allows_system_reg_access[OF assms]
  by (auto simp: system_reg_access_run_iff)

lemma no_reg_writes_to_CapIsSystemAccessEnabled[no_reg_writes_toI]:
  "no_reg_writes_to Rs (CapIsSystemAccessEnabled u)"
  unfolding CapIsSystemAccessEnabled_def Halted_def PCC_read_def bind_assoc
  by (no_reg_writes_toI)

lemma CapIsSystemAccessEnabled_accessible_regs[accessible_regsE]:
  assumes "Run (CapIsSystemAccessEnabled u) t a" and "sysreg_trace_assms t"
    and "Rs - (if a then privileged_regs ISA else {}) \<union> {''PCC''} \<subseteq> accessible_regs s"
  shows "Rs \<subseteq> accessible_regs (run s t)"
proof -
  have PCC: "{''PCC''} \<subseteq> accessible_regs s"
    using assms
    by auto
  moreover have "Rs - (if a then privileged_regs ISA else {}) \<subseteq> accessible_regs (run s t)"
    using assms
    by - (accessible_regsI)
  ultimately show ?thesis
    using CapIsSystemAccessEnabled_system_reg_access[OF assms(1,2), THEN system_reg_access_accessible_regs, of s Rs]
    by (cases a) auto
qed

lemmas CapIsSystemAccessEnabled_system_reg_access_or_ex[derivable_capsE] =
  CapIsSystemAccessEnabled_system_reg_access[THEN disjI1]

lemma Run_and_boolM_HaveCapabilitiesExt_eq[simp]:
  "and_boolM (return (HaveCapabilitiesExt ())) m = m"
  by (auto simp: HaveCapabilitiesExt_def and_boolM_def)

abbreviation
  "system_access_disabled \<equiv>
     and_boolM
       (and_boolM (return (HaveCapabilitiesExt ()))
          (CapIsSystemAccessEnabled () \<bind> (\<lambda>x. return (\<not>x))))
       (Halted () \<bind> (\<lambda>y. return (\<not>y)))"

lemma system_access_disabled_accessible_regs[accessible_regsE]:
  assumes "Run system_access_disabled t a" and "sysreg_trace_assms t"
    and "Rs - (if a then {} else privileged_regs ISA) \<union> {''PCC''} \<subseteq> accessible_regs s"
  shows "Rs \<subseteq> accessible_regs (run s t)"
proof (cases a)
  case True
  then show ?thesis
    using assms
    by - accessible_regsI
next
  case False
  then have "Run (CapIsSystemAccessEnabled ()) t True"
    using assms
    by (auto elim!: Run_bindE Run_and_boolM_E dest: Halted_False)
  then show ?thesis
    using assms(2,3) False
    by - accessible_regsI
qed

lemmas system_access_disabled_accessible_regs_or_ex[accessible_regsE] =
  system_access_disabled_accessible_regs[THEN disjI1]

lemma system_access_disabled_system_reg_access:
  assumes "Run system_access_disabled t a" and "sysreg_trace_assms t" and "\<not>a"
    and "{''PCC''} \<subseteq> accessible_regs s"
  shows "system_reg_access (run s t)"
  using assms
  by (auto elim!: Run_bindE Run_and_boolM_E CapIsSystemAccessEnabled_system_reg_access dest: Halted_False)

lemmas system_access_disabled_system_reg_access_or_ex[derivable_capsE] =
  system_access_disabled_system_reg_access[THEN disjI1]

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

definition R_name :: "int \<Rightarrow> string set" where
  "R_name n \<equiv>
     (if n =  0 then {''_R00''} else
      if n =  1 then {''_R01''} else
      if n =  2 then {''_R02''} else
      if n =  3 then {''_R03''} else
      if n =  4 then {''_R04''} else
      if n =  5 then {''_R05''} else
      if n =  6 then {''_R06''} else
      if n =  7 then {''_R07''} else
      if n =  8 then {''_R08''} else
      if n =  9 then {''_R09''} else
      if n = 10 then {''_R10''} else
      if n = 11 then {''_R11''} else
      if n = 12 then {''_R12''} else
      if n = 13 then {''_R13''} else
      if n = 14 then {''_R14''} else
      if n = 15 then {''_R15''} else
      if n = 16 then {''_R16''} else
      if n = 17 then {''_R17''} else
      if n = 18 then {''_R18''} else
      if n = 19 then {''_R19''} else
      if n = 20 then {''_R20''} else
      if n = 21 then {''_R21''} else
      if n = 22 then {''_R22''} else
      if n = 23 then {''_R23''} else
      if n = 24 then {''_R24''} else
      if n = 25 then {''_R25''} else
      if n = 26 then {''_R26''} else
      if n = 27 then {''_R27''} else
      if n = 28 then {''_R28''} else
      if n = 29 then {''_R29''} else
      if n = 30 then {''_R30''} else
      if n = 31 then {''RSP_EL0'', ''SP_EL0'', ''SP_EL1'', ''SP_EL2'', ''SP_EL3''} else
      {})"

locale Morello_Write_Cap_Automaton = Morello_ISA +
  fixes ex_traces :: bool
    and invoked_caps :: "Capability set" and invoked_regs :: "int set"
    and invoked_indirect_caps :: "Capability set" and invoked_indirect_regs :: "int set"
    and is_indirect_branch :: bool
    and no_system_reg_access :: bool
  assumes indirect_regs_indirect_branch: "invoked_indirect_regs \<noteq> {} \<longrightarrow> is_indirect_branch"
begin

lemma is_indirect_branchI[intro]:
  assumes "n \<in> invoked_indirect_regs"
  shows "is_indirect_branch"
  using assms indirect_regs_indirect_branch
  by auto

definition normalise_cursor_flags :: "Capability \<Rightarrow> bool \<Rightarrow> Capability" where
  "normalise_cursor_flags c top_bit \<equiv> CapSetFlags c (if top_bit then max_word else 0)"

definition branch_caps :: "Capability \<Rightarrow> Capability set" where
  "branch_caps c \<equiv>
     (if CapIsSealed c then
        {c}
      else
        {c, normalise_cursor_flags c (CapGetValue c !! 55), normalise_cursor_flags c False,
         set_bit c 0 False, normalise_cursor_flags (set_bit c 0 False) (CapGetValue c !! 55),
         normalise_cursor_flags (set_bit c 0 False) False})"

abbreviation mutable_perms where
  "mutable_perms \<equiv> ((CAP_PERM_STORE OR CAP_PERM_STORE_CAP) OR CAP_PERM_STORE_LOCAL) OR CAP_PERM_MUTABLE_LOAD"

definition mem_branch_caps :: "Capability \<Rightarrow> Capability set" where
  "mem_branch_caps c \<equiv>
     (if CapGetObjectType c = CAP_SEAL_TYPE_RB then {c} \<union> branch_caps (CapUnseal c)
      else branch_caps c \<union> branch_caps (clear_perm mutable_perms c))"

(* TODO *)
fun ev_assms :: "register_value event \<Rightarrow> bool" where
  "ev_assms (E_read_reg r v) =
    ((r = ''PCC'' \<longrightarrow> (\<forall>c \<in> caps_of_regval v. CapIsTagSet c \<and> \<not>CapIsSealed c \<and> (no_system_reg_access \<longrightarrow> \<not>cap_permits (CAP_PERM_EXECUTE OR CAP_PERM_SYSTEM) c))) \<and>
     (\<forall>n c. r \<in> R_name n \<and> n \<in> invoked_regs \<and> c \<in> caps_of_regval v \<and> CapIsTagSet c \<and> CapIsSealed c \<longrightarrow> branch_caps (CapUnseal c) \<subseteq> invoked_caps) \<and>
     (\<forall>n c. r \<in> R_name n \<and> n \<in> invoked_indirect_regs \<and> c \<in> caps_of_regval v \<and> CapIsTagSet c \<and> is_indirect_sentry c \<longrightarrow> CapUnseal c \<in> invoked_indirect_caps) \<and>
     (r = ''EDSCR'' \<longrightarrow> (\<forall>w. v = Regval_bitvector_32_dec w \<longrightarrow> (ucast w :: 6 word) = 2)))" (* Non-debug state *)
| "ev_assms (E_read_memt rk addr sz (bytes, tag)) =
    (is_indirect_branch \<longrightarrow> (\<forall>c. cap_of_mem_bytes bytes tag = Some c \<and> CapIsTagSet c \<longrightarrow> mem_branch_caps c \<subseteq> invoked_caps))"
| "ev_assms _ = True"

sublocale Write_Cap_Assm_Automaton
  where CC = CC and ISA = ISA and ev_assms = ev_assms ..

sublocale Morello_Axiom_Automaton where enabled = enabled and use_mem_caps = "invoked_indirect_caps = {}" ..

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
    by (auto simp: branch_caps_def normalise_cursor_flags_def test_bit_set_gen split: if_splits)
  then show ?thesis
    by (auto simp: leq_cap_def)
qed

lemma branch_caps_derivable:
  assumes "c' \<in> branch_caps c" and "CapIsTagSet c \<longrightarrow> \<not>CapIsSealed c" and "c \<in> derivable C"
  shows "c' \<in> derivable C"
  using branch_caps_leq[OF assms(1,2)] assms(3)
  by (auto intro: derivable.Restrict)

lemma branch_caps_128th_iff:
  assumes "c' \<in> branch_caps c"
  shows "c' !! 128 \<longleftrightarrow> c !! 128"
  using assms
  by (auto simp: branch_caps_def normalise_cursor_flags_def test_bit_set_gen split: if_splits)

lemma branch_caps_derivable_caps:
  assumes "c' \<in> branch_caps c" and "c \<in> derivable_caps s" and "CapIsTagSet c \<longrightarrow> \<not>CapIsSealed c"
  shows "c' \<in> derivable_caps s"
  using assms(2) branch_caps_derivable[OF assms(1,3)] branch_caps_128th_iff[OF assms(1)]
  by (auto simp: derivable_caps_def)

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

lemma CapSetFlags_CapWithTagClear_commute[simp]:
  "CapSetFlags (CapWithTagClear c) flags = CapWithTagClear (CapSetFlags c flags)"
  by (intro word_eqI)
     (auto simp: CapSetFlags_def CapWithTagClear_def test_bit_set_gen update_subrange_vec_dec_test_bit)

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
  by (auto elim!: Run_bindE Run_letE split: if_splits)

lemma C_read_branch_caps_invoked_caps[derivable_capsE]:
  assumes "Run (C_read n) t c" and "trace_assms t"
    and "n \<in> invoked_regs"
    and "CapIsTagSet c" and "CapIsSealed c"
  shows "branch_caps (CapUnseal c) \<subseteq> invoked_caps"
proof -
  obtain r where "t = [E_read_reg r (Regval_bitvector_129_dec c)]" and "r \<in> R_name n"
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

lemma C_read_unseal_invoked_indirect_caps[derivable_capsE]:
  assumes "Run (C_read n) t c" and "trace_assms t"
    and "n \<in> invoked_indirect_regs"
    and "CapIsTagSet c"
    and "CapGetObjectType c \<in> {CAP_SEAL_TYPE_LB, CAP_SEAL_TYPE_LPB}"
  shows "CapUnseal c \<in> invoked_indirect_caps"
proof -
  obtain r where "t = [E_read_reg r (Regval_bitvector_129_dec c)]" and "r \<in> R_name n"
    using assms(1,4)
    unfolding C_read_def R_read_def
    by (auto simp: R_name_def CapNull_def register_defs elim!: Run_read_regE Run_ifE)
  with assms(2-)
  show ?thesis
    by (auto simp: is_indirect_sentry_def)
qed

(*lemma CSP_read_invoked_indirect_caps[derivable_capsE]:
  assumes "Run (CSP_read u) t c" and "trace_assms t"
    and "31 \<in> invoked_indirect_regs"
    and "CapIsTagSet c"
    and "\<not>CapIsSealed c"
  shows "c \<in> invoked_indirect_caps"
proof -
  obtain r where "E_read_reg r (Regval_bitvector_129_dec c) \<in> set t" and "r \<in> R_name 31"
    using assms(1,4)
    unfolding CSP_read_def
    by (elim Run_bindE Run_if_ELs_cases Run_ifE Run_letE Run_read_regE;
        fastforce simp: R_name_def register_defs)
  then show ?thesis
    using assms(2-)
    by (induction t) (auto split: if_splits simp: is_indirect_sentry_def CapIsSealed_def)
qed*)

lemma accessed_mem_cap_of_trace_sealed_invoked_caps:
  assumes "accessed_mem_cap_of_trace_if_tagged c t"
    and "trace_assms t"
    and "CapIsTagSet c" and "CapGetObjectType c = CAP_SEAL_TYPE_RB"
    and "is_indirect_branch"
  shows "branch_caps (CapUnseal c) \<subseteq> invoked_caps"
  using assms(1-4)
  by (induction t)
     (auto simp: accessed_mem_cap_of_trace_if_tagged_def mem_branch_caps_def intro: assms(5))

lemmas tagged_mem_primitives_sealed_invoked_caps[derivable_capsE] =
  tagged_mem_primitives_accessed_mem_caps[THEN accessed_mem_cap_of_trace_sealed_invoked_caps]

lemma accessed_mem_cap_of_trace_invoked_caps:
  assumes "accessed_mem_cap_of_trace_if_tagged c t"
    and "trace_assms t"
    and "CapIsTagSet c"
    and "is_indirect_branch"
  shows "mem_branch_caps c \<subseteq> invoked_caps"
  using assms(1-3)
  by (induction t) (auto simp: accessed_mem_cap_of_trace_if_tagged_def intro: assms(4))

lemmas tagged_mem_primitives_invoked_caps[derivable_capsE] =
  tagged_mem_primitives_accessed_mem_caps[THEN accessed_mem_cap_of_trace_invoked_caps]

lemma sysreg_ev_assmsI[intro]:
  "ev_assms e \<Longrightarrow> sysreg_ev_assms e"
  by (cases e rule: sysreg_ev_assms.cases) auto

lemma sysreg_trace_assmsI[simp, intro, derivable_capsI]:
  "trace_assms t \<Longrightarrow> sysreg_trace_assms t"
  by (auto simp: sysreg_trace_assms_def trace_assms_def)

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
  (*where translate_address = translate_address
    and is_translation_event = "\<lambda>_. False"
    and translation_assms = "\<lambda>_. True"*) +
  fixes ex_traces :: bool
    and invoked_indirect_caps :: "Capability set" and invoked_indirect_regs :: "int set"
begin

fun extra_assms :: "register_value event \<Rightarrow> bool" where
  "extra_assms (E_read_reg r v) =
    ((r = ''PCC'' \<longrightarrow> (\<forall>c \<in> caps_of_regval v. CapIsTagSet c \<and> \<not>CapIsSealed c)) \<and>
     (r = ''EDSCR'' \<longrightarrow> (\<forall>w. v = Regval_bitvector_32_dec w \<longrightarrow> (ucast w :: 6 word) = 2)) \<and> \<comment> \<open>Non-debug state\<close>
     (\<forall>n c. r \<in> R_name n \<and> n \<in> invoked_indirect_regs \<and> c \<in> caps_of_regval v \<and> CapIsTagSet c \<and> is_indirect_sentry c \<longrightarrow> CapUnseal c \<in> invoked_indirect_caps))"
| "extra_assms _ = True"

sublocale Mem_Assm_Automaton
  where CC = CC and ISA = ISA
    (* and translation_assms = "\<lambda>_. True" *)
    and is_fetch = "False"
    and extra_assms = extra_assms
    and invoked_indirect_caps = invoked_indirect_caps
  ..

sublocale Morello_Axiom_Automaton
  where translate_address = "\<lambda>addr _ _. translate_address addr"
    and enabled = enabled
    (* and is_translation_event = "\<lambda>_. False" *)
    and use_mem_caps = "invoked_indirect_caps = {}"
  ..

lemma translate_address_ISA[simp]:
  "isa.translate_address ISA addr acctype t = translate_address addr"
  by (auto simp: ISA_def)

declare datatype_splits[where P = "\<lambda>m. traces_enabled m s" for s, traces_enabled_split]

lemma C_read_unseal_invoked_indirect_caps[derivable_capsE]:
  assumes "Run (C_read n) t c" and "trace_assms t"
    and "n \<in> invoked_indirect_regs"
    and "CapIsTagSet c"
    and "CapGetObjectType c \<in> {CAP_SEAL_TYPE_LB, CAP_SEAL_TYPE_LPB}"
  shows "CapUnseal c \<in> invoked_indirect_caps"
proof -
  obtain r where "t = [E_read_reg r (Regval_bitvector_129_dec c)]" and "r \<in> R_name n"
    using assms(1,4)
    unfolding C_read_def R_read_def
    by (auto simp: R_name_def CapNull_def register_defs elim!: Run_read_regE Run_ifE)
  with assms(2-)
  show ?thesis
    by (auto simp: is_indirect_sentry_def ev_assms_def)
qed

lemma CSP_read_invoked_indirect_caps[derivable_capsE]:
  assumes "Run (CSP_read u) t c" and "trace_assms t"
    and "31 \<in> invoked_indirect_regs"
    and "CapIsTagSet c"
    and "CapGetObjectType c \<in> {CAP_SEAL_TYPE_LB, CAP_SEAL_TYPE_LPB}"
  shows "CapUnseal c \<in> invoked_indirect_caps"
proof -
  obtain r where "E_read_reg r (Regval_bitvector_129_dec c) \<in> set t" and "r \<in> R_name 31"
    using assms(1,4)
    unfolding CSP_read_def
    by (elim Run_bindE Run_if_ELs_cases Run_ifE Run_letE Run_read_regE;
        fastforce simp: R_name_def register_defs)
  then show ?thesis
    using assms(2-)
    by (induction t) (auto split: if_splits simp: is_indirect_sentry_def CapIsSealed_def ev_assms_def)
qed

lemma CSP_or_C_read_unseal_invoked_indirect_caps[derivable_capsE]:
  assumes "Run (if n = 31 then CSP_read () else C_read n) t c" and "trace_assms t"
    and "n \<in> invoked_indirect_regs"
    and "CapIsTagSet c"
    and "CapGetObjectType c \<in> {CAP_SEAL_TYPE_LB, CAP_SEAL_TYPE_LPB}"
  shows "CapUnseal c \<in> invoked_indirect_caps"
  using assms
  by (auto elim!: derivable_capsE split: if_splits)

lemma sysreg_ev_assmsI[intro]:
  "ev_assms e \<Longrightarrow> sysreg_ev_assms e"
  by (cases e rule: sysreg_ev_assms.cases) (auto simp: ev_assms_def)

lemma sysreg_trace_assmsI[simp, intro, derivable_capsI]:
  "trace_assms t \<Longrightarrow> sysreg_trace_assms t"
  by (auto simp: sysreg_trace_assms_def trace_assms_def)

end

end
