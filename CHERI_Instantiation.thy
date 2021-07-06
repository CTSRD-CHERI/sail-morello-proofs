theory CHERI_Instantiation
  imports
    "Sail-Morello.Morello_lemmas"
    "Sail-T-CHERI.Cheri_axioms_lemmas"
    "Sail.Sail2_operators_mwords_lemmas"
    "Sail.Sail2_values_lemmas"
    "HOL-Library.Monad_Syntax"
    "Sail-T-CHERI.Word_Extra"
    "Sail-T-CHERI.Recognising_Automata"
    "Word_Lib.Norm_Words"
    "Sail-T-CHERI.BW2"
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

lemma and_boolM_assoc:
  "and_boolM (and_boolM m1 m2) m3 = and_boolM m1 (and_boolM m2 m3)"
  by (auto intro: bind_cong simp: and_boolM_def)

lemma or_boolM_assoc:
  "or_boolM (or_boolM m1 m2) m3 = or_boolM m1 (or_boolM m2 m3)"
  by (auto intro: bind_cong simp: or_boolM_def)

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

lemma Run_write_regE:
  assumes "Run (write_reg r v) t a"
  obtains "t = [E_write_reg (name r) (regval_of r v)]"
  using assms
  by (auto simp: write_reg_def elim: Traces_cases)

lemma concat_take_chunks_eq:
  "n > 0 \<Longrightarrow> List.concat (take_chunks n xs) = xs"
  by (induction n xs rule: take_chunks.induct) auto

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

lemma leq_bools_to_bl_iff:
  fixes x y :: "'a::len word"
  shows "leq_bools (to_bl x) (to_bl y) \<longleftrightarrow> (\<forall>n. x !! n \<longrightarrow> y !! n)"
proof
  assume leq: "leq_bools (to_bl x) (to_bl y)"
  show "\<forall>n. x !! n \<longrightarrow> y !! n"
  proof
    fix n
    have "to_bl x ! (size x - Suc n) \<longrightarrow> to_bl y ! (size y - Suc n)"
      using leq
      unfolding leq_bools_iff
      by auto
    then show "x !! n \<longrightarrow> y !! n"
      by (cases "n < LENGTH('a)") (auto simp: to_bl_nth dest: test_bit_len)
  qed
next
  assume "\<forall>n. x !! n \<longrightarrow> y !! n"
  then show "leq_bools (to_bl x) (to_bl y)"
    unfolding leq_bools_iff
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
  handled efficiently by the @{method derivable_capsI} proof method.\<close>

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
    and "a = x \<Longrightarrow> P x"
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

lemma CapGetObjectType_CapClearPerms[simp]:
  "CapGetObjectType (CapClearPerms c perms) = CapGetObjectType c"
  by (auto simp: CapClearPerms_def CapGetObjectType_def slice_update_subrange_vec_dec_above)

lemma CapIsSealed_CapClearPerms_iff[simp]:
  "CapIsSealed (CapClearPerms c perms) \<longleftrightarrow> CapIsSealed c"
  by (auto simp: CapIsSealed_def)

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

lemma CapGetPermissions_CapWithTagSet_eq[simp]:
  "CapGetPermissions (CapWithTagSet c) = CapGetPermissions c"
  unfolding CapGetPermissions_def CapWithTagSet_def
  by (intro word_eqI) (auto simp: nth_slice test_bit_set_gen)

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
    and "CapIsTagSet c'"
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

lemma HaveAArch32EL_False[simp]:
  "Run (HaveAArch32EL el) t a \<longleftrightarrow> (t = [] \<and> a = False)"
  unfolding HaveAArch32EL_def HaveAnyAArch32_def HaveEL_def
  unfolding EL0_def EL1_def EL2_def EL3_def
  by (cases el rule: exhaustive_2_word) (auto elim: Run_bindE)

lemma ELUsingAArch32_False:
  shows "\<not>Run (ELUsingAArch32 el) t True"
  unfolding ELUsingAArch32_def ELStateUsingAArch32_def ELStateUsingAArch32K_def
  by (auto elim!: Run_bindE)

lemma UsingAArch32_False[simp]:
  shows "\<not>Run (UsingAArch32 ()) t True"
  by (auto simp: UsingAArch32_def HaveAnyAArch32_def elim!: Run_elims)

lemma AddrTop_63_or_55:
  assumes "Run (AddrTop address el) t b"
  shows "b = 63 \<or> b = 55"
  using assms
  unfolding AddrTop_def
  by (auto elim!: Run_bindE simp: ELUsingAArch32_False)

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
  fix c obj_type
  show "is_tagged_method CC (seal_method CC c obj_type) = is_tagged_method CC c"
    by (auto simp: CC_def seal_def)
next
  fix c tag
  show "is_tagged_method CC (unseal_method CC c) = is_tagged_method CC c"
    by (auto simp: CC_def set_tag_def test_bit_set)
  show "is_tagged_method CC (clear_global_method CC c) = is_tagged_method CC c"
    by (auto simp: CC_def set_tag_def test_bit_set)
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
  "permits_execute_method CC c = cap_permits CAP_PERM_EXECUTE c"
  "permits_ccall_method CC c = cap_permits CAP_PERM_BRANCH_SEALED_PAIR c"
  "permits_load_method CC c = cap_permits CAP_PERM_LOAD c"
  "permits_load_cap_method CC c = cap_permits CAP_PERM_LOAD_CAP c"
  "permits_seal_method CC c = cap_permits CAP_PERM_SEAL c"
  "permits_store_method CC c = cap_permits CAP_PERM_STORE c"
  "permits_store_cap_method CC c = cap_permits CAP_PERM_STORE_CAP c"
  "permits_store_local_cap_method CC c = cap_permits CAP_PERM_STORE_LOCAL c"
  "permits_unseal_method CC c = cap_permits CAP_PERM_UNSEAL c"
  "permits_system_access_method CC c = CapIsSystemAccessPermitted c"
  "get_perms_method CC c = to_bl (CapGetPermissions c)"
  "is_global_method CC c = cap_permits CAP_PERM_GLOBAL c"
  "clear_global_method CC c = clear_perm CAP_PERM_GLOBAL c"
  by (auto simp: CC_def CapIsExecutePermitted_def get_perms_def CapIsLocal_def)

abbreviation "RV_class \<equiv> instance_Sail2_values_Register_Value_Morello_types_register_value_dict"
lemmas RV_class_def = instance_Sail2_values_Register_Value_Morello_types_register_value_dict_def

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
  "monad_return_rel (undefined_bitvector RV i) (undefined_bitvector RV j) (eq_at_bits {})"
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
  "\<exists>t. Run (choose_bool RV_class s) t b"
proof
  show "Run (choose_bool RV_class s) [E_choose s (Regval_bool b)] b"
    by (auto simp: choose_bool_def choose_convert_def choose_convert_default_def maybe_fail_def RV_class_def)
qed

lemma fold_append:
  "List.fold (\<lambda>x acc. acc @ f x) xs ys = ys @ List.concat (map f xs)"
  by (induct xs arbitrary: ys, simp_all)

lemma of_bits_nondet_witness:
  "set xs \<subseteq> {BU} \<Longrightarrow>
    \<exists>t. Run (bools_of_bits_nondet instance_Sail2_values_Register_Value_Morello_types_register_value_dict xs) t (map (\<lambda>_. False) xs)"
  using choose_bool_witness[of "''bool_of_bitU''" False]
  apply (simp add: bools_of_bits_nondet_def)
  apply (rule foreachM_witness[where g="\<lambda>_ acc. acc @ [False]"])
   apply clarsimp
   apply (frule(1) subsetD)
   apply fastforce
  apply (simp add: fold_append)
  done

lemma undefined_bitvector_witness:
  "\<exists>t. Run (undefined_bitvector instance_Sail2_values_Register_Value_Morello_types_register_value_dict n) t 0"
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

lemma get_bounds_CapWithTagSet_eq[simp]:
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

lemma CapSetObjectType_get_bounds_helpers_eq:
  "CapGetExponent (CapSetObjectType c otype) = CapGetExponent c"
  "CapGetBottom (CapSetObjectType c otype) = CapGetBottom c"
  "CapGetTop (CapSetObjectType c otype) = CapGetTop c"
  "CapGetValue (CapSetObjectType c otype) = CapGetValue c"
  unfolding CapGetExponent_def CapGetBottom_def CapGetTop_def CapGetValue_def
  unfolding CapClearPerms_def CapIsInternalExponent_def CapSetObjectType_def
  by (auto simp add: update_subrange_vec_dec_test_bit slice_update_subrange_vec_dec_above
           simp del: slice_zero)

lemma CapGetBounds_CapSetObjectType_eq:
  shows "CapGetBounds (CapSetObjectType c otype) = CapGetBounds c"
  unfolding CapGetBounds_def CapIsExponentOutOfRange_def CapSetObjectType_get_bounds_helpers_eq
  ..

lemma get_bounds_CapSetObjectType_eq:
  "get_base (CapSetObjectType c otype) = get_base c"
  "get_limit (CapSetObjectType c otype) = get_limit c"
  unfolding get_base_def CapGetBase_def get_limit_def CapGetBounds_CapSetObjectType_eq
  by auto

lemma cap_permits_CapWithTagSet_iff[simp]:
  "cap_permits perms (CapWithTagSet c) \<longleftrightarrow> cap_permits perms c"
  by (auto simp: CapCheckPermissions_def)

(* TODO: Move to Morello_Compartment locale and add system register access invariant? *)
definition cap_invariant :: "Capability \<Rightarrow> bool" where
  "cap_invariant c \<equiv> get_base c \<le> get_limit c \<and> get_limit c \<le> 2^64"

interpretation Capabilities_Invariant CC cap_invariant
  by unfold_locales
     (auto simp: cap_invariant_def seal_def get_bounds_CapClearPerms_eq get_bounds_CapUnseal_eq leq_cap_def leq_bounds_def get_bounds_CapSetObjectType_eq)

section \<open>Architecture abstraction\<close>

type_synonym instr = "(InstrEnc * 32 word)"

text \<open>TODO: Split up toplevel fetch-decode-execute function and use here.\<close>

definition instr_sem :: "instr \<Rightarrow> unit M" where
  "instr_sem instr = do {
     let (enc, opcode) = instr;
     TryInstructionExecute enc opcode
   }"

definition instr_fetch :: "instr M" where
  "instr_fetch \<equiv> do {
     CheckPendingInterrupts ();
     FetchNextInstr ()
   }"

fun caps_of_regval :: "register_value \<Rightarrow> Capability set" where
  "caps_of_regval (Regval_bitvector_129_dec c) = {c}"
| "caps_of_regval _ = {}"

text \<open>Over-approximation of invoked caps: all capabilities written to PCC.
TODO: Restrict to branching instructions and caps that result from unsealing caps in source registers.\<close>

fun instr_invokes_regs :: "instr_ast \<Rightarrow> int set" where
  "instr_invokes_regs (Instr_BRS_C_C_C (Cm, opc, Cn)) = {uint Cm, uint Cn}"
| "instr_invokes_regs (Instr_BRS_C_C (opc, Cn)) = {uint Cn}"
| "instr_invokes_regs (Instr_BLRR_C_C (opc, Cn)) = {uint Cn}"
| "instr_invokes_regs (Instr_BLRS_C_C (opc, Cn)) = {uint Cn}"
| "instr_invokes_regs (Instr_BLRS_C_C_C (Cm, opc, Cn)) = {uint Cm, uint Cn}"
| "instr_invokes_regs (Instr_BLR_C_C (opc, Cn)) = {uint Cn}"
| "instr_invokes_regs (Instr_BRR_C_C (opc, Cn)) = {uint Cn}"
| "instr_invokes_regs (Instr_BR_C_C (opc, Cn)) = {uint Cn}"
| "instr_invokes_regs (Instr_RETR_C_C (opc, Cn)) = {uint Cn}"
| "instr_invokes_regs (Instr_RETS_C_C (opc, Cn)) = {uint Cn}"
| "instr_invokes_regs (Instr_RETS_C_C_C (Cm, opc, Cn)) = {uint Cm, uint Cn}"
| "instr_invokes_regs (Instr_RET_C_C (opc, Cn)) = {uint Cn}"
| "instr_invokes_regs _ = {}"

fun instr_invokes_indirect_regs :: "instr_ast \<Rightarrow> int set" where
  "instr_invokes_indirect_regs (Instr_BLR_CI_C (imm7, Cn)) = (if uint Cn = 29 then {29} else {})"
| "instr_invokes_indirect_regs (Instr_BR_CI_C (imm7, Cn)) = (if uint Cn = 29 then {29} else {})"
| "instr_invokes_indirect_regs (Instr_LDPBLR_C_C_C (opc, Cn, Ct)) = (if uint Ct = 29 then {uint Cn} else {})"
| "instr_invokes_indirect_regs (Instr_LDPBR_C_C_C (opc, Cn, Ct)) = (if uint Ct = 29 then {uint Cn} else {})"
| "instr_invokes_indirect_regs _ = {}"

fun instr_is_indirect_branch :: "instr_ast \<Rightarrow> bool" where
  "instr_is_indirect_branch (Instr_BLR_CI_C (imm7, Cn)) = True"
| "instr_is_indirect_branch (Instr_BR_CI_C (imm7, Cn)) = True"
| "instr_is_indirect_branch (Instr_LDPBLR_C_C_C (opc, Cn, Ct)) = True"
| "instr_is_indirect_branch (Instr_LDPBR_C_C_C (opc, Cn, Ct)) = True"
| "instr_is_indirect_branch _ = False"

datatype load_auth =
  RegAuth int
  | BaseRegAuth int
  | AltBaseRegAuth int
  | PCCAuth

fun instr_load_auths :: "instr_ast \<Rightarrow> load_auth set" where
  "instr_load_auths (Instr_BLR_CI_C (imm7, Cn)) = {RegAuth (uint Cn)}"
| "instr_load_auths (Instr_BR_CI_C (imm7, Cn)) = {RegAuth (uint Cn)}"
| "instr_load_auths (Instr_ALDAR_C_R_C (L, Rn, Ct)) = {AltBaseRegAuth (uint Rn)}"
| "instr_load_auths (Instr_ALDUR_C_RI_C (op1, V, imm9, op2, Rn, Ct)) = {AltBaseRegAuth (uint Rn)}"
| "instr_load_auths (Instr_ALDR_C_RUI_C (L, imm9, op, Rn, Ct)) = {AltBaseRegAuth (uint Rn)}"
| "instr_load_auths (Instr_ALDR_C_RRB_C (Rm, sign, sz, S, L, Rn, Ct)) = {AltBaseRegAuth (uint Rn)}"
| "instr_load_auths (Instr_CASAL_C_R_C (L, Cs, R, Rn, Ct)) = {BaseRegAuth (uint Rn)}"
| "instr_load_auths (Instr_CASA_C_R_C (L, Cs, R, Rn, Ct)) = {BaseRegAuth (uint Rn)}"
| "instr_load_auths (Instr_CASL_C_R_C (L, Cs, R, Rn, Ct)) = {BaseRegAuth (uint Rn)}"
| "instr_load_auths (Instr_CAS_C_R_C (L, Cs, R, Rn, Ct)) = {BaseRegAuth (uint Rn)}"
| "instr_load_auths (Instr_LDAPR_C_R_C (Rn, Ct)) = {BaseRegAuth (uint Rn)}"
| "instr_load_auths (Instr_LDAR_C_R_C (L, Rn, Ct)) = {BaseRegAuth (uint Rn)}"
| "instr_load_auths (Instr_LDAXP_C_R_C (L, Ct2, Rn, Ct)) = {BaseRegAuth (uint Rn)}"
| "instr_load_auths (Instr_LDAXR_C_R_C (L, Rn, Ct)) = {BaseRegAuth (uint Rn)}"
| "instr_load_auths (Instr_LDNP_C_RIB_C (L, imm7, Ct2, Rn, Ct)) = {BaseRegAuth (uint Rn)}"
| "instr_load_auths (Instr_LDPBLR_C_C_C (opc, Cn, Ct)) = {RegAuth (uint Cn)}"
| "instr_load_auths (Instr_LDPBR_C_C_C (opc, Cn, Ct)) = {RegAuth (uint Cn)}"
| "instr_load_auths (Instr_LDP_CC_RIAW_C (L, imm7, Ct2, Rn, Ct)) = {BaseRegAuth (uint Rn)}"
| "instr_load_auths (Instr_LDP_C_RIB_C (L, imm7, Ct2, Rn, Ct)) = {BaseRegAuth (uint Rn)}"
| "instr_load_auths (Instr_LDP_C_RIBW_C (L, imm7, Ct2, Rn, Ct)) = {BaseRegAuth (uint Rn)}"
| "instr_load_auths (Instr_LDR_C_I_C (imm17, Ct)) = {PCCAuth}"
| "instr_load_auths (Instr_LDR_C_RIAW_C (opc, imm9, Rn, Ct)) = {BaseRegAuth (uint Rn)}"
| "instr_load_auths (Instr_LDR_C_RIBW_C (opc, imm9, Rn, Ct)) = {BaseRegAuth (uint Rn)}"
| "instr_load_auths (Instr_LDR_C_RUIB_C (L, imm12, Rn, Ct)) = {BaseRegAuth (uint Rn)}"
| "instr_load_auths (Instr_LDR_C_RRB_C (opc, Rm, sign, sz, S, Rn, Ct)) = {BaseRegAuth (uint Rn)}"
| "instr_load_auths (Instr_LDTR_C_RIB_C (opc, imm9, Rn, Ct)) = {BaseRegAuth (uint Rn)}"
| "instr_load_auths (Instr_LDUR_C_RI_C (opc, imm9, Rn, Ct)) = {BaseRegAuth (uint Rn)}"
| "instr_load_auths (Instr_LDXP_C_R_C (L, Ct2, Rn, Ct)) = {BaseRegAuth (uint Rn)}"
| "instr_load_auths (Instr_LDXR_C_R_C (L, Rn, Ct)) = {BaseRegAuth (uint Rn)}"
| "instr_load_auths (Instr_SWPAL_CC_R_C (A, R, Cs, Rn, Ct)) = {BaseRegAuth (uint Rn)}"
| "instr_load_auths (Instr_SWPA_CC_R_C (A, R, Cs, Rn, Ct)) = {BaseRegAuth (uint Rn)}"
| "instr_load_auths (Instr_SWPL_CC_R_C (A, R, Cs, Rn, Ct)) = {BaseRegAuth (uint Rn)}"
| "instr_load_auths (Instr_SWP_CC_R_C (A, R, Cs, Rn, Ct)) = {BaseRegAuth (uint Rn)}"
| "instr_load_auths (Instr_LDCT_R_R (opc, Rn, Rt)) = {BaseRegAuth (uint Rn)}"
| "instr_load_auths _ = {}"

definition cap_reg_in_load_auths :: "bool \<Rightarrow> int \<Rightarrow> load_auth set \<Rightarrow> bool" where
  "cap_reg_in_load_auths c64 n auths \<equiv> (RegAuth n \<in> auths \<or> (if c64 then BaseRegAuth n \<in> auths else AltBaseRegAuth n \<in> auths))"

definition ddc_in_load_auths :: "bool \<Rightarrow> load_auth set \<Rightarrow> bool" where
  "ddc_in_load_auths c64 auths \<equiv> (\<exists>n. if c64 then AltBaseRegAuth n \<in> auths else BaseRegAuth n \<in> auths)"

definition pcc_in_load_auths :: "load_auth set \<Rightarrow> bool" where
  "pcc_in_load_auths auths \<equiv> PCCAuth \<in> auths"

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

definition DDC_names :: "string set" where
  "DDC_names \<equiv> {''DDC_EL0'', ''RDDC_EL0'', ''DDC_EL1'', ''DDC_EL2'', ''DDC_EL3''}"

fun load_auth_reg_names :: "bool \<Rightarrow> load_auth \<Rightarrow> string set" where
  "load_auth_reg_names c64 (RegAuth n) = R_name n"
| "load_auth_reg_names c64 (BaseRegAuth n) = (if c64 then R_name n else DDC_names)"
| "load_auth_reg_names c64 (AltBaseRegAuth n) = (if c64 then DDC_names else R_name n)"
| "load_auth_reg_names c64 (PCCAuth) = {''PCC''}"

abbreviation mutable_perms where
  "mutable_perms \<equiv> ((CAP_PERM_STORE OR CAP_PERM_STORE_CAP) OR CAP_PERM_STORE_LOCAL) OR CAP_PERM_MUTABLE_LOAD"

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

definition mem_branch_caps :: "Capability \<Rightarrow> Capability set" where
  "mem_branch_caps c \<equiv>
     (if CapGetObjectType c = CAP_SEAL_TYPE_RB then {c} \<union> branch_caps (CapUnseal c)
      else branch_caps c \<union> branch_caps (clear_perm mutable_perms c))"

fun instr_of_trace :: "register_value trace \<Rightarrow> instr_ast option" where
  "instr_of_trace (E_write_reg r (Regval_instr_ast instr) # _) =
     (if r = ''__ThisInstrAbstract'' then Some instr else None)"
| "instr_of_trace _ = None"

lemma instr_of_trace_Some_iff:
  "instr_of_trace t = Some instr \<longleftrightarrow> (\<exists>t'. t = E_write_reg ''__ThisInstrAbstract'' (Regval_instr_ast instr) # t')"
  by (cases t rule: instr_of_trace.cases) auto

definition trace_invokes_indirect_regs :: "register_value trace \<Rightarrow> int set" where
  "trace_invokes_indirect_regs t \<equiv>
    (case instr_of_trace t of Some instr \<Rightarrow> instr_invokes_indirect_regs instr | None \<Rightarrow> {})"

definition trace_invokes_indirect_caps :: "register_value trace \<Rightarrow> Capability set" where
  "trace_invokes_indirect_caps t =
     {CapUnseal c' | c'.
        \<exists>n r.
         n \<in> trace_invokes_indirect_regs t \<and> r \<in> R_name n \<and>
         E_read_reg r (Regval_bitvector_129_dec c') \<in> set t \<and>
         CapIsTagSet c' \<and> CapIsSealed c' \<and> is_indirect_sentry c'}"

abbreviation invokes_indirect_caps :: "instr \<Rightarrow> register_value trace \<Rightarrow> Capability set" where
  "invokes_indirect_caps instr t \<equiv> trace_invokes_indirect_caps t"

definition trace_is_indirect_branch :: "register_value trace \<Rightarrow> bool" where
  "trace_is_indirect_branch t \<equiv> (\<exists>instr. instr_of_trace t = Some instr \<and> instr_is_indirect_branch instr)"

definition trace_invokes_regs :: "register_value trace \<Rightarrow> int set" where
  "trace_invokes_regs t \<equiv>
    (case instr_of_trace t of Some instr \<Rightarrow> instr_invokes_regs instr | None \<Rightarrow> {})"

definition trace_invokes_mem_caps :: "register_value trace \<Rightarrow> Capability set" where
  "trace_invokes_mem_caps t \<equiv>
     (if trace_is_indirect_branch t
      then {c. \<exists>rk addr sz bytes tag c'.
                 E_read_memt rk addr sz (bytes, tag) \<in> set t \<and>
                 cap_of_mem_bytes bytes tag = Some c' \<and> CapIsTagSet c' \<and>
                 c \<in> mem_branch_caps c'}
      else {})"

abbreviation invokes_mem_caps :: "instr \<Rightarrow> register_value trace \<Rightarrow> Capability set" where
  "invokes_mem_caps instr t \<equiv> trace_invokes_mem_caps t"

definition trace_invokes_caps :: "register_value trace \<Rightarrow> Capability set" where
  "trace_invokes_caps t =
     {c. \<exists>n r c'.
          n \<in> trace_invokes_regs t \<and> r \<in> R_name n \<and>
          E_read_reg r (Regval_bitvector_129_dec c') \<in> set t \<and>
          CapIsTagSet c' \<and> CapIsSealed c' \<and>
          c \<in> branch_caps (CapUnseal c')}
     \<union> invokes_mem_caps instr t"

abbreviation invokes_caps :: "instr \<Rightarrow> register_value trace \<Rightarrow> Capability set" where
  "invokes_caps instr t \<equiv> trace_invokes_caps t"

definition trace_is_in_c64 :: "register_value trace \<Rightarrow> bool" where
  "trace_is_in_c64 t \<equiv> (\<exists>pstate. E_read_reg ''PSTATE'' (Regval_ProcState pstate) \<in> set t \<and> ProcState_C64 pstate = 1)"

definition trace_load_auths :: "register_value trace \<Rightarrow> load_auth set" where
  "trace_load_auths t \<equiv>
     (case instr_of_trace t of Some instr \<Rightarrow> instr_load_auths instr | None \<Rightarrow> {})"

definition trace_uses_mem_caps :: "register_value trace \<Rightarrow> bool" where
  "trace_uses_mem_caps t \<equiv>
     (\<exists>auth r c.
        auth \<in> trace_load_auths t \<and>
        r \<in> load_auth_reg_names (trace_is_in_c64 t) auth \<and>
        E_read_reg r (Regval_bitvector_129_dec c) \<in> set t \<and>
        cap_permits CAP_PERM_LOAD_CAP c)"

abbreviation uses_mem_caps :: "instr \<Rightarrow> register_value trace \<Rightarrow> bool" where
  "uses_mem_caps instr t \<equiv> trace_uses_mem_caps t"

definition trace_has_system_reg_access :: "register_value trace \<Rightarrow> bool" where
  "trace_has_system_reg_access t \<equiv>
     (\<exists>c. E_read_reg ''PCC'' (Regval_bitvector_129_dec c) \<in> set t \<and>
          cap_permits (CAP_PERM_EXECUTE OR CAP_PERM_SYSTEM) c)"

definition instrs_of_exp :: "(register_value, 'a, 'e) monad \<Rightarrow> instr_ast set" where
  "instrs_of_exp m \<equiv> {instr. \<exists>t m'. (m, t, m') \<in> Traces \<and> instr_of_trace t = Some instr}"

definition exp_invokes_regs :: "(register_value, 'a, 'e) monad \<Rightarrow> int set" where
  "exp_invokes_regs m \<equiv> \<Union>i \<in> instrs_of_exp m. instr_invokes_regs i"

definition exp_invokes_indirect_regs :: "(register_value, 'a, 'e) monad \<Rightarrow> int set" where
  "exp_invokes_indirect_regs m \<equiv> \<Union>i \<in> instrs_of_exp m. instr_invokes_indirect_regs i"

definition exp_invokes_indirect_caps :: "(register_value, 'a, 'e) monad \<Rightarrow> Capability set" where
  "exp_invokes_indirect_caps m \<equiv> {c. \<exists>t m'. (m, t, m') \<in> Traces \<and> c \<in> trace_invokes_indirect_caps t}"

definition exp_load_auths :: "(register_value, 'a, 'e) monad \<Rightarrow> load_auth set" where
  "exp_load_auths m \<equiv> \<Union>i \<in> instrs_of_exp m. instr_load_auths i"

abbreviation "exp_is_indirect_branch m \<equiv> (\<exists>instr \<in> instrs_of_exp m. instr_is_indirect_branch instr)"

lemma exp_invokes_indirect_caps_empty_if_regs_empty[simp]:
  assumes "instr_invokes_indirect_regs instr = {}"
  shows "exp_invokes_indirect_caps (write_reg ThisInstrAbstract_ref instr \<bind> f) = {}"
  using assms
  unfolding exp_invokes_indirect_caps_def trace_invokes_indirect_caps_def trace_invokes_indirect_regs_def write_reg_def hasTrace_iff_Traces_final
  by (auto simp: instr_of_trace_Some_iff register_defs regval_of_instr_ast_def elim!: Write_reg_TracesE)

lemma instr_of_trace_bind_write_reg_ThisInstrAbstract:
  assumes "hasTrace t (write_reg ThisInstrAbstract_ref instr \<bind> f)"
  shows "instr_of_trace t = Some instr"
  using assms
  unfolding write_reg_def ThisInstrAbstract_ref_def regval_of_instr_ast_def
  by (elim hasTrace_bind_cases)
     (auto simp: hasFailure_iff_Traces_Fail hasException_iff_Traces_Exception elim!: Write_reg_TracesE)

lemma no_reg_writes_to_instr_of_trace:
  assumes "(m, t, m') \<in> Traces" and "no_reg_writes_to {''__ThisInstrAbstract''} m"
  shows "instr_of_trace t = None"
  using assms
  by (cases "instr_of_trace t";
      fastforce simp: instr_of_trace_Some_iff no_reg_writes_to_def hasTrace_iff_Traces_final)

lemma no_reg_writes_to_instrs_of_exp:
  assumes "no_reg_writes_to {''__ThisInstrAbstract''} m"
  shows "instrs_of_exp m = {}"
  using assms
  by (auto simp: instrs_of_exp_def no_reg_writes_to_instr_of_trace)

lemma instrs_of_exp_write_reg_ThisInstrAbstract[simp]:
  "instrs_of_exp (write_reg ThisInstrAbstract_ref instr \<bind> f) = {instr}"
  by (auto simp: instrs_of_exp_def  write_reg_def register_defs regval_of_instr_ast_def
           elim!: Write_reg_TracesE
           intro!: exI[where x = "[E_write_reg ''__ThisInstrAbstract'' (Regval_instr_ast instr)]"])

fun is_isa_exception :: "exception \<Rightarrow> bool" where
  "is_isa_exception (Error_ExceptionTaken u) = True"
| "is_isa_exception _ = False"

definition instr_raises_ex :: "instr \<Rightarrow> register_value trace \<Rightarrow> bool" where
  "instr_raises_ex instr t \<equiv> runTrace t (instr_sem instr) = Some (Exception (Error_ExceptionTaken ()))"

definition fetch_raises_ex :: "register_value trace \<Rightarrow> bool" where
  "fetch_raises_ex t \<equiv> runTrace t instr_fetch = Some (Exception (Error_ExceptionTaken ()))"

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
  Wellformed_Traces wellformed_ev is_isa_exception
  for wellformed_ev :: "register_value event \<Rightarrow> bool" +
  fixes translate_address :: "nat \<Rightarrow> acctype \<Rightarrow> register_value trace \<Rightarrow> nat option"
    and is_translation_event :: "register_value event \<Rightarrow> bool"
    and UNKNOWN_caps :: "Capability set"
  assumes no_cap_load_translation_events: "\<And>rk addr sz data. \<not>is_translation_event (E_read_memt rk addr sz data)"
    \<comment> \<open>TODO: Spell out assumption that register reads are well-typed, at least the ones read by
        @{term AArch64_TakeException}, guaranteeing that the latter will raise an exception rather
        than failing with a type error.\<close>
    and AArch64_TakeException_raises_isa_ex:
      "exp_raises_isa_ex (AArch64_TakeException target_el exception preferred_exception_return vect_offset)"
begin

abbreviation "translation_control_regs \<equiv>
  {''SCR_EL3'', ''TCR_EL1'', ''TCR_EL2'', ''TCR_EL3'',
   ''SCTLR_EL1'', ''SCTLR_EL2'', ''SCTLR_EL3'', ''TTBR0_EL3'', ''TTBR0_EL2'',
   ''TTBR0_EL1'', ''TTBR1_EL1'', ''TTBR1_EL2'', ''VTCR_EL2'', ''VTTBR_EL2'',
   ''MAIR_EL1'', ''MAIR_EL2'', ''MAIR_EL3'',
   ''MPAM3_EL3'', ''_MPAM2_EL2_0_62'', ''_MPAM1_EL1_0_62'',
   ''MPAM0_EL1'', ''MPAMIDR_EL1'', ''MPAMVPMV_EL2'',
   ''MPAMVPM0_EL2'', ''MPAMVPM1_EL2'', ''MPAMVPM2_EL2'', ''MPAMVPM3_EL2'',
   ''MPAMVPM4_EL2'', ''MPAMVPM5_EL2'', ''MPAMVPM6_EL2'', ''MPAMVPM7_EL2'',
   ''MPAMHCR_EL2''}"

definition "ISA \<equiv>
  \<lparr>isa.instr_sem = instr_sem,
   isa.instr_fetch = instr_fetch,
   tag_granule = 16,
   PCC = {''PCC''},
   KCC = {''VBAR_EL1'', ''VBAR_EL2'', ''VBAR_EL3''},
   IDC = {''_R29''},
   isa.caps_of_regval = caps_of_regval,
   isa.uses_mem_caps = uses_mem_caps,
   isa.invokes_indirect_caps = invokes_indirect_caps,
   isa.invokes_caps = invokes_caps,
   isa.instr_raises_ex = instr_raises_ex,
   isa.fetch_raises_ex = fetch_raises_ex,
   isa.exception_targets = exception_targets,
   read_privileged_regs = {''CDBGDTR_EL0'', ''CDLR_EL0'', ''VBAR_EL1'', ''VBAR_EL2'', ''VBAR_EL3''}, \<comment> \<open>TODO\<close>
   write_privileged_regs = {''CDBGDTR_EL0'', ''CDLR_EL0'', ''VBAR_EL1'', ''VBAR_EL2'', ''VBAR_EL3''} \<union> translation_control_regs, \<comment> \<open>TODO\<close>
   read_exception_regs = {''VBAR_EL1'', ''VBAR_EL2'', ''VBAR_EL3''},
   write_exception_regs = {},
   isa.is_translation_event = is_translation_event,
   isa.translate_address = translate_address\<rparr>"

sublocale Capability_Invariant_ISA CC ISA UNKNOWN_caps cap_invariant ..

lemma ISA_simps[simp]:
  "PCC ISA = {''PCC''}"
  "KCC ISA = {''VBAR_EL1'', ''VBAR_EL2'', ''VBAR_EL3''}"
  "IDC ISA = {''_R29''}"
  "tag_granule ISA = 16"
  "read_privileged_regs ISA = {''CDBGDTR_EL0'', ''CDLR_EL0'', ''VBAR_EL1'', ''VBAR_EL2'', ''VBAR_EL3''}"
  "write_privileged_regs ISA = {''CDBGDTR_EL0'', ''CDLR_EL0'', ''VBAR_EL1'', ''VBAR_EL2'', ''VBAR_EL3''} \<union> translation_control_regs"
  "read_exception_regs ISA = {''VBAR_EL1'', ''VBAR_EL2'', ''VBAR_EL3''}"
  "write_exception_regs ISA = {}"
  "isa.instr_sem ISA = instr_sem"
  "isa.instr_fetch ISA = instr_fetch"
  "isa.caps_of_regval ISA = caps_of_regval"
  "isa.is_translation_event ISA = is_translation_event"
  "isa.exception_targets ISA = exception_targets"
  "isa.instr_raises_ex ISA instr t = instr_raises_ex instr t"
  "isa.uses_mem_caps ISA instr t = trace_uses_mem_caps t"
  "isa.invokes_caps ISA instr t = trace_invokes_caps t"
  "isa.invokes_indirect_caps ISA instr t = trace_invokes_indirect_caps t"
  "isa.fetch_raises_ex ISA t = fetch_raises_ex t"
  "isa.translate_address ISA vaddr load t = translate_address vaddr load t"
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
  "\<And>v. instr_ast_of_regval rv = Some v \<Longrightarrow> caps_of_regval rv = {}"
  "\<And>v. bool_of_regval_method RV_class rv = Some v \<Longrightarrow> caps_of_regval rv = {}"
  "\<And>v. int_of_regval_method RV_class rv = Some v \<Longrightarrow> caps_of_regval rv = {}"
  "\<And>v. signal_of_regval rv = Some v \<Longrightarrow> caps_of_regval rv = {}"
  "\<And>xs. vector_of_regval of_rv rv = Some xs \<Longrightarrow> caps_of_regval rv = {}"
  "\<And>xs. caps_of_regval (regval_of_vector rv_of xs) = {}"
  "\<And>v. option_of_regval of_rv rv = Some v \<Longrightarrow> caps_of_regval rv = {}"
  "\<And>v. caps_of_regval (regval_of_option rv_of v) = {}"
  by (cases rv; auto simp: vector_of_regval_def regval_of_vector_def option_of_regval_def regval_of_option_def RV_class_def)+

lemma caps_of_regval_of_bitvector_129[simp]:
  "caps_of_regval (regval_of_bitvector_129_dec c) = {c}"
  by (auto simp: regval_of_bitvector_129_dec_def)

lemma member_caps_of_regval_iff[simp]:
  "c \<in> caps_of_regval rv \<longleftrightarrow> rv = Regval_bitvector_129_dec c"
  by (cases rv; auto)

lemma bitvector_129_Some_iff[simp]:
  "bitvector_129_dec_of_regval rv = Some c \<longleftrightarrow> rv = Regval_bitvector_129_dec c"
  by (cases rv) auto

lemma address_tag_aligned_iff_aligned_16[simp]:
  "address_tag_aligned ISA addr \<longleftrightarrow> aligned addr 16"
  by (auto simp: address_tag_aligned_def aligned_def)

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
  Morello_Bounds_Address_Calculation + Wellformed_Traces wellformed_ev is_isa_exception
  for wellformed_ev :: "register_value event \<Rightarrow> bool" +
  fixes translate_address :: "nat \<Rightarrow> nat option"
    and is_translation_event :: "register_value event \<Rightarrow> bool"
    (* TODO: Let assumptions refer to a trace (and possibly a state) instead of just events,
       allowing us to make assumptions about register values/fields that might change over time,
       e.g. PSTATE.EL *)
    and translation_assms :: "register_value event \<Rightarrow> bool"
    and UNKNOWN_caps :: "Capability set"
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
    and AArch64_TakeException_raises_isa_ex:
      "exp_raises_isa_ex (AArch64_TakeException target_el exception preferred_exception_return vect_offset)"
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

lemma translate_address_aligned_iff[simp]:
  assumes "translate_address vaddr = Some paddr"
    and "sz dvd 2^12"
  shows "aligned paddr sz \<longleftrightarrow> aligned vaddr sz"
proof -
  have "aligned paddr sz \<longleftrightarrow> aligned (2^12 * (paddr div 2^12) + vaddr mod 2^12) sz"
    using assms translate_address_paged[OF assms(1), where vaddr' = vaddr]
    by auto
  also have "\<dots> \<longleftrightarrow> aligned vaddr sz"
    using assms(2)
    by (auto simp: aligned_def dvd_add_right_iff dvd_mod_iff)
  finally show ?thesis
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
  using no_cap_load_translation_events AArch64_TakeException_raises_isa_ex
  by unfold_locales auto

sublocale Capability_ISA_Fixed_Translation CC ISA UNKNOWN_caps translation_assms
  by unfold_locales (auto simp: ISA_def)

end

text \<open>Instantiation of @{term translate_address} for version of spec with translation stubs\<close>

definition translate_address :: "nat \<Rightarrow> nat option" where
  "translate_address addr \<equiv> Some (addr mod 2^48)"

lemmas TranslateAddress_defs =
  AArch64_TranslateAddress_def AArch64_TranslateAddressWithTag_def AArch64_FullTranslateWithTag_def
  AArch64_FirstStageTranslateWithTag_def AArch64_SecondStageTranslate_def
  translate_address_def

section \<open>Register footprint lemmas\<close>

text \<open>The bulk of these lemmas are auto-generated in @{path CHERI_Gen_Lemmas.thy}, but we manually prove them
  for built-ins and for helper functions we prove further lemmas about below.\<close>

lemma no_reg_writes_to_undefined_bitvector[no_reg_writes_toI, simp]:
  "no_reg_writes_to Rs (undefined_bitvector RV n)"
  by (unfold undefined_bitvector_def, no_reg_writes_toI)

lemma no_reg_writes_to_undefined_bits[no_reg_writes_toI, simp]:
  "no_reg_writes_to Rs (undefined_bits RV n)"
  by (unfold undefined_bits_def, no_reg_writes_toI)

lemma no_reg_writes_to_mword_nondet[no_reg_writes_toI, simp]:
  "no_reg_writes_to Rs (mword_nondet RV n)"
  by (unfold mword_nondet_def, no_reg_writes_toI)

lemma no_reg_writes_to_undefined_bit[no_reg_writes_toI, simp]:
  "no_reg_writes_to Rs (undefined_bit u)"
  by (unfold undefined_bit_def, no_reg_writes_toI)

lemma no_reg_writes_to_undefined_bool[no_reg_writes_toI, simp]:
  "no_reg_writes_to Rs (undefined_bool RV u)"
  by (unfold undefined_bool_def, no_reg_writes_toI)

lemma no_reg_writes_to_undefined_string[no_reg_writes_toI, simp]:
  "no_reg_writes_to Rs (undefined_string RV u)"
  by (unfold undefined_string_def, no_reg_writes_toI)

lemma no_reg_writes_to_undefined_unit[no_reg_writes_toI, simp]:
  "no_reg_writes_to Rs (undefined_unit u)"
  by (unfold undefined_unit_def, no_reg_writes_toI)

lemma no_reg_writes_to_undefined_vector[no_reg_writes_toI, simp]:
  "no_reg_writes_to Rs (undefined_vector len v)"
  by (unfold undefined_vector_def, no_reg_writes_toI)

lemma no_reg_writes_to_undefined_int[no_reg_writes_toI, simp]:
  "no_reg_writes_to Rs (undefined_int RV u)"
  by (unfold undefined_int_def, no_reg_writes_toI)

lemma no_reg_writes_to_undefined_nat[no_reg_writes_toI, simp]:
  "no_reg_writes_to Rs (undefined_nat RV u)"
  by (unfold undefined_nat_def, no_reg_writes_toI)

lemma no_reg_writes_to_undefined_real[no_reg_writes_toI, simp]:
  "no_reg_writes_to Rs (undefined_real RV u)"
  by (unfold undefined_real_def, no_reg_writes_toI)

lemma no_reg_writes_to_undefined_range[no_reg_writes_toI, simp]:
  "no_reg_writes_to Rs (undefined_range RV i j)"
  by (unfold undefined_range_def, no_reg_writes_toI)

lemma no_reg_writes_to_undefined_atom[no_reg_writes_toI, simp]:
  "no_reg_writes_to Rs (undefined_atom n)"
  by (unfold undefined_atom_def, no_reg_writes_toI)

lemma no_reg_writes_to_internal_pick[no_reg_writes_toI, simp]:
  "no_reg_writes_to Rs (internal_pick RV xs)"
  by (unfold internal_pick_def, no_reg_writes_toI)

lemma no_reg_writes_to_UNKNOWN_Capability[no_reg_writes_toI, simp]:
  "no_reg_writes_to Rs (UNKNOWN_Capability n)"
  by (unfold UNKNOWN_Capability_def, no_reg_writes_toI)

lemma no_reg_writes_to_UNKNOWN_bits[no_reg_writes_toI, simp]:
  "no_reg_writes_to Rs (UNKNOWN_bits n)"
  by (unfold UNKNOWN_bits_def, no_reg_writes_toI)

lemma no_reg_writes_to_UNKNOWN_VirtualAddress[no_reg_writes_toI]:
  "no_reg_writes_to Rs (UNKNOWN_VirtualAddress u)"
  unfolding UNKNOWN_VirtualAddress_def UNKNOWN_VirtualAddressType_def undefined_VirtualAddressType_def
  by no_reg_writes_toI

(* The following register write is used inside loops with capability effects in some instructions,
   so we need a footprint lemma for the loop tactic to work automatically. *)
lemma no_reg_writes_to_write_reg_FPSR[no_reg_writes_toI]:
  "''FPSR'' \<notin> Rs \<Longrightarrow> no_reg_writes_to Rs (write_reg FPSR_ref v)"
  by (intro no_reg_writes_to_write_reg) (auto simp: register_defs)

declare datatype_splits[split]
declare datatype_splits[where P = "no_reg_writes_to Rs" for Rs, THEN iffD2, no_reg_writes_toI]
declare datatype_splits[where P = "runs_no_reg_writes_to Rs" for Rs, THEN iffD2, runs_no_reg_writes_toI]

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

lemma no_reg_writes_to_write_tag_bool[simp, no_reg_writes_toI]:
  "no_reg_writes_to Rs (write_tag_bool wk addr sz tag)"
  by (unfold write_tag_bool_def mword_nondet_def, no_reg_writes_toI)

lemma no_reg_writes_to_WriteTags[simp, no_reg_writes_toI]:
  "no_reg_writes_to Rs (WriteTags x0 x1 x2 x3)"
  by (unfold WriteTags_def, no_reg_writes_toI)

lemma no_reg_writes_to_Halted[no_reg_writes_toI]:
  "no_reg_writes_to Rs (Halted u)"
  unfolding Halted_def
  by (no_reg_writes_toI)

lemma no_reg_writes_to_CapIsSystemAccessEnabled[no_reg_writes_toI]:
  "no_reg_writes_to Rs (CapIsSystemAccessEnabled u)"
  unfolding CapIsSystemAccessEnabled_def Halted_def PCC_read_def bind_assoc
  by (no_reg_writes_toI)

section \<open>Verification framework\<close>

locale Morello_Cap_Axiom_Automaton = Morello_ISA + Cap_Axiom_Automaton CC ISA UNKNOWN_caps enabled use_mem_caps
  for enabled :: "(Capability, register_value) axiom_state \<Rightarrow> register_value event \<Rightarrow> bool"
    and use_mem_caps :: bool +
  fixes no_system_reg_access :: bool
    and is_fetch :: bool
begin

lemmas privilegeds_accessible_system_reg_access[intro] =
  privileged_accessible_system_reg_access[where r = "''VBAR_EL1''", simplified]
  privileged_accessible_system_reg_access[where r = "''VBAR_EL2''", simplified]
  privileged_accessible_system_reg_access[where r = "''VBAR_EL3''", simplified]
  privileged_accessible_system_reg_access[where r = "''CDBGDTR_EL0''", simplified]
  privileged_accessible_system_reg_access[where r = "''CDLR_EL0''", simplified]

lemma non_cap_exp_undefined_bitvector[non_cap_expI]:
  "non_cap_exp (undefined_bitvector RV n)"
  by (auto simp add: undefined_bitvector_def simp del: repeat.simps intro: non_cap_expI)

lemma non_cap_exp_undefined_bits[non_cap_expI]:
  "non_cap_exp (undefined_bits RV n)"
  by (unfold undefined_bits_def, non_cap_expI)

lemma non_cap_exp_mword_nondet[non_cap_expI]:
  "non_cap_exp (mword_nondet RV n)"
  by (unfold mword_nondet_def, non_cap_expI)

lemma non_cap_exp_undefined_bit[non_cap_expI]:
  "non_cap_exp (undefined_bit u)"
  by (unfold undefined_bit_def, non_cap_expI)

lemma non_cap_exp_undefined_bool[non_cap_expI]:
  "non_cap_exp (undefined_bool RV u)"
  by (unfold undefined_bool_def, non_cap_expI)

lemma non_cap_exp_undefined_string[non_cap_expI]:
  "non_cap_exp (undefined_string RV u)"
  by (unfold undefined_string_def, non_cap_expI)

lemma non_cap_exp_undefined_unit[non_cap_expI]:
  "non_cap_exp (undefined_unit u)"
  by (unfold undefined_unit_def, non_cap_expI)

lemma non_cap_exp_undefined_vector[non_cap_expI]:
  "non_cap_exp (undefined_vector len v)"
  by (auto simp add: undefined_vector_def simp del: repeat.simps intro: non_cap_expI)

lemma non_cap_exp_undefined_int[non_cap_expI]:
  "non_cap_exp (undefined_int RV u)"
  by (unfold undefined_int_def, non_cap_expI)

lemma non_cap_exp_undefined_nat[non_cap_expI]:
  "non_cap_exp (undefined_nat RV u)"
  by (unfold undefined_nat_def, non_cap_expI)

lemma non_cap_exp_undefined_real[non_cap_expI]:
  "non_cap_exp (undefined_real RV u)"
  by (unfold undefined_real_def, non_cap_expI)

lemma non_cap_exp_undefined_range[non_cap_expI]:
  "non_cap_exp (undefined_range RV i j)"
  by (unfold undefined_range_def, non_cap_expI)

lemma non_cap_exp_undefined_atom[non_cap_expI]:
  "non_cap_exp (undefined_atom i)"
  by (unfold undefined_atom_def, non_cap_expI)

lemma non_cap_exp_internal_pick[non_cap_expI]:
  "non_cap_exp (internal_pick RV xs)"
  by (unfold internal_pick_def, non_cap_expI)

lemma non_cap_exp_UNKNOWN_Capability[non_cap_expI]:
  "non_cap_exp (UNKNOWN_Capability u)"
  by (unfold UNKNOWN_Capability_def, non_cap_expI)

lemma non_cap_exp_UNKNOWN_bits[non_cap_expI]:
  "non_cap_exp (UNKNOWN_bits n)"
  by (unfold UNKNOWN_bits_def, non_cap_expI)

lemma non_cap_exp_UNKNOWN_VirtualAddress[non_cap_expI]:
  "non_cap_exp (UNKNOWN_VirtualAddress u)"
  unfolding UNKNOWN_VirtualAddress_def UNKNOWN_VirtualAddressType_def undefined_VirtualAddressType_def
  by non_cap_expI

declare datatype_splits[where P = "non_cap_exp", non_cap_exp_split]
declare datatype_splits[where P = "non_mem_exp", non_mem_exp_split]

lemma DDC_read_derivable[derivable_capsE]:
  "Run (DDC_read u) t c \<Longrightarrow> c \<in> derivable_caps (run s t)"
  unfolding DDC_read_def
  by (elim Run_bindE Run_if_ELs_cases Run_ifE Run_letE)
     (auto elim!: read_reg_derivable simp: register_defs accessible_regs_def)

lemma CSP_read_derivable[derivable_capsE]:
  "Run (CSP_read u) t c \<Longrightarrow> c \<in> derivable_caps (run s t)"
  unfolding CSP_read_def
  by (elim Run_bindE Run_if_ELs_cases Run_ifE Run_letE)
     (auto elim!: read_reg_derivable simp: register_defs accessible_regs_def)

lemma CapNull_derivable[simp, intro, derivable_capsI]:
  "CapNull u \<in> derivable_caps s"
  by (auto simp: derivable_caps_def CapNull_def Zeros_def zeros_def)

lemma CapWithTagClear_derivable[intro, simp, derivable_capsI]:
  "CapWithTagClear c \<in> derivable_caps s"
  by (auto simp: derivable_caps_def)

lemma leq_bools_cap_permits_imp:
  assumes "leq_bools (to_bl (CapGetPermissions c)) (to_bl (CapGetPermissions c'))"
    and "cap_permits perms c"
  shows "cap_permits perms c'"
  using assms
  by (auto simp: CapCheckPermissions_def word_eq_iff word_ops_nth_size nth_ucast leq_bools_to_bl_iff)

lemma leq_perms_cap_permits_imp:
  assumes "leq_perms CC c c'"
    and "cap_permits perms c"
  shows "cap_permits perms c'"
  by (rule leq_bools_cap_permits_imp[where c = c]) (use assms in \<open>auto simp: leq_perms_def\<close>)

lemma CapGetPermissions_eq_leq_perms:
  assumes "CapGetPermissions c = CapGetPermissions c'"
  shows "leq_perms CC c c'"
  using assms leq_bools_cap_permits_imp[of c c']
  by (auto simp: CapGetPermissions_def CapIsSystemAccessPermitted_def leq_perms_def)

lemma set_bit_low_get_bounds_helpers_eq:
  "int i < 64 \<Longrightarrow> CapGetExponent (set_bit c i b) = CapGetExponent c"
  "int i < 64 \<Longrightarrow> CapGetBottom (set_bit c i b) = CapGetBottom c"
  "int i < 64 \<Longrightarrow> CapGetTop (set_bit c i b) = CapGetTop c"
  unfolding CapGetExponent_def CapGetBottom_def CapGetTop_def CapGetValue_def
    CapIsInternalExponent_def CapBoundsAddress_def
  by (simp_all add: CAP_MW_def slice_set_bit_above slice_set_bit_below test_bit_set_gen)

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

lemma not_mask_unchanged:
  "x AND mask n = 0 \<Longrightarrow> x AND NOT (mask n) = x"
  by (simp only: word_minus_word_and_mask[symmetric], simp)

lemma mask_range_add_shiftl:
  fixes x :: "('a :: len) word"
  assumes le: "lo \<le> hi"
  shows
  "mask_range lo hi (x + (y << lo)) = (mask_range lo hi x + (y << lo)) AND mask hi"
proof -

  let ?xnolo = "x AND NOT (mask lo)"

  have low_pass:
    "(x + (y << lo)) AND NOT (mask lo) = ((x AND NOT (mask lo)) + (y << lo)) AND NOT (mask lo)"
    apply (clarsimp simp: word_eq_iff word_ops_nth_size intro!: rev_conj_cong[OF refl])
    apply (rule test_bit_plus_mask_zero[where k=lo], simp_all)
    apply (simp add: word_of_int_shiftl shiftl_mask_eq_0)
    done

  have low_outside:
    "(z AND NOT (mask lo)) AND mask hi = (z AND mask hi) AND NOT (mask lo)" for z :: "'a word"
    by (simp add: word_bool_alg.conj_commute word_bool_alg.conj_left_commute)

  have xnolo_add:
    "(?xnolo + z) AND mask lo = z AND mask lo" for z
    apply (rule HOL.trans[where s="((?xnolo AND mask lo) + z) AND mask lo"])
     apply (simp add: mask_eqs)
    apply (simp add: word_bw_assocs)
    done

  show ?thesis
    apply (simp add: mask_range_low_first I_helper_def low_pass)
    apply (simp add: mask_eqs low_outside[where z4="_ + _"])
    apply (rule not_mask_unchanged, simp)
    apply (subst mask_eqs(1)[symmetric])
    apply (simp add: word_bw_assocs shiftl_mask_eq_0)
    done
qed

lemma mask_range_add_shift_int_insert:
  fixes x :: "('a :: len) word"
  assumes le: "l \<le> h"
  shows
  "mask_range l h (x + word_of_int (Bits.shiftl i l))
    = I_helper mask_range l h (mask_range l h x + word_of_int (Bits.shiftl i l))"
  apply (simp add: mask_range_add_shiftl[OF le] word_of_int_shiftl I_helper_def)
  apply (simp add: mask_range_def)
  done

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
                     mask_range_add_shift_int_insert
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
  by (auto simp: leq_cap_def leq_bounds_CapSetFlags CapGetPermissions_eq_leq_perms)

lemma leq_bounds_set_0th:
  "leq_bounds CC (set_bit c 0 b) c"
  by (simp add: leq_bounds_def get_base_def get_limit_def
        CapGetBounds_set_bit_low_eq CAP_MW_def CapGetBase_def)

lemma leq_cap_set_0th:
  "CapIsTagSet c \<longrightarrow> \<not>CapIsSealed c \<Longrightarrow> leq_cap CC (set_bit c 0 b) c"
  using leq_perms_cap_permits_imp[rotated]
  by (auto simp: leq_cap_def test_bit_set_gen leq_bounds_set_0th CapGetPermissions_eq_leq_perms)

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
  have perms: "leq_bools (to_bl (CapGetPermissions (clear_perm perms c))) (to_bl (CapGetPermissions c))"
    unfolding leq_bools_iff CapGetPermissions_def CapClearPerms_def
    by (auto simp: to_bl_nth nth_slice update_subrange_vec_dec_test_bit word_ops_nth_size)
  moreover have "cap_permits perms' (clear_perm perms c) \<longrightarrow> cap_permits perms' c" for perms'
    using perms leq_bools_cap_permits_imp[OF perms]
    by auto
  moreover have tag: "CapIsTagSet (clear_perm perms c) \<longleftrightarrow> CapIsTagSet c"
    and "CapIsSealed (clear_perm perms c) \<longleftrightarrow> CapIsSealed c"
    unfolding CapClearPerms_def CapIsSealed_def CapGetObjectType_def
    by (auto simp: update_subrange_vec_dec_test_bit slice_update_subrange_vec_dec_above)
  ultimately show "leq_cap CC (clear_perm perms c) c"
    using assms
    by (auto simp: leq_cap_def leq_bounds_def leq_perms_def get_bounds_CapClearPerms_eq CapIsSystemAccessPermitted_def)
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
    using assms(4) CapGetPermissions_eq_leq_perms[OF perms]
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
                   mask_range_add_shift_int_insert
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

definition
  cap_bounds_calc_r3 :: "Capability \<Rightarrow> 3 word"
  where
  "cap_bounds_calc_r3 c = (let
    bottom = CapGetBottom c;
    B3 = Word.slice (nat CAP_MW - 3) bottom;
    R3 = B3 - 1
  in R3)"

definition
  cap_bounds_calc_value_a3 :: "int \<Rightarrow> 64 word \<Rightarrow> 3 word"
  where
  "cap_bounds_calc_value_a3 expon v = (let
    (a :: 66 word) = ucast (CapBoundsAddress v);
    A3 = Word.slice (nat ((CAP_MW - 3) + expon)) a
    in A3)"

(* part of the calculation of the bounds of a cap, including
   extracting the high bits of the value, getting the R3 snippet
   from the bottom, and doing a correction offset of 1 to the
   high bits if the mid bits were below the R3 snippet *)
definition
  cap_representable_base :: "Capability \<Rightarrow> 66 word"
  where
  "cap_representable_base c = (let
    bottom = CapGetBottom c;
    B3 = Word.slice (nat CAP_MW - 3) bottom;
    (R3 :: 3 word) = B3 - 1;
    expon = CapGetExponent c;
    (a :: 66 word) = ucast (CapBoundsAddress (CapGetValue c));
    A3 = Word.slice (nat (expon + CAP_MW - 3)) a;
    atop = mask_range (nat (expon + CAP_MW)) 66 a
    in atop - ((if A3 < R3 then 1 else 0) << nat (expon + CAP_MW))
  )"

lemma shiftl_minus_int_distrib:
  fixes a :: int
  shows
  "(a - b) << n = (a << n) - (b << n)"
  by (simp add: shiftl_int_def left_diff_distrib)

lemma adj_value_representable_bounds_unchanged:
  fixes c and value' :: "64 word"
  defines "c' \<equiv> (word_update c 0 63 (value' :: 64 word))"
  assumes eq: "cap_representable_base c' = cap_representable_base c"
  shows "CapGetBounds c' = CapGetBounds c"
proof -
  have sub_rearrange:
    "(a :: 66 word) + (b - c) = (a - c) + b" for a b c
    by simp

  show ?thesis
    using eq [[simproc del: let_simp]] CapGetExponent_range[of c]
    apply (simp add: CapGetBounds_def CapIsExponentOutOfRange_def
                     cap_representable_base_def c'_def
                     word_update_low_get_bounds_helpers_eq
                     vector_update_subrange_from_subrange_insert_mask
                     CAP_MW_def CAP_MAX_EXPONENT_def CAP_MAX_ENCODEABLE_EXPONENT_def
                     Let_def[where s="CapGetExponent _"]
            split del: if_split cong: if_cong)
    apply (intro if_cong refl let_cong[OF refl] bind_cong[OF refl])
    apply (unfold Let_def[where s="_ :: int"] Let_def[where s="_ :: _ word"])
    apply (intro let_cong refl if_cong)
    apply (simp add: mask_range_add_shiftl word_of_int_shiftl
        split del: if_split)
    apply (simp only: shiftl_minus_int_distrib word_of_int_shiftl[symmetric])
    apply (simp only: word_of_int_shiftl wi_hom_syms
                      if_distrib[where f="word_of_int"] word_less_nat_alt[symmetric]
                      sub_rearrange[of "mask_range _ _ _"])
    apply (simp(no_asm_use) split del: if_split cong: if_cong)
    apply simp
    done
qed

lemma CapGetValue_value_update:
  "CapGetValue (word_update c 0 63 value) = value"
  by (simp add: CapGetValue_def word_eq_iff nth_ucast test_bit_word_update)

lemma CapGetBounds_eq_leq_bounds:
  "CapGetBounds c' = CapGetBounds c \<Longrightarrow> leq_bounds CC c' c"
  by (simp add: leq_bounds_def get_base_def get_limit_def CapGetBase_def)

lemma word_le_mask_eq:
  fixes x :: "'a::len word"
  shows "(x \<le> mask n) = (x AND mask n = x)"
  apply (rule iffI)
   apply (simp add: mask_eq_iff word_le_def uint_mask)
   apply (erule order_less_le_trans)
   apply simp
  apply (metis word_and_le1)
  done

lemma plus_mask_2n_offset:
  fixes x y :: "'a::len word"
  assumes hi: "(x AND mask n) + (y AND mask n) > mask n"
  shows "(x + y) AND mask n = (x AND mask n) + (y AND mask n) - 2 ^ n"
  (is "?xy = (?plus) - 2 ^ n")
proof -
  have and_eq: "?xy AND 2 ^ n = 0"
    by (simp add: word_eq_iff word_ops_nth_size nth_w2p)

  let ?lhs = "?xy OR 2 ^ n"

  have "?plus \<noteq> ?xy"
    using hi word_and_le1[where y="x + y" and a="mask n"]
    by (metis linorder_not_le)

  then obtain j where "j < size x" "test_bit ?plus j \<noteq> test_bit ?xy j"
    by (auto simp add: word_eq_iff)

  note j = this

  have eq_lo: "?plus AND mask n = ?xy"
    by (simp add: mask_eqs)

  hence j_lo:
    "j \<ge> n"
    using j
    by (auto simp add: word_eq_iff word_ops_nth_size)

  have plus_le:
    "?plus \<le> mask (Suc n)"
    using word_and_le1[of x "mask n"] word_and_le1[of y "mask n"]
    apply (cases "Suc n < size x", simp_all)
    apply (simp add: word_le_nat_alt unat_plus_if_size unat_mask min.absorb1)
    apply arith
    done

  have j_eq:
    "j = n"
    using j j_lo plus_le[unfolded word_le_mask_eq]
    by (auto simp add: word_eq_iff word_ops_nth_size)

  have bang: "?plus !! n"
    using j_eq j
    by (simp add: word_ops_nth_size)

  have bang_eq: "i < size x \<Longrightarrow> ?lhs !! i = ?plus !! i" for i
    using bang eq_lo plus_le[unfolded word_le_mask_eq]
    apply (simp add: word_ops_nth_size nth_w2p word_eq_iff)
    apply (drule spec, drule(1) mp)+
    apply auto
    done

  hence or_eq: "?lhs = ?plus"
    by (simp add: word_eq_iff)

  thus ?thesis
    using word_plus_is_or[OF and_eq]
    by (simp add: field_simps)
qed

lemma word_plus_and_mask_eq:
  fixes x y :: "'a::len word"
  shows "x + y AND mask n = ((x AND mask n) + (y AND mask n)
     - (if (x AND mask n) + (y AND mask n) \<le> mask n then 0 else 1 << n))"
  by (clarsimp simp: word_plus_and_mask linorder_not_le plus_mask_2n_offset)

lemma word_plus_and_not_mask_eq:
  fixes x y :: "'a::len word"
  shows "x + y AND NOT (mask n) = ((x AND NOT (mask n)) + (y AND NOT (mask n))
     + (if (x AND mask n) + (y AND mask n) \<le> mask n then 0 else 1 << n))"
  by (simp add: word_minus_word_and_mask[symmetric] word_plus_and_mask_eq
         del: word_minus_word_and_mask)

lemma minus_carry_bit_mask:
  fixes x y :: "'a::len word"
  assumes x_hi: "x AND mask n = x"
  assumes y_hi: "y AND mask n = y"
  assumes n: "n < size x"
  shows "((x - y) AND mask n = (x - y)) = (y \<le> x)"
  apply (simp only: word_le_mask_eq[symmetric])
  apply (rule iffI)
   apply (simp add: word_le_def uint_sub_if_size split: if_split_asm)
   apply (cut_tac y_hi[folded word_le_mask_eq] n)
   apply (simp add: word_le_def uint_mask min.absorb1 field_simps)
   using power_increasing[where a="2 :: int" and n="Suc n" and N="size x"] uint_ge_0[where x=x]
   apply simp
  apply (rule order_trans[OF _ x_hi[folded word_le_mask_eq]])
  apply (simp add: word_sub_le_iff)
  done

lemma mask_lo_test_bit:
  "(x AND mask n = x) = (\<forall>i \<ge> n. \<not> x !! i)"
  apply (simp add: word_eq_iff word_ops_nth_size)
  apply (rule arg_cong[where f=All], rule ext)
  apply (auto dest: test_bit_size)
  done

lemma positive_2p_word:
  "((0 :: ('a :: len) word) < 2 ^ n) = (n < LENGTH ('a))"
  apply (simp only: word_neq_0_conv[symmetric] word_eq_iff)
  apply (simp add: nth_w2p)
  done

lemma word_minus_and_mask_eq:
  fixes x y :: "'a::len word"
  shows "x - y AND mask n = ((x AND mask n) - (y AND mask n)
     + (if (y AND mask n) \<le> (x AND mask n) then 0 else 1 << n))"
  (is "?lhs = ?xn - ?yn + (if ?P then _ else _)")
proof (cases "n \<ge> size x")
  case True
  then show ?thesis
    using positive_2p_word[of n, where 'a='a]
    by (simp add: word_neq_0_conv[symmetric])
next
  case False

  have less: "n < LENGTH ('a)"
    using False by simp

  have min: "min n (LENGTH ('a)) = n \<and> min (LENGTH ('a)) n = n"
    using False by auto

  let ?uxmn = "uint x mod 2 ^ n"
  let ?uymn = "uint y mod 2 ^ n"

  have "?uymn \<le> ?uxmn \<Longrightarrow> ?uxmn - ?uymn \<le> ?uxmn"
    by simp
  also have "\<dots> < 2 ^ n"
    by simp
  also have "\<dots> \<le> 2 ^ LENGTH ('a)"
    using less by simp
  also note sub_le = calculation

  have P: "(uint x - uint y) mod 2 ^ n = ((uint x mod 2 ^ n) - (uint y mod 2 ^ n)) mod 2 ^ n"
    by (simp add: pull_mods(1-4)[symmetric])

  note u2p = uint_2p[simplified positive_2p_word, OF less]

  have ineqs: "0 \<le> uint x mod 2 ^ n" "0 \<le> uint y mod 2 ^ n"
        "uint y mod 2 ^ n < 2 ^ n" "uint x mod 2 ^ n < 2 ^ n"
        "(2 ^ n) + (2 ^ n) \<le> (2 :: int) ^ LENGTH ('a)"
    using less
    by (simp_all add: power_Suc[symmetric] del: power_Suc)

  show ?thesis
    apply (clarsimp simp only: word_le_def word_uint_eq_iff uint_word_ariths uint_and_mask)
    apply (simp add: mod_exp_eq min sub_le P split del: if_split)
    apply (rule HOL.trans, rule Word.mod_sub_if_z,
        simp_all add: u2p sub_le pull_mods(5-)[symmetric])
    using ineqs
    apply (intro conjI impI int_mod_eq'[symmetric]; arith)
    done
qed

lemma word_minus_and_not_mask_eq:
  fixes x y :: "'a::len word"
  shows "x - y AND NOT (mask n) = ((x AND NOT (mask n)) - (y AND NOT (mask n))
     - (if ((y AND mask n \<le> x AND mask n)) then 0 else 1 << n))"
  by (simp add: word_minus_word_and_mask[symmetric] word_minus_and_mask_eq
         del: word_minus_word_and_mask)

lemma mask_Suc:
  "(mask (Suc n) :: ('a :: len) word) = mask n + 2 ^ n"
  by (simp add: mask_def)

lemma word_less_shift_up_add:
  fixes x :: "('a :: len) word"
  assumes "x < y"
  assumes "y < 2 ^ m"
  assumes "n + m \<le> LENGTH ('a)"
  shows "(x << n) + mask n < (y << n)"
proof -
  have u2m:
    "0 < n \<Longrightarrow> uint (2 ^ m :: 'a word) = 2 ^ m"
    using assms
    apply (cases "m = 0", simp_all)
    apply (simp add: uint_2p[simplified positive_2p_word])
    done

  have u2n:
    "0 < m \<Longrightarrow> uint (2 ^ n :: 'a word) = 2 ^ n"
    using assms
    apply (cases "n = 0", simp_all)
    apply (simp add: uint_2p[simplified positive_2p_word])
    done

  have "0 < n \<Longrightarrow> 2 ^ n * uint y < 2 ^ (n + m)"
    using assms
    by (simp add: power_add word_less_def u2m)
  also have "\<dots> \<le> 2 ^ LENGTH ('a)"
    using assms
    by simp
  also note yn_less = calculation

  have le_imp_less:
    "(x + 1 \<le> y) \<Longrightarrow> (x < y)" for x y :: int
    by simp

  show ?thesis
    using assms mult_mono[of "1 + uint x" "uint y" "2 ^ n" "2 ^ n"]
    apply (simp only: ring_distribs mult_1)
    apply (cases "m = 0", simp_all)
    apply (cases "n = 0", simp_all)
    apply (simp add: u2m u2n word_less_def mask_def shiftl_t2n uint_word_ariths yn_less)
    apply (rule order_le_less_trans[OF int_mod_le], simp_all)
    apply (rule order_le_less_trans[OF add_mono, OF int_mod_le int_mod_le], simp_all)
    apply (simp add: field_simps)
    done
qed

lemma word_less_embed:
  fixes x :: "('a :: len) word"
  assumes "x < y"
  assumes "n + size x \<le> LENGTH ('b :: len)"
  shows "(ucast x << n) + mask n < ((ucast y << n) :: 'b word)"
  using assms
  apply (cases "n = 0")
   apply (simp add: word_less_def)
  apply (rule word_less_shift_up_add[OF _ _ assms(2)])
  apply (auto simp: word_less_def uint_2p[simplified positive_2p_word])
  done

lemma word_less_embed_or:
  fixes x :: "('a :: len) word"
  assumes "x < y"
  assumes "n + size x \<le> LENGTH ('b :: len)"
  shows "(ucast x << n) OR mask n < ((ucast y << n) :: 'b word)"
  using word_less_embed[OF assms]
  by (simp add: word_plus_is_or[OF shiftl_mask_eq_0])

lemma word_le_embed:
  fixes x :: "('a :: len) word"
  assumes "x \<le> y"
  assumes "n + size x \<le> LENGTH ('b :: len)"
  shows "(ucast x << n) \<le> ((ucast y << n) :: 'b word)"
  using assms
proof -
  have P: "uint z * 2 ^ n < 2 ^ (n + size x)" for z :: "'a word"
    by (simp add: power_add)
  also have "\<dots> \<le> 2 ^ LENGTH ('b)"
    using assms
    by simp

  finally show ?thesis
    using assms
    by (simp add: word_le_def uint_shiftl bintrunc_mod2p shiftl_int_def P)
qed

lemma word_le_test_bit_mono:
  fixes x :: "('a :: len) word"
  assumes "\<forall>n < size x. x !! n \<longrightarrow> y !! n"
  shows "x \<le> y"
proof -
  have P: "x = x AND y"
    using assms
    by (simp add: word_eq_iff word_ops_nth_size cong: conj_cong)
  thus ?thesis
    by (metis word_and_le1)
qed

lemma cap_representable_base_is_sub:
  "nat (CapGetExponent c) \<le> 48 \<Longrightarrow>
  cap_representable_base c = (let
    bottom = CapGetBottom c;
    B3 = Word.slice (nat CAP_MW - 3) bottom;
    (R3 :: 3 word) = B3 - 1;
    expon = CapGetExponent c;
    a = ucast (CapBoundsAddress (CapGetValue c));
    offset = ucast R3 << (nat expon + nat CAP_MW - 3)
    in mask_range (nat (expon + CAP_MW)) 66 (a - offset)
  )"
  using CapGetExponent_range[of c]
  apply (simp add: cap_representable_base_def Let_def mask_range_def)
  apply (intro conjI impI)
   apply (simp add: word_minus_and_not_mask_eq split del: if_split)
   apply (subst if_not_P)
    apply (simp add: CAP_MW_def nat_add_distrib linorder_not_le)
    apply (subst mask_lo_test_bit[where x="_ << _", THEN iffD2])
     apply (clarsimp simp: nth_shiftl nth_ucast nth_slice dest!: test_bit_size)
     apply simp
    apply (drule word_less_embed_or[where 'b=66 and n="nat (CapGetExponent c + CAP_MW) - 3"])
     apply (simp add: CAP_MW_def)
    apply (simp add: CAP_MW_def nat_add_distrib)
    apply (erule order_le_less_trans[rotated])
    apply (rule word_le_test_bit_mono)
    apply (simp add: word_ops_nth_size nth_ucast nth_shiftl nth_slice cong: conj_cong)
    apply auto[1]
   apply simp
   apply (clarsimp simp: word_eq_iff word_ops_nth_size nth_ucast nth_shiftl
                         nat_add_distrib CAP_MW_def)
   apply (auto dest!: test_bit_size)[1]
  apply (simp add: word_minus_and_not_mask_eq split del: if_split)
  apply (subst if_P)
   apply (simp add: linorder_not_less CAP_MW_def nat_add_distrib)
   apply (rule order_trans, rule order_trans[rotated],
        erule word_le_embed[where n="nat (CapGetExponent c + CAP_MW) - 3"])
     apply (simp add: CAP_MW_def)
    apply (simp add: CAP_MW_def nat_add_distrib word_and_le2)
   apply (simp add: CAP_MW_def nat_add_distrib)
   apply (rule word_le_test_bit_mono)
   apply (clarsimp simp: word_ops_nth_size nth_shiftl nth_slice nth_ucast)
   apply arith
  apply simp
  apply (clarsimp simp: word_eq_iff word_ops_nth_size nth_ucast nth_shiftl
                        nat_add_distrib CAP_MW_def)
  apply (auto dest!: test_bit_size)[1]
  done

lemma word_le_split_mask:
  "(x \<le> y) = (x AND NOT (mask n) \<le> y AND NOT (mask n) \<and>
        (x AND NOT (mask n) = y AND NOT (mask n) \<longrightarrow> x AND mask n \<le> y AND mask n))"
  apply (rule iffI)
   apply (clarsimp simp: le_and_not_mask)
   apply (drule word_le_minus_mono_left[of _ _ "x AND NOT (mask n)"])
    apply (rule word_and_le2)
   apply (simp(no_asm_use))
   apply simp
  apply clarsimp
  apply (erule impCE)
   apply (drule(1) le_neq_trans)
   apply (rule ccontr)
   apply (simp add: linorder_not_le[symmetric] le_and_not_mask)
  apply (drule word_plus_mono_right[of _ _ "y AND mask n"])
   apply (simp add: word_and_le2)
  apply simp
  apply (drule word_plus_mono_right[of _ _ "x AND NOT (mask n)"])
   apply (subst word_plus_is_or)
    apply simp
   apply (simp add: le_word_or2)
  apply (simp add: field_simps)
  done

lemma not_mask_eq_small_diff:
  "x AND NOT (mask n) \<le> y \<Longrightarrow> y \<le> (x AND NOT (mask n)) + mask n \<Longrightarrow>
     x AND NOT (mask n) = y AND NOT (mask n)"
  using word_le_split_mask[of "x AND NOT (mask n)" y n]
    word_le_split_mask[of y "(x AND NOT (mask n)) + mask n" n]
    word_plus_is_or[of "x AND NOT (mask n)" "mask n"]
  apply (clarsimp simp: word_bw_assocs)
  apply (simp add: word_ao_dist)
  done

lemma not_mask_0_mask_same:
  "(x AND NOT (mask n) = 0) = (x AND mask n = x)"
  by (auto simp add: word_eq_iff word_ops_nth_size)

lemma not_mask_eq_small_diff2:
  "y - x \<le> mask n - (x AND mask n) \<Longrightarrow>
     x AND NOT (mask n) = y AND NOT (mask n)"
  apply (subst word_plus_and_not_mask_eq[of x "y - x" n, simplified])
  apply (subst if_P)
   apply simp
   apply (rule le_plus)
    apply (simp add: order_trans[OF word_and_le2])
   apply (rule word_and_le1)
  apply (simp add: not_mask_0_mask_same word_le_mask_eq[symmetric])
  apply (erule order_trans)
  apply (rule word_and_le1)
  done

lemma not_mask_eq_small_diff3:
  "x - y \<le> x AND mask n \<Longrightarrow>
     x AND NOT (mask n) = y AND NOT (mask n)"
  apply (subgoal_tac "y \<le> x")
   apply (rule not_mask_eq_small_diff)
    apply (frule word_le_minus_mono[OF order_refl[where x=x]])
      apply (simp add: word_and_le2)
     apply simp
    apply simp
   apply (erule order_trans)
   apply (subst word_plus_is_or)
    apply (simp add: word_bw_assocs)
   apply (rule_tac b="x OR mask n" in ord_le_eq_trans)
    apply (simp add: le_word_or2)
   apply (simp add: word_eq_iff word_ops_nth_size)
   apply blast
  apply (rule word_sub_le_iff[THEN iffD1])
  apply (erule order_trans)
  apply (simp add: word_and_le2)
  done

lemma scast_and_mask_eq_ucast:
  "n \<le> size x \<Longrightarrow> (scast x AND mask n) = (ucast x AND mask n)"
  apply (clarsimp simp: word_eq_iff word_ops_nth_size nth_ucast nth_scast)
  apply (case_tac "na = size x - 1", auto)
  done

lemma CapBoundsAddress_add_eq:
  "CapBoundsAddress (x + y) = CapBoundsAddress (x + CapBoundsAddress y)"
  apply (simp add: CapBoundsAddress_def sign_extend_def)
  apply (rule arg_cong[where f=scast])
  apply (simp only: ucast_word_and_mask[symmetric, OF order_refl, where x="_ + _"]
                    mask_eqs(2)[symmetric, where b="scast _"]
                    scast_and_mask_eq_ucast word_size)
  apply (simp only: ucast_ucast mask_eqs)
  apply simp
  done

lemma CapBoundsAddress_eq_add:
  "CapBoundsAddress x = ((x AND mask 56) + (if test_bit x 55 then NOT (mask 56) else 0))"
  apply (subst word_plus_is_or)
   apply (simp add: word_eq_iff word_ops_nth_size)
  apply (simp add: CapBoundsAddress_def sign_extend_def word_eq_iff word_ops_nth_size
                   nth_scast nth_ucast)
  apply (auto simp: linorder_not_less dest: le_imp_less_or_eq)
  done

lemma test_bit_eq_flip:
  "NO_MATCH b (test_bit w i) \<Longrightarrow> (b = test_bit x j) = (test_bit x j = b)"
  by auto

lemma CapBoundsAddress_add_66_positive:
  "(test_bit val 55 = test_bit (val + incr) 55) \<Longrightarrow>
    \<not> test_bit incr 55 \<Longrightarrow>
  let promote :: (_ \<Rightarrow> 66 word) = ucast o CapBoundsAddress in
    promote (val + incr) = promote val + promote incr"
  apply (simp add: CapBoundsAddress_def Let_def sign_extend_def)
  apply (simp add: scast_eq_ucast_or msb_nth nth_ucast ucast_or ucast_and ucast_not
                   ucast_plus_up)
  apply (simp add: word_plus_is_or[symmetric] word_bw_assocs word_bw_comms word_bw_lcs)
  apply (rule word_plus_and_mask)
  apply (simp add: test_bit_is_slice_check mask_def)
  apply (word_bitwise_eq; intro impI; simp only: simp_thms carry_def; argo)
  done

lemma CapBoundsAddress_add_66_negative:
  "(test_bit val 55 = test_bit (val + incr) 55) \<Longrightarrow>
      test_bit incr 55 \<Longrightarrow>
  let promote :: (_ \<Rightarrow> 66 word) = ucast o CapBoundsAddress in
    promote (val + incr) = promote val - ucast (- CapBoundsAddress incr)"
  apply (simp add: CapBoundsAddress_def Let_def sign_extend_def)
  apply (simp add: scast_eq_ucast_or msb_nth nth_ucast ucast_or ucast_and ucast_not
                   ucast_plus_up ucast_minus_up ucast_minus_up[where x=0, simplified]
        split del: if_split)
  apply (simp add: word_plus_is_or[symmetric] word_bw_assocs word_bw_comms word_bw_lcs)
  apply (simp add: word_plus_is_or[symmetric] ucast_not)
  apply (simp add: ucast_not word_plus_is_or[symmetric] word_bw_lcs)
  apply (simp add: word_bw_comms[where x="mask _"])
  apply (simp add: word_plus_and_mask_eq mask_eqs word_minus_and_mask_eq
                    word_minus_and_mask_eq[where x=0, simplified]
        split del: if_split)
  apply (subst if_not_P[where P="_ \<le> mask _"])
   apply (simp add: test_bit_is_slice_check mask_def)
   apply (word_bitwise_eq; intro impI; simp only: carry_def; argo)
  apply (subgoal_tac P for P, subst if_not_P[where P="_ = _"], assumption)
   prefer 2
   apply (simp add: test_bit_is_slice_check mask_def)
   apply (word_bitwise_eq; intro impI; simp only: simp_thms carry_def; argo)
  apply (simp add: test_bit_is_slice_check mask_def)
  apply (word_bitwise_eq; intro impI; unfold xor3_def carry_def; argo)
  done

lemma mask_minus_and_mask:
  fixes x :: "('a :: len) word"
  shows "mask n - (x AND mask n) = ((- 1) - x) AND mask n"
  apply (subst word_minus_and_mask_eq)
  apply (simp add: word_and_le1)
  done

lemma word_mask_eq_via_sub:
  "(x - y) AND mask n = 0 \<Longrightarrow> x AND mask n = y AND mask n"
  apply (simp add: uint_and_mask word_uint.Rep_inject[symmetric])
  apply (simp add: uint_word_ariths mod_mod_cancel le_imp_power_dvd)
  apply (drule mod_add_cong[where a'=0 and b="uint y", simplified, OF _ refl])
  apply simp
  done

(* this is only needed for diagnostic purposes
definition
  "CapGetExponent_8_word c = (of_int (CapGetExponent c) :: 8 word)"

lemma nat_CapGetExponent:
  "nat (CapGetExponent c) = unat (CapGetExponent_8_word c)"
  apply (simp add: CapGetExponent_8_word_def CapGetExponent_def)
  apply (simp add: unat_def[symmetric] of_int_uint)
  done
*)

lemma word_le_nonzero_negate_and:
  fixes x :: "('a :: len) word"
  shows "x \<le> y \<Longrightarrow> x \<noteq> 0 \<Longrightarrow> (- y) \<le> (- x) \<and> y \<noteq> 0"
  apply (frule(1) word_le_nonzero_negate)
  apply clarsimp
  done

lemma ucast_shiftl_sym:
  "(x AND mask (size x - n)) = x \<Longrightarrow> ucast x << n = ucast (x << n)"
  by (simp add: ucast_shiftl)

lemma ucast_leI:
  fixes x :: "('a :: len) word"
  fixes y :: "('b :: len) word"
  shows "x \<le> ucast y \<Longrightarrow> ucast x \<le> y"
  apply (simp only: word_le_nat_alt of_nat_unat[symmetric] unat_of_nat)
  apply (rule order_trans, erule order_trans[rotated])
   apply simp
  apply simp
  done

lemma ucast_eq_0[OF refl]:
  "z = 0 \<Longrightarrow> (ucast x = z) = (x AND mask (size z) = 0)"
  apply (simp add: word_eq_iff word_ops_nth_size nth_ucast)
  apply (safe; (simp?); frule test_bit_size; simp)
  done

lemma shiftl_eq_0_same:
  fixes x :: "('a :: len) word"
  shows "x AND NOT (mask (size x - n)) = 0 \<Longrightarrow> ((x << n) = 0) = (x = 0)"
  apply (simp add: word_eq_iff word_ops_nth_size nth_shiftl)
  apply (rule iffI; clarsimp)
  apply (drule spec, drule(1) mp, drule(1) mp)
  apply (drule_tac x="na + n" in spec)
  apply simp
  done

lemma ucast_shiftr_same[OF refl]:
  "y = ucast x \<Longrightarrow>
    (x AND mask (size y)) = x \<Longrightarrow> 
    ucast (Bits.shiftr x n) = Bits.shiftr y n"
  apply clarsimp
  apply (simp add: word_eq_iff nth_ucast nth_shiftr word_ao_nth)
  apply safe
  apply (frule test_bit_size, simp)
  apply fastforce
  done

lemma neg_neg_mask_le_or:
  "- ((- x) AND mask n) \<le> x OR NOT (mask n)"
  using plus_minus_shiftl_distrib(2)[where x="x - x" and y=1 and i=n]
  apply (simp add: word_minus_and_mask_eq[where x=0, simplified])
  apply (drule sym, drule arg_cong[where f="\<lambda>x. - x"])
  apply clarsimp
  apply (subst word_plus_is_or)
   apply (simp add: word_eq_iff word_ops_nth_size nth_shiftl)
  apply (rule word_le_test_bit_mono)
  apply (simp add: word_ops_nth_size nth_shiftl)
  done

lemma update_subrange_addr_CapIsRepresentableFast_derivable:
  assumes "Run (CapIsRepresentableFast c incr) t a" and "a"
    and "c \<in> derivable_caps s"
    and "CapIsTagSet c \<longrightarrow> \<not>CapIsSealed c"
    and "CapBoundsUsesValue (CapGetExponent c)
        \<longrightarrow> test_bit (CapGetValue c) 55 = test_bit (CapGetValue c + incr) 55"
  shows "update_subrange_vec_dec c CAP_VALUE_HI_BIT CAP_VALUE_LO_BIT (add_vec (CapGetValue c) incr) \<in> derivable_caps s"
  using assms CapGetExponent_range[of c]
  using [[simproc del: let_simp]]
  apply (clarsimp simp: derivable_caps_def test_bit_word_update update_subrange_vec_dec_def)
  apply (rule Restrict, assumption)
  apply (rule leq_cap_def[THEN iffD2, OF disjI2])
  apply (simp add: test_bit_word_update cap_permits_word_update_drop)
  apply (simp add: CapIsSealed_def CapGetObjectType_def slice_word_update_drop CapGetPermissions_def CapGetPermissions_eq_leq_perms)
  apply (rule CapGetBounds_eq_leq_bounds)
  apply (clarsimp simp: CapIsRepresentableFast_def word_less_nat_alt[symmetric] word_le_nat_alt[symmetric]
                 elim!: Run_elims cong: if_cong)
  apply (split if_split_asm)
   apply (simp add: high_exponent_update_value_bounds_unchanged)
  apply (simp add: Let_def arith_shiftr_def
                   cap_bounds_calc_r3_def[unfolded Let_def CAP_MW_def, simplified, symmetric]
            split: if_split_asm)
   (* top of incr zero case *)
   apply (simp add: uint_0_iff arith_shiftr_mword_def word_less_nat_alt[symmetric])
   apply (rule adj_value_representable_bounds_unchanged)
   apply (simp add: cap_representable_base_is_sub Let_def CapGetValue_value_update
                    word_update_low_get_bounds_helpers_eq linorder_not_le
                    CAP_MAX_EXPONENT_def CAP_MW_def nat_add_distrib)
   apply (thin_tac "Run _ _ _")+
   apply (simp add: CapGetValue_value_update
                    CapBoundsUsesValue_def CAP_MW_def CAP_VALUE_NUM_BITS_def)
   apply (drule CapBoundsAddress_add_66_positive)
    apply (drule_tac x=63 in word_eqD)+
    apply (simp add: nth_sshiftr CapBoundsAddress_def sign_extend_def nth_scast nth_ucast)
   apply (clarsimp simp: Let_def mask_range_def)
   apply (rule sym, rule not_mask_eq_small_diff2)
   apply simp
   apply (rule order_trans, rule order_trans[rotated],
        erule word_less_embed_or[where n="nat (CapGetExponent c)", THEN order_less_imp_le])
     apply simp
    apply (rule word_le_test_bit_mono)
    apply (simp add: nth_ucast word_ops_nth_size nth_shiftl nth_shiftr)
    apply clarsimp
    apply (frule_tac n=n in test_bit_size)
    apply (simp add: nth_sshiftr CAP_MW_def nat_add_distrib)
    apply (intro conjI, simp_all)[1]
    apply (rule ccontr)
    apply (drule_tac x="n - nat (CapGetExponent c + CAP_MW)" in word_eqD)+
    apply (simp add: nth_sshiftr CAP_MW_def nat_add_distrib)
   apply (simp add: word_cat_shiftl_OR)
   apply (simp add: slice_shiftr ucast_minus word_and_mask_shiftl_eq)
   apply (thin_tac "P" for P)+
   apply (simp add: plus_minus_shiftl_distrib shiftr_shiftl_alt word_and_mask_shiftl_eq
                    ucast_up_shiftr word_bw_assocs mask_eqs ucast_minus
               del: shiftl_1)
   apply (simp add: mask_minus_and_mask[simplified] ucast_and
            mask_eqs word_bw_assocs diff_diff_eq
      del: shiftl_1)
   apply (simp add: ucast_not del: shiftl_1)
   apply (simp add: field_simps del: shiftl_1)
   apply (simp add: word_bw_assocs[symmetric] word_and_mask_shiftl_eq mask_eqs add.commute
        del: shiftl_1)
   apply (rule ord_eq_le_trans[OF _ word_and_le2[where y="NOT (mask (nat (CapGetExponent c)))"]])
   apply (simp only:  word_bw_assocs word_bw_comms[where y="NOT _"])
   apply (simp only: word_bw_assocs[symmetric])
   apply (rule word_mask_eq_via_sub)
   apply (simp only: word_bw_comms[where x="NOT _"])
   apply (simp only: word_minus_word_and_mask[symmetric] field_simps)
   apply (simp add: ucast_shiftl mask_def[where n=3, simplified] word_shiftl_add[symmetric]
        del: shiftl_1)
   apply (simp add: add_and_masks shiftl_mask_eq_0 del: shiftl_1)
   apply (simp add: mask_eqs)
   apply (simp add: add.commute word_not_two_complement[symmetric]
        mask_minus_word_and_mask[symmetric] del: mask_minus_word_and_mask)
   apply (simp add: mask_def)
  (* top of incr negative (1-s) case *)
  apply (rule adj_value_representable_bounds_unchanged)
  apply (simp add: cap_representable_base_is_sub Let_def CapGetValue_value_update
                   word_update_low_get_bounds_helpers_eq linorder_not_le
                   CAP_MAX_EXPONENT_def CAP_MW_def nat_add_distrib)
  apply (thin_tac "Run _ _ _")+
  apply (simp add: CapGetValue_value_update
                   CapBoundsUsesValue_def CAP_MW_def CAP_VALUE_NUM_BITS_def
                   arith_shiftr_mword_def nat_add_distrib)
  apply (drule CapBoundsAddress_add_66_negative)
   apply (drule word_eqD[where x=63])+
   apply (simp add: nth_sshiftr CapBoundsAddress_def sign_extend_def nth_scast nth_ucast)
  apply (clarsimp simp: Let_def mask_range_def)
  apply (rule sym, rule not_mask_eq_small_diff3)
  apply simp
  apply (drule word_le_nonzero_negate_and)
   apply simp
  apply clarsimp
  apply (rule order_trans, rule order_trans[rotated],
    erule_tac n="nat (CapGetExponent c)" in word_le_embed)
    apply simp
   apply (rule ucast_leI)
   apply (rule word_le_nonzero_negateI[rotated])
    apply (simp add: ucast_eq_0)
    apply (subst word_le_mask_eq[THEN iffD1])
     apply (simp(no_asm) add: word_le_mask_eq[simplified word_eq_iff])
     apply (simp add: word_ops_nth_size nth_shiftl nth_ucast nth_shiftr
              plus_minus_shiftl_distrib[where x=0, simplified])
     apply (auto dest: test_bit_size)[1]
    apply (subst shiftl_eq_0_same)
     apply (rule word_eqI, clarsimp simp: word_ops_nth_size nth_ucast)
     apply (auto dest: test_bit_size)[1]
    apply (simp add: ucast_eq_0)
   apply (simp add: ucast_uminus plus_minus_shiftl_distrib[where x=0, simplified])
   apply (simp add: ucast_and ucast_up_shiftr ucast_shiftl min_absorb1)
   apply (simp add: ucast_uminus word_and_mask_shiftl_eq
              plus_minus_shiftl_distrib[where x=0, simplified])
   apply (rule neg_neg_mask_le_or[THEN order_trans])
   apply (rule word_le_test_bit_mono)
   apply (simp add: word_ops_nth_size nth_shiftl nth_ucast nth_shiftr)
   apply (intro allI conjI impI; clarify?)
    apply simp
   apply (drule_tac x="n - (16 + nat (CapGetExponent c))" in word_eqD[where v=max_word])
   apply (simp add: nth_sshiftr)
   apply arith
  (* down to value/bottom calculations *)
  apply (rule ord_eq_le_trans[OF _ word_and_le2[where y="NOT (mask (nat (CapGetExponent c)))"]])
  apply (thin_tac P for P)+
  apply (simp only: word_bw_assocs)
  apply (simp only:  word_bw_assocs word_bw_comms[where y="NOT _"])
  apply (simp only: word_bw_assocs[symmetric])
  apply (simp(no_asm) add: word_minus_and_not_mask_eq shiftl_mask_eq_0)
  apply (simp add: ucast_minus word_and_mask_shiftl_eq)
  apply (simp add: add.commute mask_eqs plus_minus_shiftl_distrib)

  apply (simp add: add_and_masks)
  apply (rule arg_cong2[where f="bitAND"], simp_all)[1]
  apply (rule arg_cong2[where f="(-)"])
   apply (simp add: word_eq_iff word_ops_nth_size nth_ucast nth_shiftl nth_shiftr)
   apply auto[1]
  apply (simp add: mask_eqs word_cat_shiftl_OR ucast_minus ucast_shiftl ucast_and
                   word_and_mask_shiftl_eq plus_minus_shiftl_distrib
                   word_shiftl_add[symmetric]
              del: shiftl_1)
  apply (simp add: add.commute)
  apply (simp add: add_and_masks)
  done

definition
  ex_run :: "('rv, 'a, 'e) monad \<Rightarrow> bool"
  where
  "ex_run m = (\<exists>x t. Run m t x)"

lemma ex_run_bindI:
  "ex_run f \<Longrightarrow> (\<And>x. ex_run (g x)) \<Longrightarrow> ex_run (bind f g)"
  apply (simp add: ex_run_def)
  apply (fastforce intro: Traces_bindI)
  done

lemma ex_run_return[simp]:
  "ex_run (return x)"
  by (simp add: ex_run_def)

lemma ex_run_undefined_bitvector:
  "ex_run (undefined_bitvector RV_class n)"
  apply (simp add: ex_run_def)
  apply (rule exI, rule undefined_bitvector_witness)
  done

lemma ex_run_comb:
  "(\<And>x. ex_run (f x)) \<Longrightarrow> ex_run (Let x f)"
  "ex_run p \<Longrightarrow> ex_run q \<Longrightarrow> ex_run (if P then p else q)"
  "(\<And>x y. ex_run (g x y)) \<Longrightarrow> ex_run ((\<lambda>(x, y). g x y) tup)"
  by auto

lemma CapGetTop_ex_run:
  "ex_run (CapGetTop cap)"
  unfolding CapGetTop_def
  by (intro ex_run_comb ex_run_return ex_run_bindI ex_run_undefined_bitvector)

lemma CapGetBounds_ex_run:
  "ex_run (CapGetBounds cap)"
  unfolding CapGetBounds_def
  using CapGetExponent_range[of cap]
  apply (simp only: Let_def[where s="CapGetExponent _"] split: if_split)
  apply (intro conjI impI ex_run_comb ex_run_return ex_run_bindI
        ex_run_undefined_bitvector CapGetTop_ex_run)
  apply (clarsimp simp add: CapIsExponentOutOfRange_def Let_def
        CAP_MAX_EXPONENT_def CAP_MAX_ENCODEABLE_EXPONENT_def)
  done

definition
  "annot x y = y"

lemma annot_op_ty:
  "(f :: 'a \<Rightarrow> 'b) x = annot TYPE('a \<Rightarrow> 'b) f x"
  by (simp add: annot_def)

lemmas annot_ineqs = annot_op_ty[where f="(<)"] annot_op_ty[where f="(\<le>)"]

lemmas annot_eq = annot_op_ty[where f="(=)"]

lemmas annot_ucast = annot_op_ty[where f="ucast"]

lemmas annot_vec_dec = annot_op_ty[where f="update_subrange_vec_dec"]
lemmas annot_subr = annot_op_ty[where f="vector_update_subrange_from_subrange"]

lemma slice_cat3[OF refl, simplified word_size]:
  "z = word_cat x y \<Longrightarrow> size y \<le> n \<Longrightarrow> Word.slice n z = Word.slice (n - size y) (x AND mask (size z - size y))"
  apply simp
  apply (simp add: word_eq_iff nth_slice nth_word_cat word_ao_nth)
  apply (auto; frule test_bit_size)
  apply simp_all
  done

definition
  word_slice_in :: "nat \<Rightarrow> nat \<Rightarrow> ('a :: len) word \<Rightarrow> 'a word \<Rightarrow> 'a word"
  where
  "word_slice_in i j x y = (let m = Bits.shiftl (mask j) i in
    (x AND m) OR (y AND NOT m))"

lemma word_slice_in_test_bit:
  "test_bit (word_slice_in i j x y) k =
    (if i \<le> k \<and> k < i + j then test_bit x k else test_bit y k)"
  apply (cases "k < size x", simp_all add: test_bit_above_size)
  apply (simp add: word_slice_in_def Let_def word_ops_nth_size nth_shiftl)
  apply arith
  done

lemma vector_update_subrange_from_subrange_to_word_slice_in:
  assumes cs: "e1 \<le> s1 \<and> 0 \<le> e1 \<and> e2 \<le> s2 \<and> 0 \<le> e2"
  assumes es: "(s2 - e2 + 1) = (s1 - e1 + 1)"
  shows "vector_update_subrange_from_subrange n v1 s1 e1 v2 s2 e2 =
    word_slice_in (nat e1) (nat (s1 - e1 + 1))
        (Bits.shiftl (Word.slice (nat e2) v2) (nat e1)) v1"
  apply (simp add: word_eq_iff word_slice_in_test_bit
                   nth_shiftl nth_slice es
                   test_bit_vector_update_subrange_from_subrange[OF cs])
  apply (safe; (simp(no_asm_use))?; frule test_bit_size; simp(no_asm_use))
  apply arith
  done

lemma word_update_to_word_slice_in:
  "j = i + size y - 1 \<Longrightarrow> j < size x \<Longrightarrow> 0 < size y \<Longrightarrow> 0 < j \<Longrightarrow>
  word_update x i j y = word_slice_in i (size y) (ucast y << i) x"
  apply (simp add: word_eq_iff test_bit_word_update word_slice_in_test_bit
    nth_ucast nth_shiftl)
  apply (safe, simp_all)
  done
 
lemma unat_le_ucast1:
  fixes x :: "('a :: len) word"
  shows "size x \<le> size y \<Longrightarrow> (unat x \<le> unat y) = (ucast x \<le> y)"
  by (simp add: word_le_nat_alt)

lemma unat_eq_ucast2:
  fixes x :: "('a :: len) word" and y :: "('b :: len) word"
  shows "size y \<le> size x \<Longrightarrow> (unat x = unat y) = (x = ucast y)"
  by (auto del: word_unat.Rep_eqD intro: word_unat.Rep_eqD)

lemma of_bool_test_bit:
  "of_bool (test_bit w n) = ucast (Word.slice n w :: 1 word)"
  by (simp add: word_eq_iff word_ops_nth_size nth_slice cong: rev_conj_cong)

lemma word_set_bit_to_and_or:
  fixes x :: "('a :: len0) word"
    and y :: "('b :: len0) word"
  shows
  "set_bit x n True = x OR (Bits.shiftl 1 n)"
  "set_bit x n False = x AND NOT (Bits.shiftl 1 n)"
  "set_bit x n (test_bit y i) = (x AND NOT (Bits.shiftl 1 n))
    OR Bits.shiftl (ucast (Word.slice i y :: 1 word)) n"
  by (auto simp add: word_eq_iff word_ops_nth_size test_bit_set_gen
        nth_shiftl nth_ucast nth_slice
    simp del: shiftl_1)

lemma set_bit_to_xor:
  fixes x :: "('a :: len0) word"
  shows "set_bit x n (\<not> test_bit x n) = x XOR (1 << n)"
  by (simp add: word_eq_iff test_bit_set_gen word_ops_nth_size nth_shiftl)

lemma set_bit_to_xor_eq:
  fixes x :: "('a :: len0) word"
  shows "b = (\<not> test_bit x n) \<Longrightarrow> set_bit x n b = x XOR (1 << n)"
  by (simp add: set_bit_to_xor)

termination count_leading_zero_bits
  by (relation "measure length", simp_all)

(* FIXME to sail operators lemmas *)
lemma count_leading_zero_bits_positive:
  "0 \<le> count_leading_zero_bits xs"
  by (induct xs rule: count_leading_zero_bits.induct, simp_all)

lemma count_leading_zeros_positive:
  "0 \<le> count_leading_zeros xs"
  by (simp add: count_leading_zeros_def count_leading_zeros_bv_def
        count_leading_zero_bits_positive)

lemma count_leading_zero_bits_lim:
  "count_leading_zero_bits xs \<le> length xs"
  by (induct xs rule: count_leading_zero_bits.induct, simp_all)

lemma count_leading_zeros_lim:
  "nat (count_leading_zeros x) \<le> size x"
  by (simp add: word_eq_iff word_ops_nth_size nth_shiftr
        count_leading_zeros_def count_leading_zeros_bv_def
        instance_Sail2_values_Bitvector_Machine_word_mword_dict_def
        nat_le_iff order_trans[OF count_leading_zero_bits_lim])

lemma count_leading_zero_bits_imp:
  "i < nat (count_leading_zero_bits xs) \<Longrightarrow> xs ! i = B0"
  apply (induct xs arbitrary: i rule: count_leading_zero_bits.induct, simp_all)
  apply (simp add: nth_Cons split: nat.split)
  done

lemma count_leading_zeros_nth_imp:
  "test_bit x i \<Longrightarrow> nat (count_leading_zeros x) \<le> size x - Suc i"
  using count_leading_zero_bits_imp[where xs="map bitU_of_bool (to_bl x)" and i="size x - Suc i"]
  apply (simp add: word_eq_iff word_ops_nth_size nth_shiftr
        count_leading_zeros_def count_leading_zeros_bv_def
        instance_Sail2_values_Bitvector_Machine_word_mword_dict_def)
  apply (clarsimp simp: test_bit_bl nth_rev)
  apply atomize
  apply simp
  done

lemma count_leading_zeros_lt:
  "x \<le> Bits.shiftr max_word (nat (count_leading_zeros x))"
  by (auto intro!: word_le_test_bit_mono simp: nth_shiftr
        dest: count_leading_zeros_nth_imp)

lemma count_leading_zero_bits_set:
  "count_leading_zero_bits xs < length xs \<Longrightarrow>
    xs ! (nat (count_leading_zero_bits xs)) \<noteq> B0"
  apply (induct xs rule: count_leading_zero_bits.induct, simp_all)
  apply (simp add: nat_add_distrib count_leading_zero_bits_positive)
  done

lemma count_leading_zeros_set:
  "nat (count_leading_zeros x) < size x \<Longrightarrow>
    test_bit x (size x - (nat (count_leading_zeros x) + 1))"
  apply (simp add: count_leading_zeros_def count_leading_zeros_bv_def
        instance_Sail2_values_Bitvector_Machine_word_mword_dict_def
        nat_less_iff count_leading_zero_bits_positive)
  apply (frule count_leading_zero_bits_set[OF order_less_le_trans])
   apply simp
  apply (simp add: nat_less_iff count_leading_zero_bits_positive)
  apply (simp add: bitU_of_bool_def split: if_split_asm)
  apply (simp add: to_bl_nth nat_less_iff count_leading_zero_bits_positive)
  done

lemma word_sum_eq_cut_at_bit:
  assumes "x AND NOT (mask n) = y AND NOT (mask n)"
    "z AND NOT (mask n) = 0"
    "x AND mask n = (y AND mask n) + (z AND mask n)"
  shows "x = y + z"
  using arg_cong2[where f="(+)", OF assms(1, 3)]
    word_minus_word_and_not_mask[of z n, simplified assms, symmetric]
  by simp

lemma neg_numeral_norm[OF refl, simplified word_size]:
  "w = - numeral n \<Longrightarrow> w = word_of_int (2 ^ size w - numeral n)"
  by (simp add: wi_hom_syms word_of_int_2p_len)

lemma of_bl_bin_word_of_int:
  "len = LENGTH('a) \<Longrightarrow> of_bl (bin_to_bl_aux len n []) = (word_of_int n :: ('a::len) word)"
  by (auto simp: of_bl_def bin_bl_bin')

lemma get_slice_int_bin_to_bl[OF refl, simplified word_size, simp]:
  "w = get_slice_int len n i \<Longrightarrow>
    len > 0 \<Longrightarrow> i \<ge> 0 \<Longrightarrow> nat len \<le> size w \<Longrightarrow>
    w = of_bl (bin_to_bl (nat len) (Bits.shiftr n (nat i)))"
  unfolding get_slice_int_def get_slice_int_bv_def subrange_list_def
  apply (simp add: subrange_list_dec_drop_take len_bin_to_bl_aux nat_add_distrib)
  apply (clarsimp simp: word_eq_iff test_bit_of_bl rev_nth len_bin_to_bl_aux
        cong: rev_conj_cong)
  apply (simp add: min.absorb2 nth_bin_to_bl_aux)
  done

definition
  cap_alignment :: "Capability \<Rightarrow> nat"
  where
  "cap_alignment cap = (if CapIsInternalExponent cap
    then nat (min (CapGetExponent cap) CAP_MAX_EXPONENT) + 3
    else 0)"

lemma cap_alignment_in_range:
  "cap_alignment cap = (if CapGetExponent cap = CAP_MAX_ENCODEABLE_EXPONENT
    then nat CAP_MAX_EXPONENT + 3
    else if CapIsExponentOutOfRange cap
    then nat CAP_MAX_EXPONENT + 3
    else if CapIsInternalExponent cap
    then nat (CapGetExponent cap) + 3
    else 0)"
  using CapGetExponent_range[of cap]
  apply (simp add: cap_alignment_def CapIsExponentOutOfRange_def Let_def
    CAP_MAX_EXPONENT_def CAP_MAX_ENCODEABLE_EXPONENT_def)
  apply (auto, auto simp add: CapGetExponent_def)
  done

lemma CapGetTop_aligned:
  "Run (CapGetTop cap) t x \<Longrightarrow> CapIsInternalExponent cap \<Longrightarrow>
    x AND mask 3 = 0"
  by (clarsimp simp: CapGetTop_def word_and_mask_0_iff_not_testbits
            update_subrange_vec_dec_test_bit CAP_MW_def nth_word_cat
        elim!: Run_elims split del: if_split)

lemma CapGetTop_aligned_shiftl:
  "Run (CapGetTop cap) t x \<Longrightarrow> CapIsInternalExponent cap \<Longrightarrow>
    \<exists>top. x = (top << 3)"
  apply (rule_tac x="Bits.shiftr x 3" in exI)
  apply (drule(1) CapGetTop_aligned)
  apply (simp add: word_eq_iff nth_shiftl nth_shiftr word_ao_nth)
  apply auto
  done

lemma if_caseE:
  "P (If Q x y) \<Longrightarrow> (Q \<Longrightarrow> P x \<Longrightarrow> R) \<Longrightarrow> (\<not> Q \<Longrightarrow> P y \<Longrightarrow> R) \<Longrightarrow> R"
  by (auto split: if_split_asm)

lemma CapGetBounds_aligned:
  "Run (CapGetBounds cap) t (base, limit, valid) \<Longrightarrow>
    base AND mask (cap_alignment cap) = 0 \<and>
    limit AND mask (cap_alignment cap) = 0"
  using [[simproc del: let_simp]]
    CapGetExponent_range[of cap]
  apply (cases "\<not> CapIsInternalExponent cap")
   apply (simp add: cap_alignment_def)
  apply (simp add: CapGetBounds_def update_vec_dec_bitU_of_bool word_ops_nth_size
                Let_def[where s="If _ _ _"] Let_def[where s="_ - _"]
                if_distrib[where f="word_of_int"] wi_hom_syms
                word_of_int_shiftl word_less_nat_alt[symmetric]
        cong: if_cong)
  apply (elim Run_elims)
    apply (simp add: CAP_BOUND_MIN_def CAP_BOUND_MAX_def CAP_MAX_ENCODEABLE_EXPONENT_def)
    apply (simp add: cap_alignment_def CAP_MAX_EXPONENT_def mask_def)
   apply (simp add: CAP_BOUND_MIN_def CAP_BOUND_MAX_def cap_alignment_def)
   apply word_bitwise
   apply (clarsimp simp: CAP_MAX_EXPONENT_def)
   apply arith
  apply (simp add: cap_alignment_in_range split del: if_split)
  apply (frule CapGetTop_aligned_shiftl, simp)
  apply (simp add: CapGetBottom_def split del: if_split cong: if_cong)
  apply (elim Run_elims case_prodE2[where Q="\<lambda>x. (x, _) \<in> _"] if_caseE[where P="\<lambda>x. x = _"];
    clarsimp split del: if_split;
    (thin_tac "_ = _")+;
    simp add: word_and_mask_0_iff_not_testbits word_ops_nth_size nth_ucast
            test_bit_vector_update_subrange_from_subrange
            update_subrange_vec_dec_test_bit
            CAP_MW_def CAP_MAX_EXPONENT_def nth_shiftl
            set_slice_zeros_def test_bit_slice_mask Let_def
            if_distrib[where f="\<lambda>x. test_bit x _"]
            if_bool_eq_disj test_bit_set_gen
            nat_add_distrib nth_word_cat
        split del: if_split cong: if_cong)
   apply (auto split del: if_split)
  done

lemma less_unat_eq:
  "(x < unat y) = (of_nat x < y \<and> x < 2 ^ size y)"
  apply (simp add: word_less_nat_alt unat_of_nat)
  apply (auto elim: order_le_less_trans[rotated] order_less_trans)
  done

lemma uint_eq_eq:
  "(uint x = y) = (x = word_of_int y \<and> 0 \<le> y \<and> y < 2 ^ size x)"
  by (safe, simp_all add: int_word_uint)

lemma CapGetBounds_set_bit_is_addition_lemma:
  "b \<noteq> test_bit x 64 \<Longrightarrow>
    ucast (if P then set_bit x 64 b else x) =
        (ucast (x :: 66 word) :: 65 word) + ((if P then 1 else 0) << 64)"
  by (word_bitwise, simp add: eq_commute carry_simps test_bit_set_gen)

lemma sail_mask_ucast:
  "sail_mask n x = ucast x"
  by (simp add: sail_mask_def vector_truncate_def)

lemma word_slice_in_sum:
  "word_slice_in i j x y = (y AND mask i) +
    (x AND (mask j << i)) + (y AND NOT (mask (i + j)))"
  apply (simp add: word_slice_in_def Let_def)
  apply (subst word_plus_is_or[symmetric])
   apply (simp add: word_eq_iff word_ops_nth_size)
  apply simp
  apply (subst word_plus_is_or)
   apply (simp add: word_eq_iff word_ops_nth_size)
  apply (simp add: word_ao_dist2[symmetric])
  apply (simp add: word_eq_iff word_ops_nth_size nth_shiftl)
  apply auto
  done

lemma word_or_shiftr_dist:
  "(x OR y) >> n = (x >> n :: ('a :: len) word) OR (y >> n)"
  apply (simp add: word_eq_iff word_ops_nth_size nth_shiftr)
  apply (safe; frule test_bit_size; simp add: word_ops_nth_size)
  done

lemma word_and_shiftr_dist:
  "(x AND y) >> n = (x >> n :: ('a :: len) word) AND (y >> n)"
  apply (simp add: word_eq_iff word_ops_nth_size nth_shiftr)
  apply (safe; frule test_bit_size; simp add: word_ops_nth_size)
  done

lemma mask_shiftr[OF refl]:
  "w = mask i \<Longrightarrow> w >> j = mask ((min (size w) i) - j)"
  apply hypsubst_thin
  apply (auto simp add: word_eq_iff nth_shiftr)
  done

lemma shiftr_eq_helper:
  fixes x :: "('a :: len) word"
  shows "x AND NOT (mask n) = y << n \<Longrightarrow> y AND mask (size x - n) = y \<Longrightarrow> x >> n = y"
  apply (simp add: word_eq_iff nth_shiftr nth_shiftl word_ops_nth_size)
  apply clarsimp
  apply (drule_tac x="na + n" in spec)
  apply (auto dest: test_bit_size)
  done

lemma word_add_shiftr_aligned_distrib:
  assumes al: "x AND mask n = 0"
  shows "(x + y) >> n = ((x >> n) + (y >> n)) AND mask (size x - n)"
  apply (rule shiftr_eq_helper, simp_all)
  apply (simp add: plus_minus_shiftl_distrib shiftr_shiftl)
  apply (simp add: word_plus_and_not_mask_eq al word_and_le1)
  done

lemma word_add_shiftr_aligned_distrib2:
  assumes al: "y AND mask n = 0"
  shows "(x + y) >> n = ((x >> n) + (y >> n)) AND mask (size x - n)"
  using word_add_shiftr_aligned_distrib[OF al, of x]
  by (simp add: add.commute)

lemma word_sub_shiftr_aligned_distrib:
  assumes al: "y AND mask n = 0"
  shows "(x - y) >> n = ((x >> n) - (y >> n)) AND mask (size x - n)"
  apply (rule shiftr_eq_helper, simp_all)
  apply (simp add: plus_minus_shiftl_distrib shiftr_shiftl)
  apply (simp add: word_minus_and_not_mask_eq al)
  done

lemma word_slice_in_mask:
  "word_slice_in i j x y AND mask n = word_slice_in i j (x AND mask n) (y AND mask n)"
  by (simp add: word_eq_iff word_slice_in_test_bit word_ops_nth_size)

lemma word_slice_in_shiftr:
  "word_slice_in i j x y >> n = word_slice_in (i - n) (j - (n - i)) (x >> n) (y >> n)"
  apply (simp add: word_eq_iff word_slice_in_test_bit nth_shiftr)
  apply arith
  done

lemma set_slice_zeros_shifts:
  "nat l = size w \<Longrightarrow> 0 \<le> n \<Longrightarrow>
    set_slice_zeros l w 0 n = ((w >> nat n) << nat n)"
  by (auto simp: word_eq_iff nth_shiftl nth_shiftr
        set_slice_zeros_def word_ops_nth_size test_bit_slice_mask)

lemma word_slice_in_shiftl:
  "n \<le> i \<Longrightarrow> n \<le> m \<Longrightarrow>
    (word_slice_in i j (x << m) (y << n)) =
    (word_slice_in (i - n) j (x << (m - n)) y << n)"
  by (auto simp add: word_eq_iff nth_shiftl word_slice_in_test_bit)

lemma let_extract_f:
  "(let x = f v in g x) = (let x = v in g (f x))"
  by simp

lemma ucast_set_bit[OF refl, simplified word_size]:
  "w = ucast (set_bit x i b) \<Longrightarrow>
    w = (if i < size x \<and> i < size w then set_bit (ucast x) i b else ucast x)"
  apply hypsubst_thin
  apply (simp add: word_eq_iff nth_ucast test_bit_set_gen)
  apply (auto dest: test_bit_size)
  done

lemma shiftl_shiftr:
  "(Bits.shiftr (x << i) j) = (if i < j
    then Bits.shiftr (x AND mask (size x - i)) (j - i)
    else Bits.shiftl (x AND mask (size x - i)) (i - j))"
  unfolding word_size
  apply (simp add: word_eq_iff nth_shiftl nth_shiftr
        word_ops_nth_size word_ao_nth)
  apply (auto; frule test_bit_size; auto simp: word_ops_nth_size)
  done

lemma ucast_shiftl_down:
  fixes x :: "'a ::len0 word"
  assumes "LENGTH('b) \<le> LENGTH('a)"
  shows "(ucast (x << n)::'b::len0 word) = ucast x << n"
  using assms
  by (auto simp add: word_eq_iff nth_ucast nth_shiftl)

lemma add_and_mask_ucast:
  "NO_MATCH (a AND mask b) x \<Longrightarrow>
    (ucast x AND mask n) = (ucast (x AND mask n) AND mask n)"
  apply (simp add: word_eq_iff nth_ucast word_ao_nth)
  apply (auto dest: test_bit_size)
  done

lemma word_slice_in_simple_sum_mask:
  "x AND mask i = 0 \<and>
    x AND NOT (mask (i + j)) = 0 \<and>
    y AND NOT (mask (i + j)) = 0 \<Longrightarrow>
    word_slice_in i j x y = x + (y AND mask i)"
  apply (simp add: word_slice_in_sum)
  apply (simp add: word_eq_iff word_ops_nth_size nth_shiftl)
  apply fastforce
  done

lemma add_mask_eq_le1:
  assumes "NO_MATCH i j" "j \<le> i"
  shows
  "((a AND mask i) + b) AND mask j = (a + b) AND mask j"
  (is "?lhs = ?rhs")
proof -
  have "?lhs = (((a AND mask i) AND mask j) + b) AND mask j"
    by (simp only: mask_eqs)
  also have "\<dots> = ((a AND mask j) + b) AND mask j"
    using assms by (simp add: min.absorb2)
  also have "\<dots> = ?rhs"
    by (simp add: mask_eqs)

  finally show ?thesis .
qed

lemma add_mask_eq_le2:
  assumes "NO_MATCH i j" "j \<le> i"
  shows
  "(a + (b AND mask i)) AND mask j = (a + b) AND mask j"
  using add_mask_eq_le1[OF assms, of b a]
  by (simp add: add.commute)

lemmas add_mask_eq_le = add_mask_eq_le1 add_mask_eq_le2

lemma word_slice_in_mask_only:
  "j \<le> i \<Longrightarrow> (word_slice_in 0 i x y AND mask j) = (x AND mask j)"
  by (simp add: word_eq_iff word_ao_nth word_slice_in_test_bit)

declare slice_zero[to_smt_word_del]

lemma CapGetBounds_length_mask:
  assumes run: "Run (CapGetBounds cap) t (base, limit, valid)"
  assumes exp: "(CapIsInternalExponent cap \<and> CapGetExponent cap < CAP_MAX_EXPONENT)"
  shows "(Bits.shiftr (ucast (limit - base)) (nat (CapGetExponent cap)))
        AND NOT (mask (nat CAP_MW - 2)) = (1 :: 64 word) << (nat CAP_MW - 2)"
  using [[simproc del: let_simp]]
proof -

  note if_split[split del]

  show ?thesis
    using run exp
    apply (simp add: CapGetBounds_def update_vec_dec_bitU_of_bool word_ops_nth_size
                Let_def[where s="If _ _ _"] Let_def[where s="_ - _"]
                if_distrib[where f="word_of_int"] wi_hom_syms
                word_of_int_shiftl word_less_nat_alt[symmetric]
                CAP_MAX_ENCODEABLE_EXPONENT_def CapIsExponentOutOfRange_def
                CAP_MAX_EXPONENT_def
                CapGetTop_def
        cong: if_cong)
    apply (elim Run_elims)
      apply simp
     apply (simp add: Let_def)
    apply (clarsimp elim!: Run_elims)
    apply hypsubst_thin
    apply let_dup_word
    apply (simp add: if_distrib[where f=ucast] ucast_minus_down ucast_set_bit
        cong: if_cong)
    apply (simp add:
        vector_update_subrange_from_subrange_to_word_slice_in
        update_subrange_vec_dec_def word_update_to_word_slice_in
        CAP_MW_def set_slice_zeros_shifts
        word_slice_in_shiftl nat_add_distrib
        let_extract_f[where f="\<lambda>x. Bits.shiftl x _"]
        ucast_shiftl_down plus_minus_shiftl_distrib[symmetric])
    apply (simp add: Let_def[where s="_ + _"]
        ucast_plus_down slice_shiftr
        word_add_shiftr_aligned_distrib2[where y="_ << _"]
        shiftl_mask_eq_0 shiftl_shiftr word_bw_assocs)
    apply (subst word_slice_in_simple_sum_mask[where j="nat (_ - _)"],
        solves \<open>auto simp add: word_eq_iff word_ops_nth_size nth_shiftl nth_shiftr
                word_slice_in_test_bit if_distrib[where f="\<lambda>x. test_bit x _"]
                if_bool_eq_disj
            dest: test_bit_size\<close>)+
    apply (simp add: word_slice_in_mask_only
        ucast_plus_down mask_eqs
        word_add_shiftr_aligned_distrib2[where y="_ << _"]
        shiftl_mask_eq_0 shiftl_shiftr word_bw_assocs)
    apply (simp add: Let_def[where s="_ + _"] ucast_plus_down
        ucast_shiftl_down ucast_and word_and_mask_shiftl_eq)
    apply (simp add: add_mask_eq_le add_and_masks word_bw_assocs[symmetric])
    apply (simp add: mask_eqs)
    apply (simp add: plus_minus_shiftl_distrib ucast_minus_down)
    (* common parts all cancelled! *)
    apply (rule_tac P="(1 << 14) AND mask (64 - nat (CapGetExponent cap)) = ((1 << 14) :: 64 word)"
        in rev_mp)
     apply (simp add: word_eq_iff word_ao_nth nth_shiftl del: shiftl_1)
     apply auto[1]
    apply (thin_tac _)+
    (* down to bit-blasting *)
    apply (simp add: mask_def[where n="numeral _"] word_slice_in_def)
    apply smt_word
    (* subgoal by (word_bitwise_eq; intro impI; simp only: carry_def simp_thms; elim conjE; argo) *)
    done
qed

lemma unat_eqD:
  "(unat x = y) \<Longrightarrow> y < 2 ^ size x \<and> x = of_nat y"
  by clarsimp

lemma word_and_mask_eq_iff_not_testbits:
  "(w AND mask n) = w \<longleftrightarrow> (\<forall>i. i < size w \<and> w !! i \<longrightarrow> i < n)"
  using test_bit_size[of w] by (auto simp: word_ao_nth word_eq_iff word_size)

(*
lemma CapGetBounds_length:
  "Run (CapGetBounds cap) t (base, limit, valid) \<Longrightarrow>
    let length_mantissa = ((limit - base) >> nat (CapGetExponent cap)) in
    length_mantissa < 2 ^ nat CAP_BASE_MANTISSA_NUM_BITS \<and>
        (CapGetExponent cap > 0 \<and> CapGetExponent cap < 64 - CAP_BASE_MANTISSA_NUM_BITS \<longrightarrow>
            2 ^ (nat CAP_BASE_MANTISSA_NUM_BITS - 1) \<le> length_mantissa)"
  apply (drule CapGetBounds_length_mask)
  apply (clarsimp simp add: Let_def linorder_not_less[symmetric])
  apply (subst mask_eq_iff_w2p[symmetric], simp add: CAP_BASE_MANTISSA_NUM_BITS_def)+
  apply (simp add: word_le_mask_eq linorder_not_le[symmetric])

  apply (simp add: word_and_mask_eq_iff_not_testbits word_ops_nth_size nth_shiftr)
  apply (simp add: CAP_BASE_MANTISSA_NUM_BITS_def CapBoundsUsesValue_def CAP_MW_def CAP_VALUE_NUM_BITS_def)
  apply (intro allI impI conjI; clarsimp)
   apply (frule test_bit_size; auto)
  apply (rule_tac x="i - nat (CapGetExponent cap)" in exI)
  apply auto
  done
*)

definition
  align_up :: "('a :: len) word \<Rightarrow> nat \<Rightarrow> 'a word"
  where
  "align_up x n = (x + mask n) AND NOT (mask n)"

lemma mask_add_le_trivia:
  assumes m: "mask n + x \<le> mask n"
    (is "?add \<le> ?m")
    and x: "x \<le> mask n"
  shows "x = 0 \<or> size x \<le> n"
proof (cases "n < size x")
  case False
    thus ?thesis by simp
next
  case True

  have m_less: "unat ?m < 2 ^ n"
    using True
    by (simp add: unat_mask min.absorb1)

  have "unat ?m + unat x < 2 ^ n + 2 ^ n"
    using m_less x
    by (simp add: word_le_nat_alt)
  also have "\<dots> \<le> 2 ^ (n + 1)"
    by simp
  also have "\<dots> \<le> 2 ^ (size x)"
    using True
    by (simp del: power_Suc)

  finally have m2: "?m \<le> mask n + x"
    by (simp add: no_plus_overflow_unat_size)

  show ?thesis using order_antisym[OF m m2]
    by simp
qed

lemma align_up_if:
  "align_up x n = (if x AND mask n = 0
    then x else (x AND NOT (mask n)) + 2 ^ n)"
  apply (simp add: align_up_def)
  apply (intro conjI impI)
   apply (simp add: word_plus_and_not_mask)
   apply (simp add: not_mask_unchanged)
  apply (clarsimp simp add: word_plus_and_not_mask_eq)
  apply (subst(asm) add.commute)
  apply (drule mask_add_le_trivia)
   apply (simp add: word_and_le1)
  apply (elim disjE, simp_all)
  apply (rule word_eqI)
  apply (simp add: nth_w2p)
  done

lemma align_up_neg:
  "align_up x n = - ((- x) AND NOT (mask n))"
  using word_minus_and_not_mask_eq[of 0 x n]
  by (simp add: align_up_if not_mask_unchanged)

lemma align_up_le_aligned:
  "y AND mask n = 0 \<Longrightarrow> x \<le> y \<Longrightarrow> align_up x n \<le> y"
  using le_and_not_mask[of "- y" "- x" n] word_minus_and_not_mask_eq[of 0 y n]
    not_mask_unchanged[of y n]
  apply (simp add: align_up_neg)
  apply (cases "y = 0 \<or> x = 0")
   apply auto[1]
  apply (simp add: word_le_nonzero_negate)
  apply (rule word_le_nonzero_negateI, simp_all)
  done

lemma ucast_align_up:
  "LENGTH('a) \<le> size x \<Longrightarrow> n \<le> LENGTH('a) \<Longrightarrow>
    ucast (align_up x n) = align_up (ucast x :: ('a :: len) word) n"
  by (simp add: align_up_def ucast_and ucast_not min.absorb1 ucast_plus_down)

lemma align_up_aligned:
  "align_up w n AND mask n = 0"
  by (simp add: align_up_def word_bw_assocs)

lemma aligned_le:
  "x AND mask n = 0 \<Longrightarrow> m \<le> n \<Longrightarrow> x AND mask m = 0"
  by (simp add: word_and_mask_0_iff_not_testbits)

lemma t2n_mask_n:
  "2 ^ n AND mask n = (0 :: ('a :: len) word)"
  by (simp add: word_eq_iff word_ops_nth_size nth_w2p)

lemmas t2n_mask_not_n = not_mask_unchanged[OF t2n_mask_n]

lemma align_up_eq_or:
  "align_up w n = ((w - 1) OR mask n) + 1"
  (is "?lhs = ?rhs")
proof -
  let ?w1_mask = "(w - 1) AND NOT (mask n)"

  have "?lhs = ((w - 1) + 2 ^ n) AND NOT (mask n)"
    unfolding align_up_def
    by (simp add: mask_def field_simps)
  also have "\<dots> = ?w1_mask + 2 ^ n"
    by (simp add: word_plus_and_not_mask t2n_mask_n word_and_le1 t2n_mask_not_n)
  also have "\<dots> = (?w1_mask + mask n) + 1"
    by (simp add: mask_def)
  also have "?w1_mask + mask n = ?w1_mask OR mask n"
    by (rule word_plus_is_or, simp add: word_bw_assocs)
  also have "?w1_mask OR mask n = (w - 1) OR mask n"
    by (auto simp: word_eq_iff word_ops_nth_size)
  finally show ?thesis
    by simp
qed

lemma align_up_twice:
  "align_up (align_up w n) m = align_up w (max n m)"
  apply (simp add: align_up_eq_or)
  apply (simp add: word_eq_iff word_ops_nth_size less_max_iff_disj)
  done

lemma align_up_unchanged:
  "x AND mask n = 0 \<Longrightarrow> align_up x n = x"
  by (simp add: align_up_if)

lemma exists_quotient_remainder:
  fixes n m :: nat
  shows "0 < m \<Longrightarrow> \<exists>q r. n = (q * m) + r \<and> r < m"
  by (metis dme mod_less_divisor)

lemma unat_t2n:
  "unat (2 ^ n :: ('a :: len) word) = (if n < LENGTH('a) then 2 ^ n else 0)"
  using positive_2p_word[where 'a='a and n=n]
  by (clarsimp simp: unat_def[where w="_ ^ _"] uint_2p simp flip: word_neq_0_conv)

lemma msb_eq_ineq:
  "n < size x \<Longrightarrow> ((x AND NOT (mask n)) = 2 ^ n) = (2 ^ n \<le> unat x \<and> unat x < 2 ^ Suc n)"
  using exists_quotient_remainder[of "2 ^ n" "unat x"]
  apply (simp only: unat_arith_simps unat_and_not_mask unat_t2n)
  apply clarsimp
  apply (case_tac q, simp_all)
  apply (case_tac nat, simp_all)
  done

lemma unat_shiftr:
  "unat (Bits.shiftr x n) = unat x div 2 ^ n"
  by (simp add: unat_def shiftr_div_2n nat_div_distrib nat_power_eq)

definition
  sufficient_exponent :: "65 word \<Rightarrow> 65 word \<Rightarrow> nat \<Rightarrow> bool"
  where
  "sufficient_exponent lower_b upper_b expon = (
    unat (align_up upper_b (expon + 3))
    - unat (lower_b AND NOT (mask (expon + 3)))
    < 2 ^ (expon + (nat CAP_MW - 1)))"

lemma CapGetBounds_ie_sufficient:
  "Run (CapGetBounds cap) t (base, limit, valid) \<Longrightarrow>
    cap_invariant cap \<Longrightarrow>
    CapIsInternalExponent cap \<and> CapGetExponent cap < CAP_MAX_EXPONENT \<Longrightarrow>
    sufficient_exponent base limit (nat (CapGetExponent cap)) \<or> (base = 0 \<and> limit = 2 ^ 64)"
  using CapGetExponent_range[of cap]
  apply clarsimp
  apply (frule CapGetBounds_get_base)
  apply (frule CapGetBounds_get_limit)
  apply (clarsimp simp: sufficient_exponent_def CAP_MW_def)
  apply (frule CapGetBounds_aligned)
  apply (clarsimp simp: not_mask_unchanged cap_alignment_def min.absorb1)
  apply (subst align_up_unchanged)
   apply (simp add: word_bw_assocs CAP_MAX_EXPONENT_def min.absorb1)
  apply (frule CapGetBounds_length_mask, simp)
  apply (simp add: cap_invariant_def word_le_nat_alt)
  apply (subst(asm) msb_eq_ineq)
   apply (simp add: CAP_MW_def)
  apply (clarsimp simp: unat_shiftr td_gal_lt[symmetric])
  apply (simp add: CAP_MW_def power_add mult.commute)
  apply (erule order_le_less_trans[rotated])
  apply (simp add: unat_and_mask unat_sub word_le_nat_alt)
  apply (cases "limit = 2 ^ 64")
   apply (cases "unat base = 0", simp_all)[1]
  apply (drule le_neq_trans[where a="unat limit"])
   apply (clarsimp dest!: unat_eqD)
  apply simp
  done

lemma CapGetBounds_nie_limit:
  assumes run: "Run (CapGetBounds cap) t (base, limit, valid)"
  assumes exp: "\<not> CapIsInternalExponent cap"
  shows "(ucast (limit - base)) < (1 :: 64 word) << (nat CAP_MW - 2)"
  using [[simproc del: let_simp]]
proof -

  note if_split[split del]

  show ?thesis
    using run exp
    apply (simp add: CapGetBounds_def update_vec_dec_bitU_of_bool word_ops_nth_size
                Let_def[where s="If _ _ _"] Let_def[where s="_ - _"]
                if_distrib[where f="word_of_int"] wi_hom_syms
                word_of_int_shiftl word_less_nat_alt[symmetric]
                CAP_MAX_ENCODEABLE_EXPONENT_def CapIsExponentOutOfRange_def
                CAP_MAX_EXPONENT_def
                CapGetTop_def CapGetExponent_def
        cong: if_cong)
    apply (elim Run_elims)
    apply (clarsimp elim!: Run_elims)
    apply hypsubst_thin
    apply (clarsimp simp: Let_def)
    apply let_dup_word
    apply (simp add: if_distrib[where f=ucast] ucast_minus_down ucast_set_bit
        cong: if_cong)
    apply (simp add:
        vector_update_subrange_from_subrange_to_word_slice_in
        update_subrange_vec_dec_def word_update_to_word_slice_in
        CAP_MW_def set_slice_zeros_shifts
        plus_minus_shiftl_distrib
        )

    apply (subst word_slice_in_simple_sum_mask,
        solves \<open>auto simp add: word_eq_iff word_ops_nth_size nth_shiftl nth_shiftr
                word_slice_in_test_bit if_distrib[where f="\<lambda>x. test_bit x _"]
                if_bool_eq_disj
            dest: test_bit_size\<close>)+
    (* maybe keep trying to cancel that subtraction to bring it in
        range of less-SMT methods? *)

    apply (simp add: word_slice_in_def mask_def split del: if_split)
    apply smt_word
    done
qed

lemma insufficient_exponent_original_size:
  "lower_b \<le> upper_b \<Longrightarrow>
    (upper_b - lower_b) AND NOT (mask (expon + (nat CAP_MW - 1))) \<noteq> 0 \<Longrightarrow>
    upper_b \<le> align_up upper_b (expon + 3) \<Longrightarrow>
    ~ sufficient_exponent lower_b upper_b expon"
  apply (clarsimp simp: sufficient_exponent_def)
  apply (clarsimp simp: word_eq_iff word_ops_nth_size)
  apply (erule bang_is_le[THEN notE[rotated]])
  apply (simp add: word_less_nat_alt linorder_not_le unat_t2n)
  apply (rule order_le_less_trans[rotated], erule order_less_le_trans[where y="_ ^ _"])
   apply simp
  apply (simp add: unat_sub word_le_nat_alt)
  apply (erule order_trans[OF diff_le_mono])
  apply (rule diff_le_mono2)
  apply (simp add: word_le_nat_alt[symmetric] word_and_le2)
  done

lemma insufficient_exponent_encoded_bit:
  "lower_b \<le> upper_b \<Longrightarrow>
    upper_b \<le> align_up upper_b (expon + 3) \<Longrightarrow>
    test_bit (align_up upper_b (expon + 3) - (lower_b AND NOT (mask (expon + 3)))) n \<Longrightarrow>
    expon + (nat CAP_MW - 1) \<le> n \<Longrightarrow>
    n \<le> 64 \<Longrightarrow>
    ~ sufficient_exponent lower_b upper_b expon"
  apply (clarsimp simp: sufficient_exponent_def)
  apply (erule bang_is_le[THEN notE[rotated]])
  apply (simp add: linorder_not_le word_le_nat_alt)
  apply (subst unat_sub)
   apply (simp add: word_le_nat_alt[symmetric])
   apply (erule order_trans[rotated])+
   apply (simp add: word_and_le2)
  apply (erule order_less_le_trans)
  apply (simp add: unat_t2n)
  done

lemma word_not_nth:
  fixes x :: "('a :: len) word"
  shows "(NOT x) !! n = (\<not> (x !! n) \<and> n < size x)"
  by (cases "n < size x", auto simp: word_ops_nth_size dest: test_bit_size)

lemma and_not_mask_shiftr:
  "(x AND NOT (mask m)) >> m = x >> m"
  apply (simp add: word_eq_iff nth_shiftr word_ao_nth word_not_nth)
  apply (auto dest: test_bit_size)
  done

lemma add_div_div_le:
  fixes x :: int
  shows "0 < n \<Longrightarrow> (x div n) + (y div n) \<le> (x + y) div n"
  apply (rule mult_right_le_imp_le[rotated], assumption)
  apply (simp add: ring_distribs)
  apply (simp add: minus_mod_eq_div_mult[symmetric])
  apply (rule neg_le_iff_le[THEN iffD1], simp)
  apply (subst pull_mods, rule int_mod_le)
  apply simp
  done

lemma less_mult_imp_div_less_int:
  fixes x :: int
  shows "0 < y \<Longrightarrow> x < y * z \<Longrightarrow> x div y < z"
  apply (rule mult_right_less_imp_less[where c=y])
   apply (simp add: minus_mod_eq_div_mult[symmetric])
   apply (simp add: mult.commute order_le_less_trans[where y=x])
  apply simp
  done

lemma word_add_shiftr_aligned_distrib3:
  assumes al: "x AND mask n = 0"
  assumes le: "x \<le> x + y"
  shows "(x + y) >> n = ((x >> n) + (y >> n))"
  apply (cases "n < size x", simp_all add: shiftr_zero_size)
  apply (simp add: word_add_shiftr_aligned_distrib[OF al])
  apply (simp add: word_le_mask_eq[symmetric])
  apply (simp add: word_le_def uint_word_ariths)
  apply (rule order_trans, rule int_mod_le)
   apply simp
  apply (simp add: shiftr_div_2n)
  apply (rule order_trans, rule add_div_div_le)
   apply simp
  apply (simp add: uint_mask le[simplified uint_plus_simple_iff, symmetric])
  apply (rule less_mult_imp_div_less_int)
   apply simp
  apply (simp add: power_add[symmetric])
  done

lemma shiftr_compose:
  fixes x :: "('a :: len) word"
  shows "(x >> m) >> n = x >> (m + n)"
  by (simp add: word_eq_iff nth_shiftr field_simps)

lemma align_shiftr_compose:
  assumes le_sz: "m + n < size x"
  assumes le_add: "x \<le> x + mask (m + n)"
  shows "align_up (align_up x m >> m) n >> n = align_up x (m + n) >> (m + n)"
proof -
  have R:
    "(x + mask (m + n)) = (mask n << m) + (x + mask m)"
    apply (simp add: field_simps)
    apply (subst word_plus_is_or)
     apply (auto simp: word_eq_iff word_ops_nth_size nth_shiftl)
    done

  have mask_shift_le:
    "mask n << m \<le> mask (m + n)"
    by (rule word_le_test_bit_mono, auto simp add: nth_shiftl)

  show ?thesis using le_sz
    apply (simp add: align_up_def and_not_mask_shiftr)
    apply (simp add: shiftr_compose[symmetric, where x="_ + _"])
    apply (simp add: R)
    apply (subst word_add_shiftr_aligned_distrib3[where x="_ << _"])
      apply (simp add: word_and_mask_0_iff_not_testbits nth_shiftl)
     apply (simp add: R[symmetric])
     apply (rule order_trans[OF mask_shift_le])
     apply (subst olen_add_eqv[symmetric], simp add: le_add)
    apply (simp add: shiftl_shiftr min.absorb2 add.commute)
    done
qed

lemma mask_mono:
  "m \<le> n \<Longrightarrow> mask m \<le> mask n"
  by (rule word_le_test_bit_mono, simp)

lemma shiftr_align_up_eq:
  assumes al: "x AND mask m = 0"
  assumes le_sz: "m + n < size x"
  assumes le_add: "x \<le> x + mask (m + n)"
  shows "align_up (x >> m) n = (align_up x (m + n)) >> m"
proof -
  have split_mask:
    "(x + mask (m + n)) = (mask n << m) + (x + mask m)"
    apply (simp add: field_simps)
    apply (subst word_plus_is_or)
     apply (auto simp: word_eq_iff word_ops_nth_size nth_shiftl)
    done

  have shift_and_high:
    "(x + y >> m) AND (NOT z >> m) = (x + y >> m) AND NOT (z >> m)" for y z
    by (auto simp: word_eq_iff word_ops_nth_size nth_shiftr word_not_nth
        dest: test_bit_size)

  show ?thesis using le_sz
    apply (simp add: align_up_def word_and_shiftr_dist)
    apply (simp add: shift_and_high)
    apply (simp add: split_mask)
    apply (subst word_add_shiftr_aligned_distrib3)
      apply (simp add: word_and_mask_0_iff_not_testbits nth_shiftl)
     apply (subst olen_add_eqv)
     apply (simp add: split_mask[symmetric])
     apply (simp add: word_plus_mono_right[OF mask_mono le_add])
    apply (simp add: shiftl_shiftr min.absorb2 add.commute)
    apply (simp add: word_plus_is_or[OF al] word_or_shiftr_dist mask_shiftr min.absorb2)
    done
qed

lemma count_leading_zeros_characterisation:
  "x = 0 \<or> (nat (count_leading_zeros x) < size x \<and>
    x AND NOT (mask (size x - (nat (count_leading_zeros x) + 1))) =
        (1 << (size x - (nat (count_leading_zeros x) + 1))))"
  using count_leading_zeros_set[of x]
  apply (case_tac "x = 0", simp_all)
  apply (intro conjI word_eqI impI iffI, simp_all)
    apply (clarsimp simp: word_eq_iff)
    apply (frule count_leading_zeros_nth_imp, simp)
   apply (clarsimp simp flip: shiftl_1 simp add: word_ops_nth_size nth_shiftl)
   apply (frule count_leading_zeros_nth_imp, simp)
  apply (clarsimp simp flip: shiftl_1 simp add: word_ops_nth_size nth_shiftl)
  apply (erule meta_mp)
  apply (clarsimp simp: word_eq_iff)
  apply (frule count_leading_zeros_nth_imp, simp)
  done

lemma count_leading_zeros_0[OF refl]:
  "x = 0 \<Longrightarrow> count_leading_zeros x = of_nat (size x)"
  using count_leading_zeros_lim[of x]
    count_leading_zeros_set[of x]
    count_leading_zeros_positive[of x]
  by (auto simp add: order_class.le_less)

lemma nat_less_eq_disj:
  "j \<noteq> 0 \<Longrightarrow> (i < j) = (i = j - Suc 0 \<or> (i < j - Suc 0))"
  by auto

lemma nat_eq_iff2:
  "0 < j \<Longrightarrow> (nat i = j) = (i = int j)"
  by auto

lemma unat_le_unat_eq:
  fixes x :: "('a :: len) word"
  fixes y :: "('b :: len) word"
  shows "(unat x \<le> unat y) = (if size x \<le> size y then ucast x \<le> y else x \<le> ucast y)"
  by (simp add: word_le_nat_alt)

(* clone of a HOL4-ism. cope with subterm duplication by naming the
    common term as a variable and hiding the defining equality
    under this term *)
definition
  abbrev :: "'a \<Rightarrow> 'a"
  where
  "abbrev x = x"

lemma abbrev_eqD:
  "x = y \<Longrightarrow> abbrev (x = y)"
  by (simp add: abbrev_def)

lemmas unabbrev_eq = abbrev_def[where x="x = y" for x y]

lemma CapSetBounds_decoding_brute_force:
  assumes r: "Run (CapSetBounds cap req_len exact) t cap'"
  assumes r2: "Run (CapGetBounds cap') t' (base, limit, v)"
    (* SMT confirms this is necessary *)
  assumes req_len: "req_len \<le> 2 ^ 64"
  assumes orig_limit: "get_limit cap \<le> 2 ^ 64"
  defines
    "abase \<equiv> if CapBoundsUsesValue (CapGetExponent cap)
    then CapBoundsAddress (CapGetValue cap) else (CapGetValue cap)"
  defines
    "insuff \<equiv> (test_bit req_len (nat (CapGetExponent cap') + (nat CAP_MW - 2)) \<or>
            test_bit (align_up (ucast abase + req_len) (cap_alignment cap' - 1) -
                    ((ucast abase) AND NOT (mask (cap_alignment cap' - 1))))
                (nat (CapGetExponent cap') + (nat CAP_MW - 2)))"
  shows "CapIsTagSet cap' \<longrightarrow>
    (base = (ucast abase) AND NOT (mask (cap_alignment cap')) \<and>
        limit = align_up (ucast abase + req_len) (cap_alignment cap') \<and>
        CapGetExponent cap' \<le> nat CAP_MAX_EXPONENT \<and>
        (CapGetExponent cap' = nat CAP_MAX_EXPONENT \<longrightarrow> (limit - base) \<ge> 2 ^ 64) \<and>
        (0 < nat (CapGetExponent cap') \<longrightarrow> insuff))"
proof -

  let ?z_arg = "Word.slice (nat (CAP_MW - 1)) req_len :: 50 word"
  let ?z = "count_leading_zeros ?z_arg"

  note if_split[split del] [[simproc del: let_simp]]

  note [[goals_limit = 1]]

  have uint_of_bl_6_7:
    "uint (x :: 6 word) = uint (of_bl (to_bl x) :: 7 word)" for x
    by (simp add: ucast_bl[symmetric])

  have ugh[simp]: "Suc (Suc 0) = 2" by simp

  note upt_conv_Cons[simp]
  note bl_6 = to_bl_upt[where 'a=6, simplified]

  note get_exponent_bl = CapGetExponent_def[unfolded uint_of_bl_6_7 bl_6, simplified]

  have abbrev_get_exponent:
    "abbrev (x = cap) \<Longrightarrow> CapGetExponent x = y \<Longrightarrow> abbrev (CapGetExponent cap = y)"
    for cap x y
    by (simp add: abbrev_def)

  have use_orig_limit:
    "Run (CapGetBounds cap) t x \<Longrightarrow> fst (snd x) \<le> 2 ^ 64" for t x
    using orig_limit
    apply (cases x; clarsimp)
    apply (drule CapGetBounds_get_limit)
    apply (simp add: word_le_nat_alt)
    done

  have insuff1: "?z < CAP_MAX_EXPONENT \<longrightarrow> (CapGetExponent cap' = CAP_MAX_EXPONENT - ?z)
    \<longrightarrow> insuff"
    using count_leading_zeros_set[of "?z_arg"] count_leading_zeros_positive[of "?z_arg"]
    apply (clarsimp simp: CAP_MAX_EXPONENT_def insuff_def)
    apply (drule meta_mp, simp)
    apply (simp add: nth_slice CAP_MW_def nat_diff_distrib)
    done

  note insuff2 = insuff_def[THEN meta_eq_to_obj_eq, THEN iffD2, OF disjI2]

  show ?thesis
    using r r2 insuff1 insuff2
    apply (clarsimp simp: Let_def abase_def)
    apply (clarsimp simp: CapSetBounds_def elim!: Run_elims cong: if_cong)

    apply (simp add: if_distrib[where f="\<lambda>x. test_bit x _"] test_bit_set_gen
                lift_let[where f="\<lambda>x. test_bit x _"] Let_def[where f="\<lambda>x. test_bit x _"]
                update_subrange_vec_dec_test_bit CAP_BASE_EXP_HI_BIT_def CAP_LIMIT_EXP_HI_BIT_def
                test_bit_vector_update_subrange_from_subrange
                less_diff_conv2
                CAP_MAX_EXPONENT_def CAP_MW_def
        cong: if_cong)
    apply (clarsimp simp only: simp_thms if_simps dest!: if_bool_eq_disj[where Q=False, THEN iffD1])

    apply (split if_split_asm[where Q="count_leading_zeros _ = _ \<longrightarrow> _"],
        simp_all only: simp_thms if_simps)
     prefer 2
     (* the non-ie case *)
     apply (clarsimp simp: Let_def elim!: Run_elims)
     apply (cut_tac x="?z_arg" in count_leading_zeros_lt)
     apply (clarsimp simp: CapGetBounds_def[where c="update_subrange_vec_dec _ _ _ _"]
            CapGetExponent_def[where c="update_subrange_vec_dec _ _ _ _"]
            CapIsInternalExponent_def CapGetTop_def
            update_subrange_vec_dec_test_bit nth_slice CapBoundsUsesValue_def
            test_bit_set_gen
            test_bit_vector_update_subrange_from_subrange
            word_ops_nth_size nth_word_cat integer_subrange_def
            CAP_MAX_ENCODEABLE_EXPONENT_def CAP_MAX_EXPONENT_def
            CapIsExponentOutOfRange_def
            cap_alignment_def)
     apply ((erule_tac P="(base = _ \<longrightarrow> _)" in rev_mp), simp)?
     apply ((erule_tac P="(_ \<longrightarrow> base \<noteq> _)" in rev_mp), simp)?
     apply (clarsimp elim!: Run_elims, (erule_tac P="(_ :: _ word) = _" in rev_mp)+, let_dup_word)
     apply (clarsimp simp: CAP_MW_def CAP_VALUE_NUM_BITS_def
            if_distrib[where f="word_of_int"] wi_hom_syms
            word_of_int_shiftl word_less_nat_alt[symmetric]
            word_less_nat_alt[where a="1 :: 2 word", symmetric, simplified]
            of_bl_Cons of_bool_test_bit unat_le_unat_eq zext_ones_def
            word_set_bit_to_and_or(3)[where y="NOT _" and i=0, simplified Word.msb0]
            Let_def[where f="Pair _"]
            max_word_def align_up_def
            sign_extend_def CAP_BOUND_MAX_def
            word_le_nat_alt[symmetric]
            update_subrange_vec_dec_def word_update_to_word_slice_in
            vector_update_subrange_from_subrange_to_word_slice_in
            set_slice_zeros_shifts
            update_vec_dec_bitU_of_bool
            word_set_bit_to_and_or
        cong: if_cong)
     apply (simp add: mask_def word_slice_in_def word_set_bit_to_and_or
            test_bit_is_slice_check Let_def[where s="scast _"]
            CapBoundsAddress_def CapGetBottom_def CapIsInternalExponent_def
            align_up_def CAP_VALUE_NUM_BITS_def sign_extend_def
            CapGetValue_def
        cong: if_cong)
     subgoal
     using [[argo_timeout = 1000]]
     by (word_bitwise_eq; intro impI; simp only: simp_thms carry_def; argo)

    apply (cases "CAP_MAX_EXPONENT < CapGetExponent cap'")
     (* impossibly high selected exponent *)
     apply (clarsimp elim!: Run_elims)
     apply (drule use_orig_limit)
     apply (subgoal_tac "base = 0 \<and> limit = 2 ^ 64")
      prefer 2
      apply (clarsimp simp: CapGetBounds_def elim!: Run_elims)
      apply (elim conjE disjE, simp_all add: CAP_BOUND_MIN_def CAP_BOUND_MAX_def)[1]
      apply (thin_tac "_ \<in> Traces")+
      apply (cut_tac CapGetExponent_range[where c=cap'])
      apply (simp add: CAP_MAX_ENCODEABLE_EXPONENT_def CapIsExponentOutOfRange_def[unfolded Let_def])
     apply (erule_tac P="CAP_MAX_EXPONENT < _" in rev_mp)
     apply (rule rev_mp, rule get_exponent_bl[where c=cap'])
     apply (simp add:
            CapIsInternalExponent_def CapGetTop_def
            update_subrange_vec_dec_test_bit nth_slice CapBoundsUsesValue_def
            test_bit_set_gen
            test_bit_vector_update_subrange_from_subrange
            word_ops_nth_size nth_word_cat integer_subrange_def
            CAP_MAX_ENCODEABLE_EXPONENT_def CAP_MAX_EXPONENT_def
            CAP_MW_def CAP_VALUE_NUM_BITS_def
            CapIsExponentOutOfRange_def
            cap_alignment_def
            uint_eq_eq)
     apply (rule rev_mp, rule_tac x="?z_arg" in count_leading_zeros_characterisation)
     apply (simp add: nat_less_eq_disj[where i="nat (count_leading_zeros _)"] CAP_MW_def)
     apply (simp(no_asm) add: imp_conjL nat_eq_iff2 split: if_split)
     apply (simp add: antisym_conv[OF count_leading_zeros_positive] count_leading_zeros_0
            imp_conjL[symmetric] cong: rev_conj_cong)
     (* just the one impossible case left *)
     apply clarsimp
     apply (elim Run_elims; clarsimp)
    apply (clarsimp simp: CapGetBounds_def[where c="update_subrange_vec_dec _ _ _ _"]
        elim!: Run_elims)
    apply (cut_tac CapIsInternalExponent_def[of cap'])
    apply ((erule_tac P="exact \<longrightarrow> _" in rev_mp))
    apply (clarsimp simp: update_subrange_vec_dec_test_bit test_bit_set_gen
           CAP_MAX_EXPONENT_def)
    apply (erule_tac P="(limit = _ \<longrightarrow> _)" in rev_mp)
    apply (simp add: CAP_MAX_EXPONENT_def CAP_MAX_ENCODEABLE_EXPONENT_def
           CapIsExponentOutOfRange_def[unfolded Let_def] cap_alignment_def
           word_le_nat_alt[symmetric])
    apply (simp only: eq_commute[where a=cap'], drule abbrev_eqD[where y=cap'])
    apply (frule abbrev_get_exponent, simp add: get_exponent_bl
            CapIsInternalExponent_def
            update_subrange_vec_dec_test_bit nth_slice
            test_bit_set_gen word_ops_nth_size nth_word_cat
            test_bit_vector_update_subrange_from_subrange
            integer_subrange_def
    )
    apply (elim Run_elims; clarsimp elim!: Run_elims
        simp: CapGetTop_def
        simp del: slice_beyond_length mask_max_word
            Int.nat_le_0 word_and_mask Nat.diff_is_0_eq' Word_Extra.and_ucast_mask
            Word_Extra.word_and_not_mask
        cong: if_cong;
        (thin_tac "_ = _ @ _")+;
        (erule rev_mp[where P="_ = _"] rev_mp[where P="_ \<le> _"]
                rev_mp[where P="test_bit _ _"] rev_mp[where P="_ \<longrightarrow> _"])+;
        let_dup_word;
        cut_tac x="?z_arg" in count_leading_zeros_characterisation
    )

     apply (simp_all add: CAP_MW_def CAP_VALUE_NUM_BITS_def
            if_distrib[where f="word_of_int"] wi_hom_syms
            word_of_int_shiftl word_less_nat_alt[symmetric]
            word_less_nat_alt[where a="1 :: 2 word", symmetric, simplified]
            of_bl_Cons[where xs=Nil] of_bool_test_bit unat_le_unat_eq zext_ones_def
            word_set_bit_to_and_or(3)[where y="NOT _" and i=0, simplified Word.msb0]
            Let_def[where f="Pair _"]
            max_word_def align_up_def
            sign_extend_def CAP_BOUND_MAX_def
            word_le_nat_alt[symmetric]
            update_subrange_vec_dec_def word_update_to_word_slice_in
            vector_update_subrange_from_subrange_to_word_slice_in
            set_slice_zeros_shifts
            update_vec_dec_bitU_of_bool
            word_set_bit_to_and_or
        cong: if_cong)
     apply (simp_all add: CAP_MW_def nat_less_eq_disj[where i="nat (count_leading_zeros _)"])
     apply (simp_all add: nat_eq_iff2 antisym_conv[OF count_leading_zeros_positive]
          count_leading_zeros_0)
     apply (safe elim!: thin_rl[where V="_ : Traces"])
       (* 100-odd goals from here *)

    apply (simp_all add: integer_subrange_def unabbrev_eq[where y="numeral _"]
            CapBoundsUsesValue_def CAP_MW_def CAP_VALUE_NUM_BITS_def
            count_leading_zeros_0
            unabbrev_eq[where y="1"]
            unabbrev_eq[where y="0"]
        cong: if_cong)
    apply (simp_all add: mask_def word_slice_in_def word_set_bit_to_and_or
            test_bit_is_slice_check Let_def[where s="scast _"]
            CapBoundsAddress_def CapGetBottom_def CapIsInternalExponent_def
            align_up_def CAP_VALUE_NUM_BITS_def sign_extend_def
            CapGetValue_def Let_def[where s="Word.slice _ _"]
            word_update_to_word_slice_in set_slice_zeros_shifts
            minus_one_norm
        cong: if_cong)
    apply (simp_all only: abbrev_def)
    apply (simp_all add: to_smt_word del: to_smt_word_del cong: if_cong)

    using [[smt_timeout = 10000, smt_solver=cvc4]]
    by smt_word+
qed

lemma sufficient_exponent_bounds_mono:
  "sufficient_exponent x y n \<Longrightarrow>
    x \<le> x' \<Longrightarrow> y' \<le> y \<Longrightarrow>
    y \<le> align_up y (n + 3) \<Longrightarrow>
    sufficient_exponent x' y' n"
  apply (clarsimp simp: sufficient_exponent_def)
  apply (erule order_le_less_trans[rotated])
  apply (rule order_trans[OF diff_le_mono, rotated])
   apply (rule diff_le_mono2)
   apply (simp_all add: word_le_nat_alt[symmetric])
   apply (erule le_and_not_mask)
  apply (rule align_up_le_aligned)
   apply (rule align_up_aligned)
  apply simp
  done

lemma unat_align_up_max:
  "unat (align_up x n) \<le> unat x + 2 ^ n - 1"
  (is "?lhs \<le> ?rhs")
proof (cases "n < size x")
  case True
  have "?lhs \<le> unat (x + mask n)"
    (is "_ \<le> unat (_ + ?m)")
    by (simp add: align_up_def word_le_nat_alt[symmetric] word_and_le2)
  also have "\<dots> \<le> unat x + unat ?m"
    by (simp add: unat_word_ariths)
  also have "\<dots> \<le> ?rhs"
    using True
    by (simp add: unat_mask)
  finally show ?thesis by simp
next
  case False
  then show ?thesis
    by (simp add: align_up_def)
qed

lemma unat_not_mask_min:
  "unat x - (2 ^ n - 1) \<le> unat (x AND NOT (mask n))"
proof (cases "n < size x")
  case True
  then show ?thesis
    using exists_quotient_remainder[of "2 ^ n" "unat x"]
    apply (clarsimp simp: unat_and_not_mask)
    apply (case_tac q, simp_all)
    done
next
  case False
  then show ?thesis
    using order_less_le_trans[OF unat_lt2p[of x] power_increasing[where N=n]]
    by (simp del: unat_lt2p)
qed

lemma sufficient_exponent_mono:
  assumes orig: "sufficient_exponent x y n"
  assumes conds: "n \<le> m" "x \<le> y" "m \<le> nat CAP_MAX_EXPONENT"
  shows "sufficient_exponent x y m"
proof (cases "n = m")
  case True
  then show ?thesis using orig by simp
next
  case False

  have less: "n < m" using False conds by simp

  (* need to show the alignment corrections are dominated by the increase in the
     exponential on the right, which isn't entirely obvious *)

  have le1: "unat (align_up y (m + 3)) \<le> unat (align_up y (n + 3)) + 2 ^ (m + 3)"
    (is "_ \<le> ?al_y + _")
    using conds unat_align_up_max[of "align_up y (n + 3)" "m + 3"]
    by (simp add: align_up_twice)

  have le2: "unat (x AND NOT (mask (n + 3))) - 2 ^ (m + 3) \<le> unat (x AND NOT (mask (m + 3)))"
    (is "?al_x - _ \<le> _")
    using unat_not_mask_min[of x "m + 3"] word_and_le2[of x "NOT (mask (n + 3))"]
    by (simp add: word_le_nat_alt)

  have "unat (align_up y (m + 3)) - unat (x AND NOT (mask (m + 3))) \<le>
        (?al_y + 2 ^ (m + 3)) - (?al_x - 2 ^ (m + 3))"
    using le1 le2 by simp
  also have
    "\<dots> \<le> ?al_y - ?al_x + (2 ^ (m + 3)) + (2 ^ (m + 3))"
    by simp
  also have
    "\<dots> \<le> 2 ^ (n + 15) + 2 ^ (m + 3) + 2 ^ (m + 3)"
    using orig
    by (clarsimp simp: sufficient_exponent_def CAP_MW_def)
  also have
    "\<dots> \<le> 2 ^ (m + 14) + 2 ^ (m + 3) + 2 ^ (m + 3)"
    using less
    by simp
  also have
    "\<dots> = 2 ^ (m + 3) * (2 ^ 11 + 2)"
     by (simp only: ring_distribs power_add[symmetric], simp)
  also have
    "\<dots> < 2 ^ (m + 3 + 12)"
     by (simp only: power_add, simp)

  finally show ?thesis using orig
    apply (clarsimp simp: sufficient_exponent_def CAP_MW_def)
    apply (simp only: add.commute)
    done
qed

lemma align_up_mono:
  "x \<le> x + mask n \<Longrightarrow> x \<le> align_up x n"
  using exists_quotient_remainder[of "2 ^ n" "unat x - 1"]
  apply (simp add: align_up_def word_le_nat_alt unat_and_not_mask
        unat_plus_simple[THEN iffD1])
  apply (simp add: unat_mask min_def)
  apply (cases "unat x", simp_all)
  apply clarsimp
  apply (simp add: max_word_minus)
  apply (subst(asm) unat_minus_one, auto)[1]
  done

lemma align_up_mono_le_power:
  fixes x :: "('a :: len) word"
  assumes power: "x \<le> 2 ^ m"
    and exp: "n \<le> m"
  shows "x \<le> align_up x n"
proof (cases "unat x = 0")
  case True
  then show ?thesis by (simp add: align_up_def unat_eq_0)
next
  case False

  have m_size: "m < size x"
    using power False
    by (simp add: word_le_nat_alt unat_t2n split: if_split_asm)

  have "unat x + y \<le> 2 ^ m + y" for y
    using power False
    by (simp add: word_le_nat_alt unat_t2n split: if_split_asm)
  also have "2 ^ m + unat (mask n :: 'a word) \<le> 2 ^ m + (2 ^ n - 1)"
    using exp m_size
    by (simp add: unat_mask)
  also have "\<dots> \<le> 2 ^ m + (2 ^ m - 1)"
    using exp
    by (simp only: nat_add_left_cancel_le, simp add: diff_le_mono)
  also have "\<dots> < 2 ^ Suc m"
    by (simp add: mult_2)
  also have "\<dots> \<le> 2 ^ size x"
    using m_size
    by (simp del: power_Suc)

  finally show ?thesis
    apply (simp add: unat_add_lem)
    apply (rule align_up_mono)
    apply (simp add: word_le_nat_alt)
    done
qed

lemma insufficient_exponent_test_bit_helper:
  "sufficient_exponent lower_b upper_b expon \<Longrightarrow>
    test_bit x n \<or> test_bit y n \<Longrightarrow>
    lower_b \<le> upper_b \<Longrightarrow>
    expon + (nat CAP_MW - 1) \<le> n \<Longrightarrow>
    n \<le> 64 \<Longrightarrow>
    upper_b \<le> align_up upper_b (expon + 3) \<Longrightarrow>
    test_bit x n \<longrightarrow> test_bit (upper_b - lower_b) n \<Longrightarrow>
    test_bit y n \<longrightarrow> test_bit (align_up upper_b (expon + 3) - (lower_b AND NOT (mask (expon + 3)))) n \<Longrightarrow>
    False"
  apply (erule disjE)
   apply (frule insufficient_exponent_original_size; assumption?; simp?)
   apply (simp add: word_eq_iff)
   apply (rule exI[where x=n])
   apply (simp add: word_ops_nth_size)
  apply (frule insufficient_exponent_encoded_bit; assumption?; simp?)
  done

lemma CapSetBounds_derivable_proof:
  assumes r: "Run (CapSetBounds cap req_len exact) t cap'"
  assumes deriv: "cap \<in> derivable_caps s"
  assumes unsealed: "CapIsTagSet cap \<longrightarrow> \<not>CapIsSealed cap"
  assumes req_len: "req_len \<le> 2 ^ 64"
  assumes orig_cap_invariant: "CapIsTagSet cap \<longrightarrow> cap_invariant cap"
  shows "cap' \<in> derivable_caps s"
proof (cases "CapIsTagSet cap'")
  case False
  thus ?thesis
    by (simp add: derivable_caps_def)
next
  case True

  note if_split[split del] [[simproc del: let_simp]]

  note deriv2 = deriv[simplified derivable_caps_def, simplified, rule_format]
  note Restr = derivable.Restrict[OF deriv2]

  have high_region_equal:
    "nat CAP_IE_BIT < i \<and> i < 128 \<Longrightarrow> test_bit cap' i = test_bit cap i" for i
    using r[unfolded CapSetBounds_def]
    apply (clarsimp elim!: Run_elims)
    apply (simp add: if_distrib[where f="\<lambda>x. test_bit x _"] test_bit_set_gen
                lift_let[where f="\<lambda>x. test_bit x _"] Let_def[where f="\<lambda>x. test_bit x _"]
                update_subrange_vec_dec_test_bit CAP_BASE_EXP_HI_BIT_def CAP_LIMIT_EXP_HI_BIT_def
                test_bit_vector_update_subrange_from_subrange
                less_diff_conv2
        cong: if_cong)
    done

  have encoding:
    "CapGetObjectType cap' = CapGetObjectType cap"
    "CapGetPermissions cap' = CapGetPermissions cap"
    "CapIsSealed cap' = CapIsSealed cap"
    "CapCheckPermissions cap' CAP_PERM_GLOBAL = CapCheckPermissions cap CAP_PERM_GLOBAL"
    apply (simp_all add: CapGetObjectType_def word_eq_iff word_ops_nth_size nth_slice
                     CapCheckPermissions_def CapGetPermissions_def CAP_PERM_GLOBAL_def
                     Let_def CapIsSealed_def)
    apply (simp_all add: high_region_equal cong: rev_conj_cong)
    done

  let ?z_arg = "Word.slice (nat (CAP_MW - 1)) req_len :: 50 word"
  let ?z = "count_leading_zeros ?z_arg"

  have ie_bit:
    "CapIsInternalExponent cap' = (?z = CAP_MAX_EXPONENT \<longrightarrow> test_bit req_len (nat (CAP_MW - 2)))"
    using r[unfolded CapSetBounds_def]
    apply (clarsimp elim!: Run_elims)
    apply (thin_tac _)+
    apply (simp add: CapIsInternalExponent_def
                if_distrib[where f="\<lambda>x. test_bit x _"] test_bit_set_gen
                lift_let[where f="\<lambda>x. test_bit x _"] Let_def[where f="\<lambda>x. test_bit x _"]
                update_subrange_vec_dec_test_bit CAP_BASE_EXP_HI_BIT_def CAP_LIMIT_EXP_HI_BIT_def
                test_bit_vector_update_subrange_from_subrange
                less_diff_conv2 if_bool_simps
        cong: if_cong)
    apply (auto simp add: CAP_MW_def)
    done

  let ?abase = "if CapBoundsUsesValue (CapGetExponent cap)
    then CapBoundsAddress (CapGetValue cap) else (CapGetValue cap)"
  let ?req_top = "(ucast ?abase) + (ucast req_len) :: 66 word"

  obtain orig_base orig_lim orig_v orig_get_t
  where orig_get_bounds: "Run (CapGetBounds cap) orig_get_t (orig_base, orig_lim, orig_v)"
    using CapGetBounds_ex_run[of cap]
    by (auto simp: ex_run_def)

  note orig_bounds = CapGetBounds_get_base[OF orig_get_bounds]
    CapGetBounds_get_limit[OF orig_get_bounds]

  have constraints:
    "CapIsTagSet cap \<and> orig_base \<le> ucast ?abase \<and> ucast ?req_top \<le> orig_lim"
    using r[unfolded CapSetBounds_def] True
    using [[goals_limit = 1]]
    apply (clarsimp elim!: Run_elims)
    apply (thin_tac "_ = _")+
    apply (frule CapGetBounds_get_base[symmetric]; frule CapGetBounds_get_limit[symmetric])
    apply (simp add: orig_bounds word_le_nat_alt)
    apply (simp add: if_distrib[where f="\<lambda>x. test_bit x _"] test_bit_set_gen
                lift_let[where f="\<lambda>x. test_bit x _"] Let_def[where f="\<lambda>x. test_bit x _"]
                update_subrange_vec_dec_test_bit CAP_BASE_EXP_HI_BIT_def CAP_LIMIT_EXP_HI_BIT_def
                test_bit_vector_update_subrange_from_subrange
                if_bool_eq_disj[where Q=False]
        cong: if_cong)
    done

  note tag = constraints[THEN conjunct1]
  note orig_inv = orig_cap_invariant[rule_format, OF tag]
  note ineq = constraints[THEN conjunct2]

  have orig_max:
    "orig_lim \<le> 2 ^ 64"
    using orig_inv
    by (simp add: cap_invariant_def word_le_nat_alt orig_bounds)

  let ?align = "cap_alignment cap"
  let ?align2 = "cap_alignment cap'"

  have mask_exp_align_lim:
    "(mask ?align2 :: 65 word) \<le> mask (nat CAP_MAX_EXPONENT + 3)"
    apply (rule mask_mono)
    apply (simp add: cap_alignment_def nat_mono split: if_split)
    done

  obtain new_lim new_base new_v new_get_t where new_get_bounds:
    "Run (CapGetBounds cap') new_get_t (new_base, new_lim, new_v)"
    using CapGetBounds_ex_run[of cap']
    by (auto simp add: ex_run_def)

  note new_bounds = CapGetBounds_get_base[OF new_get_bounds]
    CapGetBounds_get_limit[OF new_get_bounds]

  have decoding:
    "new_base = (ucast ?abase) AND NOT (mask ?align2) \<and>
        new_lim = align_up (ucast ?req_top) ?align2 \<and>
        CapGetExponent cap' \<le> CAP_MAX_EXPONENT \<and>
        (CapGetExponent cap' = CAP_MAX_EXPONENT \<longrightarrow> 2 ^ 64 \<le> new_lim - new_base)"
    using CapSetBounds_decoding_brute_force[OF r new_get_bounds req_len] True orig_max
    apply (simp add: word_le_nat_alt orig_bounds Let_def)
    apply (simp add: ucast_plus_down)
    apply (clarsimp simp: CAP_MAX_EXPONENT_def)
    done

  have "(ucast ?abase :: 65 word) \<le> ucast ?req_top"
    using req_len
    apply (simp add: word_le_nat_alt word_less_nat_alt unat_and_mask unat_word_ariths)
    apply (simp add: order_less_le_trans[OF add_less_mono1, OF unat_lt2p])
    done

  also have "\<dots> \<le> ucast (?req_top) + mask ?align2"
    using mask_exp_align_lim order_trans[OF ineq[THEN conjunct2] orig_max]
    apply (clarsimp simp: no_plus_overflow_unat_size)
    apply (simp add: word_le_nat_alt)
    apply (simp add: CAP_MAX_EXPONENT_def mask_def[where n="numeral _"])
    done

  finally have le:
    "(ucast ?abase :: 65 word) AND NOT (mask ?align2) \<le> align_up (ucast ?req_top) ?align2"
    by (simp add: align_up_def le_and_not_mask)

  note orig_ie_suff = CapGetBounds_ie_sufficient[OF orig_get_bounds orig_inv, OF conjI]

  have ie_bit_req_len:
    "CapIsInternalExponent cap' \<Longrightarrow> 2 ^ (nat CAP_MW - 2) \<le> req_len"
    using count_leading_zeros_set[of "?z_arg"] count_leading_zeros_lim[of "?z_arg"]
    apply (simp add: ie_bit CAP_MAX_EXPONENT_def)
    apply (rule ccontr, simp add: linorder_not_le)
    apply (drule less_mask_eq)
    apply (simp add: nth_slice CAP_MW_def)
    apply (simp add: mask_lo_test_bit)
    apply (drule meta_mp, simp+)
    done

  have orig_len:
    "unat (orig_lim - orig_base) < 2 ^ 64 \<or> (orig_base = 0 \<and> orig_lim = 2 ^ 64)"
    using orig_inv
    apply (clarsimp simp: cap_invariant_def orig_bounds unat_sub word_le_nat_alt)
    apply (cases "unat orig_base", simp_all add: unat_eq_0)
    apply (erule le_neq_trans)
    apply (clarsimp dest!: unat_eqD)
    done

  note unat_req_top_less = add_less_le_mono[OF unat_lt2p[of "?abase"]
        req_len[simplified word_le_nat_alt], simplified]

  have ie_implies:
    "CapIsInternalExponent cap' \<longrightarrow> (CapIsInternalExponent cap
        \<or> (orig_base = 0 \<and> orig_lim = 2 ^ 64))"
    using constraints CapGetBounds_nie_limit[OF orig_get_bounds] ie_bit_req_len
          orig_len unat_req_top_less
    apply (cases "CapIsInternalExponent cap"; clarsimp)
    apply (clarsimp simp: word_le_nat_alt word_less_nat_alt unat_t2n CAP_MW_def)
    apply (subst(asm) word_le_mask_eq[THEN iffD1])
     apply (simp add: mask_def word_le_nat_alt)
    apply (simp add: unat_and_mask unat_word_ariths mod_mod_cancel)
    apply (simp add: unat_sub word_le_nat_alt)
    done

  have smaller_insufficient:
    "0 < nat (CapGetExponent cap') \<Longrightarrow>
        \<not> sufficient_exponent (ucast ?abase) (ucast ?req_top) (nat (CapGetExponent cap') - 1) \<or>
        (orig_base = 0 \<and> orig_lim = 2 ^ 64)"
    using CapSetBounds_decoding_brute_force[OF r new_get_bounds req_len] True orig_max
    apply (cases "\<not> CapIsInternalExponent cap'")
     apply (simp add: CapGetExponent_def)
    apply (clarsimp simp: orig_bounds word_le_nat_alt)
    apply (frule(1) insufficient_exponent_test_bit_helper, simp_all)
        apply (simp add: ucast_plus_down no_plus_overflow_unat_size unat_req_top_less)
       apply (simp add: CAP_MW_def CAP_MAX_EXPONENT_def)
      apply (rule align_up_mono_le_power[OF order_trans, OF _ orig_max])
       apply (simp add: ineq)
      apply (simp add: CAP_MAX_EXPONENT_def)
     apply (simp add: ucast_plus_down)
    apply (simp add: ucast_plus_down cap_alignment_def min.absorb1 CAP_MAX_EXPONENT_def)
    done

  have le_alignment:
    "cap_alignment cap' \<le> cap_alignment cap \<or> (orig_base = 0 \<and> orig_lim = 2 ^ 64)"
    using CapGetExponent_range[of cap] CapGetExponent_range[of cap']
        decoding[THEN conjunct2, THEN conjunct2]
        smaller_insufficient ie_implies
    apply clarsimp
    apply (simp add: cap_alignment_def split: if_split)
    apply (simp add: min_def split: if_split)
    apply (intro conjI impI; (solves \<open>clarsimp simp: CAP_MAX_EXPONENT_def; simp\<close>)?)
    apply (cases "0 < nat (CapGetExponent cap')", simp_all)[1]
    apply (cases "CapGetExponent cap = CAP_MAX_EXPONENT", simp_all)[1]
    apply (frule orig_ie_suff, simp)
    apply (erule disjE, simp_all)[1]
    apply (rule ccontr)
    apply (erule notE, rule sufficient_exponent_mono)
       apply (erule sufficient_exponent_bounds_mono, simp_all add: ineq)[1]
       apply (rule align_up_mono_le_power[OF orig_max])
       apply (simp add: CAP_MAX_EXPONENT_def)
      apply simp
     apply (simp add: ucast_plus_down no_plus_overflow_unat_size unat_req_top_less)
    apply simp
    done

  have orig_base_aligned:
    "orig_base AND mask ?align2 = 0 \<and> orig_lim AND mask ?align2 = 0"
    using CapGetBounds_aligned[OF orig_get_bounds] le_alignment CapGetExponent_range[of cap']
    apply (elim disjE)
     apply (simp add: word_and_mask_0_iff_not_testbits)
    apply (simp only: word_bool_alg.conj_zero_left simp_thms)
    apply (rule aligned_le[OF t2n_mask_n])
    apply (simp add: cap_alignment_def CAP_MAX_EXPONENT_def nat_le_iff min_le_iff_disj split: if_split)
    done

  from True tag ineq decoding show ?thesis
    apply (simp add: derivable_caps_def)
    apply (rule Restr, simp_all)
    apply (rule leq_cap_def[THEN iffD2, OF disjI2], simp add: unsealed encoding CapGetPermissions_eq_leq_perms)
    apply (rule leq_bounds_def[THEN iffD2, OF disjI2])
    apply (clarsimp simp: orig_bounds new_bounds word_le_nat_alt[symmetric] le)
    apply (intro conjI)
     apply (rule order_trans[OF _ le_and_not_mask, rotated], assumption)
     apply (simp add: orig_base_aligned flip: word_minus_word_and_mask)
    apply (rule align_up_le_aligned)
     apply (simp add: orig_base_aligned)
    apply simp
    done
qed

lemma zero_extend_65_le_2p64:
  fixes w :: "'a::len word"
  assumes "LENGTH('a) \<le> 64"
  shows "zero_extend w 65 \<le> (2 ^ 64 :: 65 word)"
  using assms power_increasing[OF assms, where a = 2]
  by (auto simp add: word_le_def intro!: uint_less[of w, THEN order_trans])

lemmas [derivable_capsI] =
  zero_extend_65_le_2p64[of w for w :: "64 word"]
  zero_extend_65_le_2p64[of w for w :: "6 word"]

lemma place_slice_6_65_le_2p64[derivable_capsI]:
  "place_slice 65 (imm6 :: 6 word) 0 6 4 \<le> (2 ^ 64 :: 65 word)"
  by (simp add: place_slice_def slice_mask_def sail_ones_def zeros_def word_le_def uint_shiftl bintrunc_shiftl bintr_uint, auto simp: shiftl_int_def)

declare if_split[where P = "\<lambda>w. w \<le> (2 ^ 64 :: 65 word)", THEN iffD2, derivable_capsI]

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

text \<open>We assume that UNKNOWN capabilities are constrained to reachable capabilities, in line with
  rule TSNJF of the architecture.

  Formalising this is a bit tricky, as our usual approach of demanding that any newly created
  capabilities must be derived from previously read or loaded capabilities does not work here;
  some instructions like STLXR, for example, may generate UNKNOWN capabilities \<^emph>\<open>instead\<close> of
  reading some of their input registers, so constraining UNKNOWN capabilities to values appearing
  beforehand in the trace would not allow the likely behaviour of choosing the content of one of
  those registers.

  Instead, we make use of the \<open>initial_caps\<close> mechanism in T-CHERI:  We assume that UNKNOWN
  capabilities are drawn from a set that is at this point arbitrary but fixed, but will be
  constrained later (in the assumptions of the monotonicity theorem) to a subset of the
  capabilities reachable from the starting state of the concrete exection we are considering.\<close>

fun unknown_ev_assms :: "register_value event \<Rightarrow> bool" where
  "unknown_ev_assms (E_choose descr (Regval_bitvector_129_dec c)) =
     (descr = ''UNKNOWN_Capability'' \<longrightarrow> c \<in> UNKNOWN_caps)"
| "unknown_ev_assms _ = True"

definition "unknown_trace_assms t \<equiv> (\<forall>e \<in> set t. unknown_ev_assms e)"

lemma UNKNOWN_Capability_derivable[derivable_capsE]:
  assumes "Run (UNKNOWN_Capability ()) t c" and "unknown_trace_assms t"
  shows "c \<in> derivable_caps s"
  using assms
  unfolding UNKNOWN_Capability_def choose_convert_def maybe_fail_def
  by (fastforce simp: unknown_trace_assms_def derivable_caps_def split: option.splits
                elim: Traces_cases intro: derivable.Copy)

lemma [derivable_capsE]:
  assumes "Run (UNKNOWN_bits 129) t c" and "unknown_trace_assms t"
  shows "c \<in> derivable_caps s"
  using assms
  unfolding UNKNOWN_bits_def
  by (auto elim: UNKNOWN_Capability_derivable)

lemma UNKNOWN_VirtualAddress_derivable[derivable_capsE]:
  assumes "Run (UNKNOWN_VirtualAddress ()) t va" and "unknown_trace_assms t"
  shows "VA_derivable va s"
  using assms
  unfolding UNKNOWN_VirtualAddress_def
  by (fastforce simp: VA_derivable_def unknown_trace_assms_def split: VirtualAddressType.splits
                elim!: Run_bindE dest!: UNKNOWN_Capability_derivable intro: derivable_caps_run_imp)

(* System register access *)

fun sysreg_ev_assms :: "(Capability, register_value) axiom_state \<Rightarrow> register_value event \<Rightarrow> bool" where
  "sysreg_ev_assms s (E_read_reg r (Regval_bitvector_129_dec c)) =
     (r = ''PCC'' \<and> ''PCC'' \<notin> written_regs s \<longrightarrow>
        (\<not>is_fetch \<longrightarrow> CapIsTagSet c) \<and>
        (CapIsTagSet c \<longrightarrow> \<not>CapIsSealed c) \<and>
        (no_system_reg_access \<longrightarrow> \<not>cap_permits (CAP_PERM_EXECUTE OR CAP_PERM_SYSTEM) c))"
| "sysreg_ev_assms s (E_read_reg r (Regval_bitvector_32_dec v)) =
     ((r = ''CSCR_EL3'' \<longrightarrow> no_system_reg_access \<or> v !! 0) \<and>
      (r = ''EDSCR'' \<longrightarrow> (ucast v :: 6 word) = 2))" (* Non-debug state *)
| "sysreg_ev_assms s (E_read_reg r (Regval_ProcState v)) =
     (r = ''PSTATE'' \<longrightarrow> no_system_reg_access \<or> ProcState_EL v \<noteq> EL3)"
| "sysreg_ev_assms s (E_read_reg r (Regval_bool v)) =
     (r = ''__BranchTaken'' \<and> \<not>is_fetch \<longrightarrow> v \<or> ''PCC'' \<notin> written_regs s)"
| "sysreg_ev_assms _ _ = True"

abbreviation "sysreg_trace_assms \<equiv> holds_along_trace sysreg_ev_assms"

lemma bitvector_32_dec_of_regva_eq_Some_iff[simp]:
  "bitvector_32_dec_of_regval rv = Some v \<longleftrightarrow> rv = Regval_bitvector_32_dec v"
  by (cases rv) auto

(* In Debug mode, access to system registers seems to be generally enabled, so let's assume that
   we are not in Debug mode; otherwise we'd have to tweak the properties to allow for ambient
   system register access permission. *)
lemma Halted_False:
  assumes "Run (Halted u) t a" and "sysreg_trace_assms s t"
  shows "\<not>a"
  using assms
  unfolding Halted_def
  by (auto simp: EDSCR_ref_def elim!: Run_bindE Run_or_boolM_E Run_read_regE)

lemma Run_Halted_True_False[simp]:
  assumes "sysreg_trace_assms s t"
  shows "Run (Halted ()) t True \<longleftrightarrow> False"
  using assms
  by (auto dest: Halted_False)

lemma Run_Halted_accessible_regs[accessible_regsE]:
  assumes "Run (Halted u) t h" and "sysreg_trace_assms s t"
    and "Rs - (if h then read_privileged_regs ISA else {}) \<subseteq> accessible_regs s"
  shows "Rs \<subseteq> accessible_regs (run s t)"
  using assms
  by (intro accessible_regs_no_writes_run_subset[of "Halted u" t h Rs])
     (auto intro: no_reg_writes_runs_no_reg_writes no_reg_writes_to_Halted split: if_splits)

lemma PCC_tagged:
  assumes "Run (read_reg PCC_ref) t c"
    and "\<exists>s. sysreg_trace_assms s t \<and> {''PCC''} \<subseteq> accessible_regs s"
    and "\<not>is_fetch"
  shows "CapIsTagSet c"
  using assms(1,2)
  by (auto elim!: Run_read_regE simp: PCC_ref_def) (auto simp: assms(3) accessible_regs_def)

lemma PCC_unsealed:
  assumes "Run (read_reg PCC_ref) t c"
    and "\<exists>s. sysreg_trace_assms s t \<and> {''PCC''} \<subseteq> accessible_regs s"
    and "is_fetch \<longrightarrow> CapIsTagSet c"
  shows "\<not>CapIsSealed c"
  using assms(1,2)
  by (auto elim!: Run_read_regE simp: PCC_ref_def accessible_regs_def dest!: assms(3)[rule_format])

lemma CapIsSystemAccessEnabled_trace_allows_system_reg_access:
  assumes "Run (CapIsSystemAccessEnabled u) t a" and "sysreg_trace_assms s t" and "a"
    and "{''PCC''} \<subseteq> accessible_regs s" and "\<not>is_fetch"
  shows "trace_allows_system_reg_access t s"
proof -
  obtain t1 t2 c
    where t1: "Run (Halted ()) t1 False"
      and t2: "Run (read_reg PCC_ref :: Capability M) t2 c" "sysreg_trace_assms (run s t1) t2"
      and c: "CapIsSystemAccessPermitted c"
      and t: "t = t1 @ t2"
    using assms(1-3)
    by (auto simp: CapIsSystemAccessEnabled_def PCC_read_def
             elim!: Run_bindE dest: Halted_False)
  moreover have accessible: "{''PCC''} \<subseteq> accessible_regs (run s t1)"
    using t t1 assms(2,4)
    by - accessible_regsI
  moreover have "CapIsTagSet c \<and> \<not>CapIsSealed c"
    using PCC_tagged[OF _ _ \<open>\<not>is_fetch\<close>] PCC_unsealed t2 accessible
    by fastforce
  ultimately show ?thesis
    by (auto elim!: Run_read_regE simp: PCC_ref_def)
qed

lemma CapIsSystemAccessEnabled_no_system_reg_access_cases:
  assumes "Run (CapIsSystemAccessEnabled u) t a"
    and "\<exists>s. sysreg_trace_assms s t \<and> {''PCC''} \<subseteq> accessible_regs s"
  obtains "a" and "\<not>no_system_reg_access" | "\<not>a"
  using assms sysreg_ev_assms.simps(1) Run_Halted_True_False
  using no_reg_writes_to_written_regs_run_inv[OF _ no_reg_writes_to_Halted]
  unfolding CapIsSystemAccessEnabled_def CapIsSystemAccessPermitted_def PCC_read_def
  by (elim Run_bindE Run_ifE Run_read_regE; auto simp: PCC_ref_def accessible_regs_def)

lemma CapIsSystemAccessEnabled_system_reg_access[derivable_capsE]:
  assumes "Run (CapIsSystemAccessEnabled u) t a" and "sysreg_trace_assms s t" and "a"
    and "{''PCC''} \<subseteq> accessible_regs s" and "\<not>is_fetch"
  shows "system_reg_access (run s t)"
  using CapIsSystemAccessEnabled_trace_allows_system_reg_access[OF assms]
  by (auto simp: system_reg_access_run_iff)

lemma CapIsSystemAccessEnabled_accessible_regs[accessible_regsE]:
  assumes "Run (CapIsSystemAccessEnabled u) t a" and "sysreg_trace_assms s t"
    and "Rs - (if a \<and> \<not>is_fetch then read_privileged_regs ISA else {}) \<union> {''PCC''} \<subseteq> accessible_regs s"
  shows "Rs \<subseteq> accessible_regs (run s t)"
proof -
  have PCC: "{''PCC''} \<subseteq> accessible_regs s"
    using assms
    by auto
  moreover have "Rs - (if a \<and> \<not>is_fetch then read_privileged_regs ISA else {}) \<subseteq> accessible_regs (run s t)"
    using assms
    by - (accessible_regsI)
  ultimately show ?thesis
    using CapIsSystemAccessEnabled_system_reg_access[OF assms(1,2) _ PCC, THEN system_reg_access_accessible_regs, of Rs]
    by (cases "a \<and> \<not>is_fetch") auto
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
  assumes "Run system_access_disabled t a" and "sysreg_trace_assms s t"
    and "Rs - (if a \<or> is_fetch then {} else read_privileged_regs ISA) \<union> {''PCC''} \<subseteq> accessible_regs s"
  shows "Rs \<subseteq> accessible_regs (run s t)"
proof (cases "a \<or> is_fetch")
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
    using assms False
    by - accessible_regsI
qed

lemmas system_access_disabled_accessible_regs_or_ex[accessible_regsE] =
  system_access_disabled_accessible_regs[THEN disjI1]

lemma system_access_disabled_system_reg_access[derivable_capsE]:
  assumes "Run system_access_disabled t a" and "sysreg_trace_assms s t" and "\<not>a"
    and "{''PCC''} \<subseteq> accessible_regs s" and "\<not>is_fetch"
  shows "system_reg_access (run s t)"
  using assms(1-4)
  by (auto elim!: Run_bindE Run_and_boolM_E CapIsSystemAccessEnabled_system_reg_access[OF _ _ _ _ assms(5)]
           dest: Halted_False)

lemmas system_access_disabled_system_reg_access_or_ex[derivable_capsE] =
  system_access_disabled_system_reg_access[THEN disjI1]

lemma HaveEL_True[simp]: "HaveEL el = return True"
  using EL_exhaust_disj[of el]
  by (auto simp: HaveEL_def CFG_ID_AA64PFR0_EL1_EL2_def CFG_ID_AA64PFR0_EL1_EL3_def)

(*lemma Run_try_catch_leftI: "Run m t a \<Longrightarrow> Run (try_catch m h) t a"
  apply (induction m t "Done a :: ('a, 'b, 'c) monad" rule: Traces.induct)
   apply simp
  apply (erule T.cases; auto)
  done

lemma Run_liftR_iff[simp]: "Run (liftR m) t a \<longleftrightarrow> Run m t a"
  unfolding liftR_def
  apply auto
   apply (elim Run_try_catchE)
    apply (auto intro: Run_try_catch_leftI)
  done*)

lemma ELUsingAArch32_False[simp]:
  "Run (ELUsingAArch32 el) t True \<longleftrightarrow> False"
  unfolding ELUsingAArch32_def ELStateUsingAArch32_def ELStateUsingAArch32K_def
  by (auto elim!: Run_bindE)

(*lemma CHCR_EL2_SETTAG:
  assumes t: "Run (read_reg CHCR_EL2_ref) t a" "sysreg_trace_assms t"
    and no_asr: "\<not>no_system_reg_access"
  shows "a !! 0"
  using t
  by (elim Run_read_regE, simp add: sysreg_trace_assms_def CHCR_EL2_ref_def) (auto simp: no_asr)*)

lemma CSCR_EL3_SETTAG:
  assumes t: "Run (read_reg CSCR_EL3_ref) t a" "sysreg_trace_assms s t"
    and no_asr: "\<not>no_system_reg_access"
  shows "a !! 0"
  using t
  by (elim Run_read_regE, simp add: CSCR_EL3_ref_def) (auto simp: no_asr)

lemma ProcState_of_regval_eq_Some_iff[simp]:
  "ProcState_of_regval rv = Some ps \<longleftrightarrow> rv = Regval_ProcState ps"
  by (cases rv) auto

lemma not_EL3_if_system_reg_access:
  assumes t: "Run (read_reg PSTATE_ref) t ps" "sysreg_trace_assms s t"
    and no_asr: "\<not>no_system_reg_access"
  shows "ProcState_EL ps \<in> {EL0, EL1, EL2}"
  using t EL_exhaust_disj[of "ProcState_EL ps"]
  by (elim Run_read_regE, simp add: PSTATE_ref_def) (auto simp: no_asr)

lemma word1_eq_1_iff[simp]: "(w = (1 :: 1 word)) \<longleftrightarrow> w !! 0"
  by (cases w rule: exhaustive_1_word) auto

lemma IsTagSettingDisabled_not_False:
  assumes t: "sysreg_trace_assms s t" and no_asr: "\<not>no_system_reg_access"
  shows "Run (IsTagSettingDisabled ()) t False \<longleftrightarrow> False"
  using t
  unfolding IsTagSettingDisabled_def Let_def
  \<comment> \<open>Requires @{path IsTagSettingDisabled_EL.patch}\<close>
  by (auto elim!: Run_bindE Run_and_boolM_E split: if_splits simp: nth_ucast
           dest!: CSCR_EL3_SETTAG[OF _ _ no_asr] not_EL3_if_system_reg_access[OF _ _ no_asr])

text \<open>Tag setting instructions check whether tag setting is disabled, but also whether system access
  is enabled; provide elimination rules for the @{term and_boolM} combinations of those checks that
  appear in the instructions, reflecting our assumption that either system access or tag setting is
  disabled.\<close>

abbreviation
  "and_SystemAccessEnabled_TagSettingEnabled \<equiv>
     and_boolM (CapIsSystemAccessEnabled ())
               (IsTagSettingDisabled () \<bind> (\<lambda>w__2. return (\<not> w__2)))"

lemma and_SystemAccessEnabled_TagSettingEnabledE:
  assumes "Run and_SystemAccessEnabled_TagSettingEnabled t a"
    and "\<exists>s. sysreg_trace_assms s t \<and> {''PCC''} \<subseteq> accessible_regs s"
  obtains "\<not>a"
proof -
  from assms have "\<not>no_system_reg_access" if "a"
    using that
    by (elim Run_and_boolM_E CapIsSystemAccessEnabled_no_system_reg_access_cases; auto)
  from IsTagSettingDisabled_not_False[OF _ this] assms
  show thesis
    by (auto elim!: Run_and_boolM_E intro: that)
qed

abbreviation
  "and_exp_SystemAccessEnabled_TagSettingEnabled m \<equiv>
     and_boolM (and_boolM m (CapIsSystemAccessEnabled ()))
               (IsTagSettingDisabled () \<bind> (\<lambda>w__2. return (\<not> w__2)))"

lemma and_exp_SystemAccessEnabled_TagSettingEnabledE:
  assumes "Run (and_exp_SystemAccessEnabled_TagSettingEnabled m) t a"
    and "\<exists>s. sysreg_trace_assms s t \<and> {''PCC''} \<subseteq> accessible_regs s"
    and "runs_no_reg_writes_to {''PCC''} m"
  obtains "\<not>a"
  using assms accessible_regs_no_writes_run_subset[where m = m and Rs = "{''PCC''}"]
  unfolding and_boolM_assoc
  by (elim and_SystemAccessEnabled_TagSettingEnabledE Run_and_boolM_E) auto

lemma BranchTaken_or_PCC_accessible:
  assumes "Run (read_reg BranchTaken_ref) t b"
    and "(\<forall>s'. sysreg_trace_assms s' t \<longrightarrow> b \<or> {''PCC''} \<subseteq> accessible_regs s') \<longrightarrow> {''PCC''} \<subseteq> accessible_regs s"
    and "\<not>is_fetch"
  shows "{''PCC''} \<subseteq> accessible_regs s"
  using assms(1,2)
  by (auto elim!: Run_read_regE simp: BranchTaken_ref_def accessible_regs_def split: register_value.splits; simp add: assms(3))

end

locale Morello_Load_Cap_Assms = Morello_ISA +
  fixes enabled :: "(Capability, register_value) axiom_state \<Rightarrow> register_value event \<Rightarrow> bool"
    and load_auths :: "load_auth set" and load_caps_permitted :: "bool"
    and no_system_reg_access :: bool
    and is_in_c64 :: bool
    and invoked_indirect_caps :: "Capability set"
begin

abbreviation loads_via_cap_reg :: "int \<Rightarrow> bool" where
  "loads_via_cap_reg n \<equiv> cap_reg_in_load_auths is_in_c64 n load_auths"

abbreviation loads_via_ddc :: "bool" where
  "loads_via_ddc \<equiv> ddc_in_load_auths is_in_c64 load_auths"

abbreviation loads_via_pcc :: "bool" where
  "loads_via_pcc \<equiv> pcc_in_load_auths load_auths"

fun load_cap_ev_assms :: "register_value event \<Rightarrow> bool" where
  "load_cap_ev_assms (E_read_reg r v) =
     ((r = ''PCC'' \<and> loads_via_pcc \<longrightarrow> (\<forall>c \<in> caps_of_regval v. load_caps_permitted \<longleftrightarrow> cap_permits CAP_PERM_LOAD_CAP c)) \<and>
      (\<forall>n c. r \<in> R_name n \<and> loads_via_cap_reg n \<and> c \<in> caps_of_regval v \<longrightarrow> (load_caps_permitted \<longleftrightarrow> cap_permits CAP_PERM_LOAD_CAP c)) \<and>
      (\<forall>c. r \<in> DDC_names \<and> loads_via_ddc \<and> c \<in> caps_of_regval v \<longrightarrow> (load_caps_permitted \<longleftrightarrow> cap_permits CAP_PERM_LOAD_CAP c)) \<and>
      (\<forall>ps. r = ''PSTATE'' \<and> v = Regval_ProcState ps \<longrightarrow> (is_in_c64 \<longleftrightarrow> (ProcState_C64 ps = 1))) \<and>
      (\<forall>w. r = ''DCZID_EL0'' \<and> v = Regval_bitvector_32_dec w \<longrightarrow> (ucast w :: 4 word) = 4) \<comment> \<open>Morello cache line size\<close>)"
(*| "load_cap_ev_assms (E_write_reg r v) =
      (\<forall>i. r = ''__ThisInstrAbstract'' \<and> v = Regval_instr_ast i \<longrightarrow> instr_load_auths i \<subseteq> load_auths)"*)
| "load_cap_ev_assms _ = True"

definition load_cap_trace_assms :: "register_value trace \<Rightarrow> bool" where
  "load_cap_trace_assms t \<equiv> (\<forall>e \<in> set t. load_cap_ev_assms e)"

lemma load_cap_trace_assms_append[simp]:
  "load_cap_trace_assms (t1 @ t2) \<longleftrightarrow> load_cap_trace_assms t1 \<and> load_cap_trace_assms t2"
  by (auto simp: load_cap_trace_assms_def)

sublocale Morello_Cap_Axiom_Automaton
  where use_mem_caps = "invoked_indirect_caps = {} \<and> load_caps_permitted" ..

(* Assume fixed cache line size for Morello *)
lemma DCZID_EL0_assm:
  assumes "Run (read_reg DCZID_EL0_ref) t a" and "load_cap_trace_assms t"
  shows "uint (a AND mask 4) = 4"
proof -
  have "uint (a AND mask 4) = uint (ucast a :: 4 word)"
    by auto
  also have "\<dots> = 4"
    using assms
    by (elim Run_read_regE) (auto simp: DCZID_EL0_ref_def load_cap_trace_assms_def)
  finally show ?thesis .
qed

definition VA_from_load_auth :: "VirtualAddress \<Rightarrow> bool" where
  "VA_from_load_auth va \<equiv>
     (if VirtualAddress_vatype va = VA_Bits64 then loads_via_ddc
      else ((\<exists>r n. r \<in> R_name n \<and> loads_via_cap_reg n \<and> load_cap_ev_assms (E_read_reg r (Regval_bitvector_129_dec (VirtualAddress_base va))))
            \<or> (loads_via_pcc \<and> load_cap_ev_assms (E_read_reg ''PCC'' (Regval_bitvector_129_dec (VirtualAddress_base va))))))"

lemma CapSquashPostLoadCap_cases:
  assumes "Run (CapSquashPostLoadCap c base) t c'"
  obtains "c' = c"
  | "c' = CapWithTagClear c"
  | "c' = CapClearPerms c mutable_perms" and "\<not>CapIsSealed c"
  using assms
  by (auto simp: CapSquashPostLoadCap_def elim!: Run_bindE split: if_splits)

lemma Run_CapSquashPostLoadCap_use_mem_caps:
  assumes t: "Run (CapSquashPostLoadCap c base) t c'" "load_cap_trace_assms t"
    and base: "VA_from_load_auth base"
    and c': "CapIsTagSet c'"
  shows "load_caps_permitted"
proof (cases "VirtualAddress_vatype base")
  case VA_Bits64
  then show ?thesis
    using t c' base
    unfolding CapSquashPostLoadCap_def DDC_read_def Let_def bind_assoc
    by (elim Run_bindE Run_if_ELs_cases Run_ifE Run_read_regE;
        simp add: DDC_names_def VA_from_load_auth_def register_defs load_cap_trace_assms_def;
        auto)
next
  case VA_Capability
  then show ?thesis
    using t c' base
    unfolding CapSquashPostLoadCap_def VAToCapability_def Let_def
    by (elim Run_bindE Run_ifE;
        simp add: VA_from_load_auth_def VAIsBits64_def;
        auto)
qed

lemma (in Cap_Axiom_Automaton) not_tagged_derivable:
  assumes "\<not>is_tagged_method CC c"
  shows "c \<in> derivable_caps s"
  using assms
  by (auto simp: derivable_caps_def)

lemma CapSquashPostLoadCap_from_load_auth_reg_derivable_caps[derivable_capsE]:
  assumes "Run (CapSquashPostLoadCap c base) t c'" "load_cap_trace_assms t"
    and "c \<in> derivable_mem_caps s"
    and "VA_from_load_auth base"
    and "CapIsTagSet c' \<longrightarrow> invoked_indirect_caps = {}"
  shows "c' \<in> derivable_caps s"
proof -
  have "CapIsTagSet c' \<longrightarrow> c \<in> derivable_caps s"
    using derivable_mem_caps_derivable_caps[OF assms(3)]
    using Run_CapSquashPostLoadCap_use_mem_caps[OF assms(1,2,4)]
    using assms(5)
    by auto
  with assms(1) show "c' \<in> derivable_caps s"
    by (cases rule: CapSquashPostLoadCap_cases)
       (auto intro: clear_perm_derivable_caps not_tagged_derivable)
qed

lemma Run_IsInC64_E:
  assumes "Run (IsInC64 u) t a" and "load_cap_trace_assms t"
  obtains "a = is_in_c64"
  using assms
  by (auto simp: IsInC64_def load_cap_trace_assms_def PSTATE_ref_def
           elim!: Run_read_regE ProcState_of_regval.elims)

lemma CSP_read_load_cap_ev_assms:
  assumes "Run (CSP_read u) t c" and "load_cap_trace_assms t"
  obtains r where "r \<in> R_name 31" and "load_cap_ev_assms (E_read_reg r (Regval_bitvector_129_dec c))"
  using assms
  unfolding CSP_read_def Let_def load_cap_trace_assms_def
  by (elim Run_bindE Run_if_ELs_cases Run_ifE Run_read_regE)
     (auto simp add: R_name_def register_defs simp del: load_cap_ev_assms.simps)

lemma C_read_load_cap_ev_assms:
  assumes "Run (C_read n) t c" and "load_cap_trace_assms t" and "n \<noteq> 31"
  obtains r where "r \<in> R_name n" and "load_cap_ev_assms (E_read_reg r (Regval_bitvector_129_dec c))"
  using assms
  unfolding C_read_def R_read_def Let_def load_cap_trace_assms_def
  by (elim Run_bindE Run_ifE Run_read_regE)
     (auto simp add: R_name_def register_defs simp del: load_cap_ev_assms.simps)

lemma BaseReg_read_VA_from_load_auth[derivable_capsE]:
  assumes t: "Run (BaseReg_read n prefetch) t va" "load_cap_trace_assms t"
    and n: "BaseRegAuth n \<in> load_auths"
  shows "VA_from_load_auth va"
proof (cases is_in_c64)
  case True
  have *: "Run (IsInC64 ()) t False \<longleftrightarrow> False" if "load_cap_trace_assms t" for t
    using True that
    by (auto elim: Run_IsInC64_E)
  have "loads_via_cap_reg n"
    using True n
    unfolding cap_reg_in_load_auths_def
    by auto
  then show ?thesis
    using t
    unfolding BaseReg_read_def VA_from_load_auth_def
    by (elim Run_bindE Run_ifE CSP_read_load_cap_ev_assms C_read_load_cap_ev_assms)
       (auto simp add: * simp del: load_cap_ev_assms.simps)
next
  case False
  have *: "Run (IsInC64 ()) t True \<longleftrightarrow> False" if "load_cap_trace_assms t" for t
    using False that
    by (auto elim: Run_IsInC64_E)
  have "loads_via_ddc"
    using False n
    unfolding ddc_in_load_auths_def
    by auto
  then show ?thesis
    using t
    unfolding BaseReg_read_def VA_from_load_auth_def
    by (elim Run_bindE Run_ifE) (auto simp add: *)
qed

lemma BaseReg_read__1_VA_from_load_auth[derivable_capsE]:
  assumes "Run (BaseReg_read__1 n) t va" "load_cap_trace_assms t"
    and "BaseRegAuth n \<in> load_auths"
  shows "VA_from_load_auth va"
  using assms
  unfolding BaseReg_read__1_def
  by (elim BaseReg_read_VA_from_load_auth)

lemma AltBaseReg_read_VA_from_load_auth[derivable_capsE]:
  assumes t: "Run (AltBaseReg_read n prefetch) t va" "load_cap_trace_assms t"
    and n: "AltBaseRegAuth n \<in> load_auths"
  shows "VA_from_load_auth va"
proof (cases is_in_c64)
  case True
  have *: "Run (IsInC64 ()) t False \<longleftrightarrow> False" if "load_cap_trace_assms t" for t
    using True that
    by (auto elim: Run_IsInC64_E)
  have "loads_via_ddc"
    using True n
    unfolding ddc_in_load_auths_def
    by auto
  then show ?thesis
    using t
    unfolding AltBaseReg_read_def VA_from_load_auth_def
    by (elim Run_bindE Run_ifE) (auto simp add: *)
next
  case False
  have *: "Run (IsInC64 ()) t True \<longleftrightarrow> False" if "load_cap_trace_assms t" for t
    using False that
    by (auto elim: Run_IsInC64_E)
  have "loads_via_cap_reg n"
    using False n
    unfolding cap_reg_in_load_auths_def
    by auto
  then show ?thesis
    using t
    unfolding AltBaseReg_read_def VA_from_load_auth_def
    by (elim Run_bindE Run_ifE CSP_read_load_cap_ev_assms C_read_load_cap_ev_assms)
       (auto simp add: * simp del: load_cap_ev_assms.simps)
qed

lemma AltBaseReg_read__1_VA_from_load_auth[derivable_capsE]:
  assumes "Run (AltBaseReg_read__1 n) t va" "load_cap_trace_assms t"
    and "AltBaseRegAuth n \<in> load_auths"
  shows "VA_from_load_auth va"
  using assms
  unfolding AltBaseReg_read__1_def
  by (elim AltBaseReg_read_VA_from_load_auth)

lemma VAFromBits64_VA_from_load_auth[derivable_capsE]:
  assumes "Run (VAFromBits64 addr) t va"
    and "loads_via_ddc"
  shows "VA_from_load_auth va"
  using assms
  unfolding VAFromBits64_def VA_from_load_auth_def
  by auto

definition
  "load_auth_reg_cap c \<equiv>
     ((\<exists>r n. r \<in> R_name n \<and> loads_via_cap_reg n \<and> load_cap_ev_assms (E_read_reg r (Regval_bitvector_129_dec c)))
      \<or> (loads_via_pcc \<and> load_cap_ev_assms (E_read_reg ''PCC'' (Regval_bitvector_129_dec c))))"

declare Run_ifE[where thesis = "load_auth_reg_cap c" and a = c for c, derivable_caps_combinators]
declare Run_bindE[where thesis = "load_auth_reg_cap c" and a = c for c, derivable_caps_combinators]

lemma VAFromCapability_VA_from_load_auth[derivable_capsE]:
  assumes "Run (VAFromCapability c) t va"
    and "load_auth_reg_cap c"
  shows "VA_from_load_auth va"
  using assms
  unfolding VAFromCapability_def load_auth_reg_cap_def VA_from_load_auth_def
  by (elim Run_bindE Run_letE Run_returnE) auto

lemma C_read_load_auth_reg_cap[derivable_capsE]:
  assumes "Run (C_read n) t c" and "load_cap_trace_assms t"
    and "loads_via_cap_reg n" and "n \<noteq> 31"
  shows "load_auth_reg_cap c"
  using assms
  by (elim C_read_load_cap_ev_assms) (auto simp: load_auth_reg_cap_def)

lemma CSP_read_load_auth_reg_cap[derivable_capsE]:
  assumes "Run (CSP_read u) t c" and "load_cap_trace_assms t"
    and "loads_via_cap_reg 31"
  shows "load_auth_reg_cap c"
  using assms
  by (elim CSP_read_load_cap_ev_assms) (auto simp: load_auth_reg_cap_def)

lemma CSP_or_C_read_load_auth_reg_cap[derivable_capsE]:
  assumes "Run (if n = 31 then CSP_read u else C_read n) t c" and "load_cap_trace_assms t"
    and "loads_via_cap_reg n"
  shows "load_auth_reg_cap c"
  using assms
  by (auto split: if_splits elim: derivable_capsE)

lemma aligned_CSP_or_C_read_load_auth_reg_cap[derivable_capsE]:
  assumes "Run (if n = 31 then CheckSPAlignment u \<then> CSP_read u' else C_read n) t c" and "load_cap_trace_assms t"
    and "loads_via_cap_reg n"
  shows "load_auth_reg_cap c"
  using assms
  by (auto split: if_splits elim: derivable_capsE elim!: Run_bindE)

lemma RegAuth_loads_via_cap_regI[derivable_capsI, intro, simp]:
  "RegAuth n \<in> load_auths \<Longrightarrow> loads_via_cap_reg n"
  by (auto simp: cap_reg_in_load_auths_def)

lemma load_auth_reg_cap_CapUnseal_iff[simp]:
  "load_auth_reg_cap (CapUnseal c) \<longleftrightarrow> load_auth_reg_cap c"
  unfolding load_auth_reg_cap_def load_cap_ev_assms.simps
  by (simp add: CapCheckPermissions_def CapGetPermissions_CapUnseal_eq)

lemma load_auth_reg_cap_if_CapUnsealI[intro, derivable_capsI]:
  assumes "load_auth_reg_cap c"
  shows "load_auth_reg_cap (if unseal then CapUnseal c else c)"
  using assms
  by auto

lemma PCC_load_auth_reg_cap[derivable_capsE]:
  assumes "Run (read_reg PCC_ref) t c" and "load_cap_trace_assms t"
    and "loads_via_pcc"
  shows "load_auth_reg_cap c"
  using assms
  unfolding load_cap_trace_assms_def load_auth_reg_cap_def
  by (elim Run_read_regE; simp) (auto simp: PCC_ref_def)

lemma loads_via_pccI[derivable_capsI, intro, simp]:
  assumes "PCCAuth \<in> load_auths"
  shows "loads_via_pcc"
  using assms
  by (auto simp: pcc_in_load_auths_def)

definition load_instr_exp_assms :: "(register_value, 'a, 'e) monad \<Rightarrow> bool" where
  "load_instr_exp_assms m \<equiv> load_auths = exp_load_auths m"

lemma load_instr_exp_assms_write_ThisInstrAbstract_iff:
  "load_instr_exp_assms (write_reg ThisInstrAbstract_ref instr \<bind> f)
   \<longleftrightarrow> load_auths = instr_load_auths instr"
  by (auto simp: load_instr_exp_assms_def exp_load_auths_def)

end

locale Morello_Cap_Invocation_Assms = Morello_ISA +
  fixes enabled :: "(Capability, register_value) axiom_state \<Rightarrow> register_value event \<Rightarrow> bool"
    and use_mem_caps :: "bool"
    and invoked_caps :: "Capability set" and invoked_regs :: "int set"
    and invoked_indirect_caps :: "Capability set" and invoked_indirect_regs :: "int set"
    and is_indirect_branch :: bool
begin

fun invocation_ev_assms :: "register_value event \<Rightarrow> bool" where
  "invocation_ev_assms (E_read_reg r v) =
    ((\<forall>n c. r \<in> R_name n \<and> n \<in> invoked_regs \<and> c \<in> caps_of_regval v \<and> CapIsTagSet c \<and> CapIsSealed c \<longrightarrow> branch_caps (CapUnseal c) \<subseteq> invoked_caps) \<and>
     (\<forall>n c. r \<in> R_name n \<and> n \<in> invoked_indirect_regs \<and> c \<in> caps_of_regval v \<and> CapIsTagSet c \<and> is_indirect_sentry c \<longrightarrow> CapUnseal c \<in> invoked_indirect_caps))"
| "invocation_ev_assms (E_read_memt rk addr sz (bytes, tag)) =
    (is_indirect_branch \<longrightarrow> (\<forall>c. cap_of_mem_bytes bytes tag = Some c \<and> CapIsTagSet c \<longrightarrow> mem_branch_caps c \<subseteq> invoked_caps))"
| "invocation_ev_assms _ = True"

definition invocation_trace_assms :: "register_value trace \<Rightarrow> bool" where
  "invocation_trace_assms t \<equiv> (\<forall>e \<in> set t. invocation_ev_assms e)"

lemma invocation_trace_assms_append[simp]:
  "invocation_trace_assms (t1 @ t2) \<longleftrightarrow> invocation_trace_assms t1 \<and> invocation_trace_assms t2"
  by (auto simp: invocation_trace_assms_def)

sublocale Morello_Cap_Axiom_Automaton ..

definition invocation_instr_exp_assms :: "(register_value, 'a, 'e) monad \<Rightarrow> bool" where
  "invocation_instr_exp_assms m \<equiv>
     invoked_regs = exp_invokes_regs m \<and>
     invoked_indirect_regs = exp_invokes_indirect_regs m \<and>
     (exp_invokes_indirect_regs m = {} \<longrightarrow> invoked_indirect_caps = {}) \<and>
     is_indirect_branch = exp_is_indirect_branch m"

lemma invocation_instr_exp_assms_write_ThisInstrAbstract_iff:
  "invocation_instr_exp_assms (write_reg ThisInstrAbstract_ref instr \<bind> f)
   \<longleftrightarrow> (invoked_regs = instr_invokes_regs instr
     \<and> invoked_indirect_regs = instr_invokes_indirect_regs instr
     \<and> (instr_invokes_indirect_regs instr = {} \<longrightarrow> invoked_indirect_caps = {})
     \<and> is_indirect_branch = instr_is_indirect_branch instr)"
  by (auto simp: invocation_instr_exp_assms_def exp_invokes_regs_def exp_invokes_indirect_regs_def)

lemma C_read_branch_caps_invoked_caps[derivable_capsE]:
  assumes "Run (C_read n) t c" and "invocation_trace_assms t"
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
    by (auto simp: invocation_trace_assms_def)
qed

lemma C_read_invoked_caps[derivable_capsE]:
  assumes "Run (C_read n) t c" and "invocation_trace_assms t"
    and "n \<in> invoked_regs"
    and "CapIsTagSet c" and "CapIsSealed c"
  shows "CapUnseal c \<in> invoked_caps"
  using C_read_branch_caps_invoked_caps[OF assms]
  by (auto simp: branch_caps_def)

lemma C_read_unseal_invoked_indirect_caps[derivable_capsE]:
  assumes "Run (C_read n) t c" and "invocation_trace_assms t"
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
    by (auto simp: is_indirect_sentry_def invocation_trace_assms_def)
qed

lemma CSP_read_invoked_indirect_caps[derivable_capsE]:
  assumes "Run (CSP_read u) t c" and "invocation_trace_assms t"
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
    by (induction t)
       (auto split: if_splits simp: is_indirect_sentry_def CapIsSealed_def invocation_trace_assms_def)
qed

lemma CSP_or_C_read_unseal_invoked_indirect_caps[derivable_capsE]:
  assumes "Run (if n = 31 then CSP_read () else C_read n) t c" and "invocation_trace_assms t"
    and "n \<in> invoked_indirect_regs"
    and "CapIsTagSet c"
    and "CapGetObjectType c \<in> {CAP_SEAL_TYPE_LB, CAP_SEAL_TYPE_LPB}"
  shows "CapUnseal c \<in> invoked_indirect_caps"
  using assms
  by (auto elim!: derivable_capsE split: if_splits)

declare Run_ifE[where thesis = "CapUnseal c \<in> invoked_indirect_caps" and a = c for c, derivable_caps_combinators]
declare Run_bindE[where thesis = "CapUnseal c \<in> invoked_indirect_caps" and a = c for c, derivable_caps_combinators]

lemma accessed_mem_cap_of_trace_sealed_invoked_caps:
  assumes "accessed_mem_cap_of_trace_if_tagged c t"
    and "invocation_trace_assms t"
    and "CapIsTagSet c" and "CapGetObjectType c = CAP_SEAL_TYPE_RB"
    and "is_indirect_branch"
  shows "branch_caps (CapUnseal c) \<subseteq> invoked_caps"
  using assms(1-4)
  by (induction t)
     (auto simp: accessed_mem_cap_of_trace_if_tagged_def mem_branch_caps_def invocation_trace_assms_def
           intro: assms(5))

lemmas tagged_mem_primitives_sealed_invoked_caps[derivable_capsE] =
  tagged_mem_primitives_accessed_mem_caps[THEN accessed_mem_cap_of_trace_sealed_invoked_caps]

lemma accessed_mem_cap_of_trace_invoked_caps:
  assumes "accessed_mem_cap_of_trace_if_tagged c t"
    and "invocation_trace_assms t"
    and "CapIsTagSet c"
    and "is_indirect_branch"
  shows "mem_branch_caps c \<subseteq> invoked_caps"
  using assms(1-3)
  by (induction t)
     (auto simp: accessed_mem_cap_of_trace_if_tagged_def invocation_trace_assms_def intro: assms(4))

lemmas tagged_mem_primitives_invoked_caps[derivable_capsE] =
  tagged_mem_primitives_accessed_mem_caps[THEN accessed_mem_cap_of_trace_invoked_caps]

end

locale Morello_Axiom_Assms = Morello_ISA +
  fixes enabled :: "(Capability, register_value) axiom_state \<Rightarrow> register_value event \<Rightarrow> bool"
    and ex_traces :: bool
    and invoked_caps :: "Capability set" and invoked_regs :: "int set"
    and invoked_indirect_caps :: "Capability set" and invoked_indirect_regs :: "int set"
    and load_auths :: "load_auth set" and load_caps_permitted :: "bool" and is_fetch :: "bool"
    and is_indirect_branch :: bool
    and no_system_reg_access :: bool
    and is_in_c64 :: bool
    and translation_assms :: "register_value event \<Rightarrow> bool"
begin

sublocale Morello_Load_Cap_Assms ..
sublocale Morello_Cap_Invocation_Assms
 where use_mem_caps = "invoked_indirect_caps = {} \<and> load_caps_permitted" ..

fun ev_assms :: "(Capability, register_value) axiom_state \<Rightarrow> register_value event \<Rightarrow> bool" where
  "ev_assms s (E_read_reg r v) =
    (invocation_ev_assms (E_read_reg r v) \<and>
     load_cap_ev_assms (E_read_reg r v) \<and>
     sysreg_ev_assms s (E_read_reg r v) \<and>
     translation_assms (E_read_reg r v))"
| "ev_assms s (E_read_memt rk addr sz data) =
    (invocation_ev_assms (E_read_memt rk addr sz data) \<and> translation_assms (E_read_memt rk addr sz data))"
| "ev_assms s (E_choose descr rv) =
    (unknown_ev_assms (E_choose descr rv) \<and> translation_assms (E_choose descr rv))"
| "ev_assms s e = translation_assms e"

end

locale Morello_Axiom_Automaton =
  Morello_Axiom_Assms +
  Cap_Axiom_Assm_Automaton where CC = CC and ISA = ISA and initial_caps = UNKNOWN_caps
    and cap_invariant = cap_invariant and ev_assms = ev_assms
    and is_isa_exception = is_isa_exception
    and use_mem_caps = "invoked_indirect_caps = {} \<and> load_caps_permitted"
begin

(* sublocale Morello_Cap_Axiom_Automaton .. *)

lemma load_cap_ev_assmsI[intro, simp]:
  "ev_assms s e \<Longrightarrow> load_cap_ev_assms e"
  by (cases e; simp; blast)

lemma load_cap_trace_assmsI[intro, simp]:
  "trace_assms s t \<Longrightarrow> load_cap_trace_assms t"
  by (induction t arbitrary: s) (auto simp: load_cap_trace_assms_def)

lemmas inv_load_cap_trace_assms[simp, derivable_capsE, accessible_regsE] =
  inv_trace_assms_trace_assms[THEN load_cap_trace_assmsI]

lemma invocation_ev_assmsI[intro, simp]:
  "ev_assms s e \<Longrightarrow> invocation_ev_assms e"
  by (cases e; simp; blast)

lemma trace_assms_invocation_trace_assms[intro, simp]:
  "trace_assms s t \<Longrightarrow> invocation_trace_assms t"
  by (induction t arbitrary: s) (auto simp: invocation_trace_assms_def)

lemmas inv_invocation_trace_assms[simp, derivable_capsE, accessible_regsE] =
  inv_trace_assms_trace_assms[THEN trace_assms_invocation_trace_assms]

lemma sysreg_ev_assmsI[intro, simp, derivable_capsI]:
  "ev_assms s e \<Longrightarrow> sysreg_ev_assms s e"
  by (cases "(s, e)" rule: sysreg_ev_assms.cases) auto

lemma trace_assms_sysreg_trace_assms[simp, intro]:
  "trace_assms s t \<Longrightarrow> sysreg_trace_assms s t"
  by (elim holds_along_trace_imp) auto

lemmas inv_sysreg_trace_assms[simp, derivable_capsE, accessible_regsE] =
  inv_trace_assms_trace_assms[THEN trace_assms_sysreg_trace_assms]

lemmas ex_conjI = exI[where P = "\<lambda>x. P x \<and> Q x" for P Q, OF conjI]

lemmas inv_ex_sysreg_trace_assms[accessible_regsE, derivable_capsE] =
  inv_sysreg_trace_assms[THEN exI[where P = "\<lambda>s. sysreg_trace_assms s t" for t]]
  inv_sysreg_trace_assms[THEN ex_conjI[where P = "\<lambda>s. sysreg_trace_assms s t" for t]]

declare inv_sysreg_trace_assms[THEN Run_Halted_True_False, simp]

lemma unknown_ev_assmsI[intro, simp]:
  "ev_assms s e \<Longrightarrow> unknown_ev_assms e"
  by (cases e rule: unknown_ev_assms.cases; auto)

lemma trace_assms_unknown_trace_assms[intro, simp]:
  "trace_assms s t \<Longrightarrow> unknown_trace_assms t"
  by (induction t arbitrary: s) (auto simp: unknown_trace_assms_def)

lemmas inv_unknown_trace_assms[simp, derivable_capsE, accessible_regsE] =
  inv_trace_assms_trace_assms[THEN trace_assms_unknown_trace_assms]

declare datatype_splits[where P = "\<lambda>m. traces_enabled m s" for s, traces_enabled_split]

definition "instr_exp_assms m \<equiv> invocation_instr_exp_assms m \<and> load_instr_exp_assms m"

lemma instr_exp_assms_traces_enabled_ifE:
  assumes "instr_exp_assms (if c then m1 else m2)"
    and "instr_exp_assms m1 \<Longrightarrow> traces_enabled m1 s"
    and "instr_exp_assms m2 \<Longrightarrow> traces_enabled m2 s"
  shows "traces_enabled (if c then m1 else m2) s"
  using assms
  by auto

lemma instr_exp_assms_traces_enabled_letE:
  assumes "instr_exp_assms (let x = y in f x)"
    and "instr_exp_assms (f y) \<Longrightarrow> traces_enabled (f y) s"
  shows "traces_enabled (let x = y in f x) s"
  using assms
  by auto

(* For some (probably ArchEx-related) reason, __ExecuteA64 reads the PC and passes it to
   __DecodeA64 as its first argument.  However, the __DecodeA64 function we generate doesn't
   actually use the pc argument. *)
lemma DecodeA64_ignore_pc: "DecodeA64 pc opcode = DecodeA64 0 opcode"
  by (unfold DecodeA64_def, rule refl)

end

locale Morello_Instr_Axiom_Automaton = Morello_Axiom_Automaton where is_fetch = False
locale Morello_Fetch_Axiom_Automaton = Morello_Axiom_Automaton where is_fetch = True

locale Morello_Write_Cap_Automaton = Morello_ISA +
  fixes ex_traces :: bool
    and invoked_caps :: "Capability set" and invoked_regs :: "int set"
    and invoked_indirect_caps :: "Capability set" and invoked_indirect_regs :: "int set"
    and load_auths :: "load_auth set" and load_caps_permitted :: "bool" and is_fetch :: "bool"
    and no_system_reg_access :: bool
    and is_in_c64 :: bool
    and is_indirect_branch :: bool
    and translation_assms :: "register_value event \<Rightarrow> bool"
begin

sublocale Write_Cap_Automaton
  where CC = CC and ISA = ISA and initial_caps = UNKNOWN_caps and use_mem_caps = load_caps_permitted
  ..

sublocale Morello_Axiom_Assms where enabled = enabled ..

(* TODO *)
sublocale Write_Cap_Assm_Automaton
  where CC = CC and ISA = ISA and initial_caps = UNKNOWN_caps and ev_assms = ev_assms
    and is_isa_exception = is_isa_exception and wellformed_ev = wellformed_ev
    and cap_invariant = cap_invariant and use_mem_caps = load_caps_permitted ..

sublocale Morello_Axiom_Automaton where enabled = enabled ..

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
  by (auto simp: leq_cap_def CapGetPermissions_eq_leq_perms intro: leq_bounds_CapSetFlags)

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

end

locale Morello_Instr_Write_Cap_Automaton = Morello_Write_Cap_Automaton where is_fetch = False
locale Morello_Fetch_Write_Cap_Automaton = Morello_Write_Cap_Automaton where is_fetch = True
sublocale Morello_Instr_Write_Cap_Automaton \<subseteq> Morello_Instr_Axiom_Automaton where enabled = enabled ..
sublocale Morello_Fetch_Write_Cap_Automaton \<subseteq> Morello_Fetch_Axiom_Automaton where enabled = enabled ..

(* Assume stubbed out address translation for now *)
locale Morello_Mem_Axiom_Automaton =
  Morello_Fixed_Address_Translation
  (*where translate_address = translate_address
    and is_translation_event = "\<lambda>_. False"
    and translation_assms = "\<lambda>_. True"*) +
  fixes ex_traces :: bool
    and invoked_caps :: "Capability set" and invoked_regs :: "int set"
    and invoked_indirect_caps :: "Capability set" and invoked_indirect_regs :: "int set"
    and load_auths :: "load_auth set" and load_caps_permitted :: "bool" and is_fetch :: "bool"
    and no_system_reg_access :: bool
    and is_in_c64 :: bool
    and is_indirect_branch :: bool
begin

sublocale Mem_Automaton
  where CC = CC and ISA = ISA and initial_caps = UNKNOWN_caps and use_mem_caps = load_caps_permitted
  ..

sublocale Morello_Axiom_Assms
  where translate_address = "\<lambda>addr _ _. translate_address addr"
    and enabled = enabled
  ..

(*fun extra_assms :: "register_value event \<Rightarrow> bool" where
  "extra_assms (E_read_reg r v) =
    ((\<forall>n c. r \<in> R_name n \<and> n \<in> invoked_indirect_regs \<and> c \<in> caps_of_regval v \<and> CapIsTagSet c \<and> is_indirect_sentry c \<longrightarrow> CapUnseal c \<in> invoked_indirect_caps) \<and>
     (\<forall>instr. r = ''__ThisInstrAbstract'' \<and> v = Regval_instr_ast instr \<longrightarrow> instr_invokes_indirect_regs instr \<subseteq> invoked_indirect_regs) \<and>
     load_cap_ev_assms (E_read_reg r v) \<and>
     sysreg_ev_assms (E_read_reg r v))"
| "extra_assms (E_write_reg r v) = load_cap_ev_assms (E_write_reg r v)"
| "extra_assms (E_choose descr rv) = unknown_ev_assms (E_choose descr rv)"
| "extra_assms _ = True"*)

sublocale Mem_Assm_Automaton
  where CC = CC and ISA = ISA and initial_caps = UNKNOWN_caps and cap_invariant = cap_invariant
    (* and translation_assms = "\<lambda>_. True" *)
    and ev_assms = ev_assms
    and is_isa_exception = is_isa_exception and wellformed_ev = wellformed_ev
    and use_mem_caps = load_caps_permitted
proof
  fix s e
  assume "ev_assms s e"
  then show "translation_assms e"
    by (cases e) auto
qed

sublocale Morello_Axiom_Automaton
  where translate_address = "\<lambda>addr _ _. translate_address addr" and enabled = enabled
  ..

declare translation_assms_traceI[intro, simp]
declare inv_trace_assms_trace_assms[THEN translation_assms_traceI, simp]

end

locale Morello_Instr_Mem_Automaton = Morello_Mem_Axiom_Automaton where is_fetch = False
locale Morello_Fetch_Mem_Automaton = Morello_Mem_Axiom_Automaton where is_fetch = True
sublocale Morello_Instr_Mem_Automaton \<subseteq> Morello_Instr_Axiom_Automaton
  where translate_address = "\<lambda>addr _ _. translate_address addr" and enabled = enabled ..
sublocale Morello_Fetch_Mem_Automaton \<subseteq> Morello_Fetch_Axiom_Automaton
  where translate_address = "\<lambda>addr _ _. translate_address addr" and enabled = enabled ..

end
