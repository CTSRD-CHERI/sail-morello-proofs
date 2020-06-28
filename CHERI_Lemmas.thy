theory CHERI_Lemmas
  imports CHERI_Gen_Lemmas
begin

context Morello_Axiom_Automaton
begin

lemma runs_no_reg_writes_to_CapabilityAccessTrap[runs_no_reg_writes_toI, simp]:
  "runs_no_reg_writes_to Rs (CapabilityAccessTrap el)"
  by (auto simp: runs_no_reg_writes_to_def)

lemma runs_no_reg_writes_to_CheckCapabilitiesTrap[runs_no_reg_writes_toI, simp]:
  "Rs \<subseteq> {''PCC'', ''_R29''} \<Longrightarrow> runs_no_reg_writes_to Rs (CheckCapabilitiesTrap u)"
  unfolding CheckCapabilitiesTrap_def
  by (no_reg_writes_toI)

lemma runs_no_reg_writes_to_CheckCapabilitiesEnabled[runs_no_reg_writes_toI, simp]:
  "Rs \<subseteq> {''PCC'', ''_R29''} \<Longrightarrow> runs_no_reg_writes_to Rs (CheckCapabilitiesEnabled u)"
  unfolding CheckCapabilitiesEnabled_def
  by (no_reg_writes_toI)

lemma runs_no_reg_writes_to_CheckFPAdvSIMDEnabled64[runs_no_reg_writes_toI, simp]:
  "Rs \<subseteq> {''PCC'', ''_R29''} \<Longrightarrow> runs_no_reg_writes_to Rs (CheckFPAdvSIMDEnabled64 u)"
  unfolding CheckFPAdvSIMDEnabled64_def
  sorry

lemma runs_no_reg_writes_to_AltBaseReg_read[runs_no_reg_writes_toI, simp]:
  "Rs \<subseteq> {''PCC'', ''_R29''} \<Longrightarrow> runs_no_reg_writes_to Rs (AltBaseReg_read n is_prefetch)"
  sorry

lemma runs_no_reg_writes_to_AltBaseReg_read__1[runs_no_reg_writes_toI, simp]:
  "Rs \<subseteq> {''PCC'', ''_R29''} \<Longrightarrow> runs_no_reg_writes_to Rs (AltBaseReg_read__1 n)"
  by (auto simp: AltBaseReg_read__1_def)

lemma runs_no_reg_writes_to_BaseReg_read[runs_no_reg_writes_toI, simp]:
  "Rs \<subseteq> {''PCC'', ''_R29''} \<Longrightarrow> runs_no_reg_writes_to Rs (BaseReg_read n is_prefetch)"
  sorry

lemma runs_no_reg_writes_to_BaseReg_read__1[runs_no_reg_writes_toI, simp]:
  "Rs \<subseteq> {''PCC'', ''_R29''} \<Longrightarrow> runs_no_reg_writes_to Rs (BaseReg_read__1 n)"
  by (auto simp: BaseReg_read__1_def)

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

lemma traces_enabled_write_memt:
  fixes data :: "128 word"
  assumes "paccess_enabled s Store (unat paddr) 16 (mem_bytes_of_word data) tag"
    and "tag = B0 \<or> tag = B1"
    and "tag \<noteq> B0 \<Longrightarrow> Capability_of_tag_word (bitU_nonzero tag) data \<in> derivable_caps s"
  shows "traces_enabled (write_memt BC_mword BC_mword wk paddr 16 data tag) s"
  using assms
  unfolding write_memt_def
  by (auto intro!: traces_enabled_Write_memt non_cap_expI[THEN non_cap_exp_traces_enabledI]
           split: option.splits simp: legal_store_def length_mem_bytes_of_word)

lemma traces_enabled_WriteTaggedMem_single[traces_enabledI]:
  fixes tag :: "1 word" and data :: "128 word"
  assumes "paccess_enabled s Store (unat (FullAddress_address (AddressDescriptor_paddress desc))) 16 (mem_bytes_of_word data) (bitU_of_bool (tag !! 0))"
    and "Capability_of_tag_word (tag !! 0) data \<in> derivable_caps s"
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
    and "Capability_of_tag_word (tags !! 0) (ucast data) \<in> derivable_caps s"
    and "Capability_of_tag_word (tags !! 1) (Word.slice 128 data) \<in> derivable_caps s"
  shows "traces_enabled (WriteTaggedMem desc 32 accdesc tags data) s"
  using assms
  unfolding WriteTaggedMem_def
  by (cases "tags !! 0"; cases "tags !! 1")
     (auto intro!: traces_enabled_write_memt traces_enabled_bind non_cap_expI[THEN non_cap_exp_traces_enabledI]
           simp: run_write_memt)

lemma traces_enabled_WriteTaggedMem[traces_enabledI]:
  fixes tags :: "'t::len word" and data :: "'d::len word"
  assumes "paccess_enabled s Store (unat (FullAddress_address (AddressDescriptor_paddress desc))) 16 (mem_bytes_of_word (ucast data :: 128 word)) (bitU_of_bool (tags !! 0))"
    and "Capability_of_tag_word (tags !! 0) (ucast data) \<in> derivable_caps s"
    and "sz = 32 \<Longrightarrow> paccess_enabled s Store (unat (FullAddress_address (AddressDescriptor_paddress desc)) + 16) 16 (mem_bytes_of_word (Word.slice 128 data :: 128 word)) (bitU_of_bool (tags !! 1))"
    and "sz = 32 \<Longrightarrow> Capability_of_tag_word (tags !! 1) (Word.slice 128 data) \<in> derivable_caps s"
    and "sz = 16 \<or> sz = 32"
    and "LENGTH('t) = nat sz div 16" and "LENGTH('d) = 8 * nat sz"
  shows "traces_enabled (WriteTaggedMem desc sz accdesc tags data) s"
  using assms
  unfolding WriteTaggedMem_def
  by (cases "tags !! 0"; cases "tags !! 1")
     (auto intro!: traces_enabled_write_memt traces_enabled_bind non_cap_expI[THEN non_cap_exp_traces_enabledI]
           simp: run_write_memt nth_ucast)

definition store_enabled where
  "store_enabled s vaddr acctype sz data tag \<equiv>
     \<forall>paddr.
        translate_address vaddr = Some paddr \<longrightarrow>
        access_enabled s Store vaddr paddr (nat sz) (mem_bytes_of_word data) (bitU_of_bool tag)"

definition load_enabled where
  "load_enabled s vaddr acctype sz tagged \<equiv>
     \<forall>paddr data tag.
        translate_address vaddr = Some paddr \<longrightarrow>
        access_enabled s Load vaddr paddr (nat sz) data (if tagged then tag else B0)"

lemma store_enabled_runI[derivable_caps_runI]:
  assumes "store_enabled s vaddr acctype sz data tag"
  shows "store_enabled (run s t) vaddr acctype sz data tag"
  using assms
  by (auto simp: store_enabled_def intro: access_enabled_runI)

lemma load_enabled_runI[derivable_caps_runI]:
  assumes "load_enabled s vaddr acctype sz tagged"
  shows "load_enabled (run s t) vaddr acctype sz tagged"
  using assms
  by (auto simp: load_enabled_def intro: access_enabled_runI)

thm access_enabled_def authorises_access_def addrs_in_mem_region_def

lemma addrs_in_mem_region_subset:
  assumes "addrs_in_mem_region c acctype vaddr paddr sz"
    and "vaddr \<le> vaddr'" and "vaddr' + sz' \<le> vaddr + sz"
    and "translate_address vaddr' = Some paddr'"
  shows "addrs_in_mem_region c acctype vaddr' paddr' sz'"
  using assms
  unfolding addrs_in_mem_region_def
  by (auto simp: get_mem_region_def)

lemma access_enabled_data_load_subset:
  assumes "access_enabled s Load vaddr paddr sz data B0"
    and "vaddr \<le> vaddr'" and "vaddr' + sz' \<le> vaddr + sz"
    and "translate_address vaddr' = Some paddr'"
  shows "access_enabled s Load vaddr' paddr' sz' data' B0"
  using assms
  unfolding access_enabled_def authorises_access_def
  by (auto intro: addrs_in_mem_region_subset)

lemma load_enabled_data_subset[intro]:
  assumes "load_enabled s vaddr acctype sz False"
    and "vaddr \<le> vaddr'" and "vaddr' + nat sz' \<le> vaddr + nat sz"
    and "translate_address vaddr = Some paddr"
  shows "load_enabled s vaddr' acctype sz' False"
  using assms
  by (auto simp: load_enabled_def intro: access_enabled_data_load_subset)

(* TODO *)
lemma
  assumes "load_enabled s (vaddr + offset) acctype sz tagged"
    and "translate_address vaddr (acctype_of_AccType acctype False) = Some paddr"
    and "tagged \<or> tag = B0"
  shows "access_enabled s Load (paddr + offset) (nat sz) data tag"
  using assms
  unfolding access_enabled_def
  apply (cases tagged)
  apply (auto simp: load_enabled_def translate_address_def dvd_def)
  oops

text \<open>The VirtualAddress type in the ASL\<close>

definition perm_bits_included :: "64 word \<Rightarrow> 64 word \<Rightarrow> bool" where
  "perm_bits_included perms1 perms2 \<equiv> (\<forall>n < 64. perms1 !! n \<longrightarrow> perms2 !! n)"

lemma perm_bits_included_refl[simp, intro]:
  "perm_bits_included p p"
  by (auto simp: perm_bits_included_def)

lemma perm_bits_included_OR[intro]:
  assumes "perm_bits_included p p1 \<or> perm_bits_included p p2"
  shows "perm_bits_included p (p1 OR p2)"
  using assms
  by (auto simp: perm_bits_included_def word_ao_nth)

lemma VAAdd_derivable[derivable_capsE]:
  assumes t: "Run (VAAdd va offset) t va'"
    and "VA_derivable va s"
  shows "VA_derivable va' s"
proof -
  have "VA_derivable va' (run s t)"
    using assms
    by (cases "VirtualAddress_vatype va"; auto simp: VAAdd_def elim!: Run_bindE Run_ifE)
       (derivable_capsI)+
  then show ?thesis
    using non_cap_exp_Run_run_invI[OF non_cap_exp_VAAdd t]
    by simp
qed

lemma CSP_read_derivable_caps[derivable_capsE]:
  "Run (CSP_read u) t c \<Longrightarrow> c \<in> derivable_caps (run s t)"
  using EL_exhaust_disj
  by (fastforce simp: CSP_read_def Let_def register_defs derivable_caps_def accessible_regs_def
                elim!: Run_bindE Run_ifE Run_read_regE intro!: derivable.Copy)

lemma BaseReg_read_VA_derivable[derivable_capsE]:
  assumes "Run (BaseReg_read n is_prefetch) t va"
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
    unfolding BaseReg_read_def
    by - (derivable_capsI elim: CSP_read_derivable_caps)
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
    by - (derivable_capsI elim: CSP_read_derivable_caps)
  then show ?thesis
    using VA_Capability
    by (auto simp: VA_derivable_def)
qed

declare AltBaseReg_read_VA_derivable[where is_prefetch = False, folded AltBaseReg_read__1_def, derivable_capsE]

lemma tag_granule_16[simp]: "tag_granule ISA = 16"
  by (auto simp: ISA_def)

lemma address_tag_aligned_iff_aligned_16[simp]:
  "address_tag_aligned ISA addr \<longleftrightarrow> aligned addr 16"
  by (auto simp: address_tag_aligned_def aligned_def)

lemma translate_address_aligned_iff[simp]:
  assumes "translate_address vaddr acctype = Some paddr"
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

lemma TranslateAddress_aligned_vaddr_aligned_paddr:
  assumes "Run (AArch64_TranslateAddressWithTag vaddr acctype iswrite wasaligned sz iscapwrite) t addrdesc"
    and "FaultRecord_statuscode (AddressDescriptor_fault addrdesc) = Fault_None"
    and "aligned (unat vaddr) sz" and "sz dvd 2^48"
    and "trace_assms t"
  shows "aligned (unat (FullAddress_address (AddressDescriptor_paddress addrdesc))) sz"
    (is "aligned ?paddr sz")
proof -
  have *: "translate_address (unat vaddr) (acctype_of_AccType acctype iswrite) = Some ?paddr"
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

lemma CapIsTagClear_iff_not_128th[simp]:
  "CapIsTagClear c \<longleftrightarrow> \<not>CapIsTagSet c"
  by (auto simp: CapIsTagClear_def CapGetTag_def CAP_TAG_BIT_def nth_ucast test_bit_of_bl)

lemma more_CC_simps[simp]:
  "is_sealed_method CC c = CapIsSealed c"
  "get_base_method CC c = get_base c"
  "get_top_method CC c = get_limit c"
  by (auto simp: CC_def)

lemma CapGetBounds_get_base:
  assumes "Run (CapGetBounds c) t (base, limit, valid)"
  shows "get_base c = unat base"
  using assms
  apply (auto simp: CC_def get_base_def CapGetBase_def)
  apply (rule theI2)
    apply auto
  sorry

lemma CapGetBounds_get_limit:
  assumes "Run (CapGetBounds c) t (base, limit, valid)"
  shows "get_limit c = unat limit"
  sorry

lemma CapUnsignedGreaterThanOrEqual_iff_unat_geq[simp]:
  "CapUnsignedGreaterThanOrEqual x y \<longleftrightarrow> unat x \<ge> unat y"
  by (auto simp: CapUnsignedGreaterThanOrEqual_def unat_def nat_le_eq_zle)

lemma CapUnsignedLessThanOrEqual_iff_unat_geq[simp]:
  "CapUnsignedLessThanOrEqual x y \<longleftrightarrow> unat x \<le> unat y"
  by (auto simp: CapUnsignedLessThanOrEqual_def unat_def nat_le_eq_zle)

lemma CapGetBounds_base_leq_limit:
  assumes "Run (CapGetBounds c) t (base, limit, valid)"
    and "trace_assms t"
  shows "base \<le> limit"
  (* TODO: add global bounds validity assumption and prove as invariant *)
  sorry

lemma CapIsRangeInBounds_in_get_mem_region:
  assumes "Run (CapIsRangeInBounds c addr sz) t True" and "trace_assms t"
    and "unat sz \<le> 2^64"
  shows "set (address_range (unat addr) (unat sz)) \<subseteq> get_mem_region CC c"
proof -
  have "unat (ucast addr + sz) = unat addr + unat sz"
    using add_less_le_mono[OF unat_lt2p[of addr] \<open>unat sz \<le> 2^64\<close>]
    by (auto simp: unat_plus_if_size)
  then show ?thesis
    using assms CapGetBounds_base_leq_limit
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
    and sz: "nat sz \<le> 2^64" "unat vaddr \<le> vaddr'" "vaddr' + nat sz' \<le> unat vaddr + nat sz"
    and "perm_bits_included CAP_PERM_LOAD req_perms"
    and "tagged \<longrightarrow> perm_bits_included CAP_PERM_LOAD_CAP req_perms"
    and "tagged \<longrightarrow> nat sz' = 16 \<and> aligned vaddr' 16"
    and "c \<in> derivable_caps (run s t)"
  shows "load_enabled (run s t) vaddr' acctype' sz' tagged"
proof (unfold load_enabled_def, intro allI impI)
  fix paddr data tag
  assume "translate_address vaddr' (acctype_of_AccType acctype' False) = Some paddr"
  then have paddr: "translate_address vaddr' Load = Some paddr"
    by (auto simp: translate_address_def)
  let ?tag = "if tagged then tag else B0"
  let ?is_cap = "?tag \<noteq> B0"
  let ?is_local_cap = "mem_val_is_local_cap CC ISA data ?tag \<and> tag = B1"
  have tagged: "CapIsTagSet c" and not_sealed: "\<not>CapIsSealed c"
    using assms
    by (auto elim!: Run_bindE split: if_splits simp: CheckCapability_def)
  then have c: "c \<in> derivable (accessed_caps (run s t))"
    using \<open>c \<in> derivable_caps (run s t)\<close>
    by (auto simp: derivable_caps_def)
  have aligned: "nat sz' = 16 \<and> aligned paddr 16" if "tagged"
    using assms paddr that
    by auto
  obtain t' where "Run (CapIsRangeInBounds c vaddr (word_of_int sz)) t' True" and "trace_assms t'"
    using t
    by (auto elim!: Run_bindE simp: CheckCapability_def split: if_splits)
  from CapIsRangeInBounds_in_get_mem_region[OF this]
  have "paddr_in_mem_region c Load paddr (nat sz')"
    using paddr sz
    unfolding paddr_in_mem_region_def
    by (intro exI[where x = vaddr']) (auto simp: unat_def uint_word_of_int subset_eq)
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
  ultimately have "\<forall>is_local_cap. authorises_access c Load ?is_cap is_local_cap paddr (nat sz')"
    using assms tagged not_sealed
    by (auto simp: authorises_access_def)
  then show "access_enabled (run s t) Load paddr (nat sz') data ?tag"
    using c aligned
    by (fastforce simp: access_enabled_def)
qed

lemma concat_take_chunks_eq:
  "n > 0 \<Longrightarrow> List.concat (take_chunks n xs) = xs"
  by (induction n xs rule: take_chunks.induct) auto

lemma bits_of_mem_bytes_of_word_to_bl:
  "bits_of_mem_bytes (mem_bytes_of_word w) = map bitU_of_bool (to_bl w)"
  unfolding bits_of_mem_bytes_def mem_bytes_of_word_def bits_of_bytes_def
  by (auto simp add: concat_take_chunks_eq simp del: take_chunks.simps)

lemma cap_of_mem_bytes_of_word_B1_Capability_of_tag_word:
  fixes data :: "'a::len word"
  assumes "LENGTH('a) = 128"
  shows "cap_of_mem_bytes (mem_bytes_of_word data) B1 = Some (Capability_of_tag_word True (ucast data))"
  unfolding Capability_of_tag_word_def cap_of_mem_bytes_def
  by (auto simp: bind_eq_Some_conv bits_of_mem_bytes_of_word_to_bl ucast_bl)

lemma CheckCapability_store_enabled:
  fixes data :: "'a::len word"
  assumes t: "Run (CheckCapability c addr sz req_perms acctype) t vaddr" "trace_assms t"
    and sz: "nat sz \<le> 2^64" "unat vaddr \<le> vaddr'" "vaddr' + nat sz' \<le> unat vaddr + nat sz"
    and store_perm: "perm_bits_included CAP_PERM_STORE req_perms"
    and store_cap_perm: "tag \<longrightarrow> perm_bits_included CAP_PERM_STORE_CAP req_perms"
    and local_perm: "tag \<and> CapIsLocal (Capability_of_tag_word tag (ucast data)) \<longrightarrow> perm_bits_included CAP_PERM_STORE_LOCAL req_perms"
    and aligned: "tag \<longrightarrow> nat sz' = 16 \<and> aligned vaddr' 16 \<and> LENGTH('a) = 128"
    and "c \<in> derivable_caps (run s t)"
  shows "store_enabled (run s t) vaddr' acctype' sz' data tag"
proof (unfold store_enabled_def, intro allI impI)
  fix paddr
  assume "translate_address vaddr' (acctype_of_AccType acctype' True) = Some paddr"
  then have paddr: "translate_address vaddr' Store = Some paddr"
    by (auto simp: translate_address_def)
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
  then have c: "c \<in> derivable (accessed_caps (run s t))"
    using \<open>c \<in> derivable_caps (run s t)\<close>
    by (auto simp: derivable_caps_def)
  have aligned': "nat sz' = 16 \<and> aligned paddr 16" if "tag"
    using aligned paddr that
    by auto
  obtain t' where "Run (CapIsRangeInBounds c vaddr (word_of_int sz)) t' True" and "trace_assms t'"
    using t
    by (auto elim!: Run_bindE simp: CheckCapability_def split: if_splits)
  from CapIsRangeInBounds_in_get_mem_region[OF this]
  have "paddr_in_mem_region c Store paddr (nat sz')"
    using paddr sz
    unfolding paddr_in_mem_region_def
    by (intro exI[where x = vaddr']) (auto simp: unat_def uint_word_of_int subset_eq)
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
  ultimately have "authorises_access c Store tag ?is_local_cap paddr (nat sz')"
    using tagged not_sealed
    by (auto simp: authorises_access_def)
  then show "access_enabled (run s t) Store paddr (nat sz') ?bytes ?tagbit"
    using aligned' c
    by (cases tag) (auto simp: access_enabled_def)
qed

lemma Run_bindE':
  fixes m :: "('rv, 'b, 'e) monad" and a :: 'a
  assumes "Run (bind m f) t a"
    and "\<And>tm am tf. t = tm @ tf \<Longrightarrow> Run m tm am \<Longrightarrow> Run (f am) tf a \<Longrightarrow> P (tm @ tf)"
  shows "P t"
  using assms
  by (auto elim: Run_bindE)

  thm Run_bindE'[where P = "\<lambda>t. VA_derivable va (run s t)" for va s, simplified]

lemmas Run_case_prodE = case_prodE2[where Q = "\<lambda>m. Run m t a" and R = thesis for t a thesis]

lemmas VA_derivable_combinators[derivable_caps_combinators] =
  Run_bindE'[where P = "\<lambda>t. VA_derivable va (run s t)" for va s, simplified]
  Run_ifE[where thesis = "VA_derivable va (run s t)" and t = t for va s t]
  Run_letE[where thesis = "VA_derivable va (run s t)" and t = t for va s t]
  Run_case_prodE[where thesis = "VA_derivable va (run s t)" and t = t for va s t]

lemmas load_enabled_combinators[derivable_caps_combinators] =
  Run_bindE'[where P = "\<lambda>t. load_enabled (run s t) addr acctype sz tagged" for s addr acctype sz tagged, simplified]
  Run_ifE[where thesis = "load_enabled (run s t) addr acctype sz tagged" and t = t for s addr acctype sz tagged t]
  Run_letE[where thesis = "load_enabled (run s t) addr acctype sz tagged" and t = t for s addr acctype sz tagged t]
  Run_case_prodE[where thesis = "load_enabled (run s t) addr acctype sz tagged" and t = t for s addr acctype sz tagged t]

lemmas store_enabled_combinators[derivable_caps_combinators] =
  Run_bindE'[where P = "\<lambda>t. store_enabled (run s t) addr acctype sz data tag" for s addr acctype sz data tag, simplified]
  Run_ifE[where thesis = "store_enabled (run s t) addr acctype sz data tag" and t = t for s addr acctype sz data tag t]
  Run_letE[where thesis = "store_enabled (run s t) addr acctype sz data tag" and t = t for s addr acctype sz data tag t]
  Run_case_prodE[where thesis = "store_enabled (run s t) addr acctype sz data tag" and t = t for s addr acctype sz data tag t]

lemma prod_snd_derivable_caps[derivable_capsE]:
  assumes "a = (x, y)"
    and "snd a \<in> derivable_caps s"
  shows "y \<in> derivable_caps s"
  using assms
  by auto

lemma return_prod_snd_derivable_caps[derivable_capsE]:
  assumes "Run (return (x, y)) t a"
    and "y \<in> derivable_caps s"
  shows "snd a \<in> derivable_caps s"
  using assms
  by auto

lemma VADeref_load_enabled[derivable_capsE]:
  assumes "Run (VADeref va sz perms acctype) t vaddr" "trace_assms t"
    and "nat sz \<le> 2^64" and "unat vaddr \<le> vaddr'" and "vaddr' + nat sz' \<le> unat vaddr + nat sz"
    and "perm_bits_included CAP_PERM_LOAD perms"
    and "tagged \<longrightarrow> perm_bits_included CAP_PERM_LOAD_CAP perms"
    and "tagged \<longrightarrow> nat sz' = 16 \<and> aligned vaddr' 16"
    and "VA_derivable va s"
    and "{''PCC''} \<subseteq> accessible_regs s"
  shows "load_enabled (run s t) vaddr' acctype' sz' tagged"
  using assms(1,2)
  unfolding VADeref_def
  by - (derivable_capsI assms: assms(3-) elim: CheckCapability_load_enabled)

lemma VADeref_store_data_enabled[derivable_capsE]:
  assumes "Run (VADeref va sz perms acctype) t vaddr" "trace_assms t"
    and "nat sz \<le> 2^64" and "unat vaddr \<le> vaddr'" and "vaddr' + nat sz' \<le> unat vaddr + nat sz"
    and "perm_bits_included CAP_PERM_STORE perms"
    and "VA_derivable va s"
    and "{''PCC''} \<subseteq> accessible_regs s"
  shows "store_enabled (run s t) vaddr' acctype' sz' (data :: 'a::len word) False"
  using assms(1,2)
  unfolding VADeref_def
  by - (derivable_capsI assms: assms(3-) elim: CheckCapability_store_enabled)

lemma VADeref_store_enabled[derivable_capsE]:
  assumes "Run (VADeref va sz perms acctype) t vaddr" "trace_assms t"
    and "nat sz \<le> 2^64" and "unat vaddr \<le> vaddr'" and "vaddr' + nat sz' \<le> unat vaddr + nat sz"
    and "perm_bits_included CAP_PERM_STORE perms"
    and "tag \<longrightarrow> perm_bits_included CAP_PERM_STORE_CAP perms"
    and "tag \<and> CapIsLocal (Capability_of_tag_word tag data) \<longrightarrow> perm_bits_included CAP_PERM_STORE_LOCAL perms"
    and "tag \<longrightarrow> nat sz' = 16 \<and> aligned vaddr' 16"
    and "VA_derivable va s"
    and "{''PCC''} \<subseteq> accessible_regs s"
  shows "store_enabled (run s t) vaddr' acctype' sz' data tag"
  using assms(1,2)
  unfolding VADeref_def
  by - (derivable_capsI assms: assms(3-) elim: CheckCapability_store_enabled)

end

end
