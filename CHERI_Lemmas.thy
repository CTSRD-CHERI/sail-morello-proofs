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
  assumes "access_enabled s acctype addr sz v tag"
  shows "access_enabled (run s t) acctype addr sz v tag"
  using assms derivable_mono[OF accessed_caps_run_mono]
  by (auto simp: access_enabled_def)

lemma traces_enabled_ReadMemory:
  assumes "\<And>v. access_enabled s Load (unat paddr) sz v B0"
  shows "traces_enabled (ReadMemory sz paddr) s"
  using assms
  unfolding ReadMemory_def
  by (intro traces_enabled_read_mem) (auto)

lemma traces_enabled_Mem_read[traces_enabledI]:
  assumes "\<And>v. access_enabled s Load (unat (FullAddress_address (AddressDescriptor_paddress desc))) (nat sz) v B0"
  shows "traces_enabled (Mem_read desc sz accdesc) s"
  unfolding Mem_read_def bind_assoc
  by (traces_enabledI intro: traces_enabled_read_mem assms: assms)

lemma traces_enabled_ReadMem[traces_enabledI]:
  assumes "\<And>v. access_enabled s Load (unat (FullAddress_address (AddressDescriptor_paddress desc))) (nat sz) v B0"
  shows "traces_enabled (ReadMem desc sz accdesc) s"
  unfolding ReadMem_def bind_assoc
  by (traces_enabledI intro: traces_enabled_read_mem assms: assms)

lemma traces_enabled_ReadTaggedMem[traces_enabledI]:
  assumes "\<And>v tag. access_enabled s Load (unat (FullAddress_address (AddressDescriptor_paddress desc))) 16 v tag"
    and "\<And>v tag. sz = 32 \<Longrightarrow> access_enabled s Load (unat (FullAddress_address (AddressDescriptor_paddress desc)) + 16) 16 v tag"
    and "sz = 16 \<or> sz = 32"
  shows "traces_enabled (ReadTaggedMem desc sz accdesc) s"
  unfolding ReadTaggedMem_def bind_assoc
  by (traces_enabledI intro: traces_enabled_read_memt non_cap_expI[THEN non_cap_exp_traces_enabledI] access_enabled_runI assms: assms)

lemma traces_enabled_ReadTags[traces_enabledI]:
  assumes "\<And>i v tag. i < nat sz \<Longrightarrow> access_enabled s Load (unat (FullAddress_address (AddressDescriptor_paddress desc)) + (i * 16)) 16 v tag"
  shows "traces_enabled (ReadTags desc sz accdesc) s"
  unfolding ReadTags_def bind_assoc
  by (traces_enabledI intro: traces_enabled_read_memt non_cap_expI[THEN non_cap_exp_traces_enabledI] access_enabled_runI
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
  assumes "access_enabled s Store (unat paddr) (nat sz) (mem_bytes_of_word data) B0"
    and "LENGTH('a) = nat sz * 8" and "sz > 0"
  shows "traces_enabled (write_mem BC_mword BC_mword wk addr_sz paddr sz data) s"
  using assms
  unfolding write_mem_def
  by (auto intro!: traces_enabled_Write_mem non_cap_expI[THEN non_cap_exp_traces_enabledI]
           split: option.splits simp: legal_store_def length_mem_bytes_of_word)

lemma traces_enabled_Mem_set[traces_enabledI]:
  fixes data :: "'a::len word"
  assumes "access_enabled s Store (unat (FullAddress_address (AddressDescriptor_paddress desc))) (nat sz) (mem_bytes_of_word data) B0"
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
  assumes "access_enabled s Store (unat paddr) 16 (mem_bytes_of_word data) tag"
    and "tag = B0 \<or> tag = B1"
    and "tag \<noteq> B0 \<Longrightarrow> Capability_of_tag_word (bitU_nonzero tag) data \<in> derivable_caps s"
  shows "traces_enabled (write_memt BC_mword BC_mword wk paddr 16 data tag) s"
  using assms
  unfolding write_memt_def
  by (auto intro!: traces_enabled_Write_memt non_cap_expI[THEN non_cap_exp_traces_enabledI]
           split: option.splits simp: legal_store_def length_mem_bytes_of_word)

lemma traces_enabled_WriteTaggedMem_single[traces_enabledI]:
  fixes tag :: "1 word" and data :: "128 word"
  assumes "access_enabled s Store (unat (FullAddress_address (AddressDescriptor_paddress desc))) 16 (mem_bytes_of_word data) (bitU_of_bool (tag !! 0))"
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
  assumes "access_enabled s Store (unat (FullAddress_address (AddressDescriptor_paddress desc))) 16 (mem_bytes_of_word (ucast data :: 128 word)) (bitU_of_bool (tags !! 0))"
    and "access_enabled s Store (unat (FullAddress_address (AddressDescriptor_paddress desc)) + 16) 16 (mem_bytes_of_word (Word.slice 128 data :: 128 word)) (bitU_of_bool (tags !! 1))"
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
  assumes "access_enabled s Store (unat (FullAddress_address (AddressDescriptor_paddress desc))) 16 (mem_bytes_of_word (ucast data :: 128 word)) (bitU_of_bool (tags !! 0))"
    and "Capability_of_tag_word (tags !! 0) (ucast data) \<in> derivable_caps s"
    and "sz = 32 \<Longrightarrow> access_enabled s Store (unat (FullAddress_address (AddressDescriptor_paddress desc)) + 16) 16 (mem_bytes_of_word (Word.slice 128 data :: 128 word)) (bitU_of_bool (tags !! 1))"
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
        translate_address vaddr (acctype_of_AccType acctype True) = Some paddr \<longrightarrow>
        access_enabled s Store paddr (nat sz) (mem_bytes_of_word data) (bitU_of_bool tag)"

definition load_enabled where
  "load_enabled s vaddr acctype sz tagged \<equiv>
     \<forall>paddr data tag.
        translate_address vaddr (acctype_of_AccType acctype False) = Some paddr \<longrightarrow>
        access_enabled s Load paddr (nat sz) data (if tagged then tag else B0)"

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

(* TODO *)
lemma
  assumes "load_enabled s (vaddr + offset) acctype sz tagged"
    and "translate_address vaddr (acctype_of_AccType acctype False) = Some paddr"
    and "tagged \<or> tag = B0"
  shows "access_enabled s Load (paddr + offset) (nat sz) data tag"
  using assms
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

lemma VADeref_load_enabled[derivable_capsE]:
  assumes "Run (VADeref va sz perms acctype) t vaddr"
    and "perm_bits_included CAP_PERM_LOAD perms"
    and "tagged \<longrightarrow> perm_bits_included CAP_PERM_LOAD_CAP perms"
    and "sz' \<le> sz"
    and "VA_derivable va s"
    and "{''PCC''} \<subseteq> accessible_regs s"
  shows "load_enabled (run s t) (unat vaddr) acctype' sz' tagged"
  sorry

lemma VADeref_store_data_enabled[derivable_capsE]:
  assumes "Run (VADeref va sz perms acctype) t vaddr"
    and "perm_bits_included CAP_PERM_STORE perms"
    and "sz' \<le> sz"
    and "VA_derivable va s"
    and "{''PCC''} \<subseteq> accessible_regs s"
  shows "store_enabled (run s t) (unat vaddr) acctype' sz' data False"
  sorry

lemma VADeref_store_enabled[derivable_capsE]:
  assumes "Run (VADeref va sz perms acctype) t vaddr"
    and "perm_bits_included CAP_PERM_STORE perms"
    and "tag \<longrightarrow> perm_bits_included CAP_PERM_STORE_CAP perms"
    and "tag \<and> CapIsLocal (Capability_of_tag_word tag data) \<longrightarrow> perm_bits_included CAP_PERM_STORE_LOCAL perms"
    and "sz' \<le> sz"
    and "VA_derivable va s"
    and "{''PCC''} \<subseteq> accessible_regs s"
  shows "store_enabled (run s t) (unat vaddr) acctype' sz' data tag"
  sorry

end

end
