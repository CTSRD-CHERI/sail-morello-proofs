theory CHERI_Instantiation
  imports
    "Sail-Morello.Morello_lemmas"
    "Sail-T-CHERI.Cheri_axioms_lemmas"
    "Sail.Sail2_operators_mwords_lemmas"
    "Sail.Sail2_values_lemmas"
    "HOL-Library.Monad_Syntax"
    "Sail-T-CHERI.Word_Extra"
begin

no_notation Sail2_prompt_monad.bind (infixr "\<bind>" 54)
no_notation Sail2_prompt_monad_lemmas.seq (infixr "\<then>" 54)
adhoc_overloading bind Sail2_prompt_monad.bind

section \<open>General lemmas\<close>

lemma bitU_of_bool_simps[simp]:
  "bitU_of_bool True = B1"
  "bitU_of_bool False = B0"
  by (auto simp: bitU_of_bool_def)

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

section \<open>Simplification rules\<close>

declare zero_extend_def[simp]

lemma Bit_bitU_of_bool[simp]: "Morello.Bit w = bitU_of_bool (w !! 0)"
  by (auto simp: Morello.Bit_def)

lemma CapIsTagSet_bit128[simp]:
  "CapIsTagSet c \<longleftrightarrow> c !! 128"
  by (auto simp: CapIsTagSet_def CapGetTag_def CAP_TAG_BIT_def nth_ucast test_bit_of_bl)

lemma CapSetTag_set_bit128[simp]:
  "CapSetTag c t = set_bit c 128 (t !! 0)"
  by (cases "t !! 0") (auto simp: CapSetTag_def CAP_TAG_BIT_def)

lemma CapIsTagSet_CapSetTag_iff[simp]:
  "CapIsTagSet (CapSetTag c t) \<longleftrightarrow> (t !! 0)"
  by (auto simp: test_bit_set)

section \<open>Capabilities\<close>

definition is_sentry :: "Capability \<Rightarrow> bool" where
  "is_sentry c \<equiv> CapGetObjectType c \<in> {CAP_SEAL_TYPE_RB, CAP_SEAL_TYPE_LPB, CAP_SEAL_TYPE_LB}"

definition get_base :: "Capability \<Rightarrow> nat" where
  "get_base c \<equiv> unat (THE b. \<exists>t. Run (CapGetBase c) t b)"

definition get_limit :: "Capability \<Rightarrow> nat" where
  "get_limit c \<equiv> unat (THE b. \<exists>t. Run (CapGetLimit c) t b)"

definition get_perms :: "Capability \<Rightarrow> perms" where
  "get_perms c = to_bl (CapGetPerms c)"

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
   permits_ccall_method = (cap_permits CAP_PERM_BRANCH_SEALED),
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
    by (auto simp: CC_def seal_def CapIsTagSet_def CapGetTag_def CapSetObjectType_def CAP_OTYPE_HI_BIT_def CAP_OTYPE_LO_BIT_def CAP_TAG_BIT_def update_subrange_vec_dec_test_bit)
next
  fix c bytes tag
  have test_128_128: "w !! 128 \<longleftrightarrow> False" for w :: "128 word"
    by (auto dest: test_bit_len)
  assume "cap_of_mem_bytes_method CC bytes tag = Some c"
  then show "is_tagged_method CC c = (tag = B1)"
    by (cases tag)
       (auto simp: CC_def cap_of_mem_bytes_def bind_eq_Some_conv nth_ucast test_bit_cat test_128_128)
qed

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

fun is_mem_event :: "'regval event \<Rightarrow> bool" where
  "is_mem_event (E_read_memt _ _ _ _) = True"
| "is_mem_event (E_read_mem _ _ _ _) = True"
| "is_mem_event (E_write_memt _ _ _ _ _ _) = True"
| "is_mem_event (E_write_mem _ _ _ _ _) = True"
| "is_mem_event _ = False"

locale Morello_Address_Translation =
  fixes translate_address :: "nat \<Rightarrow> acctype \<Rightarrow> register_value trace \<Rightarrow> nat option"
    and is_translation_event :: "register_value event \<Rightarrow> bool"
    and translation_assms :: "register_value event \<Rightarrow> bool"
  assumes translate_correct64:
      "\<And>vaddress acctype iswrite wasaligned size iswritevalidcap addrdesc.
          Run (AArch64_TranslateAddressWithTag vaddress acctype iswrite wasaligned size iswritevalidcap) t addrdesc \<Longrightarrow>
          FaultRecord_statuscode (AddressDescriptor_fault addrdesc) = Fault_None \<Longrightarrow>
          \<forall>e \<in> set t. translation_assms e \<Longrightarrow>
          translate_address (unat vaddress) (acctype_of_AccType acctype iswrite) t =
            Some (unat (FullAddress_address (AddressDescriptor_paddress addrdesc)))"
    and translate_correct32:
      "\<And>vaddress acctype iswrite wasaligned size iswritevalidcap addrdesc.
          Run (AArch32_TranslateAddressWithTag vaddress acctype iswrite wasaligned size iswritevalidcap) t addrdesc \<Longrightarrow>
          FaultRecord_statuscode (AddressDescriptor_fault addrdesc) = Fault_None \<Longrightarrow>
          \<forall>e \<in> set t. translation_assms e \<Longrightarrow>
          translate_address (unat vaddress) (acctype_of_AccType acctype iswrite) t =
            Some (unat (FullAddress_address (AddressDescriptor_paddress addrdesc)))"
    and is_translation_event_correct64:
      "\<And>vaddress acctype iswrite wasaligned size iswritevalidcap addrdesc e.
          Run (AArch64_TranslateAddressWithTag vaddress acctype iswrite wasaligned size iswritevalidcap) t addrdesc \<Longrightarrow>
          \<forall>e' \<in> set t. translation_assms e' \<Longrightarrow>
          e \<in> set t \<Longrightarrow> is_mem_event e \<Longrightarrow>
          is_translation_event e"
    and is_translation_event_correct32:
      "\<And>vaddress acctype iswrite wasaligned size iswritevalidcap addrdesc e.
          Run (AArch32_TranslateAddressWithTag vaddress acctype iswrite wasaligned size iswritevalidcap) t addrdesc \<Longrightarrow>
          \<forall>e' \<in> set t. translation_assms e' \<Longrightarrow>
          e \<in> set t \<Longrightarrow> is_mem_event e \<Longrightarrow>
          is_translation_event e"
begin

definition "ISA \<equiv>
  \<lparr>isa.instr_sem = instr_sem,
   isa.instr_fetch = instr_fetch,
   tag_granule = 16,
   PCC = {''PCC''},
   KCC = {''CVBAR_EL1'', ''CVBAR_EL2'', ''CVBAR_EL3''},
   IDC = {''R29''},
   isa.caps_of_regval = caps_of_regval,
   isa.invokes_caps = invokes_caps,
   isa.instr_raises_ex = instr_raises_ex,
   isa.fetch_raises_ex = fetch_raises_ex,
   isa.exception_targets = exception_targets,
   privileged_regs = {''CVBAR_EL1'', ''CVBAR_EL2'', ''CVBAR_EL3''}, \<comment> \<open>TODO\<close>
   isa.is_translation_event = is_translation_event,
   isa.translate_address = translate_address \<rparr>"

sublocale Capability_ISA CC ISA ..

end

text \<open>Instantiation of translate_address for version of spec with translation stubs\<close>

definition translate_address :: "nat \<Rightarrow> acctype \<Rightarrow> register_value trace \<Rightarrow> nat option" where
  "translate_address addr acctype t \<equiv> Some (addr mod 2^52)"

lemmas TranslateAddress_defs =
  AArch64_TranslateAddress_def AArch64_TranslateAddressWithTag_def AArch64_FullTranslateWithTag_def
  AArch64_FirstStageTranslateWithTag_def AArch64_SecondStageTranslate_def
  AArch32_TranslateAddressWithTag_def AArch32_FullTranslateWithTag_def
  AArch32_FirstStageTranslateWithTag_def AArch32_SecondStageTranslate_def
  translate_address_def

lemma unat64_and_mask52_mod: "unat ((w :: 64 word) AND mask 52) = unat w mod 2^52"
  by (auto simp: and_mask_bintr unat_def uint_word_of_int bintrunc_mod2p nat_mod_distrib)

lemma unat32_and_mask52_eq: "unat (w :: 32 word) mod 4503599627370496 = unat w"
  using unat_lt2p[of w]
  by auto

interpretation Morello_Address_Translation
  where translate_address = translate_address
    and is_translation_event = "\<lambda>_. False"
    and translation_assms = "\<lambda>_. True"
  apply unfold_locales
     apply (auto simp: TranslateAddress_defs return_def unat64_and_mask52_mod elim!: Run_bindE Run_ifE)[]
  apply (auto simp: TranslateAddress_defs return_def unat32_and_mask52_eq elim!: Run_bindE Run_ifE)[]
  (* TODO: Show that translation stubs are non_mem_exp's *)
  oops

end