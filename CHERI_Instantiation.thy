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
declare CAPABILITY_DBYTES_def[simp]

lemma nat_of_bv_mword_unat[simp]: "nat_of_bv BC_mword w = Some (unat w)"
  by (auto simp: nat_of_bv_def unat_def)

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

lemma unat_paddress_plus_16[simp]:
  "unat (ucast (FullAddress_address (AddressDescriptor_paddress desc)) + (16 :: 64 word))
   = unat (FullAddress_address (AddressDescriptor_paddress desc)) + 16"
  sorry


lemmas datatype_splits =
  ArchVersion.splits Constraint.splits Unpredictable.splits Exception.splits InstrEnc.splits
  BranchType.splits Fault.splits AccType.splits DeviceType.splits MemType.splits InstrSet.splits
  GTEParamType.splits PrivilegeLevel.splits MBReqDomain.splits MBReqTypes.splits PrefetchHint.splits
  FPExc.splits FPRounding.splits FPType.splits SysRegAccess.splits OpType.splits TimeStamp.splits
  CountOp.splits ExtendType.splits FPMaxMinOp.splits FPUnaryOp.splits FPConvOp.splits
  MoveWideOp.splits ShiftType.splits LogicalOp.splits MemOp.splits MemAtomicOp.splits
  MemBarrierOp.splits SystemHintOp.splits PSTATEField.splits SystemOp.splits VBitOp.splits
  CompareOp.splits ImmediateOp.splits ReduceOp.splits AsyncErrorType.splits

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

lemma CC_simps[simp]:
  "is_tagged_method CC c = CapIsTagSet c"
  by (auto simp: CC_def)

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

locale Morello_ISA =
  fixes translate_address :: "nat \<Rightarrow> acctype \<Rightarrow> register_value trace \<Rightarrow> nat option"
    and is_translation_event :: "register_value event \<Rightarrow> bool"
begin

definition "ISA \<equiv>
  \<lparr>isa.instr_sem = instr_sem,
   isa.instr_fetch = instr_fetch,
   tag_granule = 16,
   PCC = {''PCC''},
   KCC = {''CVBAR_EL1'', ''CVBAR_EL2'', ''CVBAR_EL3''},
   IDC = {''_R29''},
   isa.caps_of_regval = caps_of_regval,
   isa.invokes_caps = invokes_caps,
   isa.instr_raises_ex = instr_raises_ex,
   isa.fetch_raises_ex = fetch_raises_ex,
   isa.exception_targets = exception_targets,
   privileged_regs = {''CVBAR_EL1'', ''CVBAR_EL2'', ''CVBAR_EL3''}, \<comment> \<open>TODO\<close>
   isa.is_translation_event = is_translation_event,
   isa.translate_address = translate_address\<rparr>"

sublocale Capability_ISA CC ISA ..

lemma ISA_simps[simp]:
  "PCC ISA = {''PCC''}"
  "KCC ISA = {''CVBAR_EL1'', ''CVBAR_EL2'', ''CVBAR_EL3''}"
  "IDC ISA = {''_R29''}"
  "privileged_regs ISA = {''CVBAR_EL1'', ''CVBAR_EL2'', ''CVBAR_EL3''}"
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

lemma caps_of_bitvector_129_regval[simp]:
  "bitvector_129_dec_of_regval rv = Some c \<Longrightarrow> caps_of_regval rv = {c}"
  by (cases rv) (auto)

end

locale Morello_Fixed_Address_Translation =
  fixes translate_address :: "nat \<Rightarrow> acctype \<Rightarrow> nat option"
    and is_translation_event :: "register_value event \<Rightarrow> bool"
    and translation_assms :: "register_value event \<Rightarrow> bool"
  assumes translate_correct:
      "\<And>vaddress acctype iswrite wasaligned size iswritevalidcap addrdesc.
          Run (AArch64_TranslateAddressWithTag vaddress acctype iswrite wasaligned size iswritevalidcap) t addrdesc \<Longrightarrow>
          FaultRecord_statuscode (AddressDescriptor_fault addrdesc) = Fault_None \<Longrightarrow>
          \<forall>e \<in> set t. translation_assms e \<Longrightarrow>
          translate_address (unat vaddress) (acctype_of_AccType acctype iswrite) =
            Some (unat (FullAddress_address (AddressDescriptor_paddress addrdesc)))"
    and is_translation_event_correct:
      "\<And>vaddress acctype iswrite wasaligned size iswritevalidcap addrdesc e.
          Run (AArch64_TranslateAddressWithTag vaddress acctype iswrite wasaligned size iswritevalidcap) t addrdesc \<Longrightarrow>
          \<forall>e' \<in> set t. translation_assms e' \<Longrightarrow>
          e \<in> set t \<Longrightarrow> is_mem_event e \<Longrightarrow>
          is_translation_event e"
begin

sublocale Morello_ISA where translate_address = "\<lambda>addr acctype _. translate_address addr acctype" .

sublocale Capability_ISA_Fixed_Translation CC ISA translation_assms
  by unfold_locales (auto simp: ISA_def)

end

text \<open>Instantiation of translate_address for version of spec with translation stubs\<close>

definition translate_address :: "nat \<Rightarrow> acctype \<Rightarrow> nat option" where
  "translate_address addr acctype \<equiv> Some (addr mod 2^48)"

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

lemma CapNull_derivable[simp, intro]: "CapNull u \<in> derivable_caps s"
  by (auto simp: derivable_caps_def CapNull_def Zeros_def zeros_def)

(* Pattern common in auto-generated register accessors *)
lemma if_ELs_derivable[derivable_capsE]:
  assumes "Run (if el = EL0 then m0 else if el = EL1 then m1 else if el = EL2 then m2 else if el = EL3 then m3 else mu) t a"
    and "el = EL0 \<longrightarrow> Run m0 t a \<longrightarrow> c \<in> derivable_caps (run s t)"
    and "el = EL1 \<longrightarrow> Run m1 t a \<longrightarrow> c \<in> derivable_caps (run s t)"
    and "el = EL2 \<longrightarrow> Run m2 t a \<longrightarrow> c \<in> derivable_caps (run s t)"
    and "el = EL3 \<longrightarrow> Run m3 t a \<longrightarrow> c \<in> derivable_caps (run s t)"
  shows "c \<in> derivable_caps (run s t)"
  using assms
  by (cases el rule: exhaustive_2_word; auto simp: EL0_def EL1_def EL2_def EL3_def)

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
  by (auto simp: VAToCapability_def VAIsCapability_def elim!: Run_bindE)

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

locale Morello_Write_Cap_Automaton = Morello_ISA +
  fixes ex_traces :: bool and invoked_caps :: "Capability set"
begin

(* TODO *)
fun ev_assms :: "register_value event \<Rightarrow> bool" where
  "ev_assms (E_read_reg r v) = (r = ''PCC'' \<longrightarrow> (\<forall>c \<in> caps_of_regval v. \<not>CapIsSealed c))"
| "ev_assms _ = True"

sublocale Write_Cap_Assm_Automaton where CC = CC and ISA = ISA and ev_assms = ev_assms ..

sublocale Morello_Axiom_Automaton where enabled = enabled ..

end

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
  where translate_address = "\<lambda>addr acctype _. translate_address addr acctype"
    and enabled = enabled
    and is_translation_event = "\<lambda>_. False"
  ..

end

end
