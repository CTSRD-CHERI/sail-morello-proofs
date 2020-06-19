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

lemma no_Run_EndOfInstruction[simp]:
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

lemma if_no_Run_then_else:
  assumes "\<not>Run m1 t a"
  shows "Run (if c then m1 else m2) t a \<longleftrightarrow> \<not>c \<and> Run m2 t a"
  using assms
  by auto

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

declare datatype_splits[split]
declare datatype_splits[where P = "non_cap_exp", non_cap_exp_split]
declare datatype_splits[where P = "non_mem_exp", non_mem_exp_split]

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

term ReadMemory
term access_enabled

lemma nat_of_bv_mword_unat[simp]: "nat_of_bv BC_mword w = Some (unat w)"
  by (auto simp: nat_of_bv_def unat_def)

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

abbreviation "perm_bits_included perms1 perms2 \<equiv> (perms1 AND perms2) = perms1"

definition VA_derivable :: "VirtualAddress \<Rightarrow> (129 word, register_value) axiom_state \<Rightarrow> bool" where
  "VA_derivable va s \<equiv>
     (case VirtualAddress_vatype va of
        VA_Capability \<Rightarrow> VirtualAddress_base va \<in> derivable_caps s
      | VA_Bits64 \<Rightarrow> True)"

lemma VA_derivable_run_imp[derivable_caps_runI]:
  assumes "VA_derivable va s"
  shows "VA_derivable va (run s t)"
  using assms
  by (auto simp: VA_derivable_def split: VirtualAddressType.splits intro: derivable_caps_runI)

lemma BaseReg_read_VA_derivable[derivable_capsE]:
  assumes "Run (BaseReg_read n is_prefetch) t va"
    and "{''_R29''} \<subseteq> accessible_regs s"
  shows "VA_derivable va (run s t)"
  sorry

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
    apply (auto elim!: Run_bindE Run_ifE)
    sorry
  then show ?thesis
    using VA_Capability
    by (auto simp: VA_derivable_def)
qed

declare AltBaseReg_read_VA_derivable[where is_prefetch = False, folded AltBaseReg_read__1_def, derivable_capsE]

lemma VADeref_load_enabled[derivable_capsE]:
  assumes "Run (VADeref va sz perms acctype) t vaddr"
    and "perm_bits_included CAP_PERM_LOAD perms"
    and "tagged \<longrightarrow> perm_bits_included CAP_PERM_LOAD_CAP perms"
    and "VA_derivable va s"
    and "{''PCC''} \<subseteq> accessible_regs s"
  shows "load_enabled (run s t) (unat vaddr) acctype sz tagged"
  sorry

lemma VADeref_store_data_enabled[derivable_capsE]:
  assumes "Run (VADeref va sz perms acctype) t vaddr"
    and "perm_bits_included CAP_PERM_STORE perms"
    and "VA_derivable va s"
    and "{''PCC''} \<subseteq> accessible_regs s"
  shows "store_enabled (run s t) (unat vaddr) acctype sz data False"
  sorry

lemma VADeref_store_enabled[derivable_capsE]:
  assumes "Run (VADeref va sz perms acctype) t vaddr"
    and "perm_bits_included CAP_PERM_STORE perms"
    and "tag \<longrightarrow> perm_bits_included CAP_PERM_STORE_CAP perms"
    and "tag \<and> CapIsLocal (Capability_of_tag_word tag data) \<longrightarrow> perm_bits_included CAP_PERM_STORE_LOCAL perms"
    and "VA_derivable va s"
    and "{''PCC''} \<subseteq> accessible_regs s"
  shows "store_enabled (run s t) (unat vaddr) acctype sz data tag"
  sorry

text \<open>Functions/instructions that need fixing in the ASL\<close>

lemma traces_enabled_DC_ZVA[traces_enabledI]:
  "traces_enabled (DC_ZVA v) s"
  sorry

end

end
