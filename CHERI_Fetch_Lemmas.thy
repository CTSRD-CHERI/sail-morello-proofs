theory CHERI_Fetch_Lemmas
  imports CHERI_Mem_Properties "Sail.Hoare"
begin

context Morello_Fetch_Automaton
begin

lemmas non_cap_exp_traces_enabled[traces_enabledI] = non_cap_expI[THEN non_cap_exp_traces_enabledI]

lemmas non_mem_exp_traces_enabled[traces_enabledI] = non_mem_expI[THEN non_mem_exp_traces_enabledI]

lemma traces_enabled_Mem_read_Fetch[traces_enabledI]:
  assumes "\<And>v. paccess_enabled s Fetch (unat (FullAddress_address (AddressDescriptor_paddress desc))) (nat sz) v B0"
  shows "traces_enabled (Mem_read desc sz accdesc) s"
  unfolding Mem_read_def bind_assoc
  by (traces_enabledI intro: traces_enabled_read_mem assms: assms)

lemma load_enabled_access_enabled_Fetch[intro]:
  assumes "load_enabled s acctype vaddr sz tagged"
    and "sz' = nat sz"
    and "translate_address vaddr = Some paddr"
    and "tagged \<or> tag = B0"
  shows "\<exists>vaddr. access_enabled s Fetch vaddr paddr sz' data tag"
  using assms
  unfolding load_enabled_def
  by (cases tagged) auto

lemma traces_enabled_AArch64_MemSingle_read[traces_enabledI]:
  assumes "translate_address (unat address) \<noteq> None \<longrightarrow> load_enabled s acctype (unat address) size__arg False"
  shows "traces_enabled (AArch64_MemSingle_read address size__arg acctype wasaligned :: 'size_times_p8::len word M) s"
  unfolding AArch64_MemSingle_read_def bind_assoc
  by (traces_enabledI assms: assms intro: traces_enabled_Mem_read_Fetch simp: exp_fails_if_then_else)

lemma traces_enabled_FetchInstr[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (FetchInstr pc) s"
  unfolding FetchInstr_def CheckPCCCapability_def bind_assoc
  by (traces_enabledI assms: assms elim: CheckCapability_load_enabled intro: derivable_or_invokedI1)

end

lemma Run_Read_mem_iff:
  "Run (Read_mem rk addr sz k) t a \<longleftrightarrow> (\<exists>t' data. t = E_read_mem rk addr sz data # t' \<and> Run (k data) t' a)"
  by (auto elim: Traces_cases)

lemma Value_returnS_iff[simp]:
  "(Value x, s') \<in> returnS a s \<longleftrightarrow> x = a \<and> s' = s"
  by (auto simp: returnS_def)

lemma Value_readS_iff[simp]:
  "(Value a, s') \<in> readS f s \<longleftrightarrow> a = f s \<and> s' = s"
  by (auto simp: readS_def)

lemma Value_updateS_iff[simp]:
  "(Value u, s') \<in> updateS f s \<longleftrightarrow> s' = f s"
  by (auto simp: updateS_def)

lemma Value_throwS_False[simp]:
  "(Value a, s') \<in> throwS ex s \<longleftrightarrow> False"
  by (auto simp: throwS_def)

lemma Value_failS_False[simp]:
  "(Value a, s') \<in> failS msg s \<longleftrightarrow> False"
  by (auto simp: failS_def)

lemma Value_maybe_failS_iff[simp]:
  "(Value a, s') \<in> maybe_failS msg x s \<longleftrightarrow> x = Some a \<and> s' = s"
  by (auto simp: maybe_failS_def split: option.splits)

lemma Value_read_memt_bytesS_iff[simp]:
  "(Value data, s') \<in> read_memt_bytesS rk a sz s \<longleftrightarrow> get_mem_bytes a sz s = Some data \<and> s' = s"
  by (auto simp: read_memt_bytesS_def elim!: Value_bindS_elim intro: bindS_intros)

lemma Value_read_mem_bytesS_iff[simp]:
  "(Value data, s') \<in> read_mem_bytesS rk a sz s \<longleftrightarrow> (\<exists>tag. get_mem_bytes a sz s = Some (data, tag) \<and> s' = s)"
  by (auto simp: read_mem_bytesS_def elim!: Value_bindS_elim intro: bindS_intros)

lemma Value_write_memt_bytesS_iff[simp]:
  "(Value b, s') \<in> write_memt_bytesS wk a sz data tag s \<longleftrightarrow> s' = put_mem_bytes a sz data tag s \<and> b"
  by (auto simp: write_memt_bytesS_def elim!: Value_bindS_elim intro: bindS_intros)

lemma Value_write_mem_bytesS_iff[simp]:
  "(Value b, s') \<in> write_mem_bytesS wk a sz data s \<longleftrightarrow> s' = put_mem_bytes a sz data B0 s \<and> b"
  by (auto simp: write_mem_bytesS_def elim!: Value_bindS_elim intro: bindS_intros)

lemma Value_read_regvalS_iff[simp]:
  "(Value a, s') \<in> read_regvalS ra r s \<longleftrightarrow> fst ra r (regstate s) = Some a \<and> s' = s"
  by (cases ra; auto elim!: Value_bindS_elim intro: bindS_intros split: option.splits)

lemma Value_write_regvalS_iff[simp]:
  "(Value u, s') \<in> write_regvalS ra r a s \<longleftrightarrow> (\<exists>rs'. snd ra r a (regstate s) = Some rs' \<and> s' = s\<lparr>regstate := rs'\<rparr>)"
  by (cases ra; auto elim!: Value_bindS_elim intro: bindS_intros split: option.splits)

lemma Value_chooseS_iff[simp]:
  "(Value x, s') \<in> chooseS xs s \<longleftrightarrow> x \<in> xs \<and> s' = s"
  by (auto simp: chooseS_def)

lemma Value_choose_boolS_iff[simp]:
  "(Value x, s') \<in> choose_boolS msg s \<longleftrightarrow> s' = s"
  by (auto simp: choose_boolS_def)

declare excl_resultS_def[simp]

lemma Value_liftState_Run_runTraceS:
  assumes "(Value a, s') \<in> liftState r m s"
  obtains t where "Run m t a" and "runTraceS r t s = Some s'"
(*proof -
  from assms obtain t where "Run m t a"
    by (elim Value_liftState_Run)
  with assms that show thesis
    apply (induction r t s rule: runTraceS.induct)
    apply auto*)
proof (use assms in \<open>induction r m arbitrary: s s' rule: liftState.induct\<close>)
  case (1 ra a)
  then show ?case by (simp)
next
  case (2 ra rk a sz k)
  (*then show ?case
    apply (auto elim!: Value_bindS_elim simp add: returnS_def maybe_failS_def failS_def readS_def read_mem_bytesS_def read_memt_bytesS_def bind_eq_Some_conv split: option.splits)
    apply (auto elim!: Value_bindS_elim intro: Traces_ConsI) *)
  then show ?case
    by (force elim!: Value_bindS_elim intro: Traces_ConsI)
    (*thm "2.IH"[rotated -1]
    apply (erule "2.IH"[rotated -1])
     apply blast
    apply (rule "2.prems")
     apply (rule Traces_ConsI)
     apply assumption
    apply (auto elim!: Value_bindS_elim)
    thm runTraceS.induct emitEventS.elims
    sorry*)
next
  case (3 ra rk a sz k)
  then show ?case
    by (force elim!: Value_bindS_elim intro: Traces_ConsI)
next
  case (4 ra wk a sz v k)
  then show ?case
    by (fastforce elim!: Value_bindS_elim intro: Traces_ConsI)
next
  case (5 ra wk a sz v t k)
  then show ?case by (fastforce elim!: Value_bindS_elim intro: Traces_ConsI)
next
  case (6 ra r k)
  then show ?case by (force elim!: Value_bindS_elim intro: Traces_ConsI)
next
  case (7 ra k)
  then show ?case by (force elim!: Value_bindS_elim intro: Traces_ConsI)
next
case (8 ra uu k)
  then show ?case by (force elim!: Value_bindS_elim intro: Traces_ConsI)
next
  case (9 ra r v k)
  then show ?case by (force elim!: Value_bindS_elim intro: Traces_ConsI)
next
  case (10 ra uv uw ux k)
  then show ?case by (force elim!: Value_bindS_elim intro: Traces_ConsI)
next
  case (11 ra k)
  then show ?case by (force elim!: Value_bindS_elim intro: Traces_ConsI)
next
  case (12 ra uy k)
  then show ?case by (force elim!: Value_bindS_elim intro: Traces_ConsI)
next
  case (13 ra uz k)
  then show ?case by (force elim!: Value_bindS_elim intro: Traces_ConsI)
next
  case (14 ra descr)
  then show ?case by (force elim!: Value_bindS_elim intro: Traces_ConsI)
next
  case (15 ra e)
  then show ?case by (force elim!: Value_bindS_elim intro: Traces_ConsI)
qed

lemma PrePostE_exp_fails:
  assumes "exp_fails m"
  shows "\<lbrace>P\<rbrace> \<lbrakk>m\<rbrakk>\<^sub>S \<lbrace>Q \<bar> \<lambda>_ _. True\<rbrace>"
  using assms
  by (intro PrePostE_I) (auto elim: Value_liftState_Run)

lemma PrePostE_any_no_ex:
  "PrePostE (\<lambda>s. \<forall>a s'. (Value a, s') \<in> m s \<longrightarrow> Q a s') m Q (\<lambda>_ _. True)"
  by (rule PrePostE_I)  auto

declare PrePostE_True_post[PrePostE_atomI del]

fun no_reg_writes_trace where
  "no_reg_writes_trace (E_write_reg _ _ # _) = False"
| "no_reg_writes_trace (_ # t) = no_reg_writes_trace t"
| "no_reg_writes_trace [] = True"

lemma no_reg_writes_trace_iff:
  "no_reg_writes_trace t \<longleftrightarrow> (\<forall>r v. E_write_reg r v \<notin> set t)"
  by (induction t rule: no_reg_writes_trace.induct; auto)

lemma Run_no_reg_writes_trace:
  assumes "Run m t a" and "runs_no_reg_writes_to UNIV m"
  shows "no_reg_writes_trace t"
  using assms
  by (auto simp: runs_no_reg_writes_to_def no_reg_writes_trace_iff)

lemma regstate_put_mem_bytes[simp]:
  "regstate (put_mem_bytes addr sz v tag s) = regstate s"
  by (auto simp: put_mem_bytes_def Let_def)

lemma no_reg_writes_trace_regstate_eq:
  assumes "runTraceS ra t s = Some s'" and "no_reg_writes_trace t"
  shows "regstate s' = regstate s"
  using assms
  by (induction t arbitrary: s rule: no_reg_writes_trace.induct) (auto split: bind_splits if_splits)

lemma PrePostE_no_reg_writes:
  assumes m: "runs_no_reg_writes_to UNIV m"
    and pp: "\<And>s0. \<lbrace>\<lambda>s. s0 = s \<and> P s\<rbrace> liftState ra m \<lbrace>\<lambda>a s. regstate s = regstate s0 \<longrightarrow> Q a s \<bar> E\<rbrace>"
  shows "\<lbrace>P\<rbrace> liftState ra m \<lbrace>Q \<bar> E\<rbrace>"
proof (rule PrePostE_I)
  fix s a s'
  assume "P s" and s': "(Value a, s') \<in> liftState ra m s"
  then obtain t where "Run m t a" and t: "runTraceS ra t s = Some s'"
    by (elim Value_liftState_Run_runTraceS)
  then show "Q a s'"
    using \<open>P s\<close> m pp[of s] s' no_reg_writes_trace_regstate_eq[OF t]
    by (elim PrePostE_elim[where s = s and s' = s' and r = "Value a"])
       (auto simp: intro: Run_no_reg_writes_trace)
next
  fix s e s'
  assume "P s" and "(Ex e, s') \<in> liftState ra m s"
  then show "E e s'"
    using pp[of s]
    by (auto elim: PrePostE_elim)
qed

fun no_mem_writes_trace where
  "no_mem_writes_trace (E_write_memt _ _ _ _ _ _ # _) = False"
| "no_mem_writes_trace (E_write_mem _ _ _ _ _ # _) = False"
| "no_mem_writes_trace (_ # t) = no_mem_writes_trace t"
| "no_mem_writes_trace [] = True"

lemma no_mem_writes_trace_iff:
  "no_mem_writes_trace t \<longleftrightarrow>
     (\<forall>wk addr sz data tag s.
        E_write_memt wk addr sz data tag s \<notin> set t \<and>
        E_write_mem wk addr sz data s \<notin> set t)"
  by (induction t rule: no_mem_writes_trace.induct; fastforce)

definition "runs_no_mem_writes m \<equiv> (\<forall>t a. Run m t a \<longrightarrow> no_mem_writes_trace t)"

lemma no_mem_writes_trace_append[simp]:
  "no_mem_writes_trace (t1 @ t2) \<longleftrightarrow> no_mem_writes_trace t1 \<and> no_mem_writes_trace t2"
  by (induction t1 rule: no_mem_writes_trace.induct) auto

lemma runs_no_mem_writes_bind:
  assumes "runs_no_mem_writes m" and "\<And>t a. Run m t a \<Longrightarrow> runs_no_mem_writes (f a)"
  shows "runs_no_mem_writes (bind m f)"
  using assms
  by (fastforce simp: runs_no_mem_writes_def elim!: Run_bindE)

lemmas runs_no_mem_writes_if_split = if_split[of runs_no_mem_writes, THEN iffD2]

lemma no_mem_writes_trace_memstate_eq:
  assumes "runTraceS ra t s = Some s'" and "no_mem_writes_trace t"
  shows "memstate s' = memstate s" and "tagstate s' = tagstate s"
  using assms
  by (induction t arbitrary: s rule: no_mem_writes_trace.induct) (auto split: bind_splits if_splits)

lemma no_reg_mem_writes_state_eq:
  assumes "runTraceS ra t s = Some s'"
    and "no_reg_writes_trace t" and "no_mem_writes_trace t"
  shows "s' = s"
  using assms
  by (intro sequential_state.equality)
     (auto simp: no_reg_writes_trace_regstate_eq no_mem_writes_trace_memstate_eq)

context Cap_Axiom_Automaton
begin

lemma non_mem_no_mem_writes_trace:
  assumes "non_mem_trace t"
  shows "no_mem_writes_trace t"
  using assms
  by (induction t rule: no_mem_writes_trace.induct) auto

lemma non_mem_exp_runs_no_mem_writes:
  assumes "non_mem_exp m"
  shows "runs_no_mem_writes m"
  using assms
  by (auto simp: non_mem_exp_def runs_no_mem_writes_def intro: non_mem_no_mem_writes_trace)

lemma PrePostE_no_writes:
  assumes m: "runs_no_reg_writes_to UNIV m" "runs_no_mem_writes m"
    and pp: "\<And>s0. \<lbrace>\<lambda>s. s0 = s \<and> P s\<rbrace> liftState ra m \<lbrace>\<lambda>a s. s = s0 \<longrightarrow> Q a s \<bar> E\<rbrace>"
  shows "\<lbrace>P\<rbrace> liftState ra m \<lbrace>Q \<bar> E\<rbrace>"
proof (rule PrePostE_I)
  fix s a s'
  assume "P s" and s': "(Value a, s') \<in> liftState ra m s"
  then obtain t where "Run m t a" and t: "runTraceS ra t s = Some s'"
    by (elim Value_liftState_Run_runTraceS)
  then show "Q a s'"
    using \<open>P s\<close> m pp[of s] s' no_reg_mem_writes_state_eq[OF t]
    by (elim PrePostE_elim[where s = s and s' = s' and r = "Value a"])
       (auto simp: runs_no_mem_writes_def intro: Run_no_reg_writes_trace)
next
  fix s e s'
  assume "P s" and "(Ex e, s') \<in> liftState ra m s"
  then show "E e s'"
    using pp[of s]
    by (auto elim: PrePostE_elim)
qed

lemma PrePostE_no_writes_any_runs:
  assumes m: "runs_no_reg_writes_to UNIV m" "runs_no_mem_writes m"
  shows "\<lbrace>P\<rbrace> liftState ra m \<lbrace>\<lambda>_. P \<bar> \<lambda>_ _. True\<rbrace>"
  by (rule PrePostE_no_writes[OF assms]) (auto intro: PrePostE_I)

end

context Morello_Axiom_Automaton
begin

lemma PrePostE_CheckCapability_tagged_unsealed:
  shows "\<lbrace>\<lambda>s. CapIsTagSet c \<and> \<not>CapIsSealed c \<longrightarrow> Q addr s\<rbrace>
           \<lbrakk>CheckCapability c addr sz perms acctype\<rbrakk>\<^sub>S
         \<lbrace>Q \<bar> \<lambda>_ _. True\<rbrace>"
  unfolding CheckCapability_def bind_assoc
  apply (rule PrePostE_no_writes)
    apply (no_reg_writes_toI)
   apply (rule non_mem_exp_runs_no_mem_writes)
  apply (non_mem_expI)
  apply (rule PrePostE_I)
   apply (auto elim!: Value_liftState_Run Run_bindE split: if_splits)
  done

abbreviation "getPCC s \<equiv> bitvector_129_dec_reg (regstate s) ''PCC''"

lemma runs_no_reg_writes_to_AArch64_CheckIllegalState[runs_no_reg_writes_toI, simp]:
  "runs_no_reg_writes_to Rs (AArch64_CheckIllegalState u)"
  by (unfold AArch64_CheckIllegalState_def, no_reg_writes_toI)

lemma runs_no_mem_writes_Mem_read:
  "runs_no_mem_writes (Mem_read desc sz accdesc)"
  unfolding Mem_read_def read_mem_def read_mem_bytes_def maybe_fail_def
  by (auto simp: runs_no_mem_writes_def Run_Read_mem_iff elim!: Run_bindE split: option.splits)

lemma runs_no_mem_writes_AArch64_MemSingle_read:
  "runs_no_mem_writes (AArch64_MemSingle_read addr sz acctype wasaligned)"
  unfolding AArch64_MemSingle_read_def Let_def
  by (intro runs_no_mem_writes_bind runs_no_mem_writes_if_split runs_no_mem_writes_Mem_read
            non_mem_exp_runs_no_mem_writes conjI impI;
      non_mem_expI)

lemma
  shows "\<lbrace>\<lambda>_. True\<rbrace> \<lbrakk>FetchInstr pc\<rbrakk>\<^sub>S \<lbrace>\<lambda>_ s. CapIsTagSet (getPCC s) \<and> \<not>CapIsSealed (getPCC s) \<bar> \<lambda>_ _. True\<rbrace>"
  unfolding FetchInstr_def CheckPCCCapability_def bind_assoc
  unfolding liftState_simp comp_def Let_def
  apply (rule PrePostE_strengthen_pre)
  apply (rule PrePostE_compositeI PrePostE_atomI)+
             apply (rule PrePostE_no_writes_any_runs)
              apply (no_reg_writes_toI)
              apply (rule non_mem_exp_runs_no_mem_writes)
              apply (non_mem_expI)
             apply (rule PrePostE_no_writes_any_runs)
               apply (no_reg_writes_toI)
             apply (rule runs_no_mem_writes_AArch64_MemSingle_read)
              apply (rule PrePostE_CheckCapability_tagged_unsealed)
             apply (rule PrePostE_atomI)
            apply (rule PrePostE_atomI)
           apply (rule PrePostE_no_writes_any_runs)
            apply (no_reg_writes_toI)
           apply (rule non_mem_exp_runs_no_mem_writes)
           apply (non_mem_expI)
          apply (rule PrePostE_no_writes_any_runs)
           apply (no_reg_writes_toI)
          apply (rule non_mem_exp_runs_no_mem_writes)
          apply (non_mem_expI)
         apply (rule PrePostE_compositeI PrePostE_atomI)+
       apply (rule PrePostE_no_writes_any_runs)
        apply (no_reg_writes_toI)
       apply (rule non_mem_exp_runs_no_mem_writes)
       apply (non_mem_expI)
       apply (rule PrePostE_no_writes_any_runs)
       apply (no_reg_writes_toI)
      apply (rule non_mem_exp_runs_no_mem_writes)
      apply (non_mem_expI)
      apply (rule PrePostE_no_writes_any_runs)
      apply (no_reg_writes_toI)
      apply (rule non_mem_exp_runs_no_mem_writes)
      apply (non_mem_expI)
     apply (simp add: PCC_ref_def)
  done

end

end
