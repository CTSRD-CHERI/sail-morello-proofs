theory CHERI_Fetch_Lemmas
  imports CHERI_Mem_Properties "Sail.Hoare" "Sail-T-CHERI.Properties"
begin

(* TODO: Move Register_Accessors from Sail-T-CHERI.Properties to an earlier T-CHERI theory or
   the Sail library. *)

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

abbreviation "runs_preserve_invariant m P \<equiv> \<lbrace>P\<rbrace> m \<lbrace>\<lambda>_ s. P s \<bar> \<lambda>_ _. True\<rbrace>"

lemma runs_preserve_invariant_conjI:
  assumes "runs_preserve_invariant m P" and "runs_preserve_invariant m (\<lambda>s. P s \<longrightarrow> Q s)"
  shows "runs_preserve_invariant m (\<lambda>s. P s \<and> Q s)"
  by (rule PrePostE_conj_conds_consequence[OF assms]) auto

lemma runs_preserve_invariant_imp_conjI:
  assumes "runs_preserve_invariant m (\<lambda>s. P s \<longrightarrow> Q s)"
    and "runs_preserve_invariant m (\<lambda>s. P s \<and> Q s \<longrightarrow> R s)"
  shows "runs_preserve_invariant m (\<lambda>s. P s \<longrightarrow> (Q s \<and> R s))"
  by (rule PrePostE_conj_conds_consequence[OF assms]) auto

abbreviation "runs_establish_invariant m P \<equiv> \<lbrace>\<lambda>_. True\<rbrace> m \<lbrace>\<lambda>_ s. P s \<bar> \<lambda>_ _. True\<rbrace>"

lemma runs_establish_invariant_runs_preserve_invariant:
  "runs_establish_invariant m P \<Longrightarrow> runs_preserve_invariant m P"
  by (auto intro: PrePostE_strengthen_pre)

lemma runs_establish_invariant_bindS_left:
  assumes "runs_establish_invariant m P"
    and "\<And>s a s'. (Value a, s') \<in> m s \<Longrightarrow> runs_preserve_invariant (f a) P"
  shows "runs_establish_invariant (bindS m f) P"
  using assms
  by (intro PrePostE_bindS) auto

lemma runs_establish_invariant_bindS_right:
  assumes "\<And>s a s'. (Value a, s') \<in> m s \<Longrightarrow> runs_establish_invariant (f a) P"
  shows "runs_establish_invariant (bindS m f) P"
  using assms
  by (intro PrePostE_bindS) auto

lemma runs_preserve_invariant_bindS:
  assumes "runs_preserve_invariant m P"
    and "\<And>s a s'. (Value a, s') \<in> m s \<Longrightarrow> P s \<Longrightarrow> P s' \<Longrightarrow> runs_preserve_invariant (f a) P"
  shows "runs_preserve_invariant (bindS m f) P"
  using assms
  apply (auto simp: PrePostE_def PrePost_def elim!: bindS_cases split: result.splits prod.splits)
  subgoal for s s' a' a s''
    apply (erule allE[where x = s])
    apply simp
    apply (erule ballE[where x = "(Value a, s'')"])
     apply (use assms(2)[of a s'' s] in \<open>auto elim: PrePostE_elim[where s = s'']\<close>)
    done
  done

context Register_Accessors
begin

abbreviation liftS where "liftS \<equiv> liftState (read_regval, write_regval)"

(* TODO: Move get_reg_val from CHERI_ISA_State to Register_Accessors *)
definition "reg_inv r P s \<equiv> (\<forall>v. read_regval r (regstate s) = Some v \<longrightarrow> P v)"

lemma runs_establish_reg_inv_write_reg:
  assumes "P (regval_of r v)" and "name r = n"
  shows "runs_establish_invariant (liftS (write_reg r v)) (reg_inv n P)"
  using assms
  by (intro PrePostE_I)
     (auto simp: write_reg_def Value_bindS_iff reg_inv_def read_absorb_write split: option.splits)

lemma runs_preserve_reg_inv_write_reg_other:
  assumes "name r \<noteq> n"
  shows "runs_preserve_invariant (liftS (write_reg r v)) (reg_inv n P)"
  using assms
  by (intro PrePostE_I)
     (auto simp: write_reg_def Value_bindS_iff reg_inv_def read_ignore_write split: option.splits)

lemma runs_preserve_reg_inv_no_reg_writes[simp]:
  assumes "runs_no_reg_writes_to {r} m"
  shows "runs_preserve_invariant (liftS m) (reg_inv r P)"
proof (intro PrePostE_I)
  fix s a s'
  assume s: "reg_inv r P s" and "(Value a, s') \<in> liftS m s"
  then obtain t where "Run m t a" and s': "runTraceS (read_regval, write_regval) t s = Some s'"
    by (elim Value_liftState_Run_runTraceS)
  then have "\<nexists>v. E_write_reg r v \<in> set t"
    using assms
    by (auto simp: runs_no_reg_writes_to_def)
  then have "read_regval r (regstate s') = read_regval r (regstate s)"
    using s'
    by (induction t arbitrary: s;
        fastforce elim!: emitEventS.elims split: bind_splits if_splits simp: read_ignore_write)
  then show "reg_inv r P s'"
    using s
    by (auto simp: reg_inv_def)
qed auto

end

locale Morello_Register_Accessors = Register_Accessors
  where read_regval = get_regval and write_regval = set_regval
begin

fun PCC_regval_inv where
  "PCC_regval_inv (Regval_bitvector_129_dec c) = (CapIsTagSet c \<longrightarrow> \<not>CapIsSealed c)"
| "PCC_regval_inv _ = True"

abbreviation "PCC_inv \<equiv> reg_inv ''PCC'' PCC_regval_inv"

lemma runs_establish_PCC_inv_write_PCC:
  assumes "CapIsTagSet c \<longrightarrow> \<not>CapIsSealed c"
  shows "runs_establish_invariant (write_regS PCC_ref c) PCC_inv"
  unfolding liftState_simp[symmetric]
  using assms
  by (intro runs_establish_reg_inv_write_reg)
     (auto simp: PCC_ref_def regval_of_bitvector_129_dec_def)

(* TODO: Move (and strengthen!) these lemmas in CHERI_Instantiation out of their too narrow context *)
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

lemma runs_establish_PCC_inv_BranchToCapability:
  "runs_establish_invariant (liftS (BranchToCapability c branch_type)) PCC_inv"
  unfolding BranchToCapability_def Let_def bind_assoc liftState_bind comp_def
  apply (rule runs_establish_invariant_bindS_right)
  apply (rule runs_establish_invariant_bindS_right)
  apply (rule runs_establish_invariant_bindS_right)
  apply (rule runs_establish_invariant_bindS_right)
  apply (rule runs_establish_invariant_bindS_right)
  apply (rule runs_establish_invariant_bindS_right)
  apply (rule runs_establish_invariant_bindS_left)
  apply (rule runs_establish_reg_inv_write_reg)
  apply (auto simp: PCC_ref_def BranchTaken_ref_def regval_of_bitvector_129_dec_def Run_BranchAddr_not_CapIsSealed_if elim!: Value_liftState_Run intro: runs_preserve_reg_inv_write_reg_other)
  done

lemma runs_establish_PCC_inv_BranchXToCapability:
  "runs_establish_invariant (liftS (BranchXToCapability c branch_type)) PCC_inv"
  unfolding BranchXToCapability_def Let_def bind_assoc liftState_bind comp_def
  by (intro runs_establish_invariant_bindS_right runs_establish_PCC_inv_BranchToCapability)

lemma
  "runs_preserve_invariant (liftS (decode_BLR_C_C opc Cn)) PCC_inv"
  unfolding decode_BLR_C_C_def execute_BLR_C_C_def
  unfolding Let_def bind_assoc liftState_bind comp_def
  by (intro runs_establish_invariant_runs_preserve_invariant
            runs_establish_invariant_bindS_right
            runs_establish_PCC_inv_BranchXToCapability)

lemma
  "runs_preserve_invariant (liftS (decode_frinti_float_aarch64_instrs_float_arithmetic_round_frint Rd Rn rmode ftype S M)) PCC_inv"
  by auto

end

end
