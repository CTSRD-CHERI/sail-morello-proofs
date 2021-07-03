section \<open>System invariants\<close>

theory Morello_Invariants
  imports CHERI_Mem_Properties "Sail.Hoare"
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
proof (use assms in \<open>induction r m arbitrary: s s' rule: liftState.induct\<close>)
  case (1 ra a)
  then show ?case by (simp)
next
  case (2 ra rk a sz k)
  then show ?case
    by (force elim!: Value_bindS_elim intro: Traces_ConsI)
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

lemma Run_runTraceS_Value_liftState:
  fixes m :: "('regval, 'ex, 'a) monad"
  assumes "Run m t a" and "runTraceS ra t s = Some s'"
  shows "(Value a, s') \<in> liftState ra m s"
  using assms
  by (induction m t "Done a :: ('regval, 'ex, 'a) monad" arbitrary: s rule: Traces.induct;
      fastforce elim!: T.cases split: bind_splits if_splits simp: Value_bindS_iff)+

lemma Value_liftState_iff:
  "(Value a, s') \<in> liftState ra m s \<longleftrightarrow> (\<exists>t. Run m t a \<and> runTraceS ra t s = Some s')"
  by (auto intro: Run_runTraceS_Value_liftState elim: Value_liftState_Run_runTraceS)

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

lemma PrePostE_FetchInstr_pcc_tagged_unsealed:
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

lemma runs_preserve_invariant_conjI_imp:
  assumes "runs_preserve_invariant m P" and "runs_preserve_invariant m (\<lambda>s. P s \<longrightarrow> Q s)"
  shows "runs_preserve_invariant m (\<lambda>s. P s \<and> Q s)"
  by (rule PrePostE_conj_conds_consequence[OF assms]) auto

lemma runs_preserve_invariant_conjI:
  assumes "runs_preserve_invariant m P" and "runs_preserve_invariant m Q"
  shows "runs_preserve_invariant m (\<lambda>s. P s \<and> Q s)"
  using PrePostE_conj_conds[OF assms]
  by auto

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

lemma runs_preserve_invariant_bindS_no_asm:
  assumes "runs_preserve_invariant m P" and "\<And>a. runs_preserve_invariant (f a) P"
  shows "runs_preserve_invariant (bindS m f) P"
  using assms
  by (intro runs_preserve_invariant_bindS)

lemmas runs_preserve_invariant_returnS[intro, simp] =
  PrePostE_returnS[where P = "\<lambda>_. P" and Q = "\<lambda>_ _. True" for P]

lemmas runs_preserve_invariant_read_regS[intro, simp] =
  PrePostE_read_regS[where Q = "\<lambda>_. P" and E = "\<lambda>_ _. True" for P]

lemma runs_preserve_invariant_throwS[simp]:
  "runs_preserve_invariant (throwS ex) P"
  by (rule PrePostE_throwS[THEN PrePostE_strengthen_pre]; auto)

lemma runs_preserve_invariant_assert_expS[simp]:
  "runs_preserve_invariant (assert_expS e msg) P"
  by (rule PrePostE_assert_expS[THEN PrePostE_strengthen_pre]; auto)

lemma runs_preserve_invariant_exitS[simp]:
  "runs_preserve_invariant (exitS u) P"
  by (rule PrePostE_exitS[THEN PrePostE_strengthen_pre]; auto)

lemmas runs_preserve_invariant_if_split =
  if_split[where P = "\<lambda>m. runs_preserve_invariant m inv" for inv, THEN iffD2]

lemmas runs_preserve_invariant_if_split_no_asm =
  if_split_no_asm[where P = "\<lambda>m. runs_preserve_invariant m inv" for inv]

context Register_State
begin

abbreviation liftS where "liftS \<equiv> liftState (get_regval, set_regval)"

definition "reg_inv r P s \<equiv> (\<forall>v. get_reg_val r s = Some v \<longrightarrow> P v)"

lemma runs_establish_reg_inv_write_reg:
  assumes "P (regval_of r v)" and "name r = n"
  shows "runs_establish_invariant (liftS (write_reg r v)) (reg_inv n P)"
  using assms
  by (intro PrePostE_I)
     (auto simp: write_reg_def Value_bindS_iff reg_inv_def read_absorb_write split: option.splits)

lemmas runs_preserve_reg_inv_write_reg =
  runs_establish_reg_inv_write_reg[THEN runs_establish_invariant_runs_preserve_invariant]

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
  then obtain t where "Run m t a" and s': "s_run_trace t s = Some s'"
    by (elim Value_liftState_Run_runTraceS)
  then have "\<nexists>v. E_write_reg r v \<in> set t"
    using assms
    by (auto simp: runs_no_reg_writes_to_def)
  then have "get_reg_val r s' = get_reg_val r s"
    using s'
    by (induction t arbitrary: s;
        fastforce elim!: emitEventS.elims split: bind_splits if_splits simp: read_ignore_write)
  then show "reg_inv r P s'"
    using s
    by (auto simp: reg_inv_def)
qed auto

lemmas runs_preserve_reg_inv_read_reg =
  no_reg_writes_to_read_reg[THEN no_reg_writes_runs_no_reg_writes, THEN runs_preserve_reg_inv_no_reg_writes]

lemma read_modify_write_reg_preserves_reg_inv:
  assumes "\<forall>rv v. of_regval r rv = Some v \<and> P rv \<longrightarrow> P (regval_of r (f v))" and "name r = n"
    and "runs_preserve_invariant (m ()) (reg_inv n P)"
  shows "runs_preserve_invariant (liftS (read_reg r) \<bind>\<^sub>S (\<lambda>v. liftS (write_reg r (f v)) \<bind>\<^sub>S m)) (reg_inv n P)"
  using assms
  by (intro runs_preserve_invariant_bindS runs_preserve_reg_inv_write_reg runs_preserve_reg_inv_read_reg)
     (auto simp: read_reg_def Value_bindS_iff reg_inv_def split: option.splits)

end

locale Morello_Register_Accessors = Register_State
  where get_regval = get_regval and set_regval = set_regval
begin

fun PCC_regval_inv where
  "PCC_regval_inv (Regval_bitvector_129_dec c) = (CapIsTagSet c \<longrightarrow> \<not>CapIsSealed c)"
| "PCC_regval_inv _ = True"

abbreviation "PCC_inv \<equiv> reg_inv ''PCC'' PCC_regval_inv"

definition "EDSCR_inv \<equiv> reg_inv ''EDSCR'' (\<lambda>rv. \<forall>v. rv = Regval_bitvector_32_dec v \<longrightarrow> (ucast v :: 6 word) = 2)"

definition "DCZID_inv \<equiv> reg_inv ''DCZID_EL0'' (\<lambda>rv. \<forall>v. rv = Regval_bitvector_32_dec v \<longrightarrow> (ucast v :: 4 word) = 4)"

lemma runs_establish_PCC_inv_write_PCC:
  assumes "CapIsTagSet c \<longrightarrow> \<not>CapIsSealed c"
  shows "runs_establish_invariant (write_regS PCC_ref c) PCC_inv"
  unfolding liftState_simp[symmetric]
  using assms
  by (intro runs_establish_reg_inv_write_reg)
     (auto simp: PCC_ref_def regval_of_bitvector_129_dec_def)

lemmas runs_preserve_PCC_inv_write_PCC_inv =
  runs_establish_PCC_inv_write_PCC[THEN runs_establish_invariant_runs_preserve_invariant]

lemma runs_preserve_sysreg_invs_write_others[simp]:
  "\<And>v. runs_preserve_invariant (write_regS ThisInstrAbstract_ref v) PCC_inv"
  "\<And>v. runs_preserve_invariant (write_regS PC_ref v) PCC_inv"
  "\<And>v. runs_preserve_invariant (write_regS BranchTaken_ref v) PCC_inv"
  "\<And>v. runs_preserve_invariant (write_regS ThisInstrAbstract_ref v) EDSCR_inv"
  "\<And>v. runs_preserve_invariant (write_regS PC_ref v) EDSCR_inv"
  "\<And>v. runs_preserve_invariant (write_regS BranchTaken_ref v) EDSCR_inv"
  "\<And>v. runs_preserve_invariant (write_regS PCC_ref v) EDSCR_inv"
  "\<And>v. runs_preserve_invariant (write_regS ThisInstrAbstract_ref v) DCZID_inv"
  "\<And>v. runs_preserve_invariant (write_regS PC_ref v) DCZID_inv"
  "\<And>v. runs_preserve_invariant (write_regS BranchTaken_ref v) DCZID_inv"
  "\<And>v. runs_preserve_invariant (write_regS PCC_ref v) DCZID_inv"
  unfolding liftState_simp[symmetric]
  by (auto simp: ThisInstrAbstract_ref_def PC_ref_def PCC_ref_def BranchTaken_ref_def no_reg_writes_runs_no_reg_writes EDSCR_inv_def DCZID_inv_def)

lemma inv_reg_simps[simp]:
  "name EDSCR_ref = ''EDSCR''"
  "\<And>v. regval_of EDSCR_ref v = Regval_bitvector_32_dec v"
  "\<And>rv v. of_regval EDSCR_ref rv = Some v \<longleftrightarrow> rv = Regval_bitvector_32_dec v"
  "name DCZID_EL0_ref = ''DCZID_EL0''"
  "\<And>v. regval_of DCZID_EL0_ref v = Regval_bitvector_32_dec v"
  "\<And>rv v. of_regval DCZID_EL0_ref rv = Some v \<longleftrightarrow> rv = Regval_bitvector_32_dec v"
  by (auto simp: register_defs regval_of_bitvector_32_dec_def elim: bitvector_32_dec_of_regval.elims)

lemmas read_modify_write_regs_preserve_reg_invs =
  read_modify_write_reg_preserves_reg_inv[where r = EDSCR_ref and n = "''EDSCR''", simplified]
  read_modify_write_reg_preserves_reg_inv[where r = DCZID_EL0_ref and n = "''DCZID_EL0''", simplified]

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

lemma branch_cap_instructions_establish_PCC_inv:
  "runs_establish_invariant (liftS (decode_BLR_C_C opc Cn)) PCC_inv"
  "runs_establish_invariant (liftS (decode_BLRR_C_C opc Cn)) PCC_inv"
  "runs_establish_invariant (liftS (decode_BLRS_C_C_C Cm opc Cn)) PCC_inv"
  "runs_establish_invariant (liftS (decode_BR_C_C opc Cn)) PCC_inv"
  "runs_establish_invariant (liftS (decode_BRR_C_C opc Cn)) PCC_inv"
  "runs_establish_invariant (liftS (decode_BRS_C_C_C Cm opc Cn)) PCC_inv"
  "runs_establish_invariant (liftS (decode_LDPBLR_C_C_C opc Cn Ct)) PCC_inv"
  "runs_establish_invariant (liftS (decode_LDPBR_C_C_C opc Cn Ct)) PCC_inv"
  "runs_establish_invariant (liftS (decode_RET_C_C opc Cn)) PCC_inv"
  "runs_establish_invariant (liftS (decode_RETR_C_C opc Cn)) PCC_inv"
  "runs_establish_invariant (liftS (decode_RETS_C_C_C Cm opc Cn)) PCC_inv"
  "runs_establish_invariant (liftS (decode_BR_CI_C imm7 Cn)) PCC_inv"
  "runs_establish_invariant (liftS (decode_BLR_CI_C imm7 Cn)) PCC_inv"
  "runs_establish_invariant (liftS (decode_BX___C opc)) PCC_inv"
  "runs_establish_invariant (liftS (decode_BLRS_C_C opc Cn)) PCC_inv"
  "runs_establish_invariant (liftS (decode_BRS_C_C opc Cn)) PCC_inv"
  "runs_establish_invariant (liftS (decode_RETS_C_C opc Cn)) PCC_inv"
  "runs_establish_invariant (liftS (decode_bra_aarch64_instrs_branch_unconditional_register Rm Rn M A op Z)) PCC_inv"
  "runs_establish_invariant (liftS (decode_reta_aarch64_instrs_branch_unconditional_register Rm Rn M A op Z)) PCC_inv"
  "runs_establish_invariant (liftS (decode_br_aarch64_instrs_branch_unconditional_register Rm Rn M A op Z)) PCC_inv"
  "runs_establish_invariant (liftS (decode_ret_aarch64_instrs_branch_unconditional_register Rm Rn M A op Z)) PCC_inv"
  "runs_establish_invariant (liftS (decode_blra_aarch64_instrs_branch_unconditional_register Rm Rn M A op Z)) PCC_inv"
  "runs_establish_invariant (liftS (decode_blr_aarch64_instrs_branch_unconditional_register Rm Rn M A op Z)) PCC_inv"
  unfolding decode_blr_aarch64_instrs_branch_unconditional_register_def
  unfolding decode_blra_aarch64_instrs_branch_unconditional_register_def
  unfolding decode_ret_aarch64_instrs_branch_unconditional_register_def
  unfolding decode_br_aarch64_instrs_branch_unconditional_register_def
  unfolding decode_reta_aarch64_instrs_branch_unconditional_register_def
  unfolding decode_bra_aarch64_instrs_branch_unconditional_register_def
  unfolding execute_aarch64_instrs_branch_unconditional_register_def
  unfolding decode_RETS_C_C_def execute_RETS_C_C_def
  unfolding decode_BRS_C_C_def execute_BRS_C_C_def
  unfolding decode_BLRS_C_C_def execute_BLRS_C_C_def
  unfolding decode_BX___C_def execute_BX___C_def
  unfolding decode_BLR_CI_C_def execute_BLR_CI_C_def
  unfolding decode_BR_CI_C_def execute_BR_CI_C_def
  unfolding decode_RETS_C_C_C_def execute_RETS_C_C_C_def
  unfolding decode_RETR_C_C_def execute_RETR_C_C_def
  unfolding decode_RET_C_C_def execute_RET_C_C_def
  unfolding decode_LDPBR_C_C_C_def execute_LDPBR_C_C_C_def
  unfolding decode_LDPBLR_C_C_C_def execute_LDPBLR_C_C_C_def
  unfolding decode_BRS_C_C_C_def execute_BRS_C_C_C_def
  unfolding decode_BRR_C_C_def execute_BRR_C_C_def
  unfolding decode_BR_C_C_def execute_BR_C_C_def
  unfolding decode_BLRS_C_C_C_def execute_BLRS_C_C_C_def
  unfolding decode_BLRR_C_C_def execute_BLRR_C_C_def
  unfolding decode_BLR_C_C_def execute_BLR_C_C_def
  unfolding Let_def bind_assoc liftState_bind comp_def
  by (intro runs_establish_invariant_bindS_right runs_establish_PCC_inv_BranchToCapability
            runs_establish_PCC_inv_BranchXToCapability)+

lemmas branch_cap_instructions_preserve_PCC_inv =
  branch_cap_instructions_establish_PCC_inv[THEN runs_establish_invariant_runs_preserve_invariant]

lemmas runs_preserve_invariant_and_boolS =
  PrePostE_and_boolS[where R = P and P = P and Q = "\<lambda>_. P" and E = "\<lambda>_ _. True" for P, simplified]

lemma bitvector_129_dec_of_regval_eq_Some_iff[simp]:
  "bitvector_129_dec_of_regval rv = Some c \<longleftrightarrow> rv = Regval_bitvector_129_dec c"
  by (cases rv; auto)

lemma read_reg_PCC_inv_unsealed[simp]:
  assumes "(Value c, s') \<in> read_regS PCC_ref s" and "PCC_inv s" and "CapIsTagSet c"
  shows "\<not>CapIsSealed c"
  using assms
  unfolding liftState_simp[symmetric] read_reg_def
  by (auto simp: Value_bindS_iff PCC_ref_def reg_inv_def split: option.splits)

lemma CapSetValue_seal_tag:
  assumes "(Value c', s') \<in> liftS (CapSetValue c v) s"
  obtains "CapIsSealed c' \<longleftrightarrow> CapIsSealed c" and "CapIsTagSet c' \<longrightarrow> CapIsTagSet c"
  using assms
  unfolding CapSetValue_def
  by (auto simp: liftState_simp Value_bindS_iff Let_def CapIsSealed_def CapWithTagClear_def update_subrange_vec_dec_test_bit test_bit_set split: if_splits)

lemma CapAdd_seal_tag:
  assumes "(Value c', s') \<in> liftS (CapAdd c v) s"
  obtains "CapIsSealed c' \<longleftrightarrow> CapIsSealed c" and "CapIsTagSet c' \<longrightarrow> CapIsTagSet c"
  using assms
  unfolding CapAdd_def
  by (auto simp: liftState_simp Value_bindS_iff Let_def CapIsSealed_def CapWithTagClear_def update_subrange_vec_dec_test_bit test_bit_set split: if_splits)

lemma BranchAddr_seal_tag:
  assumes "(Value c', s') \<in> liftS (BranchAddr c v) s"
  obtains "CapIsSealed c' \<longleftrightarrow> CapIsSealed c" and "CapIsTagSet c' \<longrightarrow> CapIsTagSet c"
  using assms
  unfolding BranchAddr_def
  by (auto simp: liftState_simp Value_bindS_iff Let_def CapIsSealed_def CapWithTagClear_def update_subrange_vec_dec_test_bit test_bit_set split: if_splits)

lemma runs_preserve_PCC_inv_BranchTo:
  "runs_preserve_invariant (liftS (BranchTo target branch_type)) PCC_inv"
  unfolding BranchTo_def Let_def bind_assoc liftState_simp comp_def
  by (intro runs_preserve_invariant_bindS runs_preserve_invariant_if_split_no_asm runs_preserve_invariant_assert_expS runs_preserve_invariant_read_regS runs_preserve_invariant_and_boolS runs_preserve_PCC_inv_write_PCC_inv)
     (auto simp: no_reg_writes_runs_no_reg_writes elim!: CapSetValue_seal_tag)

lemma runs_preserve_PCC_inv_BranchToOffset:
  "runs_preserve_invariant (liftS (BranchToOffset offset branch_type)) PCC_inv"
  unfolding BranchToOffset_def Let_def bind_assoc liftState_simp comp_def
  by (intro runs_preserve_invariant_bindS runs_preserve_invariant_if_split_no_asm runs_preserve_invariant_assert_expS runs_preserve_invariant_read_regS runs_preserve_invariant_and_boolS runs_preserve_PCC_inv_write_PCC_inv)
     (auto simp: no_reg_writes_runs_no_reg_writes elim!: CapAdd_seal_tag BranchAddr_seal_tag)

lemma runs_preserve_PCC_inv_BranchToAddr:
  "runs_preserve_invariant (liftS (BranchToAddr target branch_type)) PCC_inv"
  unfolding BranchToAddr_def Let_def bind_assoc liftState_simp comp_def
  by (intro runs_preserve_invariant_bindS runs_preserve_invariant_if_split_no_asm runs_preserve_invariant_assert_expS runs_preserve_invariant_read_regS runs_preserve_invariant_and_boolS runs_preserve_PCC_inv_write_PCC_inv)
     (auto simp: no_reg_writes_runs_no_reg_writes elim!: CapSetValue_seal_tag)

lemma branch_int_instructions_preserve_PCC_inv:
  "runs_preserve_invariant (liftS (decode_cbnz_aarch64_instrs_branch_conditional_compare Rt imm19 op sf)) PCC_inv"
  "runs_preserve_invariant (liftS (decode_cbz_aarch64_instrs_branch_conditional_compare Rt imm19 op sf)) PCC_inv"
  "runs_preserve_invariant (liftS (decode_b_cond_aarch64_instrs_branch_conditional_cond cond imm19)) PCC_inv"
  "runs_preserve_invariant (liftS (decode_tbnz_aarch64_instrs_branch_conditional_test Rt imm14 b40 op b5)) PCC_inv"
  "runs_preserve_invariant (liftS (decode_tbz_aarch64_instrs_branch_conditional_test Rt imm14 b40 op b5)) PCC_inv"
  "runs_preserve_invariant (liftS (decode_b_uncond_aarch64_instrs_branch_unconditional_immediate imm26 op)) PCC_inv"
  "runs_preserve_invariant (liftS (decode_bl_aarch64_instrs_branch_unconditional_immediate imm26 op)) PCC_inv"
  unfolding decode_bl_aarch64_instrs_branch_unconditional_immediate_def
  unfolding decode_b_uncond_aarch64_instrs_branch_unconditional_immediate_def
  unfolding execute_aarch64_instrs_branch_unconditional_immediate_def
  unfolding decode_tbz_aarch64_instrs_branch_conditional_test_def
  unfolding decode_tbnz_aarch64_instrs_branch_conditional_test_def
  unfolding execute_aarch64_instrs_branch_conditional_test_def
  unfolding decode_b_cond_aarch64_instrs_branch_conditional_cond_def
  unfolding execute_aarch64_instrs_branch_conditional_cond_def
  unfolding decode_cbz_aarch64_instrs_branch_conditional_compare_def
  unfolding decode_cbnz_aarch64_instrs_branch_conditional_compare_def
  unfolding execute_aarch64_instrs_branch_conditional_compare_def
  unfolding Let_def bind_assoc liftState_simp comp_def
  by (intro runs_preserve_invariant_bindS runs_preserve_invariant_if_split_no_asm runs_preserve_PCC_inv_BranchToOffset runs_preserve_invariant_assert_expS runs_preserve_invariant_returnS runs_preserve_invariant_exitS;
      auto simp: no_reg_writes_runs_no_reg_writes)+

lemma runs_preserve_PCC_inv_AArch64_ExceptionReturn:
  "runs_establish_invariant (liftS (AArch64_ExceptionReturnToCapability target spsr)) PCC_inv"
  unfolding AArch64_ExceptionReturnToCapability_def Let_def bind_assoc liftState_simp comp_def
  by (intro runs_establish_invariant_bindS_right runs_establish_PCC_inv_BranchToCapability)

lemma eret_establishes_PCC_inv:
  "runs_establish_invariant (liftS (decode_eret_aarch64_instrs_branch_unconditional_eret op4 Rn M A)) PCC_inv"
  "runs_establish_invariant (liftS (decode_ereta_aarch64_instrs_branch_unconditional_eret op4 Rn M A)) PCC_inv"
  unfolding decode_ereta_aarch64_instrs_branch_unconditional_eret_def
  unfolding decode_eret_aarch64_instrs_branch_unconditional_eret_def
  unfolding execute_aarch64_instrs_branch_unconditional_eret_def
  unfolding AArch64_ExceptionReturnToCapability_def Let_def bind_assoc liftState_simp comp_def
  by (intro runs_establish_invariant_bindS_right runs_establish_PCC_inv_BranchToCapability)+

lemmas eret_preserves_PCC_inv = eret_establishes_PCC_inv[THEN runs_establish_invariant_runs_preserve_invariant]

lemma ResetControlRegisters_establishes_PCC_inv:
  "runs_establish_invariant (liftS (ResetControlRegisters cold)) PCC_inv"
  unfolding ResetControlRegisters_def bind_assoc liftState_simp comp_def
  by (intro runs_establish_PCC_inv_write_PCC[THEN runs_establish_invariant_bindS_left] runs_establish_invariant_bindS_right)
     (auto simp add: vector_truncate_def CapIsSealed_def CapGetObjectType_def no_reg_writes_runs_no_reg_writes)

lemma AArch64_TakeReset_establishes_PCC_inv:
  "runs_establish_invariant (liftS (AArch64_TakeReset cold)) PCC_inv"
  unfolding AArch64_TakeReset_def AArch64_ResetControlRegisters_def bind_assoc Let_def liftState_bind comp_def
  by (intro ResetControlRegisters_establishes_PCC_inv[THEN runs_establish_invariant_bindS_left] runs_establish_invariant_bindS_right runs_preserve_invariant_bindS runs_preserve_PCC_inv_BranchTo)
     (auto simp: no_reg_writes_runs_no_reg_writes register_defs)

lemma TakeReset_preserves_PCC_inv:
  "runs_preserve_invariant (liftS (TakeReset cold)) PCC_inv"
  unfolding TakeReset_def liftState_bind liftState_if_distrib comp_def
  by (intro runs_preserve_invariant_bindS runs_preserve_invariant_if_split_no_asm AArch64_TakeReset_establishes_PCC_inv[THEN runs_establish_invariant_runs_preserve_invariant])
     (auto simp: no_reg_writes_runs_no_reg_writes register_defs)

lemma AArch64_SysRegWrite_preserves_PCC_inv:
  "runs_preserve_invariant (liftS (AArch64_SysRegWrite op0 op1 crn cr op2 v)) PCC_inv"
  unfolding AArch64_SysRegWrite_def bind_assoc liftState_bind liftState_if_distrib comp_def
  by (auto intro!: runs_preserve_invariant_bindS TakeReset_preserves_PCC_inv simp: no_reg_writes_runs_no_reg_writes)

lemma sys_reg_instrs_preserve_PCC_inv:
  "runs_preserve_invariant (liftS (decode_mrs_aarch64_instrs_system_register_system Rt op2 CRm CRn op1 o0 L)) PCC_inv"
  "runs_preserve_invariant (liftS (decode_msr_reg_aarch64_instrs_system_register_system Rt op2 CRm CRn op1 o0 L)) PCC_inv"
  unfolding decode_msr_reg_aarch64_instrs_system_register_system_def
  unfolding decode_mrs_aarch64_instrs_system_register_system_def
  unfolding execute_aarch64_instrs_system_register_system_def liftState_simp comp_def Let_def
  by (auto intro!: runs_preserve_invariant_bindS AArch64_SysRegWrite_preserves_PCC_inv simp: no_reg_writes_runs_no_reg_writes)

lemma DecodeA64_preserves_PCC_inv:
  "runs_preserve_invariant (liftS (DecodeA64 pc opcode)) PCC_inv"
  by (unfold DecodeA64_def bind_assoc Let_def liftState_simp comp_def; intro runs_preserve_invariant_if_split_no_asm branch_cap_instructions_preserve_PCC_inv branch_int_instructions_preserve_PCC_inv eret_preserves_PCC_inv sys_reg_instrs_preserve_PCC_inv runs_preserve_sysreg_invs_write_others runs_preserve_invariant_bindS runs_preserve_invariant_returnS runs_preserve_invariant_throwS; (simp add: no_reg_writes_runs_no_reg_writes)?)

lemma DecodeExecute_preserves_PCC_inv:
  "runs_preserve_invariant (liftS (DecodeExecute enc opcode)) PCC_inv"
  by (cases enc; auto intro: DecodeA64_preserves_PCC_inv simp: ExecuteA64_def ExecuteA32_def ExecuteT16_def ExecuteT32__1_def no_reg_writes_runs_no_reg_writes)

lemma instr_sem_preserves_PCC_inv:
  "runs_preserve_invariant (liftS (instr_sem instr)) PCC_inv"
  unfolding instr_sem_def TryInstructionExecute_def Let_def liftState_simp prod.case_distrib comp_def
  by (auto intro!: runs_preserve_invariant_bindS DecodeExecute_preserves_PCC_inv runs_preserve_PCC_inv_write_PCC_inv
           elim!: CapAdd_seal_tag simp: no_reg_writes_runs_no_reg_writes CapAdd__1_def)

lemma instr_fetch_preserves_PCC_inv:
  "runs_preserve_invariant (liftS instr_fetch) PCC_inv"
  unfolding instr_fetch_def liftState_simp comp_def
  by (auto intro!: runs_preserve_invariant_bindS)

lemma TakeReset_preserves_EDSCR_inv:
  "runs_preserve_invariant (liftS (TakeReset cold)) EDSCR_inv"
  unfolding TakeReset_def AArch64_TakeReset_def AArch64_ResetControlRegisters_def ResetControlRegisters_def
  unfolding bind_assoc liftState_bind liftState_if_distrib comp_def EDSCR_inv_def
  by (intro read_modify_write_regs_preserve_reg_invs runs_preserve_invariant_bindS runs_preserve_invariant_if_split allI impI conjI)
     (auto simp: no_reg_writes_runs_no_reg_writes register_defs set_slice_def nth_ucast update_subrange_vec_dec_test_bit HighestELUsingAArch32_def intro!: word_eqI)

lemma AArch64_SysRegWrite_preserves_EDSCR_inv:
  "runs_preserve_invariant (liftS (AArch64_SysRegWrite op0 op1 crn cr op2 v)) EDSCR_inv"
  unfolding AArch64_SysRegWrite_def bind_assoc liftState_bind liftState_if_distrib comp_def
  by (intro runs_preserve_invariant_bindS runs_preserve_invariant_if_split_no_asm TakeReset_preserves_EDSCR_inv)
     (auto simp: no_reg_writes_runs_no_reg_writes EDSCR_inv_def)

lemma sys_reg_instrs_preserve_EDSCR_inv:
  "runs_preserve_invariant (liftS (decode_mrs_aarch64_instrs_system_register_system Rt op2 CRm CRn op1 o0 L)) EDSCR_inv"
  "runs_preserve_invariant (liftS (decode_msr_reg_aarch64_instrs_system_register_system Rt op2 CRm CRn op1 o0 L)) EDSCR_inv"
  unfolding decode_msr_reg_aarch64_instrs_system_register_system_def
  unfolding decode_mrs_aarch64_instrs_system_register_system_def
  unfolding execute_aarch64_instrs_system_register_system_def liftState_simp comp_def Let_def
  by (intro runs_preserve_invariant_bindS runs_preserve_invariant_if_split_no_asm AArch64_SysRegWrite_preserves_EDSCR_inv;
      auto simp: no_reg_writes_runs_no_reg_writes EDSCR_inv_def)+

lemma Halted_EDSCR_invE:
  assumes "(Value a, s') \<in> liftS (Halted u) s" and "EDSCR_inv s"
  obtains "\<not>a"
  using assms
  unfolding Halted_def bind_assoc liftState_bind liftState_or_boolM comp_def liftState_return or_boolS_def
  by (auto simp: Value_bindS_iff EDSCR_inv_def reg_inv_def EDSCR_ref_def read_reg_def
           split: if_splits option.splits elim!: bitvector_32_dec_of_regval.elims)

lemma debug_instrs_preserve_EDSCR_inv:
  "runs_preserve_invariant (liftS (decode_dcps1_aarch64_instrs_system_exceptions_debug_exception LL imm16)) EDSCR_inv"
  "runs_preserve_invariant (liftS (decode_dcps2_aarch64_instrs_system_exceptions_debug_exception LL imm16)) EDSCR_inv"
  "runs_preserve_invariant (liftS (decode_dcps3_aarch64_instrs_system_exceptions_debug_exception LL imm16)) EDSCR_inv"
  "runs_preserve_invariant (liftS (decode_drps_aarch64_instrs_branch_unconditional_dret u)) EDSCR_inv"
  unfolding decode_dcps1_aarch64_instrs_system_exceptions_debug_exception_def
  unfolding decode_dcps2_aarch64_instrs_system_exceptions_debug_exception_def
  unfolding decode_dcps3_aarch64_instrs_system_exceptions_debug_exception_def
  unfolding decode_drps_aarch64_instrs_branch_unconditional_dret_def
  unfolding liftState_simp comp_def Let_def or_boolS_def
  by (intro runs_preserve_invariant_bindS runs_preserve_invariant_if_split allI impI conjI;
      auto simp: no_reg_writes_runs_no_reg_writes EDSCR_inv_def Value_bindS_iff split: if_splits elim!: Halted_EDSCR_invE)+

lemma DecodeA64_preserves_EDSCR_inv:
  "runs_preserve_invariant (liftS (DecodeA64 pc opcode)) EDSCR_inv"
  by (unfold DecodeA64_def bind_assoc Let_def liftState_simp comp_def; intro runs_preserve_invariant_if_split_no_asm sys_reg_instrs_preserve_EDSCR_inv debug_instrs_preserve_EDSCR_inv runs_preserve_sysreg_invs_write_others runs_preserve_invariant_bindS runs_preserve_invariant_returnS runs_preserve_invariant_throwS; (simp add: no_reg_writes_runs_no_reg_writes EDSCR_inv_def)?)

lemma DecodeExecute_preserves_EDSCR_inv:
  "runs_preserve_invariant (liftS (DecodeExecute enc opcode)) EDSCR_inv"
  by (cases enc; auto intro: DecodeA64_preserves_EDSCR_inv simp: ExecuteA64_def ExecuteA32_def ExecuteT16_def ExecuteT32__1_def no_reg_writes_runs_no_reg_writes liftState_simp comp_def)

lemma instr_sem_preserves_EDSCR_inv:
  "runs_preserve_invariant (liftS (instr_sem instr)) EDSCR_inv"
  unfolding instr_sem_def TryInstructionExecute_def Let_def liftState_simp prod.case_distrib comp_def
  by (auto intro!: runs_preserve_invariant_bindS DecodeExecute_preserves_EDSCR_inv;
      simp add: no_reg_writes_runs_no_reg_writes EDSCR_inv_def)

lemma instr_fetch_preserves_EDSCR_inv:
  "runs_preserve_invariant (liftS instr_fetch) EDSCR_inv"
  unfolding instr_fetch_def liftState_simp comp_def
  by (auto intro!: runs_preserve_invariant_bindS simp: no_reg_writes_runs_no_reg_writes EDSCR_inv_def)

thm update_subrange_vec_dec_test_bit

lemma ucast_update_subrange_vec_dec_above:
  fixes w :: "'a::len word" and w' :: "'b::len word" and i j :: "int"
  defines "w'' \<equiv> ucast (update_subrange_vec_dec w i j w') :: 'c::len word"
  assumes "0 \<le> j" and "j \<le> i" and "nat i < LENGTH('a)" and "LENGTH('b) = nat (i - j + 1)"
    and "nat j \<ge> LENGTH('c)"
  shows "w'' = ucast w"
  using assms
  by (auto simp: nth_ucast update_subrange_vec_dec_test_bit intro: word_eqI)

lemma ucast_update_subrange_vec_dec_0:
  fixes w :: "'a::len word" and w' :: "'b::len word" and i :: "int"
  defines "w'' \<equiv> ucast (update_subrange_vec_dec w i 0 w') :: 'c::len word"
  assumes "0 \<le> i" and "nat i < LENGTH('a)" and "LENGTH('b) = nat (i + 1)"
    and "LENGTH('c) = nat i + 1"
  shows "w'' = ucast w'"
  using assms
  by (auto simp: nth_ucast update_subrange_vec_dec_test_bit intro: word_eqI)

lemmas ucast_update_subrange_vec_dec_simps = ucast_update_subrange_vec_dec_above ucast_update_subrange_vec_dec_0

lemma AArch64_IMPDEFResets_preserves_DCZID_inv:
  "runs_preserve_invariant (liftS (AArch64_IMPDEFResets u)) DCZID_inv"
  unfolding AArch64_IMPDEFResets_def HasArchVersion_def HaveVirtHostExt_def bind_assoc liftState_bind liftState_if_distrib liftState_return comp_def DCZID_inv_def
  by (intro read_modify_write_regs_preserve_reg_invs runs_preserve_invariant_bindS_no_asm runs_preserve_invariant_if_split_no_asm runs_preserve_reg_inv_read_reg runs_preserve_reg_inv_write_reg_other)
     (auto simp: set_slice_def ucast_update_subrange_vec_dec_simps register_defs no_reg_writes_runs_no_reg_writes)

lemma TakeReset_preserves_DCZID_inv:
  "runs_preserve_invariant (liftS (TakeReset cold)) DCZID_inv"
  unfolding TakeReset_def AArch64_TakeReset_def AArch64_ResetControlRegisters_def ResetControlRegisters_def
  unfolding bind_assoc liftState_bind liftState_if_distrib comp_def
  by (intro AArch64_IMPDEFResets_preserves_DCZID_inv runs_preserve_invariant_bindS_no_asm runs_preserve_invariant_if_split_no_asm)
     (auto simp: DCZID_inv_def no_reg_writes_runs_no_reg_writes register_defs)

lemma sys_reg_instrs_preserve_DCZID_inv:
  "runs_preserve_invariant (liftS (decode_mrs_aarch64_instrs_system_register_system Rt op2 CRm CRn op1 o0 L)) DCZID_inv"
  "runs_preserve_invariant (liftS (decode_msr_reg_aarch64_instrs_system_register_system Rt op2 CRm CRn op1 o0 L)) DCZID_inv"
  unfolding decode_msr_reg_aarch64_instrs_system_register_system_def
  unfolding decode_mrs_aarch64_instrs_system_register_system_def
  unfolding execute_aarch64_instrs_system_register_system_def
  unfolding AArch64_SysRegWrite_def bind_assoc liftState_simp comp_def Let_def
  by (intro runs_preserve_invariant_bindS runs_preserve_invariant_if_split_no_asm TakeReset_preserves_DCZID_inv;
      auto simp: no_reg_writes_runs_no_reg_writes DCZID_inv_def)+

lemma DecodeA64_preserves_DCZID_inv:
  "runs_preserve_invariant (liftS (DecodeA64 pc opcode)) DCZID_inv"
  by (unfold DecodeA64_def bind_assoc Let_def liftState_simp comp_def; intro runs_preserve_invariant_if_split_no_asm sys_reg_instrs_preserve_DCZID_inv runs_preserve_sysreg_invs_write_others runs_preserve_invariant_bindS runs_preserve_invariant_returnS runs_preserve_invariant_throwS; (simp add: no_reg_writes_runs_no_reg_writes DCZID_inv_def)?)

lemma DecodeExecute_preserves_DCZID_inv:
  "runs_preserve_invariant (liftS (DecodeExecute enc opcode)) DCZID_inv"
  by (cases enc; auto intro: DecodeA64_preserves_DCZID_inv simp: ExecuteA64_def ExecuteA32_def ExecuteT16_def ExecuteT32__1_def no_reg_writes_runs_no_reg_writes liftState_simp comp_def)

lemma instr_sem_preserves_DCZID_inv:
  "runs_preserve_invariant (liftS (instr_sem instr)) DCZID_inv"
  unfolding instr_sem_def TryInstructionExecute_def Let_def liftState_simp prod.case_distrib comp_def
  by (auto intro!: runs_preserve_invariant_bindS DecodeExecute_preserves_DCZID_inv runs_preserve_sysreg_invs_write_others;
      simp add: no_reg_writes_runs_no_reg_writes DCZID_inv_def)

lemma instr_fetch_preserves_DCZID_inv:
  "runs_preserve_invariant (liftS instr_fetch) DCZID_inv"
  unfolding instr_fetch_def liftState_simp comp_def
  by (auto intro!: runs_preserve_invariant_bindS simp: no_reg_writes_runs_no_reg_writes DCZID_inv_def)

end

end
