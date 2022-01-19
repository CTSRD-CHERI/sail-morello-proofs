section \<open>System invariants\<close>

theory State_Invariants
  imports "Sail-T-CHERI.Trace_Assumptions" (*CHERI_Mem_Properties*) "Sail.Hoare"
begin

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
  shows "\<lbrace>P\<rbrace> (liftState ra m) \<lbrace>Q \<bar> \<lambda>_ _. True\<rbrace>"
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

(*context Cap_Axiom_Automaton
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

end*)

abbreviation "runs_preserve_invariant m P \<equiv> \<lbrace>P\<rbrace> m \<lbrace>\<lambda>_ s. P s \<bar> \<lambda>_ _. True\<rbrace>"

named_theorems runs_preserve_invariantI
named_theorems runs_preserve_invariant_split

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

lemma runs_preserve_invariant_bindS[runs_preserve_invariantI]:
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

lemmas runs_preserve_invariant_returnS[runs_preserve_invariantI, intro, simp] =
  PrePostE_returnS[where P = "\<lambda>_. P" and Q = "\<lambda>_ _. True" for P]

lemmas runs_preserve_invariant_read_regS[runs_preserve_invariantI, intro, simp] =
  PrePostE_read_regS[where Q = "\<lambda>_. P" and E = "\<lambda>_ _. True" for P]

lemma runs_preserve_invariant_throwS[runs_preserve_invariantI, simp]:
  "runs_preserve_invariant (throwS ex) P"
  by (rule PrePostE_throwS[THEN PrePostE_strengthen_pre]; auto)

lemma runs_preserve_invariant_assert_expS[runs_preserve_invariantI, simp]:
  "runs_preserve_invariant (assert_expS e msg) P"
  by (rule PrePostE_assert_expS[THEN PrePostE_strengthen_pre]; auto)

lemma runs_preserve_invariant_exitS[runs_preserve_invariantI, simp]:
  "runs_preserve_invariant (exitS u) P"
  by (rule PrePostE_exitS[THEN PrePostE_strengthen_pre]; auto)

lemmas runs_preserve_invariant_if_split[runs_preserve_invariant_split] =
  if_split[where P = "\<lambda>m. runs_preserve_invariant m inv" for inv, THEN iffD2]

lemmas runs_preserve_invariant_foreachS[runs_preserve_invariantI] =
  PrePostE_foreachS_invariant[where Q = "\<lambda>_. P" and E = "\<lambda>_ _. True" for P]

lemmas runs_preserve_invariant_and_boolS[runs_preserve_invariantI] =
  PrePostE_and_boolS[where P = P and Q = "\<lambda>_. P" and R = P and E = "\<lambda>_ _. True" for P, simplified]
lemmas runs_preserve_invariant_or_boolS[runs_preserve_invariantI] =
  PrePostE_or_boolS[where P = P and Q = "\<lambda>_. P" and R = P and E = "\<lambda>_ _. True" for P, simplified]

(* TODO: Move *)
lemma if_split_no_asm: "P x \<Longrightarrow> P y \<Longrightarrow> P (if b then x else y)"
  by auto

lemma liftState_let[liftState_simp]: "liftState ra (let x = y in f x) = (let x = y in liftState ra (f x))"
  by simp

(* lemmas liftState_comp[liftState_simp] = comp_def[where f = "liftState ra" for ra] *)

lemmas runs_preserve_invariant_if_split_no_asm =
  if_split_no_asm[where P = "\<lambda>m. runs_preserve_invariant m inv" for inv]

(* TOD: Move *)
lemmas listState_prod_case_distrib[liftState_simp] = prod.case_distrib[where h = "liftState ra" for ra]

lemma Value_read_regS_iff: "(Value a, s') \<in> read_regS r s \<longleftrightarrow> (read_from r (regstate s) = a \<and> s' = s)"
  by (auto simp: read_regS_def)

lemma Value_and_boolS_elim:
  assumes "(Value a, s') \<in> and_boolS l r s"
  obtains (Left) "(Value False, s') \<in> l s" and "\<not>a"
  | (Right) s'' where "(Value True, s'') \<in> l s" and "(Value a, s') \<in> r s''"
  using assms
  by (auto simp: and_boolS_def elim: Value_bindS_elim split: if_splits)

lemma Value_or_boolS_elim:
  assumes "(Value a, s') \<in> or_boolS l r s"
  obtains (Left) "(Value True, s') \<in> l s" and "a"
  | (Right) s'' where "(Value False, s'') \<in> l s" and "(Value a, s') \<in> r s''"
  using assms
  by (auto simp: or_boolS_def elim: Value_bindS_elim split: if_splits)

lemma no_reg_writes_to_union:
  "no_reg_writes_to (Rs \<union> Rs') m \<longleftrightarrow> no_reg_writes_to Rs m \<and> no_reg_writes_to Rs' m"
  by (auto simp: no_reg_writes_to_def)

lemma no_reg_writes_to_insert:
  "no_reg_writes_to (insert r Rs) m \<longleftrightarrow> no_reg_writes_to {r} m \<and> no_reg_writes_to Rs m"
  by (auto simp: no_reg_writes_to_def)

lemma no_reg_writes_to_mono:
  assumes "no_reg_writes_to Rs m" and "Rs' \<subseteq> Rs"
  shows "no_reg_writes_to Rs' m"
  using assms
  by (auto simp: no_reg_writes_to_def)

lemmas runs_preserve_invariant_prod_split[runs_preserve_invariant_split] =
  prod.split[where P = "\<lambda>m. runs_preserve_invariant m P" for P, THEN iffD2]

context Register_State
begin

definition "reg_inv r P s \<equiv> (\<forall>v. get_reg_val r s = Some v \<longrightarrow> P v)"

lemma runs_establish_reg_inv_write_reg:
  assumes "P (regval_of r v)" and "name r = n"
  shows "runs_establish_invariant (liftState (get_regval, set_regval) (write_reg r v)) (reg_inv n P)"
  using assms
  by (intro PrePostE_I)
     (auto simp: write_reg_def Value_bindS_iff reg_inv_def read_absorb_write split: option.splits)

lemmas runs_preserve_reg_inv_write_reg =
  runs_establish_reg_inv_write_reg[THEN runs_establish_invariant_runs_preserve_invariant]

lemma runs_preserve_reg_inv_write_reg_other:
  assumes "name r \<noteq> n"
  shows "runs_preserve_invariant (liftState (get_regval, set_regval) (write_reg r v)) (reg_inv n P)"
  using assms
  by (intro PrePostE_I)
     (auto simp: write_reg_def Value_bindS_iff reg_inv_def read_ignore_write split: option.splits)

lemma runs_no_reg_writes_to_get_regval_eq:
  assumes "(Value a, s') \<in> liftState (get_regval, set_regval) m s" and "runs_no_reg_writes_to {r} m"
  shows "get_reg_val r s' = get_reg_val r s"
proof -
  from assms(1) obtain t where "Run m t a" and s': "s_run_trace t s = Some s'"
    by (elim Value_liftState_Run_runTraceS)
  with assms(2) have "\<nexists>v. E_write_reg r v \<in> set t"
    by (auto simp: runs_no_reg_writes_to_def)
  then show ?thesis
    using s'
    by (induction t arbitrary: s;
        fastforce elim!: emitEventS.elims split: bind_splits if_splits simp: read_ignore_write)
qed

lemma runs_no_reg_writes_to_reg_inv_iff:
  assumes "(Value a, s') \<in> liftState (get_regval, set_regval) m s" and "runs_no_reg_writes_to {r} m"
  shows "reg_inv r P s' = reg_inv r P s"
  using runs_no_reg_writes_to_get_regval_eq[OF assms]
  by (auto simp: reg_inv_def)

lemma runs_preserve_reg_inv_no_reg_writes[simp]:
  assumes "runs_no_reg_writes_to {r} m"
  shows "runs_preserve_invariant (liftState (get_regval, set_regval) m) (reg_inv r P)"
  using assms
  by (intro PrePostE_I) (auto dest: runs_no_reg_writes_to_reg_inv_iff)

lemmas runs_preserve_reg_inv_read_reg =
  no_reg_writes_to_read_reg[THEN no_reg_writes_runs_no_reg_writes, THEN runs_preserve_reg_inv_no_reg_writes]

lemma read_modify_write_reg_preserves_reg_inv:
  assumes "\<forall>rv v. of_regval r rv = Some v \<and> P rv \<longrightarrow> P (regval_of r (f v))" and "name r = n"
    and "runs_preserve_invariant (m ()) (reg_inv n P)"
  shows "runs_preserve_invariant (liftState (get_regval, set_regval) (read_reg r) \<bind>\<^sub>S (\<lambda>v. liftState (get_regval, set_regval) (write_reg r (f v)) \<bind>\<^sub>S m)) (reg_inv n P)"
  using assms
  by (intro runs_preserve_invariant_bindS runs_preserve_reg_inv_write_reg runs_preserve_reg_inv_read_reg)
     (auto simp: read_reg_def Value_bindS_iff reg_inv_def split: option.splits)

method preserves_invariant_step uses intro elim simp =
  (rule intro allI impI conjI
    | erule elim TrueE
    | rule runs_preserve_invariantI TrueI
    | rule runs_preserve_invariant_split TrueI)

end

end
