theory Trace_Properties
  imports
    "Sail.Sail2_prompt"
    "HOL-Eisbach.Eisbach_Tools"
begin

(* TODO: Move to library *)

lemma return_Traces_iff: "(return a, t, m) \<in> Traces \<longleftrightarrow> (t = [] \<and> m = Done a)"
  by (auto simp: return_def)

lemma Exception_eq_bind_iff:
  "Exception e = (m \<bind> f) \<longleftrightarrow> (m = Exception e \<or> (\<exists>a. m = Done a \<and> f a = Exception e))"
  by (cases m; auto)

lemma bind_Exception_cases:
  assumes "(m \<bind> f, t, Exception e) \<in> Traces"
  obtains (Left) "(m, t, Exception e) \<in> Traces"
  | (Bind) tm a tf where "Run m tm a" and "(f a, tf, Exception e) \<in> Traces" and "t = tm @ tf"
  using assms
  by (cases rule: bind_Traces_cases) (auto simp: Exception_eq_bind_iff)

lemma bind_Traces_Exception_left:
  assumes "(m, t, Exception e) \<in> Traces"
  shows "(m \<bind> f, t, Exception e) \<in> Traces"
  using assms
  (* by (induction m arbitrary: t) (auto simp: Traces_iff_Cons) *)
  sorry

(* *)

locale Stateful_Full_Trace_Property =
  fixes pred :: "'state \<Rightarrow> 'regval trace \<Rightarrow> bool"
    and update_state :: "'state \<Rightarrow> 'regval trace \<Rightarrow> 'state"
  assumes pred_update_state_append: "\<And>s t1 t2. pred s t1 \<Longrightarrow> pred (update_state s t1) t2 \<Longrightarrow> pred s (t1 @ t2)"
    and update_state_append: "\<And>s t1 t2. update_state s (t1 @ t2) = update_state (update_state s t1) t2"
    and update_state_Nil: "\<And>s. update_state s [] = s"
begin

definition traces_satisfy_pred_from :: "'state \<Rightarrow> ('regval, 'a, 'e) monad \<Rightarrow> bool"
  (* where "traces_satisfy_pred_from s m \<equiv> (\<forall>t m'. (m, t, m') \<in> Traces \<longrightarrow> pred s t)" *)
  where "traces_satisfy_pred_from s m \<equiv> (\<forall>t. hasTrace t m \<longrightarrow> pred s t)"

named_theorems traces_satisfy_pred_fromI
named_theorems traces_satisfy_pred_from_combinatorsI
named_theorems traces_satisfy_pred_from_iff

lemma traces_satisfy_pred_from_bind:
  assumes "traces_satisfy_pred_from s m"
    and "\<And>t a. Run m t a \<Longrightarrow> traces_satisfy_pred_from (update_state s t) (f a)"
  shows "traces_satisfy_pred_from s (m \<bind> f)"
  using assms
  unfolding traces_satisfy_pred_from_def
  (* by (fastforce elim!: bind_Traces_cases  intro: pred_update_state_append) *)
  apply (auto elim!: bind_Traces_cases simp: hasTrace_iff_Traces_final intro: pred_update_state_append)
  sorry

lemma traces_satisfy_pred_from_bind_ignore_left:
  assumes "traces_satisfy_pred_from s m" and "\<And>s a. traces_satisfy_pred_from s (f a)"
  shows "traces_satisfy_pred_from s (m \<bind> f)"
  using assms
  by (blast intro: traces_satisfy_pred_from_bind)

lemma traces_satisfy_pred_from_return_iff[traces_satisfy_pred_from_iff]:
  "traces_satisfy_pred_from s (return a) \<longleftrightarrow> pred s []"
  by (auto simp: traces_satisfy_pred_from_def return_def)

lemmas traces_satisfy_pred_from_return = traces_satisfy_pred_from_return_iff[THEN iffD2]

lemma traces_satisfy_pred_from_Fail_iff[traces_satisfy_pred_from_iff]:
  "traces_satisfy_pred_from s (Fail msg) \<longleftrightarrow> pred s []"
  by (auto simp: traces_satisfy_pred_from_def)

lemmas traces_satisfy_pred_from_Fail = traces_satisfy_pred_from_Fail_iff[THEN iffD2]

lemma Run_traces_satisfy_pred_fromE:
  assumes "Run m t a" and "traces_satisfy_pred_from s m"
  shows "pred s t"
  using assms
  by (auto simp: traces_satisfy_pred_from_def)

lemma traces_satisfy_pred_from_throw_iff[traces_satisfy_pred_from_iff]:
  "traces_satisfy_pred_from s (throw e) \<longleftrightarrow> pred s []"
  by (auto simp: traces_satisfy_pred_from_def throw_def)

lemma traces_satisfy_pred_from_try_catch:
  assumes "traces_satisfy_pred_from s m"
    and "\<And>t e. (m, t, Exception e) \<in> Traces \<Longrightarrow> traces_satisfy_pred_from (update_state s t) (h e)"
  shows "traces_satisfy_pred_from s (try_catch m h)"
  using assms
  unfolding traces_satisfy_pred_from_def
  by (fastforce elim!: try_catch_Traces_cases intro: pred_update_state_append)

lemma traces_satisfy_pred_from_early_return_iff[traces_satisfy_pred_from_iff]:
  "traces_satisfy_pred_from s (early_return a) \<longleftrightarrow> pred s []"
  by (auto simp: early_return_def traces_satisfy_pred_from_throw_iff)

lemma traces_satisfy_pred_from_catch_early_return[traces_satisfy_pred_fromI]:
  assumes "traces_satisfy_pred_from s m"
  shows "traces_satisfy_pred_from s (catch_early_return m)"
  using assms
  unfolding traces_satisfy_pred_from_def catch_early_return_def
  by (auto simp: return_def throw_def split: sum.splits elim!: try_catch_Traces_cases)

lemma traces_satisfy_pred_from_liftR[traces_satisfy_pred_fromI]:
  assumes "traces_satisfy_pred_from s m"
  shows "traces_satisfy_pred_from s (liftR m)"
  using assms
  unfolding traces_satisfy_pred_from_def liftR_def
  by (auto simp: throw_def split: sum.splits elim!: try_catch_Traces_cases)

lemma traces_satisfy_pred_from_try_catchR:
  assumes "traces_satisfy_pred_from s m"
    and "\<And>t e. (m, t, Exception (Inr e)) \<in> Traces \<Longrightarrow> traces_satisfy_pred_from (update_state s t) (h e)"
  shows "traces_satisfy_pred_from s (try_catchR m h)"
  using assms
  unfolding traces_satisfy_pred_from_def try_catchR_def
  by (fastforce elim!: try_catch_Traces_cases split: sum.splits simp: throw_def intro: pred_update_state_append)

lemma traces_satisfy_pred_from_maybe_fail_iff[traces_satisfy_pred_from_iff]:
  "traces_satisfy_pred_from s (maybe_fail msg x) \<longleftrightarrow> pred s []"
  by (auto simp: traces_satisfy_pred_from_def maybe_fail_def return_def split: option.splits)

lemma traces_satisfy_pred_from_assert_exp_iff[traces_satisfy_pred_from_iff]:
  "traces_satisfy_pred_from s (assert_exp e msg) \<longleftrightarrow> pred s []"
  by (auto simp: traces_satisfy_pred_from_def assert_exp_def)

(*lemma Read_reg_Traces_iff: "(Read_reg r k, t, m') \<in> Traces \<longleftrightarrow> (\<exists>v t'. t = E_read_reg r v # t' \<and> (k v, t', m') \<in> Traces) \<or> (t = [] \<and> m' = Read_reg r k)"
  by (auto elim: Traces_cases intro: Traces_ConsI)

abbreviation "trace_characterisation m P \<equiv> (\<forall>t m'. (m, t, m') \<in> Traces \<longleftrightarrow> P t m' \<or> (t = [] \<and> m' = m))"

lemma read_reg_trace_characterisation:
  "trace_characterisation (read_reg r) (\<lambda>t m'. \<exists>rv. t = [E_read_reg (name r) rv] \<and> m' = (maybe_fail ''read_reg: unrecognised value'' (of_regval r rv)))"
  unfolding read_reg_def maybe_fail_def return_def
  by (auto split: option.splits; fastforce intro: Traces_ConsI elim: Traces_cases)

lemma traces_satisfy_pred_from_read_reg:
  "traces_satisfy_pred_from s (read_reg r) \<longleftrightarrow> (\<forall>rv. pred s [E_read_reg (name r) rv]) \<and> pred s []"
  using read_reg_trace_characterisation[of r]
  by (auto simp: traces_satisfy_pred_from_def)*)

definition "primitive_exp m \<equiv> (\<forall>t m'. (m, t, m') \<in> Traces \<longrightarrow> t = [] \<or> final m')"

lemma final_bind_iff:
  "final (m \<bind> f) \<longleftrightarrow> final m \<and> (\<forall>a. m = Done a \<longrightarrow> final (f a))"
  by (cases m) (auto simp: final_def)

lemma final_Traces_Nil:
  assumes "final m" and "(m, t, m') \<in> Traces"
  shows "t = []" and "m' = m"
  using assms
  by (auto simp: final_def split: monad.splits)

lemma primitive_exp_bind_left:
  assumes "primitive_exp m" and f: "\<And>a. final (f a)"
  shows "primitive_exp (m \<bind> f)"
  using assms final_Traces_Nil[OF f]
  by (fastforce simp: primitive_exp_def final_bind_iff elim!: bind_Traces_cases)

(*lemma primitive_exp_read_reg: "primitive_exp (read_reg r)"
  by (auto simp: primitive_exp_def read_reg_def final_def elim: Traces_cases split: option.splits)*)

lemmas builtin_primitive_exp_defs =
  return_def throw_def early_return_def maybe_fail_def assert_exp_def headM_def tailM_def
  read_reg_def write_reg_def choose_regval_def choose_convert_def choose_convert_default_def
  choose_bool_def choose_bit_def choose_int_def choose_real_def choose_string_def
  read_memt_bytes_def read_memt_def read_mem_bytes_def read_mem_def excl_result_def
  write_mem_ea_def write_mem_def write_memt_def barrier_def footprint_def

lemma builtin_primitive_exps:
  "\<And>r. primitive_exp (read_reg r)"
  "\<And>r v. primitive_exp (write_reg r v)"
  "\<And>descr. primitive_exp (choose_regval descr)"
  "\<And>of_rv descr. primitive_exp (choose_convert of_rv descr)"
  "\<And>of_rv x descr. primitive_exp (choose_convert_default of_rv x descr)"
  "\<And>RV descr. primitive_exp (choose_bool RV descr)"
  "\<And>RV descr. primitive_exp (choose_bit RV descr)"
  "\<And>RV descr. primitive_exp (choose_int RV descr)"
  "\<And>RV descr. primitive_exp (choose_real RV descr)"
  "\<And>RV descr. primitive_exp (choose_string RV descr)"
  "\<And>xs. primitive_exp (headM xs)"
  "\<And>xs. primitive_exp (tailM xs)"
  "\<And>BVa BVb rk addr sz. primitive_exp (read_memt_bytes BVa BVb rk addr sz)"
  "\<And>BVa BVb rk addr sz. primitive_exp (read_memt BVa BVb rk addr sz)"
  "\<And>BVa BVb rk addr sz. primitive_exp (read_mem_bytes BVa BVb rk addr sz)"
  "\<And>BVa BVb addr_sz rk addr sz. primitive_exp (read_mem BVa BVb rk addr_sz addr sz)"
  "\<And>BVa addr_sz wk addr sz. primitive_exp (write_mem_ea BVa wk addr_sz addr sz)"
  "\<And>BVa BVb addr_sz wk addr sz v. primitive_exp (write_mem BVa BVb wk addr_sz addr sz v)"
  "\<And>BVa BVb wk addr sz v tag. primitive_exp (write_memt BVa BVb wk addr sz v tag)"
  "\<And>u. primitive_exp (excl_result u)"
  "\<And>bk. primitive_exp (barrier bk)"
  "\<And>u. primitive_exp (footprint u)"
  unfolding builtin_primitive_exp_defs
  by (auto simp: primitive_exp_def final_def elim: Traces_cases
           split: option.splits list.splits (*result.splits*))

lemma runTrace_final_case_simps:
  "runTrace t (Done a) = (case t of [] \<Rightarrow> Some (Done a) | _ \<Rightarrow> None)"
  "runTrace t (Fail msg) = (case t of [] \<Rightarrow> Some (Fail msg) | _ \<Rightarrow> None)"
  "runTrace t (Exception e) = (case t of [] \<Rightarrow> Some (Exception e) | _ \<Rightarrow> None)"
  (* by (auto split: list.splits Option.bind_splits elim: emitEvent_cases) *)
  sorry

lemma builtin_primitive_exps_hasTrace_iffs:
  "\<And>r. hasTrace t (read_reg r) \<longleftrightarrow> (\<exists>rv. t = [E_read_reg (name r) rv])"
  "\<And>r v. hasTrace t (write_reg r v) \<longleftrightarrow> (t = [E_write_reg (name r) (regval_of r v)])"
  "\<And>descr. hasTrace t (choose_regval descr) \<longleftrightarrow> (\<exists>v. t = [E_choose descr v])"
  "\<And>of_rv descr. hasTrace t (choose_convert of_rv descr) \<longleftrightarrow> (\<exists>v. t = [E_choose descr v])"
  "\<And>of_rv x descr. hasTrace t (choose_convert_default of_rv x descr) \<longleftrightarrow> (\<exists>v. t = [E_choose descr v])"
  "\<And>RV descr. hasTrace t (choose_bool RV descr) \<longleftrightarrow> (\<exists>v. t = [E_choose descr v])"
  "\<And>RV descr. hasTrace t (choose_bit RV descr) \<longleftrightarrow> (\<exists>v. t = [E_choose descr v])"
  "\<And>RV descr. hasTrace t (choose_int RV descr) \<longleftrightarrow> (\<exists>v. t = [E_choose descr v])"
  "\<And>RV descr. hasTrace t (choose_real RV descr) \<longleftrightarrow> (\<exists>v. t = [E_choose descr v])"
  "\<And>RV descr. hasTrace t (choose_string RV descr) \<longleftrightarrow> (\<exists>v. t = [E_choose descr v])"
  "\<And>xs. hasTrace t (headM xs) \<longleftrightarrow> (t = [])"
  "\<And>xs. hasTrace t (tailM xs) \<longleftrightarrow> (t = [])"
  (*"\<And>BV req. hasTrace t (sail_mem_read BV req) \<longleftrightarrow> (\<exists>v. t = [E_mem_read_request (mem_read_request_to_bl req) v])"
  "\<And>req. hasTrace t (sail_mem_write req) \<longleftrightarrow> (\<exists>v. t = [E_mem_write_request (mem_write_request_to_bl req) v])"
  "\<And>req. hasTrace t (sail_mem_write_announce_address req) \<longleftrightarrow> (t = [E_mem_write_announce_address req])"
  "\<And>tsi. hasTrace t (sail_translation_start tsi) \<longleftrightarrow> (t = [E_translation_start tsi])"
  "\<And>tei. hasTrace t (sail_translation_end tei) \<longleftrightarrow> (t = [E_translation_end tei])"
  "\<And>BV addr_size addr. hasTrace t (branch_announce BV addr_size addr) \<longleftrightarrow> (t = [E_branch_announce_address (bits_of_method BV addr)])"
  "\<And>f. hasTrace t (sail_take_exception f) \<longleftrightarrow> (t = [E_fault_announce f])"
  "\<And>pa. hasTrace t (sail_return_exception pa) \<longleftrightarrow> (t = [E_eret_announce pa])"
  "\<And>op. hasTrace t (sail_tlbi op) \<longleftrightarrow> (t = [E_tlb_op_request op])"
  "\<And>b. hasTrace t (sail_barrier b) \<longleftrightarrow> (t = [E_barrier_request b])"
  "\<And>c. hasTrace t (sail_cache_op c) \<longleftrightarrow> (t = [E_cache_op_request c])"*)
  unfolding builtin_primitive_exp_defs
  (*by (auto simp: hasTrace_def emitEvent_intros final_def runTrace_final_case_simps
           split: option.splits Option.bind_splits list.splits result.splits
           elim!: runTrace.elims emitEvent_cases)*)
  sorry

lemma primitive_exp_traces_satisfy_pred_from:
  assumes "primitive_exp m"
  shows "traces_satisfy_pred_from s m \<longleftrightarrow> (\<forall>t. hasTrace t m \<longrightarrow> pred s t) \<and> pred s []"
  using assms Traces.Nil[of m]
  unfolding primitive_exp_def traces_satisfy_pred_from_def hasTrace_iff_Traces_final
  by auto

lemmas builtin_primitive_exp_traces_satisfy_pred_from[traces_satisfy_pred_from_iff] =
  builtin_primitive_exps[THEN primitive_exp_traces_satisfy_pred_from,
                         unfolded builtin_primitive_exps_hasTrace_iffs]

(*lemma
  "traces_satisfy_pred_from s (read_reg r) \<longleftrightarrow> (\<forall>rv. pred s [E_read_reg (name r) rv]) \<and> pred s []"
  using primitive_exp_read_reg[of r, THEN primitive_exp_traces_satisfy_pred_from, where s = s]
  unfolding hasTrace_read_reg
  by auto*)

lemma traces_satisfy_pred_from_if_ignore_cond:
  assumes "traces_satisfy_pred_from s m1" and "traces_satisfy_pred_from s m2"
  shows "traces_satisfy_pred_from s (if c then m1 else m2)"
  using assms
  by auto

lemma traces_satisfy_pred_from_if:
  assumes "c \<Longrightarrow> traces_satisfy_pred_from s m1" and "\<not>c \<Longrightarrow> traces_satisfy_pred_from s m2"
  shows "traces_satisfy_pred_from s (if c then m1 else m2)"
  using assms
  by auto

lemma traces_satisfy_pred_from_let[traces_satisfy_pred_fromI]:
  assumes "traces_satisfy_pred_from s (f y)"
  shows "traces_satisfy_pred_from s (let x = y in f x)"
  using assms
  by auto

lemma foreachM_append:
  "foreachM (xs @ ys) vars body = foreachM xs vars body \<bind> (\<lambda>vars'. foreachM ys vars' body)"
  by (induction xs arbitrary: vars) auto

lemma traces_satisfy_pred_from_foreachM_Inv:
  assumes Inv_0: "Inv 0 vars s" and pred_Nil: "pred s []"
    and body: "\<And>idx vars t.
            idx < length xs \<Longrightarrow>
            Inv idx vars (update_state s t) \<Longrightarrow>
            pred s t \<Longrightarrow>
            traces_satisfy_pred_from (update_state s t) (body (xs ! idx) vars)"
    and Inv': "\<And>idx vars t t' vars'.
            idx < length xs \<Longrightarrow>
            Inv idx vars (update_state s t) \<Longrightarrow>
            pred s t \<Longrightarrow>
            Run (body (xs ! idx) vars) t' vars' \<Longrightarrow>
            pred (update_state s t) t' \<Longrightarrow>
            Inv (Suc idx) vars' (update_state (update_state s t) t')"
  shows "traces_satisfy_pred_from s (foreachM xs vars body)"
proof -
  have "traces_satisfy_pred_from s (foreachM (take n xs) vars body)" (is "?pred n")
    and "(\<forall>t vars'. Run (foreachM (take n xs) vars body) t vars' \<longrightarrow> Inv n vars' (update_state s t))"
       (is "?Inv n")
    if "n \<le> length xs" for n
  proof (use that in \<open>induction n\<close>)
    case 0
    from Inv_0 pred_Nil show "?pred 0" and "?Inv 0"
      by (auto simp: traces_satisfy_pred_from_return update_state_Nil return_Traces_iff)
  next
    case (Suc n)
    show pred: "?pred (Suc n)" if n: "Suc n \<le> length xs"
      using Suc n
      by (auto simp: take_Suc_conv_app_nth foreachM_append elim: Run_traces_satisfy_pred_fromE
               intro!: body traces_satisfy_pred_from_bind)
    show "?Inv (Suc n)" if n: "Suc n \<le> length xs"
    proof (intro allI impI)
      fix t vars'
      assume "Run (foreachM (take (Suc n) xs) vars body) t vars'"
      then obtain t1 t2 vars'' where t: "t = t1 @ t2"
        and t1: "Run (foreachM (take n xs) vars body) t1 vars''"
        and t2: "Run (body (xs ! n) vars'') t2 vars'"
        using n
        by (auto simp: take_Suc_conv_app_nth foreachM_append elim!: Run_bindE)
      then show "Inv (Suc n) vars' (update_state s t)"
        using Suc n body[of n vars'' t1]
        using Run_traces_satisfy_pred_fromE[OF t1, of s]
        using Run_traces_satisfy_pred_fromE[OF t2, of "update_state s t1"]
        by (auto simp: update_state_append intro: Inv'[of n vars'' t1 t2 vars'])
    qed
  qed
  from this[of "length xs"] show ?thesis
    by auto
qed

lemma traces_satisfy_pred_from_foreachM:
  assumes "\<And>t x vars'. x \<in> set xs \<Longrightarrow> pred s t \<Longrightarrow> traces_satisfy_pred_from (update_state s t) (body x vars')"
    and "pred s []"
  shows "traces_satisfy_pred_from s (foreachM xs vars body)"
  by (rule traces_satisfy_pred_from_foreachM_Inv[where Inv = "\<lambda>_ _ _. True"]) (use assms in auto)

lemma traces_satisfy_pred_from_untilM_Inv:
  assumes dom: "untilM_dom (vars, cond, body)"
    and Inv: "Inv s vars"
             "\<And>s t vars vars'. Inv s vars \<Longrightarrow> Run (body vars) t vars' \<Longrightarrow> Inv (update_state s t) vars'"
             "\<And>s t vars c. Inv s vars \<Longrightarrow> Run (cond vars) t c \<Longrightarrow> Inv (update_state s t) vars"
    and body: "\<And>s vars. Inv s vars \<Longrightarrow> traces_satisfy_pred_from s (body vars)"
    and cond: "\<And>s vars. Inv s vars \<Longrightarrow> traces_satisfy_pred_from s (cond vars)"
    and pred_Nil: "\<And>s vars. Inv s vars \<Longrightarrow> pred s []"
  shows "traces_satisfy_pred_from s (untilM vars cond body)"
  apply (use Inv body cond pred_Nil in \<open>induction arbitrary: s rule: untilM.pinduct[OF dom]\<close>)
  subgoal premises prems for vars cond body s
    apply (unfold untilM.psimps[OF prems(1)])
    using prems(2-)
    apply (auto intro!: traces_satisfy_pred_from_bind traces_satisfy_pred_from_return)
    apply (blast intro: prems)
    done
  done

lemmas traces_satisfy_pred_from_untilM =
  traces_satisfy_pred_from_untilM_Inv[where Inv = "\<lambda>_ _. True", simplified]

(*lemma traces_satisfy_pred_from_untilMT_aux_Inv:
  assumes Inv: "Inv s vars"
             "\<And>s t vars vars'. Inv s vars \<Longrightarrow> Run (body vars) t vars' \<Longrightarrow> Inv (update_state s t) vars'"
             "\<And>s t vars c. Inv s vars \<Longrightarrow> Run (cond vars) t c \<Longrightarrow> Inv (update_state s t) vars"
    and body: "\<And>s vars. Inv s vars \<Longrightarrow> traces_satisfy_pred_from s (body vars)"
    and cond: "\<And>s vars. Inv s vars \<Longrightarrow> traces_satisfy_pred_from s (cond vars)"
    and pred_Nil: "\<And>s vars. Inv s vars \<Longrightarrow> pred s []"
  shows "traces_satisfy_pred_from s (untilMT_aux limit vars cond body)"
proof (use assms in \<open>induction limit vars cond body arbitrary: s rule: untilMT_aux.induct[case_names Suc 0]\<close>)
  case (Suc limit vars cond body)
  then show ?case
    by (auto intro!: traces_satisfy_pred_from_bind traces_satisfy_pred_from_return traces_satisfy_pred_from_if intro: Suc.prems)
qed (auto intro: traces_satisfy_pred_from_Fail)

lemmas traces_satisfy_pred_from_untilMT_Inv =
  traces_satisfy_pred_from_untilMT_aux_Inv[where vars = vars and limit = "nat \<bar>measure vars + 1\<bar>" for vars measure, folded untilMT_def]

lemmas traces_satisfy_pred_from_untilMT =
  traces_satisfy_pred_from_untilMT_Inv[where Inv = "\<lambda>_ _. True"]*)

lemma traces_satisfy_pred_from_whileM_Inv:
  assumes dom: "whileM_dom (vars, cond, body)"
    and Inv: "Inv s vars"
             "\<And>s t vars vars'. Inv s vars \<Longrightarrow> Run (body vars) t vars' \<Longrightarrow> Inv (update_state s t) vars'"
             "\<And>s t vars c. Inv s vars \<Longrightarrow> Run (cond vars) t c \<Longrightarrow> Inv (update_state s t) vars"
    and body: "\<And>s vars. Inv s vars \<Longrightarrow> traces_satisfy_pred_from s (body vars)"
    and cond: "\<And>s vars. Inv s vars \<Longrightarrow> traces_satisfy_pred_from s (cond vars)"
    and pred_Nil: "\<And>s vars. Inv s vars \<Longrightarrow> pred s []"
  shows "traces_satisfy_pred_from s (whileM vars cond body)"
  apply (use Inv body cond pred_Nil in \<open>induction arbitrary: s rule: whileM.pinduct[OF dom]\<close>)
  subgoal premises prems for vars cond body s
    apply (unfold whileM.psimps[OF prems(1)])
    using prems(2-)
    apply (auto intro!: traces_satisfy_pred_from_bind traces_satisfy_pred_from_return; blast)
    done
  done

lemmas traces_satisfy_pred_from_whileM =
  traces_satisfy_pred_from_whileM_Inv[where Inv = "\<lambda>_ _. True", simplified]

(*lemma traces_satisfy_pred_from_whileMT_aux_Inv:
  assumes Inv: "Inv s vars"
             "\<And>s t vars vars'. Inv s vars \<Longrightarrow> Run (body vars) t vars' \<Longrightarrow> Inv (update_state s t) vars'"
             "\<And>s t vars c. Inv s vars \<Longrightarrow> Run (cond vars) t c \<Longrightarrow> Inv (update_state s t) vars"
    and body: "\<And>s vars. Inv s vars \<Longrightarrow> traces_satisfy_pred_from s (body vars)"
    and cond: "\<And>s vars. Inv s vars \<Longrightarrow> traces_satisfy_pred_from s (cond vars)"
    and pred_Nil: "\<And>s vars. Inv s vars \<Longrightarrow> pred s []"
  shows "traces_satisfy_pred_from s (whileMT_aux limit vars cond body)"
proof (use assms in \<open>induction limit vars cond body arbitrary: s rule: whileMT_aux.induct[case_names Suc 0]\<close>)
  case (Suc limit vars cond body)
  then show ?case
    by (auto intro!: traces_satisfy_pred_from_bind traces_satisfy_pred_from_return; blast)
qed (auto intro: traces_satisfy_pred_from_Fail)

lemmas traces_satisfy_pred_from_whileMT_Inv =
  traces_satisfy_pred_from_whileMT_aux_Inv[where vars = vars and limit = "nat \<bar>measure vars + 1\<bar>" for vars measure, folded whileMT_def]

lemmas traces_satisfy_pred_from_whileMT =
  traces_satisfy_pred_from_whileMT_Inv[where Inv = "\<lambda>_ _. True"]*)

lemmas traces_satisfy_pred_from_builtin_combinators =
  traces_satisfy_pred_from_bind traces_satisfy_pred_from_try_catch traces_satisfy_pred_from_try_catchR
  traces_satisfy_pred_from_if traces_satisfy_pred_from_foreachM
  traces_satisfy_pred_from_untilM traces_satisfy_pred_from_whileM
  (* traces_satisfy_pred_from_untilMT traces_satisfy_pred_from_whileMT *)

end

locale Stateless_Full_Trace_Property =
  fixes pred :: "'regval trace \<Rightarrow> bool"
  assumes pred_append: "\<And>t1 t2. pred t1 \<Longrightarrow> pred t2 \<Longrightarrow> pred (t1 @ t2)"
begin

sublocale Stateful_Full_Trace_Property where pred = "\<lambda>_ t. pred t" and update_state = "\<lambda>_ _. ()"
  using pred_append
  by unfold_locales auto

abbreviation "traces_satisfy_pred \<equiv> traces_satisfy_pred_from ()"

end

end
