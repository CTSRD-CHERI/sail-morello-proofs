theory VM_Inst
  imports
    "CHERI_Instantiation"
begin

ML \<open>
structure Let_Atom = struct

fun is_atom t = is_Bound t orelse is_Const t orelse is_Var t orelse is_Free t

fun is_atom_eq t = case try HOLogic.dest_eq t of
    SOME (x, y) => is_atom x andalso is_atom y
  | _ => false

val let_atom_simproc = Simplifier.make_simproc @{context} "let_atom"
  {lhss = [@{term "Let x f"}, @{term "Abbrev (x = y)"}], proc = fn _ => fn _ => fn ct => let
    val t = Thm.term_of ct
    val (f, xs) = strip_comb t
    val f_nm = try (dest_Const #> fst) f
  in
    if f_nm = SOME @{const_name Let} andalso length xs = 2 andalso is_atom (hd xs)
    then SOME (@{thm Let_def})
    else if f_nm = SOME @{const_name Abbrev} andalso is_atom_eq (hd xs)
    then SOME (@{thm Abbrev_def})
    else NONE
  end}

fun tac ctxt = simp_tac (put_simpset HOL_basic_ss ctxt addsimprocs [let_atom_simproc])

fun method ctxt = Method.SIMPLE_METHOD (CHANGED (tac ctxt 1))

end
\<close>

method_setup let_atom = \<open>Scan.succeed (Let_Atom.method)\<close>

fun(sequential)
  read_const_regs :: "(string set \<times> (string \<Rightarrow> register_value option)) \<Rightarrow> register_value event \<Rightarrow> bool"
where
    "read_const_regs cfg (E_read_reg nm rv) = (if nm \<in> fst cfg 
        then (snd cfg nm = Some rv) else True)"
  | "read_const_regs el ev = True"

definition
  "const_regs_translate cfg = read_const_regs
    ({''PSTATE'', ''SCR_EL3'', ''HCR_EL2'', ''TCR_EL1'', ''TCR_EL2'', ''TCR_EL3'',
        ''SCTLR_EL1'', ''SCTLR_EL2'', ''SCTLR_EL3'', ''TTBR0_EL3'', ''TTBR0_EL2'',
        ''TTBR0_EL1'', ''TTBR1_EL1'', ''TTBR1_EL2'', ''VTCR_EL2'', ''VTTBR_EL2'',
        ''MAIR_EL1'', ''MAIR_EL2'', ''MAIR_EL3'',
        ''MPAM3_EL3'', ''_MPAM2_EL2_0_62'', ''_MPAM1_EL1_0_62'',
        ''MPAM0_EL1'', ''MPAMIDR_EL1'', ''MPAMVPMV_EL2'',
        ''MPAMVPM0_EL2'', ''MPAMVPM1_EL2'', ''MPAMVPM2_EL2'', ''MPAMVPM3_EL2'',
        ''MPAMVPM4_EL2'', ''MPAMVPM5_EL2'', ''MPAMVPM6_EL2'', ''MPAMVPM7_EL2'',
        ''MPAMHCR_EL2''}, cfg)"

definition
  "translate_address_concrete cfg vaddr =
    (if vaddr < 2 ^ 64
    then let res = monad_result_of (const_regs_translate cfg)
        (AArch64_FullTranslateWithTag (of_nat vaddr) AccType_NORMAL False True 1 False)
     in (if IsFault res then None else Some (unat (AddressDescriptor_vaddress res)))
    else None)"

abbreviation(input)
  "no_exception m \<equiv> (\<forall>tr e. (m, tr, Exception e) \<notin> Traces)"

abbreviation(input)
  "monad_semideterm assms m P \<equiv> monad_return_rel assms m m P (=)"

named_theorems no_exception

declare undefined_bitvector_exception[no_exception]

named_theorems monad_return_rel

named_theorems monad_return_rel_unfold

(* giving this a name helps some automation. we definitely know
   that we don't know the relation between these vars *)
definition
  unknown :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
where
  "unknown a b = True"

lemma monad_return_rel_unknown:
  "no_exception f \<Longrightarrow> monad_return_rel assms f f unknown E"
  apply (rule monad_return_rel_rel_weaken[where E=E], rule monad_return_rel_triv, simp_all)
  apply (auto simp add: unknown_def)
  done

lemma unknown_tupleD:
  "unknown (a, b) (c, d) \<Longrightarrow> unknown a c \<and> unknown b d"
  by (simp add: unknown_def)

(* this is more silly, avoiding "False" appearing in unification
   candidates gets away from an annoying capture scenario *)
definition
  impossible :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
where
  "impossible a b = False"

lemmas monad_return_rel_impossible =
    FalseE[where P="monad_return_rel assms f g impossible E" for assms f g E]

lemma impossibleE:
  "impossible a b \<Longrightarrow> P"
  by (simp add: impossible_def)

(* this one is mostly to make rels easier to type *)
definition
  known_unknown_rel :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'c \<Rightarrow> 'c \<Rightarrow> bool"
where
  "known_unknown_rel f x y = (\<exists>known unknown_l unknown_r. x = f known unknown_l \<and> y = f known unknown_r)"

lemma known_unknown_relE:
  "known_unknown_rel f x y \<Longrightarrow>
    (\<And> k u_x u_y. unknown u_x u_y \<Longrightarrow> x = f k u_x \<Longrightarrow> y = f k u_y \<Longrightarrow> P) \<Longrightarrow>
    P"
  by (clarsimp simp: known_unknown_rel_def unknown_def)

lemma undefined_bool_exception[no_exception]:
  "no_exception (undefined_bool s)"
  by (clarsimp simp: undefined_bool_def choose_bool_def dest!: Choose_exception)

lemmas monad_return_rel_undefined_bool[monad_return_rel] =
    monad_return_rel_unknown[where f="undefined_bool _",
        simplified undefined_bool_exception, simplified]

lemma undefined_int_exception[no_exception]:
  "no_exception (undefined_int s)"
  by (auto simp: undefined_int_def Let_def no_exception
          dest!: bind_Traces_final_cases)

lemmas monad_return_rel_undefined_int[monad_return_rel] =
    monad_return_rel_unknown[where f="undefined_int _",
        simplified undefined_int_exception, simplified]

ML \<open>
fun dest_unknown (Const (@{const_name unknown}, _) $ x $ y) = (x, y)
  | dest_unknown t = raise TERM ("dest_unknown", [t])

fun conv_schem_apps (Abs (nm, T, t)) = Abs (nm, T, conv_schem_apps t)
  | conv_schem_apps (f $ x) = if is_Var (head_of f)
    then Free ("schem_app", fastype_of (f $ x))
    else conv_schem_apps f $ conv_schem_apps x
  | conv_schem_apps t = t

fun drop_unknown_tac ctxt = SUBGOAL (fn (t, i) => let
    val concl = Logic.strip_assums_concl t
    val concl_bvars = loose_bnos (conv_schem_apps concl) |> Inttab.make_set
    fun can_drop_atom (Bound i) = not (Inttab.defined concl_bvars i)
      | can_drop_atom _ = false
    fun can_drop_unknown t = let
        val (x, y) = dest_unknown (HOLogic.dest_Trueprop t)
      in can_drop_atom x andalso can_drop_atom y end
        handle TERM _ => false
  in filter_prems_tac ctxt (not o can_drop_unknown) i end)
\<close>

method_setup drop_unknown = \<open>Scan.succeed () >> (fn _ => fn ctxt =>
    (Method.SIMPLE_METHOD (drop_unknown_tac ctxt 1)))\<close>

lemma genlistM_exception:
  "(\<And>i. i < n \<Longrightarrow> no_exception (f i)) \<Longrightarrow> no_exception (genlistM f n)"
  apply (clarsimp simp add: genlistM_def genlist_def)
  apply (subst(asm) foreachM_no_exception, simp_all)
  apply (auto dest!: bind_Traces_final_cases)
  done

lemma choose_bool_exception[no_exception]:
  "no_exception (choose_bool s)"
  by (auto simp: choose_bool_def dest!: Choose_exception)

lemma choose_bools_exception[no_exception]:
  "no_exception (choose_bools s n)"
  by (auto simp: choose_bools_def simp: no_exception intro!: genlistM_exception)

lemma internal_pick_exception[no_exception]:
  "no_exception (internal_pick xs)"
  by (auto simp: internal_pick_def chooseM_def no_exception
    dest!: bind_Traces_final_cases
    split: option.split_asm)

lemma undefined_AccType_exception[no_exception]:
  "no_exception (undefined_AccType s)"
  by (auto simp: undefined_AccType_def no_exception)

lemma undefined_Fault_exception[no_exception]:
  "no_exception (undefined_Fault s)"
  by (auto simp: undefined_Fault_def no_exception)

lemma undefined_FaultRecord_exception[no_exception]:
  "no_exception (undefined_FaultRecord s)"
  by (auto simp: undefined_FaultRecord_def no_exception
          dest!: bind_Traces_final_cases)

lemmas monad_return_rel_undefined_FaultRecord[monad_return_rel] =
    monad_return_rel_unknown[where f="undefined_FaultRecord s", simplified no_exception, simplified]

lemma bind_no_exception_right:
  "no_exception f \<Longrightarrow> ((bind f g, tr, Exception e) \<in> Traces) =
    (\<exists>tra trb x. tr = tra @ trb \<and> Run f tra x \<and> (g x, trb, Exception e) \<in> Traces)"
  by (auto elim: Traces_bindI dest!: bind_Traces_final_cases)

lemmas def_to_exception = ssubst[where P="no_exception"]

lemmas undefined_MemType_exception[no_exception] =
    undefined_MemType_def[THEN def_to_exception, simplified no_exception, simplified]

lemmas undefined_DeviceType_exception[no_exception] =
    undefined_DeviceType_def[THEN def_to_exception, simplified no_exception, simplified]

lemmas monad_return_rel_undefined_DeviceType [monad_return_rel] =
    undefined_DeviceType_exception[THEN monad_return_rel_unknown]

lemmas undefined_MemAttrHints_exception[no_exception] =
    undefined_MemAttrHints_def[THEN def_to_exception, simplified no_exception bind_no_exception_right simp_thms, simplified]

lemmas monad_return_rel_undefined_MemAttrHints[monad_return_rel] =
    undefined_MemAttrHints_exception[THEN monad_return_rel_unknown]

lemmas undefined_FullAddress_exception[no_exception] =
    undefined_FullAddress_def[THEN def_to_exception, simplified no_exception bind_no_exception_right simp_thms, simplified]

lemmas undefined_MemoryAttributes_exception[no_exception] =
    undefined_MemoryAttributes_def[THEN def_to_exception, simplified no_exception bind_no_exception_right simp_thms, simplified]

lemmas monad_return_rel_undefined_MemoryAttributes[monad_return_rel] =
    undefined_MemoryAttributes_exception[THEN monad_return_rel_unknown]

lemmas undefined_MPAMinfo_exception[no_exception] =
    undefined_MPAMinfo_def[THEN def_to_exception, simplified no_exception bind_no_exception_right simp_thms, simplified]

lemmas monad_return_rel_undefined_MPAMinfo [monad_return_rel] =
    undefined_MPAMinfo_exception[THEN monad_return_rel_unknown]

lemmas undefined_AccessDescriptor_exception[no_exception] =
    undefined_AccessDescriptor_def[THEN def_to_exception, simplified no_exception bind_no_exception_right simp_thms, simplified]

lemmas monad_return_rel_undefined_AccessDescriptor[monad_return_rel] =
    undefined_AccessDescriptor_exception[THEN monad_return_rel_unknown]

lemmas undefined_AddressDescriptor_exception[no_exception] =
    undefined_AddressDescriptor_def[THEN def_to_exception, simplified no_exception bind_no_exception_right simp_thms, simplified]

lemmas monad_return_rel_undefined_AddressDescriptor[monad_return_rel] =
    undefined_AddressDescriptor_exception[THEN monad_return_rel_unknown]

lemmas undefined_Permissions_exception[no_exception] =
    undefined_Permissions_def[THEN def_to_exception, simplified no_exception bind_no_exception_right simp_thms, simplified]

lemmas undefined_DescriptorUpdate_exception[no_exception] =
    undefined_DescriptorUpdate_def[THEN def_to_exception, simplified no_exception bind_no_exception_right simp_thms, simplified]

lemmas undefined_TLBRecord_exception[no_exception] =
    undefined_TLBRecord_def[THEN def_to_exception, simplified no_exception bind_no_exception_right simp_thms, simplified]

lemmas monad_return_rel_undefined_TLBRecord[monad_return_rel] =
    undefined_TLBRecord_exception[THEN monad_return_rel_unknown]

lemmas undefined_Constraint_exception[no_exception] =
    undefined_Constraint_def[THEN def_to_exception, simplified no_exception bind_no_exception_right simp_thms, simplified]

lemmas monad_return_rel_undefined_Constraint[monad_return_rel] =
    undefined_Constraint_exception[THEN monad_return_rel_unknown]


(*
template for the above

lemmas _exception[no_exception] =
    _def[THEN def_to_exception, simplified no_exception bind_no_exception_right simp_thms, simplified]

lemmas monad_return_rel_ [monad_return_rel] =
    _exception[THEN monad_return_rel_unknown]
*)

lemmas monad_return_rel_undefined_bitvector_unknown =
    monad_return_rel_unknown[where f="undefined_bitvector _",
        simplified undefined_bitvector_exception, simplified]

lemma read_reg_exception[no_exception, simp]:
  "no_exception (read_reg r)"
  apply (auto simp: read_reg_def)
  apply (erule Traces.cases; auto elim!: T.cases split: option.split_asm)
  done

lemma read_reg_monad_return_rel:
  "name r \<in> fst cfg \<Longrightarrow> monad_determ (read_const_regs cfg) (read_reg r)"
  by (auto simp add: monad_return_rel_def elim!: Run_read_regE split: monad.split)

lemma monad_return_rel_throw:
  "E x y \<Longrightarrow> monad_return_rel assms (throw x) (throw y) R E"
  by (simp add: monad_return_rel_def)

definition
  rel_min :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
where
  "rel_min P Q x y = (P x y \<or> Q x y)"

lemma rel_min_simp[simp]:
  "rel_min P P = P"
  "rel_min P (rel_min P Q) = rel_min P Q"
  "rel_min P (rel_min Q R) = rel_min Q (rel_min P R)"
  "rel_min P impossible = P"
  "rel_min impossible P = P"
  "rel_min unknown P = unknown"
  "rel_min P unknown = unknown"
  by (auto simp add: fun_eq_iff rel_min_def unknown_def impossible_def)

lemma monad_return_rel_if_P:
  "G = G' \<Longrightarrow> (G \<Longrightarrow> monad_return_rel assms f f' P1 E)
    \<Longrightarrow> (\<not> G \<Longrightarrow> monad_return_rel assms g g' P2 E)
    \<Longrightarrow> monad_return_rel assms (If G f g) (If G' f' g') (If G' P1 P2) E"
  by simp

lemma monad_return_rel_if_rel_min[monad_return_rel]:
  "G = G' \<Longrightarrow> (G \<Longrightarrow> monad_return_rel assms f f' P1 E)
    \<Longrightarrow> (\<not> G \<Longrightarrow> monad_return_rel assms g g' P2 E)
    \<Longrightarrow> monad_return_rel assms (If G f g) (If G' f' g') (rel_min P1 P2) E"
  by (auto simp: rel_min_def elim!: monad_return_rel_rel_weaken)

lemma monad_return_rel_and_boolM[monad_return_rel]:
  "monad_return_rel assms x x' P E \<Longrightarrow>
    (\<And>sw sw'. Abbrev and_boolM x x = and_boolM x x \<Longrightarrow> P sw sw' \<longrightarrow> sw = sw') \<Longrightarrow>
    monad_return_rel assms y y' Q E \<Longrightarrow>
    monad_return_rel assms (and_boolM x y) (and_boolM x' y') (rel_min Q (=)) E"
  apply (simp add: and_boolM_def Abbrev_def)
  apply (erule monad_return_rel_bind)
  apply (auto simp: rel_min_def intro: monad_return_rel_return elim: monad_return_rel_rel_weaken)
  done

lemma monad_return_rel_or_boolM[monad_return_rel]:
  "monad_return_rel assms x x' P E \<Longrightarrow>
    (\<And>sw sw'. Abbrev or_boolM x x = or_boolM x x \<Longrightarrow> P sw sw' \<longrightarrow> sw = sw') \<Longrightarrow>
    monad_return_rel assms y y' Q E \<Longrightarrow>
    monad_return_rel assms (or_boolM x y) (or_boolM x' y') (rel_min Q (=)) E"
  apply (simp add: or_boolM_def Abbrev_def)
  apply (erule monad_return_rel_bind)
  apply (auto simp: rel_min_def intro: monad_return_rel_return elim: monad_return_rel_rel_weaken)
  done

lemma try_catch_Traces_final_cases:
  "(try_catch f (\<lambda>x. g x), t, r) \<in> Traces \<Longrightarrow>
    (case r of Done _ \<Rightarrow> False | Exception _ \<Rightarrow> False | _ \<Rightarrow> True) \<or>
    (\<exists>e ta tb. t = ta @ tb \<and> (f, ta, Exception e) \<in> Traces \<and> (
        (\<exists>y. r = Done y \<and> Run (g e) tb y) \<or>
        (\<exists>e'. r = Exception e' \<and> (g e, tb, Exception e') \<in> Traces))) \<or>
    (\<exists>x. r = Done x \<and> Run f t x)"
  apply (erule try_catch_Traces_cases)
   apply (case_tac m', simp_all)[1]
   apply (simp split: monad.split)
   apply (fastforce intro: exI[where x=Nil])
  apply (simp split: monad.split)
  apply auto[1]
  done

lemma monad_return_rel_try_catch:
  "monad_return_rel assms f f' P C \<Longrightarrow> (\<And>x x'. C x x' \<Longrightarrow> monad_return_rel assms (g x) (g' x') P E)
    \<Longrightarrow> monad_return_rel assms (try_catch f g) (try_catch f' (\<lambda>x'. g' x')) P E"
  apply (subst monad_return_rel_def, clarsimp)
  apply (simp split: monad.split)
  apply (erule try_catch_Traces_final_cases[THEN disjE], fastforce)
  apply (erule try_catch_Traces_final_cases[THEN disjE], fastforce)
  apply (elim disjE; clarsimp; drule(2) monad_return_relD; clarsimp?)
  apply (elim meta_allE, drule(1) meta_mp)
  apply (clarsimp simp: ball_Un)
  apply (auto dest: monad_return_relD)
  done

lemma monad_return_rel_liftR:
  "monad_return_rel assms f g P E
    \<Longrightarrow> monad_return_rel assms (liftR f) (liftR g) P (rel_sum C E)"
  apply (simp add: liftR_def)
  apply (erule monad_return_rel_try_catch)
  apply (rule monad_return_rel_throw)
  apply simp
  done

lemma monad_return_rel_catch_early_return:
  "monad_return_rel assms f g P (rel_sum P E)
    \<Longrightarrow> monad_return_rel assms (catch_early_return f) (catch_early_return g) P E"
  apply (simp add: catch_early_return_def)
  apply (erule monad_return_rel_try_catch)
  apply (erule rel_sum.cases, simp_all)
   apply (rule monad_return_rel_return, simp)
  apply (rule monad_return_rel_throw, simp)
  done

lemma monad_return_rel_return_same:
  "monad_return_rel assms (return x) (return x) (\<lambda>a b. a = b \<and> Abbrev (a = x)) E"
  apply (rule monad_return_rel_return)
  apply (simp add: Abbrev_def)
  done

lemma monad_return_rel_return_same_weak:
  "monad_return_rel assms (return x) (return x) (=) E"
  by (rule monad_return_rel_return, simp)

lemma monad_return_rel_return_unit:
  "monad_return_rel assms (return (x :: unit)) (return y) (=) E"
  by (rule monad_return_rel_return, simp)

lemmas monad_return_rel_return_unknown = monad_return_rel_return[where P="unknown"]

lemma monad_return_rel_bind_assoc_sym:
  "monad_return_rel assms
        (bind (bind f (\<lambda>x. g x)) (\<lambda>y. h y))
        (bind (bind f' (\<lambda>x. g' x)) (\<lambda>y. h' y)) P E \<Longrightarrow>
    monad_return_rel assms
        (bind f (\<lambda>x. bind (g x) (\<lambda>y. h y))) 
        (bind f' (\<lambda>x. bind (g' x) (\<lambda>y. h' y))) P E"
  by simp

lemma monad_return_rel_let_as_bind:
  "monad_return_rel assms (bind (return v) (\<lambda>x. f x)) (bind (return v') (\<lambda>y. g y)) P E \<Longrightarrow>
    monad_return_rel assms (let x = v in f x) (let y = v' in g y) P E"
  "monad_return_rel assms (bind (return v) (\<lambda>x. return (j x))) (bind (return v') (\<lambda>y. return (k y))) P E \<Longrightarrow>
    monad_return_rel assms (return (let x = v in j x)) (return (let y = v' in k y)) P E"
  by simp_all

lemma monad_return_rel_return_tuple:
  "monad_return_rel assms (return x) (return x') P E \<Longrightarrow>
    monad_return_rel assms (return y) (return y') Q E \<Longrightarrow>
    monad_return_rel assms (return (x, y)) (return (x', y')) (rel_prod P Q) E"
  by (simp add: monad_return_rel_def)

lemma monad_return_rel_weaken_P:
  "monad_return_rel assms f g P E \<Longrightarrow> (\<And>x y. P x y \<longrightarrow> P' x y) \<Longrightarrow>
    monad_return_rel assms f g P' E"
  by (erule monad_return_rel_rel_weaken, simp_all)

lemma rel_min_imp:
  "P x y \<longrightarrow> R \<Longrightarrow> Q x y \<longrightarrow> R \<Longrightarrow> rel_min P Q x y \<longrightarrow> R"
  by (simp add: rel_min_def)

lemma rel_min_rel_prodD:
  "rel_min (rel_prod A B) (rel_prod C D) x y \<Longrightarrow> rel_prod (rel_min A C) (rel_min B D) x y"
  by (auto simp: rel_min_def elim!: rel_prod.cases)

lemmas rel_min_rel_prodDs = 
    rel_min_rel_prodD[where A="(=)" and B="(=)", simplified prod.rel_eq]
    rel_min_rel_prodD[where C="(=)" and D="(=)", simplified prod.rel_eq]
    rel_min_rel_prodD[where A="(=)" and C="(=)", simplified rel_min_simp]
    rel_min_rel_prodD[where A="(=)" and C="unknown", simplified rel_min_simp]
    rel_min_rel_prodD[where A="(=)" and C="impossible", simplified rel_min_simp]
    rel_min_rel_prodD[where A="unknown" and C="(=)", simplified rel_min_simp]
    rel_min_rel_prodD[where A="unknown" and C="unknown", simplified rel_min_simp]
    rel_min_rel_prodD[where A="unknown"and C="impossible", simplified rel_min_simp]
    rel_min_rel_prodD[where A="impossible" and C="(=)", simplified rel_min_simp]
    rel_min_rel_prodD[where A="impossible" and C="unknown", simplified rel_min_simp]
    rel_min_rel_prodD[where A="impossible"and C="impossible", simplified rel_min_simp]

lemmas init_monad_return_rel[monad_return_rel] =
    monad_return_rel_assert_exp_P
    monad_return_rel_assert_exp
    monad_return_rel_if_rel_min
    monad_return_rel_and_boolM
    monad_return_rel_or_boolM
    monad_return_rel_catch_early_return
    monad_return_rel_return_same_weak
    monad_return_rel_return_unit
    monad_return_rel_undefined_bitvector_unknown
    monad_return_rel_return_tuple

lemmas init_return_rel_unfold[monad_return_rel_unfold] =
    split_paired_all rel_prod_inject case_prod_conv fst_conv snd_conv prod.inject

lemmas monad_return_rel_comb = rel_min_imp conjI impI refl
        monad_return_rel_bind_assoc_sym
        monad_return_rel_bind monad_return_rel_liftR
        monad_return_rel_let_as_bind

method read_reg_monad_return_rel =
    ((simp(no_asm) only: const_regs_translate_def)?,
        rule read_reg_monad_return_rel,
        (solves \<open>simp add: register_defs\<close>)?)

method monad_return_rel_step = determ \<open>intro monad_return_rel monad_return_rel_comb
    | rule monad_return_rel
    | (rule monad_return_rel_impossible,
        solves \<open>simp only: monad_return_rel_unfold rel_min_simp impossible_def\<close>)
    | simp only: monad_return_rel_unfold rel_min_simp
    | let_atom
    | drop_unknown
    | elim conjE conjE[OF unknown_tupleD] exE in_inv_imagep[THEN iffD1, elim_format]
        known_unknown_relE
    | erule monad_return_rel_return_unknown rel_min_rel_prodDs[elim_format]
    | (rule monad_return_rel_weaken_P, rule monad_return_rel)
    | read_reg_monad_return_rel
    | (rule monad_return_rel_impossible, solves \<open>clarsimp; simp\<close>)
  \<close>

method monad_return_rel = monad_return_rel_step+

lemma AArch64_AccessUsesEL_monad_return_rel[monad_return_rel]:
  "monad_determ (const_regs_translate cfg) (AArch64_AccessUsesEL acctype)"
  apply (simp add: AArch64_AccessUsesEL_def split del: if_split)
  apply monad_return_rel
  done

lemma HaveEL_monad_return_rel[monad_return_rel]:
  "monad_determ assms (HaveEL el)"
  apply (simp add: HaveEL_def)
  apply monad_return_rel
  done

lemma IMPDEF_boolean_monad_return_rel[monad_return_rel]:
  "monad_determ assms (IMPDEF_boolean nm)"
  unfolding IMPDEF_boolean_def IMPDEF_boolean_map_def
  by (intro monad_return_rel_if refl monad_return_rel_return monad_return_rel_throw TrueI)

lemma IsSecureBelowEL3_monad_return_rel[monad_return_rel]:
  "monad_determ (const_regs_translate cfg) (IsSecureBelowEL3 x)"
  apply (simp add: IsSecureBelowEL3_def SCR_GEN_read_def const_regs_translate_def
             cong: if_cong)
  apply monad_return_rel
  done

lemma HighestEL_monad_return_rel[monad_return_rel]:
  "monad_semideterm assms (HighestEL ())
    (\<lambda>rg rg'. rg = rg' \<and> rg \<in> {EL1, EL2, EL3})"
  (is "monad_return_rel _ _ _ ?R _")
  apply (simp add: HighestEL_def)
  apply (rule monad_return_rel_return[where P="?R"]
    | monad_return_rel_step
    | simp)+
  done

lemmas EL_exhaust_imp = EL_exhaust_disj[simplified disj_imp, rule_format]

lemma HaveAArch32EL_monad_return_rel[monad_return_rel]:
  "monad_determ assms (HaveAArch32EL el)"
  apply (simp add: HaveAArch32EL_def)
  apply (rule
        monad_return_rel_if_rel_min[where ?P1.0="(=)" and ?P2.0="(=)", simplified]
    | monad_return_rel_step
    | drule(2) EL_exhaust_disj[simplified disj_imp, rule_format]
  )+
  done

lemma ELStateUsingAArch32K_monad_return_rel[monad_return_rel]:
  "monad_return_rel (const_regs_translate cfg)
    (ELStateUsingAArch32K el x) (ELStateUsingAArch32K el x)
    (\<lambda>(known, x) (known', y). known = known' \<and> (known \<longrightarrow> x = y)) (=)"
  (is "monad_return_rel _ _ _ ?R _")
  apply (simp add: ELStateUsingAArch32K_def)
  apply (
    clarsimp simp: UNKNOWN_boolean_def
    | rule monad_return_rel_return[where P="?R"]
    | monad_return_rel_step
  )+
  sorry

lemma ELStateUsingAArch32_monad_return_rel[monad_return_rel]:
  "monad_determ (const_regs_translate cfg) (ELStateUsingAArch32 el x)"
  apply (simp add: ELStateUsingAArch32_def)
  apply (monad_return_rel | clarsimp)+
  done

lemma monad_return_rel_assms_weaken:
  "monad_return_rel assms' x y R E \<Longrightarrow> (\<forall>ev. assms ev \<longrightarrow> assms' ev) \<Longrightarrow>
    monad_return_rel assms x y R E"
  apply (subst monad_return_rel_def, clarsimp)
  apply (drule(2) monad_return_relD, simp_all)
  done

declare ELUsingAArch32_def[monad_return_rel_unfold]

lemma S1TranslationRegime_monad_return_rel[monad_return_rel]:
  "monad_return_rel (const_regs_translate cfg)
    (S1TranslationRegime x) (S1TranslationRegime x)
    (\<lambda>rg rg'. rg = rg' \<and> rg \<in> {EL1, EL2, EL3}) (=)"
  (is "monad_return_rel _ _ _ ?R _")
  using EL_exhaust_disj[of x]
  apply (simp add: S1TranslationRegime_def HaveVirtHostExt_def HasArchVersion_def ELIsInHost_def
                   monad_return_rel_return
        split del: if_split cong: if_cong)
  apply (rule monad_return_rel_return[where P="?R"]
    | monad_return_rel_step
    | clarsimp)+
  done

lemma unat_ELs:
  "map unat [EL0, EL1, EL2, EL3] = [0, 1, 2, 3]"
  by (simp add: EL0_def EL1_def EL2_def EL3_def)

lemma ELIsInHost_monad_return_rel[monad_return_rel]:
  "monad_determ (const_regs_translate cfg) (ELIsInHost el)"
  apply (simp add: ELIsInHost_def)
  apply monad_return_rel
  done

lemma AddrTop_monad_return_rel[monad_return_rel]:
  "monad_determ (const_regs_translate cfg) (AddrTop vaddr el)"
  using unat_ELs
  apply (clarsimp simp add: AddrTop_def split del: if_split)
  apply (rule TrueI
    | (rule monad_return_rel_return[where P="(=)"], clarsimp)
    | monad_return_rel_step
    | simp only: Let_def
  )+
  done

lemma HasS2Translation_monad_return_rel[monad_return_rel]:
  "monad_determ (const_regs_translate cfg) (HasS2Translation ())"
  apply (simp add: HasS2Translation_def EL2Enabled_def IsInHost_def)
  apply monad_return_rel
  done

declare SCTLR_read__1_def[monad_return_rel_unfold]
    S1TranslationRegime__1_def[monad_return_rel_unfold]

lemma SCTLR_read_monad_return_rel[monad_return_rel]:
  "el \<in> {EL1, EL2, EL3} \<Longrightarrow> monad_determ (const_regs_translate cfg) (SCTLR_read el)"
  apply (simp add: SCTLR_read_def)
  apply (monad_return_rel)
  apply (simp add: impossible_def)
  done

lemma AArch64_IsStageOneEnabled_monad_return_rel[monad_return_rel]:
  "monad_determ (const_regs_translate cfg) (AArch64_IsStageOneEnabled acc_type)"
  apply (simp add: AArch64_IsStageOneEnabled_def)
  apply (monad_return_rel | clarsimp)+
  done

lemma liftR_bind_split:
  "liftR (bind f (\<lambda>x. g x)) = bind (liftR f) (\<lambda>x. liftR (g x))"
  apply (simp add: liftR_def)
  apply (induct f, simp_all)
  apply (simp add: throw_def)
  done

lemma UsingAArch32_monad_return_rel[monad_return_rel]:
  "monad_determ (const_regs_translate cfg) (UsingAArch32 x)"
  apply (simp add: UsingAArch32_def Let_def)
  apply (monad_return_rel | simp)+
  done

lemma IsSecure_monad_return_rel[monad_return_rel]:
  "monad_determ (const_regs_translate cfg) (IsSecure x)"
  apply (simp add: IsSecure_def
             cong: if_cong)
  apply (monad_return_rel)
  done

(* possibly a lie, it seems the configuration is wrong somewhere *)
lemma tlb_disabled:
  "\<not> tlb_enabled"
  sorry

lemma monad_return_rel_acc_disagree:
  "(\<And>x y. Abbrev (x = acc a) \<Longrightarrow> Abbrev (y = acc b) \<Longrightarrow> monad_return_rel assms (f x) (g y) P E) \<Longrightarrow>
    monad_return_rel assms (let x = acc a in f x) (let y = acc b in g y) P E"
  by (simp add: Abbrev_def)

lemma ConstrainUnpredictable_monad_return_rel[monad_return_rel]:
  "monad_determ assms (ConstrainUnpredictable X)"
  by (cases X, simp_all, monad_return_rel)

declare HasArchVersion_def[monad_return_rel_unfold]

lemma Have52BitVAExt_monad_return_rel[monad_return_rel]:
  "monad_determ assms (Have52BitVAExt ())"
  apply (simp add: Have52BitVAExt_def)
  apply monad_return_rel
  done

lemma S1CacheDisabled_monad_return_rel[monad_return_rel]:
  "monad_determ (const_regs_translate cfg) (S1CacheDisabled acctype)"
  apply (simp add: S1CacheDisabled_def)
  apply (monad_return_rel | clarsimp)+
  done

lemma S2CacheDisabled_monad_return_rel[monad_return_rel]:
  "monad_determ (const_regs_translate cfg) (S2CacheDisabled acctype)"
  apply (simp add: S2CacheDisabled_def)
  apply (monad_return_rel | clarsimp)+
  done

(*
lemma eq_merge_rel_apply_update:
  "(\<forall>r x. acc (f x r) = x) \<Longrightarrow>
    eq_merge_rel g_r r r' \<Longrightarrow>
    eq_merge_rel g_x x x' \<Longrightarrow>
    eq_merge_rel (\<lambda>k u. f (g_x (acc o k o Cons Two_A) (acc o u o Cons Two_A)) (g_r (k o Cons Two_B) (u o Cons Two_B)))
        (f x r) (f x' r')"
  apply (clarsimp dest!: eq_merge_relD)
  apply (rule_tac known="\<lambda>xs. case xs of Two_A # ys \<Rightarrow> f (knowna ys) undefined | Two_B # ys \<Rightarrow> known ys" and
        unknown_l="\<lambda>xs. case xs of Two_A # ys \<Rightarrow> f (unknown_la ys) undefined | Two_B # ys \<Rightarrow> unknown_l ys" and
        unknown_r="\<lambda>xs. case xs of Two_A # ys \<Rightarrow> f (unknown_ra ys) undefined | Two_B # ys \<Rightarrow> unknown_r ys" in
    eq_merge_relI)
  apply (simp add: o_def)
  done

lemmas monad_return_rel_return_merge = monad_return_rel_return[where P="eq_merge_rel f" for f]

lemma monad_return_rel_let_eq_merge:
  "eq_merge_rel f_x x y \<Longrightarrow>
    (\<And>a b. Abbrev (a = x) \<Longrightarrow> Abbrev (b = y) \<Longrightarrow> eq_merge_rel f_x x y \<Longrightarrow>
        monad_return_rel assms (f a) (g b) P E) \<Longrightarrow>
    monad_return_rel assms (let a = x in f a) (let b = y in g b) P E"
  by (simp add: Abbrev_def)

lemmas MemAttrs_merge =
    eq_merge_rel_apply_update[where acc="MemAttrHints_hints" and
        f="\<lambda>x. MemAttrHints_hints_update (\<lambda>_. x)", simplified]
    eq_merge_rel_apply_update[where acc="MemAttrHints_attrs" and
        f="\<lambda>x. MemAttrHints_attrs_update (\<lambda>_. x)", simplified]

lemma eq_merge_rel_refl:
  "eq_merge_rel (\<lambda>k u. k []) x x"
  by (auto simp add: eq_merge_rel_def)

lemma eq_merge_rel_knownD[dest!]:
  "(eq_merge_rel (\<lambda>k u. f k) x y) \<Longrightarrow> (x = y)"
  by (auto simp add: eq_merge_rel_def)
*)

definition
  "liftM f m = (bind m (\<lambda>x. return (f x)))"

lemma bind_exception_leftI:
  "(f, t, Exception e) \<in> Traces \<Longrightarrow> (bind f g, t, Exception e) \<in> Traces"
  by (induct f arbitrary: t; simp; erule Traces.cases; auto elim!: T.cases)

lemma monad_return_rel_liftM:
  "monad_return_rel assms (liftM f m) (liftM f m') P E =
    monad_return_rel assms m m' (\<lambda>x y. P (f x) (f y)) E"
  apply (rule iffI; subst monad_return_rel_def; clarsimp simp: liftM_def)
   apply (simp split: monad.split)
   apply (intro conjI impI allI; clarsimp?;
     (drule monad_return_relD, ((erule Traces_bindI, simp) | erule bind_exception_leftI)+);
     simp)
  apply (simp split: monad.split)
  apply (auto dest!: bind_Traces_final_cases dest: monad_return_relD)
  done

lemma rec_to_tuple_coercions:
  "(\<forall>x. absf (repf x) = x) \<Longrightarrow>
    bind f (\<lambda>x. g x) = bind (liftM repf f) (\<lambda>x. g (absf x)) \<and>
    (let x = v in h x) = (let x = repf v in h (absf x)) \<and>
    (let x = a in j x) = absf (let x = a in repf (j x)) \<and>
    (if b then v else v') = absf (if b then repf v else repf v') \<and>
    (unknown v v') = (\<exists>a b. v = absf a \<and> v' = absf b \<and> unknown a b) \<and>
    (toplevel \<longrightarrow> (monad_return_rel assms f f' (P) (=) =
        monad_return_rel assms (liftM repf f) (liftM repf f') (\<lambda>x y. P (absf x) (absf y)) (=)))"
  apply (simp add: monad_return_rel_liftM)
  apply (simp add: liftM_def unknown_def)
  apply (auto intro: exI[where x="repf v"] exI[where x="repf v'"])
  done

lemma liftM_return:
  "liftM f (return x) = return (f x)"
  by (simp add: liftM_def)

lemma liftM_bind:
  "liftM f (bind g (\<lambda>x. h x)) = bind g (\<lambda>x. liftM f (h x))"
  by (simp add: liftM_def)

lemma liftM_let:
  "liftM f (let x = v in g x) = (let x = v in liftM f (g x))"
  by simp

lemmas liftM_if = if_distrib[where f="liftM f" for f]

lemma liftM_liftR:
  "liftM f (liftR m) = liftR (liftM f m)"
  apply (simp add: liftM_def liftR_def)
  apply (induct m, simp_all)
  apply (simp add: throw_def)
  done

lemmas rec_to_tuple_extra =
    liftM_if liftM_return liftM_bind liftM_let liftM_liftR

lemma liftM_unknown:
  "monad_return_rel assms m m' unknown E \<Longrightarrow>
    monad_return_rel assms (liftM f m) (liftM f m') unknown E"
  apply (simp add: liftM_def)
  apply (erule monad_return_rel_bind)
  apply (rule monad_return_rel_return)
  apply (simp add: unknown_def)
  done

lemma return_rel_via_rep:
  "monad_return_rel assms (liftM repf f) (liftM repf f') (P) E \<Longrightarrow>
    monad_return_rel assms f f' (inv_imagep P repf) E"
  by (simp add: monad_return_rel_liftM inv_imagep_def)

lemma unknown_repD:
  "unknown x y \<Longrightarrow> unknown (repf x) (repf y)"
  by (simp add: unknown_def)

ML \<open>
fun mk_rec_to_tuple_thms ctxt toplevel ty = let
    val (nm, _) = dest_Type ty
    val thy = Proof_Context.theory_of ctxt
    val info = Record.the_info thy (Long_Name.qualifier nm)
    val (flds, more) = Record.get_extT_fields thy ty
    val sels = map (fn (nm, ty2) => Const (nm, ty --> ty2)) (flds @ [more])
    val r = Free ("r", ty)
    val rep = lambda r (HOLogic.mk_tuple (map (fn sel => sel $ r) sels))
    val ext_nm = #ext_def info |> Thm.lhs_of |> Thm.term_of |> head_of |> dest_Const |> fst
    val fld_vs = map (Free o apfst Long_Name.base_name) (flds @ [more])
    val ext = Const (ext_nm, map type_of fld_vs ---> ty)
    val abs = HOLogic.tupled_lambda (HOLogic.mk_tuple fld_vs) (list_comb (ext, fld_vs))
    val top_t = if toplevel then @{cterm True} else @{cterm False}
    val inst = infer_instantiate ctxt
        [(("absf", 0), Thm.cterm_of ctxt abs), (("repf", 0), Thm.cterm_of ctxt rep),
            (("toplevel", 0), top_t)]
        @{thm rec_to_tuple_coercions}
    val thm = inst |> simp_tac ctxt 1 |> Seq.hd
    val t = Var (("t", 0), domain_type (fastype_of abs))
    val ss_ctxt = put_simpset HOL_basic_ss ctxt
        addsimps @{thms case_prod_beta} addsimps #select_convs info
    val sel_apps = map (fn s => s $ (abs $ t)) sels
        |> map (Thm.cterm_of ctxt #> Simplifier.rewrite ss_ctxt)
  in thm :: #select_convs info @ #update_convs info @ sel_apps end

fun mk_rec_to_tuple_rules ctxt ty = let
    val thy = Proof_Context.theory_of ctxt
    val (nm, _) = dest_Type ty
    val info = Record.the_info thy (Long_Name.qualifier nm)
    val (flds, more) = Record.get_extT_fields thy ty
    val sels = map (fn (nm, ty2) => Const (nm, ty --> ty2)) (flds @ [more])
    val r = Free ("r", ty)
    val rep = lambda r (HOLogic.mk_tuple (map (fn sel => sel $ r) sels))
    val f = infer_instantiate ctxt [(("repf", 0), Thm.cterm_of ctxt rep)]
  in
    ([f @{thm return_rel_via_rep}, #equality info], [f @{thm unknown_repD}])
  end

fun get_tuple_tys1 ctxt t = let
    val thy = Proof_Context.theory_of ctxt
    val const_tys = Term.add_consts t [] |> map snd
    val tys = fold (Term.fold_subtypes (curry (op ::))) const_tys []
        |> sort_distinct Term_Ord.typ_ord
  in tys |> filter (can (Record.get_extT_fields thy)) end

fun get_tuple_tys ctxt t = let
    val thy = Proof_Context.theory_of ctxt
    val consts = Term.add_consts t []
    val const_nms = consts |> map fst |> Ord_List.make fast_string_ord
        |> filter_out (String.isPrefix "HOL")
    fun shared_consts tms = fold Term.add_consts tms []
        |> map fst
        |> Ord_List.make fast_string_ord
        |> Ord_List.inter fast_string_ord const_nms
    val cands = consts
        |> map (snd #> strip_type #> snd)
        |> sort_distinct Term_Ord.typ_ord
  in cands
    |> filter (can (dest_Type #> fst #> Long_Name.qualifier
        #> Record.the_info thy
        #> #update_convs #> map Thm.concl_of #> shared_consts #> hd))
  end

fun rec_via_tuple_tac ctxt = SUBGOAL (fn (t, i) => let
    val tys = get_tuple_tys1 ctxt t
    val thms = map (mk_rec_to_tuple_rules ctxt) tys
    val ss = put_simpset HOL_basic_ss ctxt addsimps @{thms rec_to_tuple_extra}
        addsimprocs [Record.simproc]
    val intros = maps fst thms
    val dests = maps snd thms
  in (FIRST' [resolve_tac ctxt intros, dresolve_tac ctxt dests,
    resolve_tac ctxt @{thms monad_return_rel_weaken_P} THEN' resolve_tac ctxt intros]
    THEN_ALL_NEW simp_tac ss) i end)

fun rec_to_tuple_tac ctxt toplevel = SUBGOAL (fn (t, i) => let
    val tys = get_tuple_tys ctxt t
    val thms = maps (mk_rec_to_tuple_thms ctxt toplevel) tys
  in CHANGED (simp_tac (put_simpset HOL_basic_ss ctxt
        addsimps thms
        addsimps @{thms rec_to_tuple_extra prod.collapse}
        addsimprocs [Record.simproc]) i) end)
\<close>

method_setup rec_to_tuple = \<open>Scan.lift (Scan.option Parse.name) >> (fn arg => fn ctxt =>
    Method.SIMPLE_METHOD (rec_to_tuple_tac ctxt (arg = SOME "toplevel") 1))\<close>

method_setup rec_via_tuple = \<open>Scan.succeed () >> (fn _ => fn ctxt =>
    Method.SIMPLE_METHOD (rec_via_tuple_tac ctxt 1))\<close>

lemma ShortConvertAttrsHints_monad_return_rel[monad_return_rel]:
  "monad_determ (const_regs_translate cfg)
     (ShortConvertAttrsHints RGN acctype sndstage)"

  unfolding ShortConvertAttrsHints_def
  apply (rule monad_return_rel_weaken_P)
  apply ((monad_return_rel
    | (rule liftM_unknown, rule monad_return_rel)
    | rec_via_tuple
    | rule monad_return_rel_return_tuple monad_return_rel_let_as_bind
  )+)[1]
  apply simp
  done

declare UNKNOWN_bits_def[monad_return_rel_unfold] UNKNOWN_integer_def[monad_return_rel_unfold]
    UNKNOWN_boolean_def[monad_return_rel_unfold]

lemma known_unknown_simpleI:
  "(\<exists>a b. f x a = x \<and> f x b = y) \<Longrightarrow> known_unknown_rel f x y"
  apply (clarsimp simp: known_unknown_rel_def)
  apply metis
  done

lemma AArch64_AccessFlagFault_monad_return_rel[monad_return_rel]:
  "monad_semideterm assms
    (AArch64_AccessFlagFault ipaddress level acctype iswrite sndstage s2fs1walk)
    (known_unknown_rel (\<lambda>r (x, y, z, d). r \<lparr> FaultRecord_debugmoe := x, FaultRecord_errortype := y,
        FaultRecord_extflag := z, FaultRecord_domain := d \<rparr> ))"
  apply (simp add: AArch64_AccessFlagFault_def AArch64_CreateFaultRecord_def)
  apply (monad_return_rel | rec_via_tuple)+
  apply (clarsimp intro!: known_unknown_simpleI)
  apply (intro exI conjI FaultRecord.equality, simp_all)
  done

lemma AArch64_AddressSizeFault_monad_return_rel[monad_return_rel]:
  "monad_semideterm assms
    (AArch64_AddressSizeFault ipaddress level acctype iswrite sndstage s2fs1walk)
    (known_unknown_rel (\<lambda>r (x, y, z, d). r \<lparr> FaultRecord_debugmoe := x, FaultRecord_errortype := y,
        FaultRecord_extflag := z, FaultRecord_domain := d \<rparr> ))"
  apply (simp add: AArch64_AddressSizeFault_def AArch64_CreateFaultRecord_def)
  apply monad_return_rel
  apply (rule monad_return_rel_return)
  apply (clarsimp intro!: known_unknown_simpleI simp only: split_paired_Ex)
  apply (intro exI conjI FaultRecord.equality, simp_all)
  done

lemma AArch64_NoFault_monad_return_rel[monad_return_rel]:
  "monad_semideterm assms
    (AArch64_NoFault x)
    (known_unknown_rel (\<lambda>r (x, y, z, a, b, c, d).
        r \<lparr> FaultRecord_debugmoe := x, FaultRecord_errortype := y,
        FaultRecord_extflag := z, FaultRecord_domain := d, FaultRecord_level := a,
        FaultRecord_ipaddress := b, FaultRecord_write := c \<rparr> ))"
  apply (simp add: AArch64_NoFault_def AArch64_CreateFaultRecord_def)
  apply monad_return_rel
  apply (rule monad_return_rel_return)
  apply (clarsimp intro!: known_unknown_simpleI)
  apply (intro exI conjI FaultRecord.equality, simp_all)
  done

declare HaveMPAMExt_def[monad_return_rel_unfold]

lemma MPAM2_EL2_read_monad_return_rel[monad_return_rel]:
  "monad_determ (const_regs_translate cfg) (MPAM2_EL2_read u)"
  apply (simp add: MPAM2_EL2_read_def)
  apply monad_return_rel
  apply (rule monad_return_rel_return)
  apply (simp add: set_slice_def update_subrange_vec_dec_def)
  apply (rule word_eqI, simp add: test_bit_word_update)
  done

lemma unknown_eq_at_bits:
  "unknown x y \<Longrightarrow> eq_at_bits {} x y"
  by (simp add: eq_at_bits_def)

lemmas monad_return_rel_return_eq_at_bits = monad_return_rel_return[where P="eq_at_bits S" for S]

lemma return_word_update_lemma:
  assumes eq: "eq_at_bits S x x'"
   and extra: "j = i + size y - 1" "j < size x" "0 < size y"
  shows "monad_return_rel assms (return (word_update x i j y)) (return (word_update x' i j y))
    (eq_at_bits (S \<union> {nat i ..< nat j + 1})) E"
  using eq extra
  by (auto simp: eq_at_bits_def test_bit_word_update intro!: monad_return_rel_return)

lemma MPAM1_EL1_read_monad_return_rel[monad_return_rel]:
  "monad_determ (const_regs_translate cfg) (MPAM1_EL1_read u)"
  apply (simp add: MPAM1_EL1_read_def)
  apply (simp only: set_slice_def update_subrange_vec_dec_def)
  apply (rule monad_return_rel_weaken_P)
   apply (monad_return_rel
     | (rule return_word_update_lemma, (assumption | erule unknown_eq_at_bits),
         simp+)[1]
     | erule monad_return_rel_return_eq_at_bits
   )+
  apply (auto dest: eq_at_bits_complete)
  done

lemma MPAMisEnabled_monad_return_rel[monad_return_rel]:
  "monad_determ (const_regs_translate cfg) (MPAMisEnabled u)"
  apply (simp add: MPAMisEnabled_def)
  apply ((rule monad_return_rel_impossible, solves \<open>simp\<close>)
    | monad_return_rel_step)+
  apply (simp add: impossible_def)
  done

lemma EL2Enabled_monad_return_rel[monad_return_rel]:
  "monad_determ (const_regs_translate cfg) (EL2Enabled u)"
  apply (simp add: EL2Enabled_def)
  apply monad_return_rel
  done

lemma getMPAM_PARTID_monad_return_rel[monad_return_rel]:
  "MPAMn \<in> {0, 1, 2, 3} \<Longrightarrow> monad_determ (const_regs_translate cfg) (getMPAM_PARTID MPAMn in_d)"
  apply (simp only: getMPAM_PARTID_def Let_def[where s=MPAMn] mem_simps)
  apply (elim disjE; simp cong: if_cong)
     apply monad_return_rel
  done

lemma MPAMisVirtual_monad_return_rel[monad_return_rel]:
  "monad_determ (const_regs_translate cfg) (MPAMisVirtual MPAMn)"
  apply (simp add: MPAMisVirtual_def)
  apply monad_return_rel
  done

lemma mapvpmw_monad_return_rel[monad_return_rel]:
  "monad_determ (const_regs_translate cfg) (mapvpmw partid)"
  apply (simp add: mapvpmw_def)
  apply monad_return_rel
  done

lemma MAP_vPARTID_monad_return_rel[monad_return_rel]:
  "monad_determ (const_regs_translate cfg) (MAP_vPARTID partid)"
  apply (simp add: MAP_vPARTID_def)
  apply monad_return_rel
  apply clarsimp
  apply monad_return_rel
  done

lemma genPARTID_monad_return_rel[monad_return_rel]:
  "MPAMn \<in> {0, 1, 2, 3} \<Longrightarrow> monad_determ (const_regs_translate cfg) (genPARTID MPAMn in_d)"
  apply (simp add: genPARTID_def)
  apply monad_return_rel
  apply (simp only: mem_simps simp_thms)
  apply monad_return_rel
  done

lemma getMPAM_PMG_monad_return_rel[monad_return_rel]:
  "el \<in> {0, 1, 2, 3} \<Longrightarrow> monad_determ (const_regs_translate cfg) (getMPAM_PMG el in_d)"
  apply (simp add: getMPAM_PMG_def cong: if_cong)
  apply ((rule monad_return_rel_impossible, solves \<open>simp\<close>)
    | monad_return_rel_step
    | simp add: impossible_def)+
  done

lemma genPMG_monad_return_rel[monad_return_rel]:
  "el \<in> {0, 1, 2, 3} \<Longrightarrow> monad_determ (const_regs_translate cfg) (genPMG el in_d partid_err)"
  apply (simp add: genPMG_def)
  apply (monad_return_rel | simp)+
  done

lemma genMPAM_monad_return_rel[monad_return_rel]:
  "el \<in> {0, 1, 2, 3} \<Longrightarrow> monad_determ (const_regs_translate cfg) (genMPAM el in_d secure)"
  apply (simp only: genMPAM_def Let_def[where s="if _ then _ else el"])
  apply (monad_return_rel | rec_via_tuple | simp)+
  done

lemma DefaultMPAMinfo_monad_return_rel[monad_return_rel]:
  "monad_determ (const_regs_translate cfg) (DefaultMPAMinfo sec)"
  apply (simp add: DefaultMPAMinfo_def)
  apply (monad_return_rel | rec_via_tuple)+
  done

lemma GenMPAMcurEL_monad_return_rel[monad_return_rel]:
  "monad_determ (const_regs_translate cfg) (GenMPAMcurEL inD)"
  apply (simp add: GenMPAMcurEL_def)
  apply monad_return_rel
    apply (rule word_uint.Rep[THEN subsetD[rotated]])
    apply (simp add: uints_unats unats_def lessThan_def[symmetric]
        lessThan_nat_numeral lessThan_Suc)
   apply monad_return_rel
  done

lemma CreateAccessDescriptorPTW_monad_return_rel[monad_return_rel]:
  "monad_determ (const_regs_translate cfg) (CreateAccessDescriptorPTW acctype sndstage s2fs1walk level)"
  apply (simp add: CreateAccessDescriptorPTW_def)
  apply (monad_return_rel | rec_via_tuple)+
  done

lemmas more_unknowns[monad_return_rel_unfold] =
  UNKNOWN_DeviceType_def UNKNOWN_MemAttrHints_def UNKNOWN_bits_def

lemma rel_min_inv_image[simp, monad_return_rel_unfold]:
  "rel_min (inv_imagep A f) (inv_imagep B f) x y = rel_min A B (f x) (f y)"
  by (auto simp: rel_min_def)

lemma unknownI:
  "unknown a b"
  by (simp add: unknown_def)

lemma MemAttrDefaults_monad_return_rel[monad_return_rel]:
  "monad_return_rel assms
    (MemAttrDefaults x)
    (MemAttrDefaults x)
    (\<lambda>r r'. \<exists>inn out fgen dev. r = r' \<lparr>MemoryAttributes_inner := inn, MemoryAttributes_outer := out, MemoryAttributes_readtagfaulttgen := fgen, MemoryAttributes_device := dev\<rparr> 
        \<and> unknown (inn, out, fgen, dev) (MemoryAttributes_inner r', MemoryAttributes_outer r', MemoryAttributes_readtagfaulttgen r', MemoryAttributes_device r')) (=)"
  apply (simp add: MemAttrDefaults_def split del: if_split)
  apply (rule monad_return_rel_weaken_P)
   apply (monad_return_rel
    | (rule liftM_unknown, rule monad_return_rel)
    | rule monad_return_rel_let_Abbrev
    | simp only: if_distrib[where f=return]
    | rec_via_tuple
  )+
  apply (intro impI exI conjI unknownI MemoryAttributes.equality, simp_all)
  done

lemma monad_return_rel_liftM_intro:
  "monad_return_rel assms m m' P E \<Longrightarrow>
    monad_return_rel assms (liftM f m) (liftM g m') (\<lambda>x y. \<exists>x' y'. x = f x' \<and> y = g y' \<and> P x' y') E"
  apply (simp add: liftM_def)
  apply (erule monad_return_rel_bind)
  apply (rule monad_return_rel_return)
  apply auto
  done

lemma WalkAttrDecode_monad_return_rel[monad_return_rel]:
  "monad_semideterm (const_regs_translate cfg)
    (WalkAttrDecode SH ORGN IRGN sndstage)
    (\<lambda>r r'. \<exists>fgen dev. r = r' \<lparr>MemoryAttributes_readtagfaulttgen := fgen, MemoryAttributes_device := dev\<rparr> 
        \<and> unknown (fgen, dev) (MemoryAttributes_readtagfaulttgen r', MemoryAttributes_device r'))"
  apply (simp add: WalkAttrDecode_def MemAttrDefaults_def)
  apply (rule monad_return_rel_weaken_P)

  apply (monad_return_rel
    | rule monad_return_rel_let_Abbrev
    | simp only: if_distrib[where f=return]
    | rec_via_tuple
)+
  apply (intro impI exI conjI unknownI MemoryAttributes.equality, simp_all)
  done

declare MAIR_read__1_def[monad_return_rel_unfold]

lemma MAIR_read_monad_return_rel[monad_return_rel]:
  "el \<in> {EL1, EL2, EL3} \<Longrightarrow> monad_determ (const_regs_translate cfg) (MAIR_read el)"
  apply (simp add: MAIR_read_def)
  apply monad_return_rel
  apply (simp add: impossible_def)
  done

declare Unreachable_def[monad_return_rel_unfold]

lemma LongConvertAttrsHints_monad_return_rel[monad_return_rel]:
  "monad_semideterm (const_regs_translate cfg)
    (LongConvertAttrsHints attr acctype)
    (known_unknown_rel (\<lambda>r x. r \<lparr> MemAttrHints_transient := x  \<rparr> ))"
  apply (simp add: LongConvertAttrsHints_def)
  apply (rule monad_return_rel_weaken_P)
  apply (monad_return_rel
    | simp only: if_distrib[where f=return]
    | rec_via_tuple
    | rule known_unknown_simpleI exI)+
  done

lemma assert_exp_False:
  "assert_exp False s = Fail s"
  by (simp add: assert_exp_def)

lemmas monad_return_rel_return_spec =
    monad_return_rel_return[where x=z and y=z and P="\<lambda>x y. x = z \<and> y = z" for z]

lemma monad_return_rel_Fail[monad_return_rel]:
  "monad_return_rel assms (Fail s) (Fail s') impossible E"
  by (simp add: monad_return_rel_def)

lemmas rel_minE = rel_min_def[THEN iffD1, THEN disjE]

lemma monad_return_rel_rel_min_split:
  "rel_min P Q x y \<Longrightarrow>
    (P x y \<Longrightarrow> monad_return_rel assms f g R E) \<Longrightarrow>
    (Q x y \<Longrightarrow> monad_return_rel assms f g S E) \<Longrightarrow>
    monad_return_rel assms f g (rel_min R S) E"
  by (auto simp: rel_min_def elim!: monad_return_rel_weaken_P)

lemma AArch64_S1AttrDecode_monad_return_rel[monad_return_rel]:
  "monad_semideterm (const_regs_translate cfg)
    (AArch64_S1AttrDecode SH attr acctype)
    (known_unknown_rel (\<lambda>r (inn, out, fgen, dev). r \<lparr> MemoryAttributes_inner := inn,
        MemoryAttributes_outer := out, MemoryAttributes_readtagfaulttgen := fgen, MemoryAttributes_device := dev\<rparr>))"
  apply (simp add: AArch64_S1AttrDecode_def)
  apply (simp only: ConstrainUnpredictableBits_def[where which=Unpredictable_RESMAIR, simplified]
                    Unreachable_def assert_exp_False bind.simps Let_def)
  apply (rule monad_return_rel_weaken_P)
   apply ((rule monad_return_rel_return_spec[where z=MemType_Device]
        | monad_return_rel_step
        | rec_via_tuple)+)
  apply (erule monad_return_rel_rel_min_split;
    simp add: MemAttrDefaults_def liftM_bind liftM_return split del: if_split)
   apply (monad_return_rel
    | simp only: if_distrib[where f=return]
    | rec_via_tuple
    | (rule known_unknown_simpleI; simp; intro exI conjI MemoryAttributes.equality; simp)
    | drule rel_min_rel_prodD
  )+
  done

lemma S2ConvertAttrsHints_monad_return_rel[monad_return_rel]:
  "monad_determ assms (S2ConvertAttrsHints attr acctype)"
  apply (simp add: S2ConvertAttrsHints_def)
  apply (rule monad_return_rel_weaken_P)
   apply (monad_return_rel | rec_via_tuple)+
  done

declare UNKNOWN_MemoryAttributes_def[monad_return_rel_unfold]

lemma S2AttrDecode_monad_return_rel[monad_return_rel]:
  "monad_semideterm (const_regs_translate cfg)
    (S2AttrDecode SH attr acctype)
    (known_unknown_rel (\<lambda>r (inn, out, fgen, dev). r \<lparr> MemoryAttributes_inner := inn,
        MemoryAttributes_outer := out, MemoryAttributes_readtagfaulttgen := fgen, MemoryAttributes_device := dev\<rparr>))"
  apply (simp add: S2AttrDecode_def)
  apply (simp only: bind_assoc[symmetric] mem_simps, intro monad_return_rel_bind
                    assert_exp_False bind.simps)
    apply ((rule monad_return_rel_return_spec[where z=MemType_Device]
        | monad_return_rel_step
        | rec_via_tuple)+)[2]
  apply simp
  (* OK, this is interesting. The attributes of this are set unspecified in
     a very unspecified way, which was probably not intended. *)
  sorry


text {*
lemma AArch64_TranslationTableWalk_monad_return_rel[monad_return_rel]:
  "monad_determ (const_regs_translate cfg)
    (AArch64_TranslationTableWalk ipaddress vaddr acctype iswrite sndstage s2fs sz)"
  using [[simproc del: let_simp]]
  apply (simp only: AArch64_TranslationTableWalk_def tlb_disabled bind_assoc[symmetric] if_simps)
  apply (monad_return_rel
    | rule monad_return_rel_let_Abbrev monad_return_rel_let_as_bind
    | simp only: liftR_bind_split
    | (rule liftM_unknown, rule monad_return_rel)
    | erule monad_return_rel_return_unknown monad_return_rel_return_eq_at_bits rel_min_rel_prodDs[elim_format]
  )+

  apply (drop_unknown | rec_via_tuple)+

  apply (monad_return_rel
    | rule monad_return_rel_let_Abbrev monad_return_rel_return_tuple monad_return_rel_let_as_bind
    | simp only: liftR_bind_split
    | erule monad_return_rel_return_unknown monad_return_rel_return_eq_at_bits rel_min_rel_prodDs[elim_format]
    | drop_unknown | rec_via_tuple
  )+

apply rec_via_tuple

apply rec_via_tuple

apply rec_via_tuple

apply monad_return_rel

apply rec_via_tuple


  apply rec_to_tuple

  apply (monad_return_rel
    | rule monad_return_rel_let_Abbrev monad_return_rel_return_tuple
    | simp only: liftR_bind_split
  )+

  apply (monad_return_rel
    | rule
   monad_return_rel_if_P[where G="_ = EL3", THEN monad_return_rel_bind_eq]
   monad_return_rel_if_P[where G="_ < _", THEN monad_return_rel_bind_eq]
        monad_return_rel_let_Abbrev
        monad_return_rel_bind[where P="(=) :: bool \<Rightarrow> _"]
    | clarify elim!: TrueE
)+
apply (
thm TrueE
apply (rule monad_return_rel_bind_eq)
apply monad_return_rel[1]


thm ConstrainUnpredictable.simps
thm simp_thms
thm if_simps
  apply (
        monad_return_rel_bind[where P="(=) :: bool \<Rightarrow> _"]
)
thm bind_return
thm tlb_enabled_def


thm monad.split
thm TLBLookup_def
thm monad_return_rel_assert_exp
thm 
        monad_return_rel_and_boolM
thm 
monad_return_rel_undefined_AccessDescriptor[THEN monad_return_rel_liftR, THEN monad_return_rel_bind]

text {*
lemma AArch64_FirstStageTranslateWithTag_monad_return_rel[monad_return_rel]:
  "monad_return_rel (const_regs_translate cfg)
    (AArch64_FirstStageTranslateWithTag vaddr acctype iswrite wasaligned sz iswritevalidcap)
    (AArch64_FirstStageTranslateWithTag vaddr acctype iswrite wasaligned sz iswritevalidcap)
    (\<lambda>res res'. IsFault res = IsFault res' \<and> (\<not> IsFault res \<longrightarrow>
        AddressDescriptor_vaddress res = AddressDescriptor_vaddress res'))"
  apply (simp add: AArch64_FirstStageTranslateWithTag_def)
  apply (monad_return_rel
    | rule
        monad_return_rel_and_boolM[THEN monad_return_rel_bind]
        monad_return_rel_bind[OF monad_return_rel_triv[where f="undefined_FaultRecord _"]]
        monad_return_rel_bind[OF monad_return_rel_triv[where f="undefined_TLBRecord _"]]
    | simp add:
        AArch64_AddressSizeFault_def UNKNOWN_bits_def AArch64_CreateFaultRecord_def
    | solves \<open>simp add: IsFault_def\<close>)+
  done

lemma AArch64_FullTranslateWithTag_monad_return_rel:
  "monad_return_rel (const_regs_translate cfg)
    (AArch64_FullTranslateWithTag vaddr acctype iswrite wasaligned sz iswritevalidcap)
    (AArch64_FullTranslateWithTag vaddr acctype iswrite wasaligned sz iswritevalidcap)
    (\<lambda>res res'. IsFault res = IsFault res' \<and> (\<not> IsFault res \<longrightarrow>
        AddressDescriptor_vaddress res = AddressDescriptor_vaddress res'))"
  apply (simp add: AArch64_FullTranslateWithTag_def)
  apply (monad_return_rel
    | rule
        monad_return_rel_and_boolM[THEN monad_return_rel_bind]
    | simp add: AArch64_SecondStageTranslate_def
  )+
  apply (clarsimp simp: AArch64_SecondStageTranslate_def split: if_split_asm)
  done

thm AArch64_SecondStageTranslate_def

locale Morello_Fixed_Address_Translation =
  Morello_Bounds_Address_Calculation +
  fixes translate_address :: "nat \<Rightarrow> nat option"
    and is_translation_event :: "register_value event \<Rightarrow> bool"
    (* TODO: Let assumptions refer to a trace (and possibly a state) instead of just events,
       allowing us to make assumptions about register values/fields that might change over time,
       e.g. PSTATE.EL *)
    and translation_assms :: "register_value event \<Rightarrow> bool"
  assumes translate_correct[simp]:
      "\<And>vaddress acctype iswrite wasaligned size iswritevalidcap addrdesc.
          Run (AArch64_FullTranslateWithTag vaddress acctype iswrite wasaligned size iswritevalidcap) t addrdesc \<Longrightarrow>
          \<not>IsFault addrdesc \<Longrightarrow>
          \<forall>e \<in> set t. translation_assms e \<Longrightarrow>
          translate_address (unat vaddress) = Some (unat (FullAddress_address (AddressDescriptor_paddress addrdesc)))"
    and no_cap_load_translation_events: "\<And>rk addr sz data. \<not>is_translation_event (E_read_memt rk addr sz data)"
    and translation_el: "\<And>t acctype el. Run (AArch64_AccessUsesEL acctype) t el \<Longrightarrow> \<forall>e \<in> set t. translation_assms e \<Longrightarrow> translation_el acctype = el"
    and s1_enabled: "\<And>t acctype s1e. Run (AArch64_IsStageOneEnabled acctype) t s1e \<Longrightarrow> \<forall>e \<in> set t. translation_assms e \<Longrightarrow> s1_enabled acctype = s1e"
    and tbi_enabled: "\<And>t acctype addr top. Run (AddrTop addr (translation_el acctype)) t top \<Longrightarrow> \<forall>e \<in> set t. translation_assms e \<Longrightarrow> tbi_enabled acctype (unat addr) = (top \<noteq> 63)"
    and in_host: "\<And>t acctype ih. Run (ELIsInHost (translation_el acctype)) t ih \<Longrightarrow> \<forall>e \<in> set t. translation_assms e \<Longrightarrow> in_host acctype = ih"
    and translate_address_valid: "\<And>vaddr acctype paddr. translate_address vaddr = Some paddr \<Longrightarrow> valid_address acctype vaddr"
    and translate_bounds_address: "\<And>vaddr acctype. valid_address acctype vaddr \<Longrightarrow> translate_address (bounds_address acctype vaddr) = translate_address vaddr"
    (* Memory pages are at least 4KB in AArch64 *)
    and translate_address_paged: "\<And>vaddr vaddr' paddr. translate_address vaddr = Some paddr \<Longrightarrow> vaddr' div 2^12 = vaddr div 2^12 \<Longrightarrow> translate_address vaddr' = Some (2^12 * (paddr div 2^12) + vaddr' mod 2^12)"
    (*and translate_address_paged: "\<And>vaddr vaddr' acctype paddr paddr'. translate_address vaddr acctype = Some paddr \<Longrightarrow> translate_address vaddr' acctype = Some paddr' \<Longrightarrow> vaddr div 2^12 = vaddr' div 2^12 \<Longrightarrow> paddr div 2^12 = paddr' div 2^12"
    and translate_address_page_offset: "\<And>vaddr acctype paddr. translate_address vaddr acctype = Some paddr \<Longrightarrow> paddr mod 2^12 = vaddr mod 2^12"*)
begin

end
