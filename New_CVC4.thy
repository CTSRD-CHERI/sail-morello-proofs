section \<open>CVC4 dependency\<close>

theory New_CVC4

imports
    "Sail-T-CHERI.BW2"
begin

text \<open>
There are two issues with using CVC4 in the existing Isabelle2020
setup. The first is that CVC4-1.5 as shipped in Isabelle2020 seems
unstable and segmentation-faults on at least one of our machines.
The second is that the word SMT setup overrides the logic to nothing
rather than ALL, which seems to be accepted by Z3 but causes CVC4 to
print a warning which then confuses the result parser.

The below hacks the path to pick CVC4-1.8 and hacks the output
parser to drop warnings talking about set-logic.

The CVC4-1.8 component for Isabelle can be obtained by unpacking
\<^url>\<open>https://isabelle.in.tum.de/components/cvc4-1.8.tar.gz\<close>
into Isabelle's \<^path>\<open>contrib\<close> directory (typically either
a subdirectory of the Isabelle installation or
\<^path>\<open>$HOME/.isabelle/contrib\<close>.)
\<close>
ML \<open>
fun get_warning line = if match_string "cache-io-" line
  then SOME (space_explode ":" line |> drop 1 |> space_implode ":")
  else NONE

fun fetch_outcome solver_name [] =
    (warning (solver_name ^ ": no output"); (SMT_Solver.Unknown, []))
  | fetch_outcome solver_name lines = let
    val line = hd lines
    val warns_4 = map get_warning (take 4 lines)
    val has_set_logic = match_string "set-logic"
  in
    if List.all is_some warns_4 andalso has_set_logic (the (hd warns_4))
        andalso has_set_logic (the (List.last warns_4))
    then fetch_outcome solver_name (drop 4 lines)
    else if is_some (hd warns_4)
    then (warning (solver_name ^ ": " ^ the (hd warns_4));
        fetch_outcome solver_name (drop 1 lines))
    else if String.isPrefix "unsat" line then (SMT_Solver.Unsat, [line])
    else if String.isPrefix "sat" line then (SMT_Solver.Sat, [line])
    else (SMT_Solver.Unknown, [line])
  end
\<close>

ML \<open>
val cvc4_1_5_path = getenv "CVC4_SOLVER"
val cvc4_1_8_path = cvc4_1_5_path |> space_explode (Path.root |> Path.implode)
  |> map (fn s => if String.isPrefix "cvc4-1" s then "cvc4-1.8" else s)
  |> space_implode (Path.root |> Path.implode)

fun cvc4_options ctxt = [
    "--random-seed=" ^ string_of_int (Config.get ctxt SMT_Config.random_seed),
    "--lang=smt2",
    "--tlimit", string_of_int (Real.ceil (1000.0 * Config.get ctxt SMT_Config.timeout))]

val cvc4_1_8: SMT_Solver.solver_config =
{
  name = "cvc4_1_8",
  class = K SMTLIB_Interface.smtlibC,
  avail = (fn _ => true),
  command = (fn _ => [cvc4_1_8_path]),
  options = cvc4_options,
  smt_options = [(":produce-unsat-cores", "true")],
  default_max_relevant = 400 (* FUDGE *),
  outcome = fetch_outcome,
  parse_proof = SOME (K CVC4_Proof_Parse.parse_proof),
  replay = NONE }
\<close>

setup \<open>SMT_Solver.add_solver cvc4_1_8\<close>

(* testing *)
lemma
  fixes x :: "12 word"
  shows "(x XOR 12) >> 2 = (x >> 2) XOR 3"
  using [[smt_solver=cvc4_1_8]]
  using [[smt_trace]]
  by smt_word

end
