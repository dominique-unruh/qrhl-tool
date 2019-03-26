structure Misc =
struct

val current_simpset = simpset_of \<^context>

fun prove_handle ctxt vars goal tac =
  Goal.prove ctxt vars [] goal (fn {context,...} => tac context)
  handle ERROR _ => raise TERM("Failed to prove goal",[goal])

fun SOLVE1 tac st = 
  (tac THEN COND (has_fewer_prems (Thm.nprems_of st)) all_tac no_tac) st

fun conv_from_tac check tac ctxt ct =
  let val t = Thm.term_of ct
      val _ = check ctxt t
      val maxidx = Thm.maxidx_of_cterm ct
      val T = Thm.typ_of_cterm ct
      val goal = Logic.mk_equals (Thm.term_of ct, Var(("result",maxidx+1), T))
      val thm = prove_handle ctxt [] goal tac
  in
    thm
  end


(* Converts e into (\<lambda>(x\<^sub>1,x\<^sub>2,x\<^sub>3,..). e (x\<^sub>1,x\<^sub>2,x\<^sub>3,..)).
  Names and types of x\<^sub>i are given by varlist.
  (Names are renamed to be distinct.)
 *)
fun pat_lambda_conv ctxt varlist ct = let
  val (tn,tT) = Variable.variant_frees ctxt [] [("term",Thm.typ_of_cterm ct)] |> hd
  val t' = Free(tn,tT)
  val varlist' = Name.variant_list [tn] (map fst varlist)
  val varlist'' = map2 (fn n => fn (_,T) => (n,T)) varlist' varlist
  val pattern = HOLogic.mk_tuple (map Free varlist'')
  val rhs = HOLogic.tupled_lambda pattern (t' $ pattern)
  val goal = Logic.mk_equals (t', rhs)
  val thm = 
    if varlist=[] then @{thm pat_lambda_conv_aux} else
    prove_handle ctxt ["term"] goal (fn context => simp_tac (put_simpset current_simpset context) 1)
  in
    infer_instantiate ctxt [(("term",0),ct)] thm
  end

fun change_conv conv ct =
  let val thm = conv ct
      val _ = if Thm.term_of (Thm.lhs_of thm) = Thm.term_of (Thm.rhs_of thm) then raise (CTERM("not changed",[ct])) else ()
  in
    thm
  end

fun conditional_conv test conv1 conv2 ct = if test ct then conv1 ct else conv2 ct

fun repeat_until_conv' test conv ct = 
  (conv 
  then_conv
  conditional_conv (test (SOME ct)) Conv.all_conv (repeat_until_conv' test conv)) ct

fun repeat_until_conv test conv ct =
  if test NONE ct then Conv.all_conv ct else repeat_until_conv' test conv ct
  

structure MethodErrorStack = Proof_Data (
  type T = (unit -> string) list
  fun init _ = []
)
datatype lazy_error = Lazy_Error of unit -> string
exception LAZY_ERROR of lazy_error
fun lazy_error msg = LAZY_ERROR (Lazy_Error msg)
val _ = ML_system_pp (fn depth => fn _ => fn Lazy_Error msg => Pretty.to_polyml (Pretty.str (msg ())))
fun method_error_push msg = MethodErrorStack.map (fn st => msg::st)
(* val method_error = Attrib.setup_config_bool \<^binding>\<open>method_error\<close> (K false) *)
fun msg_to_string ctxt msg () = String.concatWith "\n" (msg() :: map (fn m => "- "^m()) (MethodErrorStack.get ctxt))
fun error_ctac msg (ctx,_) = Seq.single (Seq.Error (msg_to_string ctx msg))
fun error_tac msg ctx _ = raise lazy_error (msg_to_string ctx msg)
fun error_tac' msg ctxt i st = error_tac (fn _ => msg (nth (Thm.prems_of st) (i-1))) ctxt i st
fun error_method msg = CONTEXT_METHOD (K (error_ctac msg))
fun fail_on_LAZY_ERROR f x = f x handle LAZY_ERROR (Lazy_Error msg) => raise ERROR (msg())

(* Solves a goal of the form "?x = a"
   by applying conv to a and then instantiating ?x with the result *)
fun schematic_conv_tac str conv ctxt i =
  (CONVERSION (Conv.params_conv ~1 (K (Conv.arg_conv (Conv.arg_conv (conv ctxt)))) ctxt) i
   ORELSE error_tac' (fn t => "Could not evaluate expression on lhs, not a " ^ str ^ ": " ^ 
        Syntax.string_of_term ctxt t) ctxt i)
  THEN solve_tac ctxt @{thms refl} i

fun mk_equals_cterm ct1 ct2 = let
  val T = Thm.typ_of_cterm ct1
  val thy = Thm.theory_of_cterm ct1
  val equals = Thm.global_cterm_of thy (Const(\<^const_name>\<open>Pure.eq\<close>,T --> T --> \<^typ>\<open>prop\<close>))
  in
    Thm.apply (Thm.apply equals ct1) ct2
  end


(* Given a tactic which solves a subgoal of the form "?x = a" by
  instantiating ?x:=a', produces a conversion that converts a to a' *)
fun schematic_tac_conv ctxt tac ct = let
  val var = Thm.var (("x",Thm.maxidx_of_cterm ct + 1),Thm.ctyp_of_cterm ct)
  val goal = mk_equals_cterm ct var
  val st = Goal.init goal
  val st = case Tactical.SINGLE (resolve_tac ctxt @{thms eq_reflection_swap} 1) st of
             SOME st => st
           | NONE => raise TERM ("schematic_tac_conv: eq_reflection", Thm.prems_of st)
  val st = case Tactical.SINGLE tac st of
             SOME st => st
           | NONE => raise TERM ("schematic_tac_conv: tactic failed", Thm.prems_of st)
  val _ = if not (Thm.no_prems st) then raise TERM ("schematic_tac_conv: tactic left subgoals", Thm.prems_of st) else ()
  val thm = Goal.finish ctxt st
  (* val goal = Logic *)
  in thm end


fun append_list_tac ctxt =
  CONVERSION (Raw_Simplifier.rewrite ctxt false
   @{thms append_Nil[THEN eq_reflection] append_Cons[THEN eq_reflection]})
  THEN' resolve_tac ctxt @{thms refl}

end
