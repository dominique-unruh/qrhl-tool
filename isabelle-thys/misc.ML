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
  
(* Solves a goal of the form "?x = a"
   by applying conv to a and then instantiating ?x with the result *)
fun schematic_conv_tac conv ctxt =
  CONVERSION (Conv.arg_conv (Conv.arg_conv (conv ctxt))) THEN' solve_tac ctxt @{thms refl}

end
