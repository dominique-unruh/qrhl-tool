structure Weakest_Precondition =
struct


(* TODO: rename as wp_tac (like joint_measure_tac) *)
(* "wp_tac true ctxt i" is a tactic that operates on the i-th goal which is assumed to be of 
   the form "qrhl ?A p1 skip B" where ?A is a schematic variable.
   wp_tac solves the subgoal (if p1 is built only from supported statements) and instantiates ?A
   to be the weakest precondition.

   "wp_tac false" operates analogously, except that it expects a goal of the form "qrhl ?A skip p2 B"
*)
fun wp_tac left ctxt = SUBGOAL (fn (goal,n) => let
  val (pre,p1,p2,post) = Encoding.dest_qrhl_goal goal
  fun lr l r = if left then l else r
  val stmts = HOLogic.dest_list (lr p1 p2)
  fun error kind = Misc.error_tac (fn _ => "Cound not instantiate "^Syntax.string_of_term ctxt pre^
        " (should be schematic variable) with precondition of \""^Syntax.string_of_term ctxt post^
        "\" for "^kind^" "^Syntax.string_of_term ctxt (if left then p1 else p2)) ctxt
  in case stmts of

    [Const(\<^const_name>\<open>assign\<close>,_) $ _ $ _] => 
      (resolve_tac ctxt (lr @{thms wp1_assign_tac} @{thms wp2_assign_tac}) n
       ORELSE error "assign-statement")
      THEN Expressions.index_tac ctxt n
      THEN Expressions.index_tac ctxt n
      THEN Expressions.subst_expression_tac ctxt n

  | [Const(\<^const_name>\<open>sample\<close>,_) $ _ $ _] =>
      (resolve_tac ctxt (lr @{thms wp1_sample_tac} @{thms wp2_sample_tac}) n
       ORELSE error "sample-statement")
      THEN Expressions.index_tac ctxt n
      THEN Expressions.index_tac ctxt n
      THEN Expressions.subst_expression_tac ctxt n
      
  | [Const(\<^const_name>\<open>block\<close>,_) $ _] => 
      resolve_tac ctxt (lr @{thms wp1_block_tac} @{thms wp2_block_tac}) n THEN wp_tac left ctxt n
      ORELSE error "block"

  | [Const(\<^const_name>\<open>qapply\<close>,_) $ _ $ _] => 
      (resolve_tac ctxt (lr @{thms wp1_qapply_tac} @{thms wp2_qapply_tac}) n
       ORELSE error "quantum application")
      THEN Expressions.index_tac ctxt n
      THEN Expressions.index_tac ctxt n
      THEN Expressions.map_expression_tac ctxt n

  | [Const(\<^const_name>\<open>qinit\<close>,_) $ _ $ _] => 
      (resolve_tac ctxt (lr @{thms wp1_qinit_tac} @{thms wp2_qinit_tac}) n
       ORELSE error "quantum initialization")
      THEN Expressions.index_tac ctxt n
      THEN Expressions.index_tac ctxt n
      THEN Expressions.map_expression_tac ctxt n

  | [Const(\<^const_name>\<open>ifthenelse\<close>,_) $ _ $ _ $ _] => 
      (resolve_tac ctxt (lr @{thms wp1_if_tac} @{thms wp2_if_tac}) n
       ORELSE error "if-statement")
      THEN Expressions.index_tac ctxt n
      THEN wp_tac left ctxt n
      THEN wp_tac left ctxt n
      THEN Expressions.map_expression_tac ctxt n
      
  | [Const(\<^const_name>\<open>measurement\<close>,_) $ _ $ _ $ _] => 
      (resolve_tac ctxt (lr @{thms wp1_measure_tac} @{thms wp2_measure_tac}) n
       ORELSE error "measurement-statement")
      THEN Expressions.index_tac ctxt n
      THEN Expressions.index_tac ctxt n
      THEN Expressions.index_tac ctxt n
      THEN Expressions.subst_expression_tac ctxt n
      THEN Expressions.map_expression_tac ctxt n

  | [] => 
      resolve_tac ctxt @{thms skip_rule} n
      ORELSE error "empty program"

  | _::_::_ => 
      (resolve_tac ctxt (lr @{thms wp1_cons_tac} @{thms wp2_cons_tac}) n
       ORELSE error "list of statements")
      THEN wp_tac left ctxt (n+1) (* Must happen first to instantiate B' *)
      THEN wp_tac left ctxt n

  | [s] => Misc.error_tac (fn _ => "Statement must be one of assign/sample/block/qinit/qapply/measure/if, not '"^Syntax.string_of_term ctxt s^"'") ctxt
  end)

fun get_wp_via_tac tac left (prog:term) (post:term) ctxt =
  let val progl = HOLogic.mk_list \<^typ>\<open>program\<close> [prog]
      val skip = \<^term>\<open>[]::program list\<close>
      val goal = \<^const>\<open>qrhl\<close> $ Var(("pre",0),\<^typ>\<open>predicate expression\<close>) $ 
                      (if left then progl else skip) $ (if left then skip else progl) $ post |> HOLogic.mk_Trueprop                    
      val thm = Goal.prove ctxt [] [] goal (fn {context,...} => tac context)
      val prop = Thm.prop_of thm
      val pre = case HOLogic.dest_Trueprop prop of
        Const(\<^const_name>\<open>qrhl\<close>,_) $ pre $ _ $ _ $ _ => pre
        | _ => error "internal error"
  in
    (pre,thm)
  end

fun get_wp_not_cleaned left = get_wp_via_tac (fn ctxt => wp_tac left ctxt 1) left

(* Cleans up the result of get_wp. That is, removes all index_{var,vars,expressions} and map_expression 
   and variants from the precondition of a qrhl judgement (i.e., "Trueprop (qrhl A p1 p2 B)"),
   and makes the expression explicit well-formed.

   Assuming all involved variables, variable lists, and expressions are all explicit. *)
fun wp_cleanup_conv ctxt =
 (Expressions.index_conv ctxt (* TODO this should be done directly as in joint_measure_simple_tac *)
  then_conv
  Conv.bottom_conv (fn ctxt => Conv.try_conv (Encoding.subst_expression_old_conv ctxt)) ctxt  (* TODO this should be done directly as in joint_measure_simple_tac *)
  then_conv
  Encoding.map_expression_subterm_conv ctxt (* TODO this should be done directly as in joint_measure_simple_tac *)
  then_conv
  Conv.try_conv (Expressions.clean_expression_conv ctxt)
  )
    |> Conv.arg_conv (* Trueprop *)
    |> Conv.fun_conv |> Conv.fun_conv |> Conv.fun_conv |> Conv.arg_conv (* precondition of qrhl *)

(* Computes a "weakest" (or as weak as we can) precondition
   for post w.r.t prograpm prog. Returns (pre,qrhl)
   where pre is the precondition, and qrhl is a 
   judgement "qrhl pre prog [] post" (if left=True)
   and  "qrhl pre [] prog post" (if left=False).

   If post is well-formed explicit, and so is prog (TODO: define
   well-formed explicit prog's), then pre is well-formed explicit.
 *)
fun get_wp left prog post ctxt = let
  val (_,thm) = Misc.fail_on_LAZY_ERROR (get_wp_not_cleaned left prog post) ctxt
(* val _ = @{print} thm *)
  val thm2 = Conv.fconv_rule (wp_cleanup_conv ctxt) thm
(* val _ = @{print} thm2 *)
  val (wp,_,_,_) = thm2 |> Thm.prop_of |> Encoding.dest_qrhl_goal
in
  (wp,thm2)         
end  

(* fun get_wp_clean left prog post ctxt = 
  let val (_,thm) = get_wp left prog post ctxt
      val thm2 = 
  in
    thm
  end *)

(*
fun get_wp1 prog post ctxt =
  case prog of
    Const(@{const_name assign},_) $ _ $ _ => get_wp1_assign prog post ctxt
  | Const(@{const_name sample},_) $ _ $ _ => get_wp1_sample prog post ctxt
  | _ => raise TERM ("get_wp1: Expected explicit single statement",[prog])
*)

(* fun wp1_tac ctxt = seq_tac -2 -1
SUBGOAL (fn (goal,i) => let
  val 
) *)

fun wp_seq_tac ctxt left i = 
  Tactics.seq_tac (if left then ~2 else ~1) (if left then ~1 else ~2)
           (Var(("precondition",0),\<^typ>\<open>predicate expression\<close>)) ctxt i THEN
  SUBGOAL (fn (goal,n) =>
    let val (_,p1,p2,B) = Encoding.dest_qrhl_goal goal
        val stmt = HOLogic.dest_list (if left then p1 else p2) |> the_single
        val (_,thm) = get_wp left stmt B ctxt
    in
      resolve_tac ctxt [thm] n
    end
  ) (i+1)


fun wp_tac_on_term left ctx = 
  Tactics.tac_on_term_concl (wp_seq_tac ctx left 1) ctx


end
 