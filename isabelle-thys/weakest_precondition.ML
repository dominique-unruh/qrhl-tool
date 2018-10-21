structure Weakest_Precondition =
struct


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
      THEN Expressions.map_expression_tac ctxt n
      
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

fun get_wp left (prog:term) (post:term) ctxt =
  let val progl = HOLogic.mk_list \<^typ>\<open>program\<close> [prog]
      val skip = \<^term>\<open>[]::program list\<close>
      val goal = \<^const>\<open>qrhl\<close> $ Var(("pre",0),\<^typ>\<open>predicate expression\<close>) $ 
                      (if left then progl else skip) $ (if left then skip else progl) $ post |> HOLogic.mk_Trueprop                    
      val thm = Goal.prove ctxt [] [] goal (fn {context=ctxt,...} => Misc.fail_on_LAZY_ERROR (wp_tac left ctxt) 1)
      (* val thm = Conv.fconv_rule (wp_cleanup_conv ctxt) thm *)
      val prop = Thm.prop_of thm
      val pre = case HOLogic.dest_Trueprop prop of
        Const(\<^const_name>\<open>qrhl\<close>,_) $ pre $ _ $ _ $ _ => pre
        | _ => error "internal error"
  in
    (pre,thm)
  end

fun wp_seq_tac left ctxt i = 
  Tactics.seq_tac (if left then ~2 else ~1) (if left then ~1 else ~2)
           (Var(("precondition",0),\<^typ>\<open>predicate expression\<close>)) ctxt i
  THEN
  wp_tac left ctxt i
(*   SUBGOAL (fn (goal,n) =>
    let val (_,p1,p2,B) = Encoding.dest_qrhl_goal goal
        val stmt = HOLogic.dest_list (if left then p1 else p2) |> the_single
        val (_,thm) = get_wp left stmt B ctxt (* TODO: this looks silly, why not use wp_tac? *)
    in
      resolve_tac ctxt [thm] n
    end
  ) (i+1)
 *)

fun wp_tac_on_term left ctxt = 
  Tactics.tac_on_term_concl (wp_seq_tac left ctxt 1) ctxt


end
