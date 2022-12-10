structure Strongest_Postcondition =
struct


(* "sp_tac0 true ctxt i" is a tactic that operates on the i-th goal which is assumed to be of 
   the form "qrhl A p1 skip ?B" where ?B is a schematic variable.
   sp_tac0 solves the subgoal (if p1 is built only from supported statements) and instantiates ?B
   to be the strongest precondition. (Strongest is not proven strongest, just best effort.)

   It also may produce additional new subgoals with required side conditions (e.g., losslessness, variable distinctness)

   "sp_tac0 false" operates analogously, except that it expects a goal of the form "qrhl A skip p2 ?B"
*)
fun sp_tac0 left ctxt = SUBGOAL (fn (goal,n) => let
  val (pre,p1,p2,post) = Relational_Hoare.dest_qrhl_goal goal
  fun lr l r = if left then l else r
  val stmts = HOLogic.dest_list (lr p1 p2)
  fun error kind = Misc.error_tac (fn _ => "Cound not instantiate "^Syntax.string_of_term ctxt post^
        " (should be schematic variable) with postcondition of \""^Syntax.string_of_term ctxt pre^
        "\" for "^kind^" "^Syntax.string_of_term ctxt (if left then p1 else p2)) ctxt
  in case stmts of

    [Const(\<^const_name>\<open>assign\<close>,_) $ _ $ _] => 
      (resolve_tac ctxt (lr @{thms sp1_assign_tac} @{thms sp2_assign_tac}) n
       ORELSE error "assign-statement")
       THEN Prog_Variables.distinct_vars_tac ctxt n
(*        THEN Expressions.index_tac ctxt n
       THEN Expressions.index_tac ctxt n
       THEN Expressions.subst_expression_tac ctxt n
       THEN Expressions.subst_expression_tac ctxt n
       THEN Expressions.map_expression_tac ctxt n *)

   | [Const(\<^const_name>\<open>sample\<close>,_) $ _ $ _] =>
      (resolve_tac ctxt (lr @{thms sp1_sample_tac} @{thms sp2_sample_tac}) n
       ORELSE error "sample-statement")
      THEN Prog_Variables.distinct_vars_tac ctxt n
(*       THEN Expressions.index_tac ctxt n
      THEN Expressions.index_tac ctxt n
      THEN Expressions.subst_expression_tac ctxt n
      THEN Expressions.subst_expression_tac ctxt n
      THEN Expressions.map_expression_tac ctxt n
      THEN Expressions.map_expression_tac ctxt n *)

  | [Const(\<^const_name>\<open>block\<close>,_) $ _] => 
      resolve_tac ctxt (lr @{thms sp1_block_tac} @{thms sp2_block_tac}) n THEN sp_tac0 left ctxt n
      ORELSE error "block"

  | [Const(\<^const_name>\<open>qapply\<close>,_) $ _ $ _] => 
      (resolve_tac ctxt (lr @{thms sp1_qapply_tac} @{thms sp2_qapply_tac}) n
       ORELSE error "quantum application")
      THEN Prog_Variables.distinct_vars_tac ctxt n
(*       THEN Expressions.index_tac ctxt n
      THEN Expressions.index_tac ctxt n
      THEN Expressions.map_expression_tac ctxt n
      THEN Expressions.map_expression_tac ctxt n *)

  | [Const(\<^const_name>\<open>qinit\<close>,_) $ _ $ _] => 
      (resolve_tac ctxt (lr @{thms sp1_qinit_tac} @{thms sp2_qinit_tac}) n
       ORELSE error "quantum initialization")
       THEN Prog_Variables.distinct_vars_tac ctxt n
(*       THEN Expressions.index_tac ctxt n
      THEN Expressions.index_tac ctxt n
      THEN Expressions.map_expression_tac ctxt n
      THEN Expressions.map_expression_tac ctxt n
      THEN Expressions.map_expression_tac ctxt n *)

  | [Const(\<^const_name>\<open>ifthenelse\<close>,_) $ _ $ _ $ _] => 
      (resolve_tac ctxt (lr @{thms sp1_if_tac} @{thms sp2_if_tac}) n
       ORELSE error "if-statement")
(*       THEN Expressions.index_tac ctxt (n+5) (* Doing it backwards because sp_tac0 can produce extra subgoals *)
      THEN Expressions.map_expression_tac ctxt (n+4)
      THEN Expressions.map_expression_tac ctxt (n+3) *)
      THEN sp_tac0 left ctxt (n+1)
      THEN sp_tac0 left ctxt n
      (* THEN Expressions.map_expression_tac ctxt n *)

  | [Const(\<^const_name>\<open>measurement\<close>,_) $ _ $ _ $ _] => 
      (resolve_tac ctxt (lr @{thms sp1_measure_tac} @{thms sp2_measure_tac}) n
       ORELSE error "measurement-statement")
      THEN Prog_Variables.distinct_vars_tac ctxt n
      THEN Prog_Variables.distinct_vars_tac ctxt n
(*       THEN Expressions.index_tac ctxt n
      THEN Expressions.index_tac ctxt n
      THEN Expressions.index_tac ctxt n
      THEN Expressions.subst_expression_tac ctxt n
      THEN Expressions.subst_expression_tac ctxt n
      THEN Expressions.map_expression_tac ctxt n
      THEN Expressions.map_expression_tac ctxt n *)

  | [] => 
      resolve_tac ctxt @{thms skip_rule} n
      ORELSE error "empty program"

   | _::_::_ => 
      (resolve_tac ctxt (lr @{thms sp1_cons_tac} @{thms sp2_cons_tac}) n
       ORELSE error "list of statements")
      THEN sp_tac0 left ctxt (n+1) (* Must happen first to instantiate A'; also to avoid subgoal indexing confusion from new subgoals *)
      THEN sp_tac0 left ctxt n

  | [s] => Misc.error_tac (fn _ => "Statement must be one of assign/sample/block/qinit/qapply/measure/if, not '"^Syntax.string_of_term ctxt s^"'") ctxt
  end)

fun sp_tac ctxt = SUBGOAL (fn (goal,n) => let
  val (_,p1,p2,_) = Relational_Hoare.dest_qrhl_goal goal
  in
    if p1 = \<^term>\<open>[]::program list\<close> then sp_tac0 false ctxt n
    else if p2 = \<^term>\<open>[]::program list\<close> then sp_tac0 true ctxt n
    else 
      resolve_tac ctxt @{thms sp_split_left_right_tac} n
      THEN
      sp_tac0 false ctxt (n+1)
      THEN
      sp_tac0 true ctxt n
  end)


fun get_sp left (prog:term) (pre:term) ctxt =
  let val progl = HOLogic.mk_list \<^typ>\<open>program\<close> [prog]
      val skip = \<^term>\<open>[]::program list\<close>
      val goal = \<^const>\<open>qrhl\<close> $ pre $ 
                      (if left then progl else skip) $ (if left then skip else progl) $ 
                      Var(("post",0),\<^typ>\<open>predicate expression2\<close>) |> HOLogic.mk_Trueprop                    
      val side_conditions = Unsynchronized.ref []
      fun tac ctxt = sp_tac0 left ctxt 1
                     THEN (fn st => (side_conditions := Thm.prems_of st; all_tac st))
                     THEN (ALLGOALS (Skip_Proof.cheat_tac ctxt))
      val thm = Goal.prove ctxt [] [] goal (fn {context=ctxt,...} => Misc.fail_on_LAZY_ERROR tac ctxt)
      val prop = Thm.prop_of thm
      val post = case HOLogic.dest_Trueprop prop of
        Const(\<^const_name>\<open>qrhl\<close>,_) $ _ $ _ $ _ $ post => post
        | _ => error "internal error"
  in
    (post,thm,!side_conditions)
  end

fun sp_seq_tac left right ctxt i = 
  Tactics.seq_tac left right
           (Var(("postcondition",0),\<^typ>\<open>predicate expression2\<close>)) ctxt i
  THEN
  sp_tac ctxt i

end
