structure Relational_Hoare =
struct

fun dest_qrhl (Const(\<^const_name>\<open>qrhl\<close>,_) $ A $ p1 $ p2 $ B) = (A,p1,p2,B)
  | dest_qrhl _ = raise Match
fun dest_qrhl_goal t = Logic.strip_imp_concl t |> HOLogic.dest_Trueprop |> dest_qrhl

(* fun read_predicate ctx str =
  let val preterm = Syntax.parse_term ctx str
      val t = Syntax.check_term ctx (Type.constraint \<^typ>\<open>predicate\<close> preterm)
  in Expressions.term_to_expression ctx t end *)

datatype qrhl_judgment = QRHL_Judgment of term * Programs.statement list * Programs.statement list * term

(* fun qrhl_judgment_to_term ctxt (QRHL_Judgment (pre, p1, p2, post)) =
  \<^const>\<open>qrhl\<close>
    $ Expressions.term_to_expression ctxt pre
    $ Programs.statements_to_term ctxt p1 $ Programs.statements_to_term ctxt p2
    $ Expressions.term_to_expression ctxt post

fun term_to_qrhl_judgment ctxt (Const(\<^const_name>\<open>qrhl\<close>,_) $ pre $ p1 $ p2 $ post) =
  QRHL_Judgment (Expressions.expression_to_term ctxt pre,
                 Programs.term_to_statements ctxt p1,
                 Programs.term_to_statements ctxt p2,
                 Expressions.expression_to_term ctxt post) *)

end
