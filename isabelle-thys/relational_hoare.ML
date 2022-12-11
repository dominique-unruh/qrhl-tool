structure Relational_Hoare =
struct

fun dest_qrhl (Const(\<^const_name>\<open>qrhl\<close>,_) $ A $ p1 $ p2 $ B) = (A,p1,p2,B)
  | dest_qrhl _ = raise Match
fun dest_qrhl_goal t = Logic.strip_imp_concl t |> HOLogic.dest_Trueprop |> dest_qrhl

fun read_predicate ctxt str =
  let val preterm = Syntax.parse_term ctxt str
      val expr = Programs.term_to_expression ctxt dummyT preterm
      val t = Syntax.check_term ctxt (Type.constraint \<^typ>\<open>predicate expression2\<close> expr)
  in t end

datatype qrhl_judgment = QRHL_Judgment of term * Programs.statement list * Programs.statement list * term

fun qrhl_judgment_to_term ctxt (QRHL_Judgment (pre, p1, p2, post)) =
  \<^const>\<open>qrhl\<close>
    $ pre
    $ Programs.statements_to_term ctxt p1 $ Programs.statements_to_term ctxt p2
    $ post

fun term_to_qrhl_judgment ctxt (Const(\<^const_name>\<open>qrhl\<close>,_) $ pre $ p1 $ p2 $ post) =
  QRHL_Judgment (pre,
                 Programs.term_to_statements ctxt p1,
                 Programs.term_to_statements ctxt p2,
                 post)
  | term_to_qrhl_judgment _ t = raise TERM("term_to_qrhl_judgment: not a qRHL judgment", [t])

end
