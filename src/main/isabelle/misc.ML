structure Misc =
struct

fun SOLVE1 tac st = 
  (tac THEN COND (has_fewer_prems (Thm.nprems_of st)) all_tac no_tac) st

fun conv_from_tac check tac ctxt ct =
  let val t = Thm.term_of ct
      val _ = check ctxt t
      val maxidx = Thm.maxidx_of_cterm ct
      val T = Thm.typ_of_cterm ct
      val goal = Logic.mk_equals (Thm.term_of ct, Var(("result",maxidx+1), T))
      val thm = Goal.prove ctxt [] [] goal (fn {context,...} => tac context THEN print_tac context "conv_from_tac subgoals:")
  in
    thm
  end

end
