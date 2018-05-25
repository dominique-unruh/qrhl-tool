structure Tactics =
struct

fun take_n_thm ctx n = 
  let val T = TFree(("'a"),@{sort type})
      val Tlist = HOLogic.listT T
      val l = Free(("l"),Tlist)
      val ss = List.tabulate (n, fn i => Free(("s"^string_of_int (i+1)),T))
      val ss_names = map (fst o dest_Free) ss
      val lhs = fold_rev (fn s => fn l => HOLogic.cons_const T $ s $ l) ss l
      val rhs = Const(@{const_name append}, Tlist --> Tlist --> Tlist) $ HOLogic.mk_list T ss $ l
      val prop = HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs,rhs))
      (* fun tac {context=ctx, ...} = ALLGOALS (Skip_Proof.cheat_tac ctx) *)
      fun tac {context=ctx, ...} = ALLGOALS (simp_tac ctx)
      (* fun tac {context=ctx, ...} = Method.NO_CONTEXT_TACTIC ctx (Method.sleep (seconds 5.0)) *)
      val thm = Goal.prove ctx ("l"::ss_names) [] prop tac
  in
    thm
  end

fun seq_tac i j B ctx = 
  let 
val _ = @{print} (@{thm seq} OF [take_n_thm ctx i])
val rule = @{thm seq} OF [take_n_thm ctx i, take_n_thm ctx j]
val _ = @{print} rule
      val rule = infer_instantiate ctx [(("B",0), Thm.cterm_of ctx B)] rule |> @{print}
  in
  resolve_tac ctx [rule] end

fun tac_on_term tac ctx t =
let val goal = Goal.init (Thm.cterm_of ctx (HOLogic.mk_Trueprop t))
in
case Seq.pull (tac goal) of
    NONE => NONE
  | SOME (goal',_) => SOME (Thm.prems_of goal' |> map HOLogic.dest_Trueprop)
end

fun seq_tac_on_term i j B ctx = tac_on_term (seq_tac i j B ctx 1) ctx

end