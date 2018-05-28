structure Tactics =
struct

fun take_n_thm ctxt n : thm = 
  let val (names,ctxt1) = Variable.variant_fixes ("'a"::"l"::List.tabulate (n, fn i => "s"^string_of_int (i+1))) ctxt
      val (Tname,lname,ssnames) = case names of Tname::lname::ssnames => (Tname,lname,ssnames) | _  => error "internal"
      val T = TFree(Tname,@{sort type})
      val Tlist = HOLogic.listT T
      val l = Free(lname,Tlist)
      val ss = map (fn n => Free(n,T)) ssnames
      val lhs = fold_rev (fn s => fn l => HOLogic.cons_const T $ s $ l) ss l
      val rhs = Const(@{const_name append}, Tlist --> Tlist --> Tlist) $ HOLogic.mk_list T ss $ l
      val prop = HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs,rhs))
      fun tac {context=ctxt', ...} = ALLGOALS (simp_tac ctxt')
      val thm = Goal.prove ctxt1 [] [] prop tac
      val thm2 = Variable.export ctxt1 ctxt [thm] |> the_single
  in
    thm2
  end

val method_error = Attrib.setup_config_bool @{binding method_error} (K false)
fun error_ctac msg (ctx,_) = if Config.get ctx method_error
  then Seq.single (Seq.Error msg) else Seq.empty
fun error_tac msg ctx = if Config.get ctx method_error
  then K (raise ERROR(msg ())) else K Seq.empty
fun error_method msg = CONTEXT_METHOD (K (error_ctac msg))

(* is_list l i returns true if l is an explicit list of length >= i.
Formally, if l is of the form "x1#x2#x3#...#xi#y" *)
fun is_list l n = if n<=0 then true
  else case l of Const(@{const_name Cons},_) $ _ $ l => is_list l (n-1)
               | _ => false
      

fun seq_tac_checks i j goal = 
  let val prop = Logic.strip_imp_concl goal in
  case prop of
    Const(@{const_name Trueprop},_) $ (Const(@{const_name qrhl},_) $ _ $ p1 $ p2 $ _) => 
      if not (is_list p1 i) then SOME (fn _ => "Left program must consist of "^string_of_int i^" statements")
      else if not (is_list p2 j) then SOME (fn _ => "Right program must consist of "^string_of_int j^" statements")
      else NONE
    | _ => SOME (K "Subgoal is not a qRHL judgement")
  end

fun seq_tac_checks_hard i j =
  if i < 0 then raise ERROR ("seq_tac: First argument must be nonnegative")
  else if j < 0 then raise ERROR ("seq_tac: Second argument must be nonnegative")
  else ()

fun seq_tac i j B ctx = 
  (seq_tac_checks_hard i j;
  SUBGOAL (fn (goal,n) => case seq_tac_checks i j goal of
    SOME msg => error_tac (fn _ => "seq_tac: "^msg()) ctx
  | NONE => let val rule = @{thm seq} OF [take_n_thm ctx i, take_n_thm ctx j]
            val rule = infer_instantiate ctx [(("B",0), Thm.cterm_of ctx B)] rule
            in
              resolve_tac ctx [rule] n
            end))

fun tac_on_term tac ctx t =
let val goal = Goal.init (Thm.cterm_of ctx (HOLogic.mk_Trueprop t))
in
case Seq.pull (tac goal) of
    NONE => NONE
  | SOME (goal',_) => SOME (Thm.prems_of goal' |> map HOLogic.dest_Trueprop)
end

fun seq_tac_on_term i j B ctx = tac_on_term (seq_tac i j B ctx 1) ctx

fun get_wp1 (prog:term) (post:term) ctxt =
  let val goal = @{const qrhl} $ Var(("pre",0),@{typ "predicate expression"}) $ 
                      prog $ @{term "[]::program list"} $ post |> HOLogic.mk_Trueprop
      fun tac {context,prems=_} = resolve_tac context @{thms wp1_assign} 1
      val thm = Goal.prove ctxt [] [] goal tac
      val prop = Thm.prop_of thm
      val pre = case HOLogic.dest_Trueprop prop of
        Const(@{const_name qrhl},_) $ pre $ _ $ _ $ _ => pre
        | _ => error "internal error"
  in
    (pre,thm)
  end

val _ =
 (get_wp1 @{term "[assign x e]"} @{term "post :: predicate expression"} @{context})
|> fst |> Thm.cterm_of @{context}

|> @{print}

end