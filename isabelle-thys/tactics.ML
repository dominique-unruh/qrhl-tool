structure Tactics =
struct

fun take_n_thm ctxt n : thm = 
  let val (names,ctxt1) = Variable.variant_fixes ("'a"::"l"::List.tabulate (n, fn i => "s"^string_of_int (i+1))) ctxt
      val (Tname,lname,ssnames) = case names of Tname::lname::ssnames => (Tname,lname,ssnames) | _  => error "internal"
      val T = TFree(Tname,\<^sort>\<open>type\<close>)
      val Tlist = HOLogic.listT T
      val l = Free(lname,Tlist)
      val ss = map (fn n => Free(n,T)) ssnames
      val lhs = fold_rev (fn s => fn l => HOLogic.cons_const T $ s $ l) ss l
      val rhs = Const(\<^const_name>\<open>append\<close>, Tlist --> Tlist --> Tlist) $ HOLogic.mk_list T ss $ l
      val prop = HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs,rhs))
      fun tac {context=ctxt', ...} = ALLGOALS (simp_tac ctxt')
      val thm = Goal.prove ctxt1 [] [] prop tac
      val thm2 = Variable.export ctxt1 ctxt [thm] |> the_single
  in
    thm2
  end


(* is_list l i returns true if l is an explicit partial list of length >= i.
Formally, if l is of the form "x1#x2#x3#...#xi#y" *)
fun is_list l n = if n<=0 then true
  else case l of Const(\<^const_name>\<open>Cons\<close>,_) $ _ $ l => is_list l (n-1)
               | _ => false

(* is_list l i returns true if l is an explicit list of length >= i.
Formally, if l is of the form "[x1,x2,x3,...,xi,...]" *)
fun is_complete_list (Const(\<^const_name>\<open>Nil\<close>,_)) n = n <= 0
  | is_complete_list (Const(\<^const_name>\<open>Cons\<close>,_) $ _ $ tl) n = is_complete_list tl (n-1)
  | is_complete_list _ _ = false

exception TAC_CHECK of unit -> string


(* fun seq_tac_checks_hard i j =
  if i < 0 then raise ERROR ("seq_tac: First argument must be nonnegative")
  else if j < 0 then raise ERROR ("seq_tac: Second argument must be nonnegative")
  else () *)

val dummy_term = \<^const>\<open>Pure.prop\<close> $ (@{const Pure.term(prop)} $ @{const Pure.dummy_pattern(prop)})

fun SUBGOAL_with_check ctxt check tac i st = 
  if Thm.prop_of st = dummy_term then no_tac st else
  if Thm.nprems_of st < i then Misc.error_tac (fn _ => "No subgoal number "^string_of_int i^" (only "^string_of_int (Thm.nprems_of st)^" subgoals)") ctxt st else
  SUBGOAL (fn (goal,n) =>
  case (check goal; NONE) handle TAC_CHECK msg => SOME msg of
    NONE => tac (goal,n)
  | SOME msg => Misc.error_tac msg ctxt) i st


fun seq_tac_checks i j goal : unit = 
  let val prop = Logic.strip_imp_concl goal in
  case prop of
    Const(\<^const_name>\<open>Trueprop\<close>,_) $ (Const(\<^const_name>\<open>qrhl\<close>,_) $ _ $ p1 $ p2 $ _) => (
    (* Check i *)
    if i >= 0 andalso not (is_list p1 i) then raise TAC_CHECK (fn _ => "Left program must consist of \<ge>"^string_of_int i^" statements") else ();
    if i < 0 andalso not (is_complete_list p1 (~i-1)) then raise TAC_CHECK (fn _ => "Left program must consist of \<ge>"^string_of_int (~i-1)^" statements") else ();

    (* Check j *)
    if j >= 0 andalso not (is_list p2 j) then raise TAC_CHECK (fn _ => "Right program must consist of \<ge>"^string_of_int j^" statements") else ();
    if j < 0 andalso not (is_complete_list p2 (~j-1)) then raise TAC_CHECK (fn _ => "Right program must consist of \<ge>"^string_of_int (~j-1)^" statements") else ();
  ())
  | _ => raise TAC_CHECK (K "Subgoal is not a qRHL judgement")
  end

(* Splits goal after the first i/j statements on left/right with intermediate pre/postcondition B.

If i/j is negative, count from the end (where i = -1 means splitting after the last statement, i = -2 means splitting off one statement, etc.)
 *)
fun seq_tac i j B ctxt = SUBGOAL_with_check ctxt (seq_tac_checks i j) (fn (goal,n) => 
    let val (p1,p2) = case Logic.strip_imp_concl goal |> HOLogic.dest_Trueprop of 
            Const(\<^const_name>\<open>qrhl\<close>,_) $ _ $ p1 $ p2 $ _ => (p1,p2)
            | _ => raise Match
        val i = if i>=0 then i else length (HOLogic.dest_list p1) + i + 1
        val j = if j>=0 then j else length (HOLogic.dest_list p2) + j + 1
        val rule = @{thm seqREMOVE} OF [take_n_thm ctxt i, take_n_thm ctxt j]
        val rule = infer_instantiate ctxt [(("B",0), Thm.cterm_of ctxt B)] rule
    in
      resolve_tac ctxt [rule] n
    end)

fun atomize ctxt t =
  let val t' = Object_Logic.atomize_term ctxt t
      val _ = if fastype_of t' <> \<^typ>\<open>bool\<close> then
                raise TERM("QRHL_Operations.atomize: could not convert term to a bool",[t])
              else ()
  in t' end

(* Applies tactic tac to the goal t.
   Returns NONE if tac fails, and the list of new subgoals otherwise.

   t has to be a term of type bool.
   The subgoals are returned without Trueprop *)
fun tac_on_term tac ctxt t =
  let val goal = Goal.init (Thm.cterm_of ctxt (HOLogic.mk_Trueprop t))
  in
  case Seq.pull (tac goal) of
      NONE => NONE
    | SOME (goal',_) => SOME (Thm.prems_of goal' |> map (atomize ctxt))
  end

(* Like tac_on_term, but works on terms of the form A1-->A2-->\<dots>-->B and
   operates on B only. (Carries over the premises to all subgoals.) *)
fun tac_on_term_concl tac ctxt (Const(\<^const_name>\<open>implies\<close>,_) $ a $ b) = 
      Option.map (map (fn t => HOLogic.mk_imp (a, t)))
      (tac_on_term_concl tac ctxt b)
  | tac_on_term_concl tac ctxt b = tac_on_term tac ctxt b


fun apply_to_concl f (Const(\<^const_name>\<open>implies\<close>,_) $ a $ b) = 
      (* Option.map (map (fn t => HOLogic.mk_imp (a, t))) *)
      HOLogic.mk_imp (a, apply_to_concl f b)
  | apply_to_concl f b = f b

(* fun seq_tac_on_term i j B ctx = tac_on_term_concl (seq_tac i j B ctx 1) ctx *)

(* fun get_wp1_rule rule = get_wp1_tac (fn ctxt => resolve_tac ctxt rule 1)

val get_wp1_assign = get_wp1_rule @{thms wp1_assign}
val get_wp1_sample = get_wp1_rule @{thms wp1_sample} *)

end
