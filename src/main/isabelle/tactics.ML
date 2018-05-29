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

structure MethodErrorStack = Proof_Data (
  type T = (unit -> string) list
  fun init _ = []
)
fun method_error_push msg = MethodErrorStack.map (fn st => msg::st)
val method_error = Attrib.setup_config_bool @{binding method_error} (K false)
fun msg_to_string ctxt msg = String.concatWith "\n" (msg() :: map (fn m => "- "^m()) (MethodErrorStack.get ctxt))
fun error_ctac msg (ctx,_) = if Config.get ctx method_error
  then Seq.single (Seq.Error (fn _ => msg_to_string ctx msg)) else Seq.empty
fun error_tac msg ctx = if Config.get ctx method_error
  then K (raise ERROR(msg_to_string ctx msg)) else K Seq.empty
fun error_method msg = CONTEXT_METHOD (K (error_ctac msg))

(* is_list l i returns true if l is an explicit partial list of length >= i.
Formally, if l is of the form "x1#x2#x3#...#xi#y" *)
fun is_list l n = if n<=0 then true
  else case l of Const(@{const_name Cons},_) $ _ $ l => is_list l (n-1)
               | _ => false

(* is_list l i returns true if l is an explicit list of length >= i.
Formally, if l is of the form "[x1,x2,x3,...,xi,...]" *)
fun is_complete_list (Const(@{const_name Nil},_)) n = n <= 0
  | is_complete_list (Const(@{const_name Cons},_) $ _ $ tl) n = is_complete_list tl (n-1)
  | is_complete_list _ _ = false

exception TAC_CHECK of unit -> string


(* fun seq_tac_checks_hard i j =
  if i < 0 then raise ERROR ("seq_tac: First argument must be nonnegative")
  else if j < 0 then raise ERROR ("seq_tac: Second argument must be nonnegative")
  else () *)

val dummy_term = @{const Pure.prop} $ (@{const Pure.term(prop)} $ @{const Pure.dummy_pattern(prop)})

fun SUBGOAL_with_check ctxt check tac i st = 
  if Thm.prop_of st = dummy_term then no_tac st else
  if Thm.nprems_of st < i then error_tac (fn _ => "No subgoal number "^string_of_int i^" (only "^string_of_int (Thm.nprems_of st)^" subgoals)") ctxt st else
  SUBGOAL (fn (goal,n) =>
  case (check goal; NONE) handle TAC_CHECK msg => SOME msg of
    NONE => tac (goal,n)
  | SOME msg => error_tac msg ctxt) i st


fun seq_tac_checks i j goal : unit = 
  let val prop = Logic.strip_imp_concl goal in
  case prop of
    Const(@{const_name Trueprop},_) $ (Const(@{const_name qrhl},_) $ _ $ p1 $ p2 $ _) => (
    (* Check i *)
    if i >= 0 andalso not (is_list p1 i) then raise TAC_CHECK (fn _ => "Left program must consist of \<ge>"^string_of_int i^" statements") else ();
    if i < 0 andalso not (is_complete_list p1 (~i-1)) then raise TAC_CHECK (fn _ => "Left program must consist of \<ge>"^string_of_int (~i-1)^" statements") else ();

    (* Check j *)
    if j >= 0 andalso not (is_list p2 j) then raise TAC_CHECK (fn _ => "Right program must consist of \<ge>"^string_of_int j^" statements") else ();
    if j < 0 andalso not (is_complete_list p2 (~j-1)) then raise TAC_CHECK (fn _ => "Right program must consist of \<ge>"^string_of_int (~j-1)^" statements") else ();
  ())
  | _ => raise TAC_CHECK (K "Subgoal is not a qRHL judgement")
  end

fun seq_tac i j B ctxt = SUBGOAL_with_check ctxt (seq_tac_checks i j) (fn (goal,n) => 
    let val (p1,p2) = case Logic.strip_imp_concl goal |> HOLogic.dest_Trueprop of 
            Const(@{const_name qrhl},_) $ _ $ p1 $ p2 $ _ => (p1,p2)
            | _ => raise Match
        val i = if i>=0 then i else length (HOLogic.dest_list p1) + i + 1
        val j = if j>=0 then j else length (HOLogic.dest_list p2) + j + 1
        val rule = @{thm seq} OF [take_n_thm ctxt i, take_n_thm ctxt j]
        val rule = infer_instantiate ctxt [(("B",0), Thm.cterm_of ctxt B)] rule
    in
      resolve_tac ctxt [rule] n
    end)


fun tac_on_term tac ctx t =
  let val goal = Goal.init (Thm.cterm_of ctx (HOLogic.mk_Trueprop t))
  in
  case Seq.pull (tac goal) of
      NONE => NONE
    | SOME (goal',_) => SOME (Thm.prems_of goal' |> map HOLogic.dest_Trueprop)
  end

fun seq_tac_on_term i j B ctx = tac_on_term (seq_tac i j B ctx 1) ctx

(* fun get_wp1_rule rule = get_wp1_tac (fn ctxt => resolve_tac ctxt rule 1)

val get_wp1_assign = get_wp1_rule @{thms wp1_assign}
val get_wp1_sample = get_wp1_rule @{thms wp1_sample} *)


fun dest_qrhl_goal t = case Logic.strip_imp_concl t |> HOLogic.dest_Trueprop of 
  Const(@{const_name qrhl},_) $ A $ p1 $ p2 $ B => (A,p1,p2,B)
| _ => raise Match

fun wp1_tac ctxt = SUBGOAL_with_check ctxt (fn _ => ()) (fn (goal,n) => let
  val (_,p1,_,_) = dest_qrhl_goal goal
  val stmts = HOLogic.dest_list p1
  in case stmts of
    [Const(@{const_name assign},_) $ _ $ _] => resolve_tac ctxt @{thms wp1_assign} n
  | [Const(@{const_name sample},_) $ _ $ _] => resolve_tac ctxt @{thms wp1_sample} n
  | [Const(@{const_name block},_) $ _] => resolve_tac ctxt @{thms wp1_block} n THEN wp1_tac ctxt n
  | [] => resolve_tac ctxt @{thms wp1_skip} n
  | _::_::_ => error_tac (K "lists of statements not yet supported") ctxt
  | [_] => error_tac (fn _ => "Statement must be one of assign/sample/block, not '"^Syntax.string_of_term ctxt (the_single stmts)^"'") ctxt
  end
)

fun get_wp1_tac tac (prog:term) (post:term) ctxt =
  let val goal = @{const qrhl} $ Var(("pre",0),@{typ "predicate expression"}) $ 
                      HOLogic.mk_list @{typ program} [prog] $ @{term "[]::program list"} $ post |> HOLogic.mk_Trueprop                    
      val thm = Goal.prove ctxt [] [] goal (fn {context,...} => tac context)
      val prop = Thm.prop_of thm
      val pre = case HOLogic.dest_Trueprop prop of
        Const(@{const_name qrhl},_) $ pre $ _ $ _ $ _ => pre
        | _ => error "internal error"
  in
    (pre,thm)
  end

val get_wp1 = get_wp1_tac (fn ctxt => wp1_tac ctxt 1)

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

fun wp1_tac ctxt i = seq_tac ~2 ~1 (Var(("precondition",0),@{typ "predicate expression"})) ctxt i THEN
  SUBGOAL (fn (goal,n) =>
    let val (_,p1,_,B) = dest_qrhl_goal goal
        val stmt = HOLogic.dest_list p1 |> the_single
        val (_,thm) = get_wp1 stmt B ctxt
    in
      resolve_tac ctxt [thm] n
    end
  ) (i+1)
  
val error_context = @{context} |> Config.put method_error true |> method_error_push (K "While testing") |> method_error_push (K "And more")
val _ =
 get_wp1 @{term "assign x e :: program"} @{term "post :: predicate expression"} error_context
|> fst |> Thm.cterm_of @{context}
|> @{print}

end