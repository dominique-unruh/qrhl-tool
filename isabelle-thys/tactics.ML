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

structure MethodErrorStack = Proof_Data (
  type T = (unit -> string) list
  fun init _ = []
)
fun method_error_push msg = MethodErrorStack.map (fn st => msg::st)
val method_error = Attrib.setup_config_bool \<^binding>\<open>method_error\<close> (K false)
fun msg_to_string ctxt msg = String.concatWith "\n" (msg() :: map (fn m => "- "^m()) (MethodErrorStack.get ctxt))
fun error_ctac msg (ctx,_) = if Config.get ctx method_error
  then Seq.single (Seq.Error (fn _ => msg_to_string ctx msg)) else Seq.empty
fun error_tac msg ctx = if Config.get ctx method_error
  then (fn _ => raise ERROR(msg_to_string ctx msg)) else K Seq.empty
fun error_method msg = CONTEXT_METHOD (K (error_ctac msg))

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
  if Thm.nprems_of st < i then error_tac (fn _ => "No subgoal number "^string_of_int i^" (only "^string_of_int (Thm.nprems_of st)^" subgoals)") ctxt st else
  SUBGOAL (fn (goal,n) =>
  case (check goal; NONE) handle TAC_CHECK msg => SOME msg of
    NONE => tac (goal,n)
  | SOME msg => error_tac msg ctxt) i st


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

(* Applies tactic tac to the goal t.
   Returns NONE if tac fails, and the list of new subgoals otherwise.

   t has to be a term of type bool.
   The subgoals are returned without Trueprop *)
fun tac_on_term tac ctxt t =
  let val ctxt = Config.put method_error true ctxt
      val goal = Goal.init (Thm.cterm_of ctxt (HOLogic.mk_Trueprop t))
  in
  case Seq.pull (tac goal) of
      NONE => NONE
    | SOME (goal',_) => SOME (Thm.prems_of goal' |> map HOLogic.dest_Trueprop)
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

fun seq_tac_on_term i j B ctx = tac_on_term_concl (seq_tac i j B ctx 1) ctx

(* fun get_wp1_rule rule = get_wp1_tac (fn ctxt => resolve_tac ctxt rule 1)

val get_wp1_assign = get_wp1_rule @{thms wp1_assign}
val get_wp1_sample = get_wp1_rule @{thms wp1_sample} *)

(* "wp_tac0 true ctxt i" is a tactic that operates on the i-th goal which is assumed to be of 
   the form "qrhl ?A p1 skip B" where ?A is a schematic variable.
   wp_tac0 solves the subgoal (if p1 is built only from supported statements) and instantiates ?A
   to be the weakest precondition.

   "wp_tac0 false" operates analogously, except that it expects a goal of the form "qrhl ?A skip p2 B"

   The resulting weakest precondition is not cleaned up (e.g., contains terms such as 
   subst_expression etc.)
*)
fun wp_tac0 left ctxt = SUBGOAL_with_check ctxt (fn _ => ()) (fn (goal,n) => let
  val (pre,p1,p2,post) = Encoding.dest_qrhl_goal goal
  fun lr l r = if left then l else r
  val stmts = HOLogic.dest_list (lr p1 p2)
  fun error kind = error_tac (fn _ => "Cound not instantiate "^Syntax.string_of_term ctxt pre^
        " (should be schematic variable) with precondition of \""^Syntax.string_of_term ctxt post^
        "\" for "^kind^" "^Syntax.string_of_term ctxt (if left then p1 else p2)) ctxt
  in case stmts of
    [Const(\<^const_name>\<open>assign\<close>,_) $ _ $ _] => 
      resolve_tac ctxt (lr @{thms wp1_assign} @{thms wp2_assign}) n
      ORELSE error "assign-statement"
  | [Const(\<^const_name>\<open>sample\<close>,_) $ _ $ _] =>
      resolve_tac ctxt (lr @{thms wp1_sample} @{thms wp2_sample}) n
      ORELSE error "sample-statement"
  | [Const(\<^const_name>\<open>block\<close>,_) $ _] => 
      resolve_tac ctxt (lr @{thms wp1_block} @{thms wp2_block}) n THEN wp_tac0 left ctxt n
      ORELSE error "block"
  | [Const(\<^const_name>\<open>qapply\<close>,_) $ _ $ _] => 
      resolve_tac ctxt (lr @{thms wp1_qapply} @{thms wp2_qapply}) n
      ORELSE error "quantum application"
  | [Const(\<^const_name>\<open>qinit\<close>,_) $ _ $ _] => 
      resolve_tac ctxt (lr @{thms wp1_qinit} @{thms wp2_qinit}) n
      ORELSE error "quantum initialization"
  | [Const(\<^const_name>\<open>ifthenelse\<close>,_) $ _ $ _ $ _] => 
      resolve_tac ctxt (lr @{thms wp1_if} @{thms wp2_if}) n
      THEN wp_tac0 left ctxt n
      THEN wp_tac0 left ctxt n
      ORELSE error "if-statement"
  | [Const(\<^const_name>\<open>measurement\<close>,_) $ _ $ _ $ _] => 
      resolve_tac ctxt (lr @{thms wp1_measure} @{thms wp2_measure}) n
      ORELSE error "measurement-statement"
  | [] => 
      resolve_tac ctxt @{thms wp_skip} n
      ORELSE error "empty program"
  | _::_::_ => 
      (resolve_tac ctxt (lr @{thms wp1_cons} @{thms wp2_cons}) n
       THEN wp_tac0 left ctxt (n+1) (* Must happen first to instantiate B' *)
       THEN wp_tac0 left ctxt n)
      ORELSE error "list of statements"
  | [s] => error_tac (fn _ => "Statement must be one of assign/sample/block/qinit/qapply/measure/if, not '"^Syntax.string_of_term ctxt s^"'") ctxt
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

fun get_wp_not_cleaned left = get_wp_via_tac (fn ctxt => wp_tac0 left ctxt 1) left

(* Cleans up the result of get_wp. That is, removes all index_{var,vars,expressions} and map_expression 
   and variants from the precondition of a qrhl judgement (i.e., "Trueprop (qrhl A p1 p2 B)"),
   and makes the expression explicit well-formed.

   Assuming all involved variables, variable lists, and expressions are all explicit. *)
fun wp_cleanup_conv ctxt =
 (Expressions.index_conv ctxt (* TODO this should be done directly as in joint_measure_simple_tac *)
  then_conv
  Conv.bottom_conv (fn ctxt => Conv.try_conv (Encoding.subst_expression_conv ctxt)) ctxt  (* TODO this should be done directly as in joint_measure_simple_tac *)
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
  val (_,thm) = get_wp_not_cleaned left prog post ctxt
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

(* TODO rewrite using cert-functions *)
fun wp_tac ctxt left i = 
  seq_tac (if left then ~2 else ~1) (if left then ~1 else ~2)
           (Var(("precondition",0),\<^typ>\<open>predicate expression\<close>)) ctxt i THEN
  SUBGOAL (fn (goal,n) =>
    let val (_,p1,p2,B) = Encoding.dest_qrhl_goal goal
        val stmt = HOLogic.dest_list (if left then p1 else p2) |> the_single
        val (_,thm) = get_wp left stmt B ctxt
    in
      resolve_tac ctxt [thm] n
    end
  ) (i+1)


  (*
fun wp_tac_on_term left ctx = 
  tac_on_term_concl (wp_tac ctx left 1) ctx
   *)
  
  (* TODO: warning: checks are disabled in cert_codegen *)
fun wp_tac_on_term left ctx t =
      let fun f t = let val (t',cert) = Autogen_WP.wp1_tac ctx (if left then \<^const>\<open>True\<close> else \<^const>\<open>False\<close>) t val _ = cert () in 
    t'
  end
in SOME [apply_to_concl f t] end


end
