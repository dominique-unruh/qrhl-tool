structure Misc =
struct

val current_simpset = simpset_of \<^context>

val dddot_var = Syntax.var Auto_Bind.dddot

fun string_of_term_truncated ctxt depth t = let
  fun trunc d t = if d <= 0 then dddot_var
    else case t of
      \<^Const_>\<open>numeral _\<close> $ _ => t
    | u $ v => trunc d u $ trunc (d-1) v
    | Abs(x, T, body) => Abs(x, T, trunc (d-1) body)
    | _ => t
in Syntax.string_of_term ctxt (trunc depth t) end

fun prove_handle ctxt goal tac =
  Goal.prove_internal ctxt [] goal (fn _ => tac ctxt)
  handle ERROR _ => raise CTERM("Failed to prove goal",[goal])

fun SOLVE1 tac st = 
  (tac THEN COND (has_fewer_prems (Thm.nprems_of st)) all_tac no_tac) st

fun generalized_reflexivity ct1 ct2 = let
  val thm1 = (Thm.beta_conversion true then_conv Thm.eta_conversion) ct1
  val thm2 = (Thm.beta_conversion true then_conv Thm.eta_conversion) ct2
  val thm = Thm.transitive thm1 (Thm.symmetric thm2)
          handle THM _ => raise CTERM ("generalized_reflexivity: mismatch", [ct1, ct2])
in thm end


(* (* Converts e into (\<lambda>(x\<^sub>1,x\<^sub>2,x\<^sub>3,..). e (x\<^sub>1,x\<^sub>2,x\<^sub>3,..)).
  Names and types of x\<^sub>i are given by varlist.
  (Names are renamed to be distinct.)
 *)
fun pat_lambda_conv ctxt varlist ct = let
  val (tn,tT) = Variable.variant_frees ctxt [] [("term",Thm.typ_of_cterm ct)] |> hd
  val t' = Free(tn,tT)
  val varlist' = Name.variant_list [tn] (map fst varlist)
  val varlist'' = map2 (fn n => fn (_,T) => (n,T)) varlist' varlist
  val pattern = HOLogic.mk_tuple (map Free varlist'')
  val rhs = HOLogic.tupled_lambda pattern (t' $ pattern)
  val goal = Logic.mk_equals (t', rhs)
  val thm = 
    if varlist=[] then @{thm pat_lambda_conv_aux} else
    prove_handle ctxt ["term"] goal (fn context => simp_tac (put_simpset current_simpset context) 1)
  in
    infer_instantiate ctxt [(("term",0),ct)] thm
  end *)

fun change_conv conv ct =
  let val thm = conv ct
      val _ = if Thm.term_of (Thm.lhs_of thm) = Thm.term_of (Thm.rhs_of thm) then raise (CTERM("not changed",[ct])) else ()
  in
    thm
  end

fun conditional_conv test conv1 conv2 ct = if test ct then conv1 ct else conv2 ct

fun repeat_until_conv' test conv ct = 
  (conv 
  then_conv
  conditional_conv (test (SOME ct)) Conv.all_conv (repeat_until_conv' test conv)) ct

fun repeat_until_conv test conv ct =
  if test NONE ct then Conv.all_conv ct else repeat_until_conv' test conv ct
  
(* Like Thm.is_dummy but also says true on "prop TERM _" and not just "TERM _".
(Seems to occur sometimes as a dummy goal.)  *)
fun is_dummy2 thm =
  let fun unprotect_maybe t = (Logic.unprotect t handle TERM _ => t)
  in case try Logic.dest_term (unprotect_maybe (Thm.concl_of thm)) of
    NONE => false
  | SOME t => Term.is_dummy_pattern (Term.head_of t) end


structure MethodErrorStack = Proof_Data (
  type T = (unit -> string) list
  fun init _ = []
)
datatype lazy_error = Lazy_Error of unit -> string
exception LAZY_ERROR of lazy_error
fun lazy_error msg = LAZY_ERROR (Lazy_Error msg)
val _ = ML_system_pp (fn _ => fn _ => fn Lazy_Error msg => Pretty.to_polyml (Pretty.str (msg ())))
fun method_error_push msg = MethodErrorStack.map (fn st => msg::st)
(* val method_error = Attrib.setup_config_bool \<^binding>\<open>method_error\<close> (K false) *)
fun msg_to_string ctxt msg () = String.concatWith "\n" (msg() :: map (fn m => "- "^m()) (MethodErrorStack.get ctxt))
fun error_ctac msg (ctx,_) = Seq.single (Seq.Error (msg_to_string ctx msg))
fun error_tac msg ctx : tactic = fn st => if is_dummy2 st then no_tac st else raise lazy_error (msg_to_string ctx msg)
fun error_tac' msg ctxt i : tactic = fn st => error_tac (fn () => 
  let val goal = nth (Thm.prems_of st) (i-1) handle Subscript => \<^prop>\<open>not_enough_subgoals\<close>
  in msg goal end) ctxt st
fun error_method msg = CONTEXT_METHOD (K (error_ctac msg))
fun fail_on_LAZY_ERROR f x = f x handle LAZY_ERROR (Lazy_Error msg) => raise ERROR (msg())
fun remove_LAZY_ERROR_in_seq xq =
  Seq.make (fn () => (case Seq.pull xq of NONE => NONE 
                   | SOME (x, xq') => SOME (x, remove_LAZY_ERROR_in_seq xq')
                  handle LAZY_ERROR _ => NONE))

fun fail_tac_on_LAZY_ERROR tac st = 
  (tac st |> remove_LAZY_ERROR_in_seq)
  handle LAZY_ERROR _ => Seq.empty

fun succeed_or_error_tac' tac ctxt msg = SUBGOAL (fn (_,i) => tac i ORELSE error_tac' msg ctxt i)

(* Solves a goal of the form "?x = a"
   by applying conv to a and then instantiating ?x with the result *)
fun schematic_conv_tac str conv ctxt i =
  (CONVERSION (Conv.params_conv ~1 (K (Conv.arg_conv (Conv.arg_conv (conv ctxt)))) ctxt) i
   ORELSE error_tac' (fn t => "Could not evaluate expression on lhs, not a " ^ str ^ ": " ^ 
        Syntax.string_of_term ctxt t) ctxt i)
  THEN solve_tac ctxt @{thms refl} i

fun mk_equals_cterm ct1 ct2 = let
  val T = Thm.typ_of_cterm ct1
  val thy = Thm.theory_of_cterm ct1
  val equals = Thm.global_cterm_of thy (Const(\<^const_name>\<open>Pure.eq\<close>,T --> T --> \<^typ>\<open>prop\<close>))
  in
    Thm.apply (Thm.apply equals ct1) ct2
  end


(* Given a tactic which solves a subgoal of the form "?x = a" by
  instantiating ?x:=a', produces a conversion that converts a to a' *)
fun schematic_tac_conv ctxt tac ct = let
  val var = Thm.var (("x",Thm.maxidx_of_cterm ct + 1),Thm.ctyp_of_cterm ct)
  val goal = mk_equals_cterm ct var
  val st = Goal.init goal
  val st = case Tactical.SINGLE (resolve_tac ctxt @{thms eq_reflection_swap} 1) st of
             SOME st => st
           | NONE => raise TERM ("schematic_tac_conv: eq_reflection", Thm.prems_of st)
  val st = case Tactical.SINGLE tac st of
             SOME st => st
           | NONE => raise TERM ("schematic_tac_conv: tactic failed", Thm.prems_of st)
  val _ = if not (Thm.no_prems st) then raise TERM ("schematic_tac_conv: tactic left subgoals", Thm.prems_of st) else ()
  val thm = Goal.finish ctxt st
  (* val goal = Logic *)
  in thm end

fun append_list_tac ctxt = SUBGOAL (fn (t,i) => case t |> Logic.strip_assums_concl |> HOLogic.dest_Trueprop |> HOLogic.dest_eq |> snd of
  Const(\<^const_name>\<open>append\<close>,_) $ Const(\<^const_name>\<open>Nil\<close>,_) $ _ => resolve_tac ctxt @{thms append_Nil[symmetric]} i
  | Const(\<^const_name>\<open>append\<close>,_) $ (Const(\<^const_name>\<open>Cons\<close>,_) $ _ $ _) $ _ => 
      resolve_tac ctxt @{thms append_list_tac_aux} i
      THEN append_list_tac ctxt i
  | _ => raise TERM("rhs is not a concatenation of explicit lists",[t]))

(* Expects a goal of the form lhs = rhs
   where lhs is built from schematic variables and # and @
   and rhs is an explicit list.

   The lhs may contain at most one schematic variable matching lists (i.e., ?a @ ?b is not allowed)

   Solves that goal by instantiating the schematic variable on the lhs *)
fun match_list_tac ctxt = SUBGOAL (fn (t,i) => case t |> Logic.strip_assums_concl |> HOLogic.dest_Trueprop |> HOLogic.dest_eq of
  (Const(\<^const_name>\<open>Cons\<close>,_) $ _ $ _, Const(\<^const_name>\<open>Cons\<close>,_) $ _ $ _) =>
      resolve_tac ctxt @{thms match_list_tac_aux1} i
      THEN match_list_tac ctxt i
  | (Const(\<^const_name>\<open>append\<close>,_) $ (Const(\<^const_name>\<open>Cons\<close>,_) $ _ $ _) $ _, Const(\<^const_name>\<open>Cons\<close>,_) $ _ $ _) =>
      resolve_tac ctxt @{thms match_list_tac_aux2} i
      THEN match_list_tac ctxt i
  | (Const(\<^const_name>\<open>append\<close>,_) $ Const(\<^const_name>\<open>Nil\<close>,_) $ _, _) =>
      resolve_tac ctxt @{thms match_list_tac_aux3} i
      THEN match_list_tac ctxt i
  | (Const(\<^const_name>\<open>append\<close>,_) $ Var _ $ rest, rhs) =>
      let val rlen = length (HOLogic.dest_list rest)
                     handle TERM _ => raise TERM("match_list_tac: need an explicit list on rhs of lhs",[t,rest])
          val llen = length (HOLogic.dest_list rhs)
                     handle TERM _ => raise TERM("match_list_tac: need an explicit list on lhs",[t,rhs])
      in
        if rlen < llen then
          resolve_tac ctxt @{thms match_list_tac_aux2} i
          THEN match_list_tac ctxt i
        else if rlen = llen then
          resolve_tac ctxt @{thms match_list_tac_aux3} i
          THEN match_list_tac ctxt i
        else
          raise TERM("match_list_tac: mismatch (not enough elements on rhs)",[t])
      end
  | (Var _, _) =>
      resolve_tac ctxt @{thms refl} i
  | (Const(\<^const_name>\<open>Nil\<close>,_), Const(\<^const_name>\<open>Nil\<close>,_)) => 
      resolve_tac ctxt @{thms refl} i
  | (_,_) => raise TERM("match_list_tac: mismatch",[t])
)

fun mk_less_eq t u = let val T = fastype_of t in Const(\<^const_name>\<open>less_eq\<close>, T --> T --> HOLogic.boolT) $ t $ u end

fun dest_numeral_syntax (Const(\<^const_syntax>\<open>Num.num.One\<close>, _)) = 1
  | dest_numeral_syntax (Const(\<^const_syntax>\<open>Num.num.Bit0\<close>, _) $ bs) = 2 * dest_numeral_syntax bs
  | dest_numeral_syntax (Const (\<^const_syntax>\<open>Num.num.Bit1\<close>, _) $ bs) = 2 * dest_numeral_syntax bs + 1
  | dest_numeral_syntax (Const ("_constrain", _) $ t $ _) = dest_numeral_syntax t
  | dest_numeral_syntax t = raise TERM ("dest_numeral_syntax", [t]);

fun dest_number_syntax (Const (\<^const_syntax>\<open>Groups.zero_class.zero\<close>, _)) = 0
  | dest_number_syntax (Const (\<^const_syntax>\<open>Groups.one_class.one\<close>, _)) = 1
  | dest_number_syntax (Const (\<^const_syntax>\<open>Num.numeral_class.numeral\<close>, _) $ t) =
      dest_numeral_syntax t
  | dest_number_syntax (Const (\<^const_syntax>\<open>Groups.uminus_class.uminus\<close>, _) $ t) =
      ~ (dest_number_syntax t)
  | dest_number_syntax (Const ("_constrain", _) $ t $ _) = dest_number_syntax t
  | dest_number_syntax t = raise TERM ("dest_number_syntax", [t])

structure MLThmAttribData = Proof_Data (
  type T = Proof.context -> thm -> thm
  fun init _ _ thm = raise THM ("uninitialized MLThmAttribData", 0, [thm]))

(* Invoked as \<open>thm[ML_thm \<open>mlcode\<close>]\<close> or \<open>[[ML_thm \<open>mlcode\<close>]]\<close> where \<open>mlcode\<close> is of type \<open>Proof.context -> thm -> thm\<close>,
  it runs \<open>mlcode\<close> on the theorem \<open>thm\<close> (or on a dummy fact) and returns the resulting theorem.
  Optionally, after \<open>mlcode\<close>, we can give \<open>(is \<open>pattern\<close>)\<close> to bind schematic variables by pattern 
  matching the theorem. *)
val _ = Theory.setup (Attrib.setup \<^binding>\<open>ML_thm\<close>
  (Args.context -- Scan.lift Parse.ML_source 
      -- Scan.lift (Scan.optional (Parse.$$$ "(" |-- Parse.!!! (Scan.repeat1 (Parse.$$$ "is" |-- Parse.prop) --| Parse.$$$ ")")) []) 
      >> (fn ((ctxt,source),is_props) =>
  let
    val function = 
        ctxt |> Context.Proof
        |> ML_Context.expression (Input.pos_of source)
              (ML_Lex.read "Theory.local_setup (Misc.MLThmAttribData.put ((" @
                 ML_Lex.read_source source @ ML_Lex.read ") : Proof.context -> thm -> thm))")
        |> Context.the_proof
        |> MLThmAttribData.get
    val is_props = is_props |> map (Syntax.read_prop (Proof_Context.set_mode Proof_Context.mode_pattern ctxt))
    val attrib = Thm.mixed_attribute (fn (context,thm) => let
        val thm' = function (Context.proof_of context) thm
        val context = if null is_props then context else let
                        val binds = Proof_Context.simult_matches ctxt (Thm.prop_of thm', is_props)
                      in Context.map_proof (fold Proof_Context.bind_term binds) context end
        in (context,thm') end)
  in
    attrib
  end))
  "Apply ML function to the given fact")

fun mk_ct_equals ct1 ct2 = let
  val eq = \<^instantiate>\<open>'a=\<open>Thm.ctyp_of_cterm ct1\<close> in cterm Pure.eq\<close>
  in
    Thm.apply (Thm.apply eq ct1) ct2
  end

(* For debugging. Never call outside of experiments (has a hardcoded Linux terminal in it) *)
val tty_handle = Lazy.lazy (fn () => TextIO.openOut "/dev/pts/2")
fun tty s = (TextIO.output (Lazy.force tty_handle, (s |> Output.output |> YXML.content_of) ^ "\n"); TextIO.flushOut (Lazy.force tty_handle))

(* Transforms str into a valid identifier (if it isn't one yet).
   (Simply by truncating or replacing by "x".) *)
fun make_identifier str = let
  val symbols = Symbol_Pos.explode (str, Position.none)
  val good_prefix = (Scan.finite Symbol_Pos.stopper Symbol_Pos.scan_ident || Scan.succeed []) symbols |> fst
  val new_id = if null good_prefix then "x" else good_prefix |> Symbol_Pos.implode
  val _ = \<^assert> (Symbol_Pos.is_identifier new_id)
in
  new_id
end

(* Searches for the first occurrence of pattern `pat` in `term`. 
   Returns the matching subterm (not the position).
   First-order matching is performed.
 *)
fun first_order_search thy pat term = 
  (if Term.is_open term then raise Pattern.MATCH
   else Pattern.first_order_match thy (pat,term) (Vartab.empty,Vartab.empty); SOME term)
  handle Pattern.MATCH => case term of
    t1 $ t2 => (case first_order_search thy pat t1 of SOME t => SOME t
                      | NONE => first_order_search thy pat t2)
  | Abs(_,_,body) => first_order_search thy pat body
  | _ => NONE

(* Finds all occurrences of `subterm` in `term`.
   Occurrences must be \<alpha>-convertible to `subterm`.
   Returns a context (with a free bound variable indicating the hole). *)
fun find_all_subterm_occurrences subterm term i =
  if term aconv subterm then Bound i
  else case term of
    t1 $ t2 => find_all_subterm_occurrences subterm t1 i $ find_all_subterm_occurrences subterm t2 i
  | Abs(v,T,body) => Abs(v,T,find_all_subterm_occurrences subterm body (i+1))
  | t => t

(* Finds first occurrence `st` of `pat` in the subgoal `t`. 
   Then replaces `t` by `\<And>x. C[x]` (where C is t with all occurrences of st removed).
   The name `x` of the bound variable is returned by the function `varname st`.
 *)
fun generalize_tac ctxt varname pat = SUBGOAL (fn (t,i) => case first_order_search (Proof_Context.theory_of ctxt) pat t of
  NONE => (* raise TERM("generalize_tac: did not find pattern", [pat,t]) *) no_tac
  | SOME subterm => let
    val context = find_all_subterm_occurrences subterm t 0
    val subterm_ct = Thm.cterm_of ctxt subterm
    val subtermT = Thm.ctyp_of_cterm subterm_ct
    val context_ct = Thm.cterm_of ctxt (Abs("", Thm.typ_of subtermT, context))
    val var = varname subterm |> make_identifier
    val rule = \<^instantiate>\<open>context_ct and subterm_ct and 'a=subtermT in
                   lemma \<open>(\<And>bound. PROP context_ct bound) \<Longrightarrow> PROP context_ct subterm_ct\<close> by assumption\<close>
    (* Rename the bound variable to var, this provides the default for the variable in the final goal *)
    val rule = rule |> Thm.rename_boundvars (Abs("bound",dummyT,Term.dummy)) (Abs(var,dummyT,Term.dummy))
    val tac = compose_tac ctxt (false, rule, 1) i
  in tac end)

fun mk_ctxt_conv (f: conv -> conv) (conv: Proof.context -> conv) (ctxt: Proof.context) : conv = 
  f (conv ctxt)

fun mk_ctxt_conv2 (f: conv -> conv -> conv) (conv1: Proof.context -> conv) (conv2: Proof.context -> conv) (ctxt: Proof.context) : conv = 
  f (conv1 ctxt) (conv2 ctxt)

fun then_ctxt_conv (conv1: Proof.context -> conv) (conv2: Proof.context -> conv) (ctxt: Proof.context) : conv = 
  conv1 ctxt then_conv conv2 ctxt

fun concl_conv2 conv ctxt ct = case Thm.term_of ct of
  \<^Const_>\<open>Pure.all _\<close> $ Abs _ => Conv.arg_conv (Conv.abs_conv (fn (_,ctxt) => concl_conv2 conv ctxt) ctxt) ct
  | \<^Const>\<open>Pure.imp\<close> $ _ $ _ => Conv.arg_conv (concl_conv2 conv ctxt) ct
  | _ => conv ctxt ct

fun concl_conv_Trueprop conv = conv |> mk_ctxt_conv HOLogic.Trueprop_conv |> concl_conv2

fun print_here_tac ctxt here = print_tac ctxt ("Goal state" ^ Position.here here ^ ":")

(* Like resolve_tac, except:
   - no backtracking (returns an option not a seq)
   - returns the applied rule *)
fun resolve_and_remember_rule _    []            i st : (thm * thm) option = NONE
  | resolve_and_remember_rule ctxt (rule::rules) i st =
      case resolve_tac ctxt [rule] i st |> Seq.pull of
        SOME (st',_) => SOME (rule, st')
      | NONE => resolve_and_remember_rule ctxt rules i st

(* Stringifies a theorem either via its name (if known) or its term.
   Prefixed with pfx_name or pfx_term, respectively. *)
fun theorem_or_name ctxt pfx_name pfx_term thm = 
  if Thm.has_name_hint thm
  then pfx_name ^ (Pretty.marks_str (Proof_Context.markup_extern_fact ctxt (Thm.get_name_hint thm)) |> Pretty.string_of)
  else pfx_term ^ Syntax.string_of_term ctxt (Thm.prop_of thm)

(* (* Removes outermost unused \<And>'s from goal. *)
fun clean_params_tac i = REPEAT (CONVERSION (Conv.rewr_conv @{thm triv_forall_equality}) i) *)

fun forall_dest_list ct = case Thm.term_of ct of
  \<^Const_>\<open>Pure.all _\<close> $ Abs _ => let 
      val (param, body) = Thm.dest_abs_global (Thm.dest_arg ct)
      val (params, body') = forall_dest_list body
      in (param::params, body') end
  | _ => ([], ct)                           

(* Runs tactic tac on the i-th subgoal as the only subgoal.
   tac must solve the subgoal.
   Parameters (outermost \<And>'s) are removed.
   Schematics are preserved.
   Note: When tac solves the goal, MY_SUBGOAL can still fail. E.g.:
         Goal is \<open>\<And>x. x = ?y\<close> (unprovable), but tac sees \<open>x = ?y\<close> (provable).

   Current limitations:
   - tac is implicitly made deterministic (no backtracking)
*)
fun MY_SUBGOAL ctxt tac : int -> tactic = CSUBGOAL (fn (subgoal,i) => let
  val (params, body) = forall_dest_list subgoal
  val thm = Goal.prove_internal ctxt [] body
            (K (tac {ctxt=ctxt, csubgoal=subgoal, cparams=params}
                ORELSE error_tac (K "MY_SUBGOAL: subgoals not solved") ctxt))
  val thm = Drule.forall_intr_list params thm
  val tac' = Thm.bicompose (SOME ctxt) {match=false, flatten=false, incremented=false}
               (false, thm, 0) i
  in tac' end)

fun strip_params_concl (Const("Pure.all", _) $ Abs (a, T, t)) = strip_params_concl t
  | strip_params_concl B = B;

(* Rewrites with theorems thms, but uses prover for conditions.
Prover is invoked with a context that contains the original simpset, even though
we replace it for Raw_Simplifier.rewrite_cterm. *)
fun rewrite_with_prover (prover: Proof.context -> tactic) rules ctxt = let
  val simpset = simpset_of ctxt
  val ctxt = Simplifier.init_simpset rules ctxt
  fun prover' ctxt = SINGLE (prover (put_simpset simpset ctxt))
  val tac = Raw_Simplifier.rewrite_cterm (false,false,false) prover' ctxt
in tac end
fun rewrite_with_prover_tac prover rules ctxt =
  CONVERSION (rewrite_with_prover prover rules ctxt)

(* Takes a tactic that proves goals of the form "something \<equiv> ?rhs" and
   creates a conversion from it that converts "something" into whatever the tactic 
   instantiated ?rhs with.

   The resulting conversion does not support terms containing schematic variables.
*)
fun conv_from_tac ctxt tac ct = let
  val _ = Term.is_schematic (Thm.term_of ct) andalso error "schematic vars in conv_from_tac not yet supported"
  val idx = Thm.maxidx_of_cterm ct + 1
  val goal = Thm.apply (Thm.apply (Thm.cterm_of ctxt \<^Const>\<open>Pure.eq \<open>Thm.typ_of_cterm ct\<close>\<close>)
                                  ct)
                       (Thm.var ((("rhs",idx),Thm.ctyp_of_cterm ct)))
  val thm = Goal.prove_internal ctxt [] goal (K tac)
in thm end
(* TODO keep this or the above conv_from_tac, not both (what are the differences?) *)
fun conv_from_tac' check tac ctxt ct =
  let val t = Thm.term_of ct
      val _ = check ctxt t
      val maxidx = Thm.maxidx_of_cterm ct
      val T = Thm.ctyp_of_cterm ct
      val goal = mk_equals_cterm ct (Thm.var (("result",maxidx+1), T))
      val thm = prove_handle ctxt goal tac
      val thm = if Thm.term_of (Thm.lhs_of thm) = Thm.term_of ct then thm
                else let val refl = generalized_reflexivity ct (Thm.lhs_of thm)
                             handle CTERM _ => error ("conv_from_tac: tactic changed lhs")
(* val _ = \<^print> ("FIXUP", Thm.prop_of refl, Thm.prop_of thm) *)
                     in Thm.transitive refl thm end
  in
    thm
  end



end
