structure Registers_Unsorted = struct

fun dest_qregisterT (\<^Type>\<open>qregister T U\<close>) = (T,U)
  | dest_qregisterT (\<^Type>\<open>dummy\<close>) = (dummyT, dummyT) (* So that it also works in not yet type-inferred terms *)
  | dest_qregisterT T = raise TYPE("dest_qregisterT", [T], [])


fun is_empty_qregisterT ctxt (\<^Type>\<open>qregister T _\<close>) = Sign.of_sort (Proof_Context.theory_of ctxt) (T,\<^sort>\<open>CARD_1\<close>)
  | is_empty_qregisterT _ T = raise TYPE("is_empty_qregisterT: not a qregister type", [T], [])

fun is_empty_qregister ctxt t = is_empty_qregisterT ctxt (fastype_of t)
  handle TYPE(_, Ts, _) => raise TYPE("is_empty_qregister: not a qregister type", Ts, [t])


(* Transforms [F1,\<dots>,Fn] into (F1;\<dots>Fn). *)
(* Note: not an exact inverse of explode_variable: it's only guaranteed that 
   "implode_variable (explode_variable X)" is equivalent to X *)
(* TODO: support cregisters as well *)
fun implode_variable T [a] = a
  | implode_variable T [] = \<^Const>\<open>empty_qregister HOLogic.unitT T\<close>
  | implode_variable T (F::Gs) = let
      val G = implode_variable T Gs
      in
       \<^Const>\<open>qregister_pair \<open>fastype_of F |> dest_qregisterT |> fst\<close> \<open>fastype_of F |> dest_qregisterT |> snd\<close> \<open>fastype_of G |> dest_qregisterT |> fst\<close>\<close> 
        $ F $ G
      end

(* Transforms F into [F1,\<dots>,Fn] such that F is equivalent to (F1;\<dots>Fn). *)
(* TODO: support cregisters as well *)
fun explode_variable (Const(\<^const_name>\<open>qregister_pair\<close>,_) $ F $ G) = explode_variable F @ explode_variable G
  | explode_variable (Const(\<^const_name>\<open>qregister_chain\<close>,_) $ \<^Const_>\<open>qregister_id _\<close> $ G) = explode_variable G
  | explode_variable (Const(\<^const_name>\<open>qregister_chain\<close>,_) $ F $ \<^Const_>\<open>qregister_id _\<close>) = explode_variable F
  | explode_variable (Const(\<^const_name>\<open>qregister_chain\<close>,_) $ F $ G) =
      explode_variable G |> map (fn g =>
         \<^Const>\<open>qregister_chain \<open>fastype_of F |> dest_qregisterT |> fst\<close> \<open>fastype_of F |> dest_qregisterT |> snd\<close> \<open>fastype_of g |> dest_qregisterT |> fst\<close>\<close> 
        $ F $ g)
  | explode_variable \<^Const_>\<open>empty_qregister _ _\<close> = []
  | explode_variable F = [F]    

(* TODO something more reliable than just simp'ing *)
fun distinct_vars_tac ctxt = let
  val ctxt = (Config.put Simplifier.simp_trace false ctxt) addsimps @{thms 
    distinct_cvars_split2 ccompatible3 ccompatible3' (* cregister_chain_id *)
    qcompatible3 distinct_qvars_split2 qcompatible3 qcompatible3' (* qregister_chain_id *)
    Cccompatible_CREGISTER_of Qqcompatible_QREGISTER_of}
  in Misc.succeed_or_error_tac' (SOLVED' (simp_tac ctxt)) ctxt (fn t => "Cannot prove that the variables are variables and distinct (using simp): " ^ Syntax.string_of_term ctxt t) end


(* Normalizes a register (e.g., removes id registers etc.) *)
val normalize_register_conv = 
  Misc.rewrite_with_prover (fn ctxt => distinct_vars_tac ctxt 1)
    @{thms qregister_chain_id[THEN eq_reflection] qregister_id_chain[THEN eq_reflection]
           qregister_chain_pair[symmetric, THEN eq_reflection] pair_fst_snd[THEN eq_reflection]
           qregister_chain_empty_right[THEN eq_reflection] qregister_chain_empty_left[THEN eq_reflection]}

(* Like normalize_register_conv, but prefers \<lbrakk>Fst o X, Fst o Y\<rbrakk> over Fst o \<lbrakk>X, Y\<rbrakk> *)
fun normalize_register_conv2 ctxt = 
  normalize_register_conv ctxt then_conv Conv.top_rewrs_conv @{thms qregister_chain_pair[THEN eq_reflection]} ctxt

(* Tactic to fully prove a goal of the form `qregister_le F G` *)
(* TODO: support cregisters as well *)
fun qregister_le_tac ctxt = let
  fun tac' ctxt i st = st |>
          ((resolve_tac ctxt @{thms qregister_le_refl qregister_le_id} i THEN distinct_vars_tac ctxt i)
          ORELSE
          (resolve_tac ctxt @{thms qregister_le_pair_rightI1 qregister_le_pair_rightI2} i THEN distinct_vars_tac ctxt i THEN tac' ctxt i)
          ORELSE
          (resolve_tac ctxt @{thms qregister_le_pair_leftI} i THEN distinct_vars_tac ctxt i THEN tac' ctxt i THEN tac' ctxt i)
          ORELSE
          (resolve_tac ctxt [@{lemma \<open>qregister Q ==> qregister_le empty_qregister Q\<close> by simp}] i THEN distinct_vars_tac ctxt i)
          )
in SUBGOAL (fn (t,i) => 
  CONVERSION (normalize_register_conv2 ctxt) i 
  (* THEN print_tac ctxt "qregister_le_tac" *)
  THEN 
  (case t of Const(\<^const_name>\<open>Trueprop\<close>,_) $ (Const(\<^const_name>\<open>qregister_le\<close>,_) $ (Const(\<^const_name>\<open>qregister_pair\<close>,_) $ _ $ _) $ _) =>
    (* Why to we have this special case? *)
    resolve_tac ctxt @{thms qregister_le_pair_leftI} i THEN distinct_vars_tac ctxt i THEN qregister_le_tac ctxt i THEN qregister_le_tac ctxt i
  | _ =>  tac' ctxt i))
end



(* Given variables F,G, returns an upper bound FG.
   (Heuristically. Is not guaranteed to be a true upper bound.
   But in simple cases, should be a lub.) *)
(* TODO: support cregisters as well *)
fun join_registers (_:Proof.context) F G = if F aconv G then SOME F else let
  val Fs = explode_variable F
  val Gs = explode_variable G
  fun is_id \<^Const_>\<open>qregister_id _\<close> = true
    | is_id _ = false
  val (_, memoryT) = dest_qregisterT (fastype_of F)
  in if exists is_id Fs orelse exists is_id Fs then
        SOME \<^Const>\<open>qregister_id memoryT\<close>
     else if subset (op aconv) (Gs, Fs) then SOME F
     else if subset (op aconv) (Fs, Gs) then SOME G
     else let
      val FGs = Fs @ Gs |> sort_distinct Term_Ord.fast_term_ord
      val FG = implode_variable memoryT FGs
      in
      SOME FG
      end
  end


local
val qregister_conversion_to_register_conv_simpset = 
  \<^context> addsimps @{thms qregister_chain_pair qregister_chain_assoc[symmetric] 
                          qregister_of_cregister_Fst qregister_of_cregister_Snd}
  |> simpset_of
(* Specifically for \<lbrakk>F \<mapsto> qregister_id\<rbrakk> *)
val qregister_conversion_to_register_conv_id = Conv.rewr_conv @{thm qregister_conversion_id[THEN eq_reflection]}
fun qregister_conversion_to_register_conv0 ctxt ct = let
  val (lhs,rhs) = case Thm.term_of ct of Const(\<^const_name>\<open>qregister_conversion\<close>,_) $ lhs $ rhs => (lhs,rhs)
                                       | _ => raise CTERM ("qregister_conversion_to_register_conv: not a register conversion", [ct])
  val (rhs_inT, _) = dest_qregisterT (fastype_of rhs)
  fun add_to_path prefix path = case path of \<^Const_>\<open>qregister_id _\<close> => prefix | _ =>
    let val (prefix_inT, _) = dest_qregisterT (fastype_of prefix)
        val (path_inT, path_outT) = dest_qregisterT (fastype_of path)
    in \<^Const>\<open>qregister_chain path_inT path_outT prefix_inT\<close> $ path $ prefix end
  fun get_rhs_registers (\<^Const_>\<open>qregister_pair T1 _ T2\<close> $ r1 $ r2) path found = 
      found |> get_rhs_registers r1 (add_to_path \<^Const>\<open>qFst T1 T2\<close> path)
            |> get_rhs_registers r2 (add_to_path \<^Const>\<open>qSnd T2 T1\<close> path)
   | get_rhs_registers reg path found = 
      if is_empty_qregister ctxt reg then found
      else (reg,path) :: found
  val rhs_registers = get_rhs_registers rhs \<^Const>\<open>qregister_id rhs_inT\<close> []
  fun map_lhs (Const(\<^const_name>\<open>qregister_pair\<close>,_) $ r1 $ r2) : term = let
    val r1' = map_lhs r1
    val r2' = map_lhs r2
    val (r1'in, r1'out) = dest_qregisterT (fastype_of r1')
    val (r2'in, _) = dest_qregisterT (fastype_of r2')
    in
      \<^Const>\<open>qregister_pair r1'in r1'out r2'in for r1' r2'\<close>
    end
    | map_lhs r = 
      if is_empty_qregister ctxt r
      then \<^Const>\<open>empty_qregister \<open>fastype_of r |> dest_qregisterT |> fst\<close> rhs_inT\<close>
      else
        (case AList.lookup (op aconv) rhs_registers r of
          NONE => raise TERM ("qregister_conversion_to_register_conv: could not find register from lhs in rhs", [r,Thm.term_of ct])
        | SOME path => path)
  val new_reg = map_lhs lhs |> Thm.cterm_of ctxt
  val new_reg = Conv.bottom_rewrs_conv @{thms qregister_chain_assoc[THEN eq_reflection]} ctxt new_reg |> Thm.rhs_of
  val goal = Misc.mk_ct_equals ct new_reg
  val outer_simpset = simpset_of ctxt
  val simpset_ctxt = ctxt 
          |> put_simpset qregister_conversion_to_register_conv_simpset
          (* |> Raw_Simplifier.set_subgoaler (fn ctxt => K (print_tac ctxt "xxx") THEN' simp_tac (put_simpset outer_simpset ctxt)) *)
          |> Raw_Simplifier.set_subgoaler (fn ctxt => distinct_vars_tac (put_simpset outer_simpset ctxt))
  val tac = resolve_tac ctxt @{thms qregister_conversion_as_register[THEN eq_reflection]} 1
            THEN
            distinct_vars_tac ctxt 1
            THEN
            Misc.succeed_or_error_tac' (SOLVED' (simp_tac simpset_ctxt))
            ctxt (fn t => "qregister_conversion_to_register_conv: cannot prove precondition for rewriting '" ^ 
                Syntax.string_of_term ctxt (Thm.term_of ct) ^ "' into a register:\n" ^ Syntax.string_of_term ctxt t) 1
  val thm = Goal.prove_internal ctxt [] goal (K tac)
in
  thm
end
in
(* Tries to rewrite a `qregister_conversion F G` into an index-register.
   (Index-registers are registers build from chain, pair, Fst, Snd, id, empty.) *)
fun qregister_conversion_to_register_conv ctxt = 
  normalize_register_conv2 ctxt then_conv 
  (qregister_conversion_to_register_conv_id else_conv qregister_conversion_to_register_conv0 ctxt)
end


(* Solves a goal of the form \<open>qregister_le Q ?QR \<and> qregister_le R ?QR\<close> by instantiating ?QR
   as small as possible.
*)
fun qregister_lub_tac ctxt = Misc.MY_SUBGOAL ctxt (fn {ctxt, csubgoal, ...} => let
  (* val _ = \<^print>("qregister_lub_tac", Thm.cterm_of ctxt t) *)
  val (Q,R) = case Thm.term_of csubgoal of
            \<^Const_>\<open>Trueprop\<close> $ (\<^Const_>\<open>conj\<close> $ (\<^Const_>\<open>qregister_le _ _ _\<close> $ Q $ _)
                                              $ (\<^Const_>\<open>qregister_le _ _ _\<close> $ R $ _))
                => (Q,R)
          | _ => error "qregister_lub_tac"
  (* val _ = \<^print> (Q,R) *)
  val QR = case join_registers ctxt Q R of
             SOME QR => QR | NONE => error ("could not find upper bound of " ^ Syntax.string_of_term ctxt Q ^ " and " ^ Syntax.string_of_term ctxt R)
  (* val _ = \<^print> QR *)
  val lemma = @{lemma \<open>qregister_le Q QR \<Longrightarrow> qregister_le R QR \<Longrightarrow> qregister_le Q QR \<and> qregister_le R QR\<close> by simp}
  val lemma = infer_instantiate ctxt [(("QR",0), Thm.cterm_of ctxt QR), (("Q",0), Thm.cterm_of ctxt Q), (("R",0), Thm.cterm_of ctxt R)] lemma
  val tac =
   (* Misc.print_here_tac ctxt \<^here> THEN  *)
    resolve_tac ctxt [lemma] 1
 (* THEN Misc.print_here_tac ctxt \<^here>  *)
    THEN qregister_le_tac ctxt 1
 (* THEN Misc.print_here_tac ctxt \<^here>  *)
    THEN qregister_le_tac ctxt 1
  (* THEN Misc.print_here_tac ctxt \<^here>  *)
  in
    tac ORELSE Misc.error_tac (K "qregister_lub_tac: failed to prove le") ctxt
  end
)



(* 
Does not backtrack once tmp1 succeeds.
*)
fun translate_to_index_registers_assm_lub_tac ctxt = Misc.MY_SUBGOAL ctxt (fn {ctxt,...} =>
  (resolve_tac ctxt @{thms translate_to_index_registers_assm_lub_tac_aux}
  THEN' (qregister_lub_tac ctxt ORELSE' Misc.error_tac' (fn g => "Could not find lub in: " ^ Syntax.string_of_term ctxt g) ctxt)
  THEN' (CONVERSION (qregister_conversion_to_register_conv ctxt |> Conv.arg1_conv |> HOLogic.Trueprop_conv) ORELSE' Misc.error_tac' (K "TODO proper error message in translate_to_index_registers_assm_lub_tac") ctxt)
  THEN' (resolve_tac ctxt @{thms refl} ORELSE' Misc.error_tac' (K "TODO proper error message in translate_to_index_registers_assm_lub_tac") ctxt)
  THEN' (CONVERSION (qregister_conversion_to_register_conv ctxt |> Conv.arg1_conv |> HOLogic.Trueprop_conv) ORELSE' Misc.error_tac' (K "TODO proper error message in translate_to_index_registers_assm_lub_tac") ctxt)
  THEN' (resolve_tac ctxt @{thms refl} ORELSE' Misc.error_tac' (K "TODO proper error message in translate_to_index_registers_assm_lub_tac") ctxt)) 1)

(* TODO: Maybe use this fragment for error messages in translate_to_index_registers_conv_tac:

  fun raise_error e = let
     val term_str = Misc.string_of_term_truncated ctxt 5 (Thm.term_of ct)
     fun exception_to_str (Misc.LAZY_ERROR (Misc.Lazy_Error e)) = e ()
       | exception_to_str e = Runtime.exn_message (Runtime.exn_context (SOME ctxt) e)
  in raise ERROR ("I was trying to process the following subterm:\n  " 
        ^ term_str ^ "\nThis subterm was the result of transforming its children into index registers "
        ^ "(where possible)\nand bringing non-index-registers to the top.\n"
        ^ "In the current step, I tried to push the non-index-registers up further (using lemmas\nfrom "
        ^ (Pretty.marks_str (Proof_Context.markup_extern_fact \<^context> \<^named_theorems>\<open>translate_to_index_registers\<close>) |> Pretty.string_of)
        ^ ") but that failed with the following error:\n" ^ exception_to_str e)
    end

 *)

(* TODO: rewrite all [translate_to_index_registers] rules *)

type translate_to_index_registers_conv_options = {
  trace: bool, (* Activates detailed trace *)
  level: int, (* Nesting level of this invocation (for indentation in tracing) *)
  descend: bool (* If true, descends into the term until it finds something involving registers *)
}

val translate_to_index_registers_conv_default_options : translate_to_index_registers_conv_options =
  {trace = false, level = 0, descend = true}
fun translate_to_index_registers_conv_options_inc_level {trace, level, descend} : translate_to_index_registers_conv_options =
  {trace = trace, level = level+1, descend = descend}
fun translate_to_index_registers_conv_options_trace trace {trace=_, level, descend} : translate_to_index_registers_conv_options =
  {trace = trace, level = level+1, descend = descend}

fun translate_to_index_registers_conv_tac0 ctxt config rules (st:thm) = let
  fun named_thms_str () = (Pretty.marks_str (Proof_Context.markup_extern_fact ctxt \<^named_theorems>\<open>translate_to_index_registers\<close>) |> Pretty.string_of)
  val thisgoal = Thm.cprem_of st 1 |> Thm.term_of
  val thisgoal_str = Lazy.lazy (fn () => thisgoal |> Syntax.string_of_term ctxt)
  fun err msg = error ("translate_to_index_registers_conv_tac: TODO need better error message: " ^ msg ^ ", goal: " ^ Lazy.force thisgoal_str)
  val _ = Thm.nprems_of st = 1 orelse err "internal error"
  val next_config = translate_to_index_registers_conv_options_inc_level config
  val trace = if #trace config then
    let val indent = replicate_string (#level config) "  " in fn str => 
        let val lines = split_lines (str ())
            val indented_lines = map (fn line => indent ^ line) lines
            val indented_str = cat_lines indented_lines in        
        tracing indented_str end end
    else fn _ => ()
  val _ = trace (fn () => "Attempting to translate registers in:\n  " ^ Lazy.force thisgoal_str)
  (* fun guarded_some guard x = if guard then SOME x else NONE *)
  val fallback_rules = [
     @{lemma \<open>TTIR_APPLY_QREGISTER A F B \<Longrightarrow> PROP TTIR_EQ A (apply_qregister F B)\<close> by (simp add: TTIR_EQ_def TTIR_APPLY_QREGISTER_def)},
     @{lemma \<open>TTIR_APPLY_QREGISTER_SPACE A F B \<Longrightarrow> PROP TTIR_EQ A (apply_qregister_space F B)\<close> by (simp add: TTIR_EQ_def TTIR_APPLY_QREGISTER_SPACE_def)},
     @{lemma \<open>TTIR_APPLY_QREGISTER_SPACE A qregister_id A\<close> by (simp add: apply_qregister_space_def TTIR_APPLY_QREGISTER_SPACE_def)},
     @{lemma \<open>TTIR_APPLY_QREGISTER A qregister_id A\<close> by (simp add: TTIR_APPLY_QREGISTER_def)}]
  val st = case Misc.resolve_and_remember_rule ctxt rules 1 st of
               SOME (rule,st) => (trace (fn () => "Successfully applied a rule from " ^ named_thms_str () ^ Misc.theorem_or_name ctxt ". Namely " ".\nNamely " rule);
                                  st)
             | NONE => 
           case Misc.resolve_and_remember_rule ctxt fallback_rules 1 st of
               SOME (rule,st) => (trace (fn () => "Successfully applied a fallback rule." ^ Misc.theorem_or_name ctxt " Namely " "\nNamely " rule);
                                  st)
             | NONE => 
           case (#descend config, Misc.strip_params_concl thisgoal) of
               (true, \<^Const_>\<open>TTIR_EQ _\<close> $ (t $ u) $ _) => (trace (fn () => "Descending into subterms separately.");
                                 SINGLE (resolve_tac ctxt [infer_instantiate ctxt [(("A",0), Thm.cterm_of ctxt t), (("B",0), Thm.cterm_of ctxt u)]
                                         @{lemma \<open>PROP TTIR_EQ (A::'a::{}\<Rightarrow>'b::{}) C \<Longrightarrow> PROP TTIR_EQ B D ==> PROP TTIR_EQ (A B) (C D)\<close> by (simp add: TTIR_EQ_def)}] 1) st |> the)
             | (true, \<^Const_>\<open>TTIR_EQ _\<close> $ (Abs _) $ _) => (trace (fn () => "Descending into lambda abstraction.");
                                 SINGLE (resolve_tac ctxt [@{lemma \<open>(\<And>x. PROP TTIR_EQ (A x) (B x)) \<Longrightarrow> PROP TTIR_EQ (A::'a::{}\<Rightarrow>'b::{}) B\<close> by (auto simp add: TTIR_EQ_def intro!: pure_extensional)}] 1) st |> the)
             | (true, \<^Const_>\<open>TTIR_EQ _\<close> $ _ $ _) => (trace (fn () => "Doing nothing.");
                                 SINGLE (resolve_tac ctxt [@{lemma \<open>PROP TTIR_EQ (A::'a::{}) A\<close> by (simp add: TTIR_EQ_def)}] 1) st |> the)
             | _ => 
           error ("No rule matched in " ^ named_thms_str() ^ " when trying to solve:\n" ^ Lazy.force thisgoal_str)
  val nr_new_goals = Thm.nprems_of st
  fun condition_tac' st = let
    val ngoals = Thm.nprems_of st
    val subgoal = Thm.cprem_of st 1 |> Thm.term_of
    val subgoal_str = Lazy.lazy (fn () => subgoal |> Syntax.string_of_term ctxt)
    val _ = trace (fn () => "Solving subgoal " ^ Lazy.force subgoal_str)
    val st = case Logic.strip_assums_concl subgoal of
               (* TODO: Also need to descend into registers themselves via TTIR_EQ *)
               \<^Const_>\<open>Trueprop\<close> $ (\<^Const_>\<open>TTIR_APPLY_QREGISTER_SPACE _ _\<close> $ _ $ _ $ _) => 
                 SINGLE (translate_to_index_registers_conv_tac1 ctxt next_config rules 1) st
             | \<^Const_>\<open>Trueprop\<close> $ (\<^Const_>\<open>TTIR_APPLY_QREGISTER _ _\<close> $ _ $ _ $ _) => 
                 SINGLE (translate_to_index_registers_conv_tac1 ctxt next_config rules 1) st
             | \<^Const_>\<open>TTIR_EQ _\<close> $ _ $ _ => 
                 SINGLE (translate_to_index_registers_conv_tac1 ctxt next_config rules 1) st
             | \<^Const_>\<open>Trueprop\<close> $ (\<^Const_>\<open>TTIR_LUB _ _ _ _\<close> $ _ $ _ $ _ $ _ $ _) => 
                 SINGLE (translate_to_index_registers_assm_lub_tac ctxt 1) st
             | \<^Const_>\<open>Trueprop\<close> $ (\<^Const_>\<open>TTIR_QREGISTER _ _\<close> $ _) =>
                SINGLE (resolve_tac ctxt [@{lemma \<open>qregister F \<Longrightarrow> TTIR_QREGISTER F\<close> for F by (simp add: TTIR_QREGISTER_def)}] 1
                        THEN distinct_vars_tac ctxt 1) st
             | t => (raise ERROR ("When translating registers, got a condition of the wrong form (" ^ Syntax.string_of_term ctxt subgoal
                                 ^ ").\nThis probably means a there is a malformed rule in " ^ named_thms_str() ^ "."))
    val st = case st of SOME st => st
                      | NONE => err ("condition tac failed")
(*     val st = case SINGLE (condition_tac i) st of SOME st => st
             | NONE => err ("condition_tac failed (subgoal " ^ Lazy.force subgoal_str ^ ")") *)
    val _ = Thm.nprems_of st < ngoals - 1 andalso err ("condition_tac removed more than one subgoal (subgoal " ^ Lazy.force subgoal_str ^ ")")
    val _ = Thm.nprems_of st >= ngoals andalso err ("condition_tac did not remove subgoal (subgoal " ^ Lazy.force subgoal_str ^ ")")
    in st end
  fun repeat_condition_tac 0 st = st
    | repeat_condition_tac n st = condition_tac' st |> repeat_condition_tac (n-1) 
  val st = repeat_condition_tac nr_new_goals st
  val _ = trace (fn () => "Successfully translated.")
in 
  Seq.single st
end

  and translate_to_index_registers_conv_tac1 ctxt config rules  = 
    Misc.MY_SUBGOAL ctxt (fn {ctxt,...} => translate_to_index_registers_conv_tac0 ctxt config rules)

fun translate_to_index_registers_conv_tac ctxt config rules =
  resolve_tac ctxt [@{lemma \<open>PROP TTIR_EQ A B \<Longrightarrow> A::'a::{} \<equiv> B\<close> by (simp add: TTIR_EQ_def)}]
  THEN' translate_to_index_registers_conv_tac1 ctxt config rules

(* TODO move to Misc *)
fun conv_from_tac ctxt tac ct = let
  val _ = Term.is_schematic (Thm.term_of ct) andalso error "schematic vars in conv_from_tac not yet supported"
  val idx = Thm.maxidx_of_cterm ct + 1
  val goal = Thm.apply (Thm.apply (Thm.cterm_of ctxt \<^Const>\<open>Pure.eq \<open>Thm.typ_of_cterm ct\<close>\<close>)
                                  ct)
                       (Thm.var ((("rhs",idx),Thm.ctyp_of_cterm ct)))
(* val _ = goal |> \<^print> *)
  val thm = Goal.prove_internal ctxt [] goal (K tac)
(* val _ = thm |> \<^print> *)
in thm end

fun translate_to_index_registers_conv ctxt config = let
  val rules = \<^named_theorems>\<open>translate_to_index_registers\<close> |> Proof_Context.get_thms ctxt
  in conv_from_tac ctxt (translate_to_index_registers_conv_tac ctxt config rules 1) end

fun register_thms_of thm regs = let
  val reg = case Thm.prop_of thm of
      Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>cregister\<close>, _) $ reg) => reg
    | Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>qregister\<close>, _) $ reg) => reg
    | _ => raise THM ("register_thms_of: expecting a fact of the form \<open>c/qregister ...\<close>", 0, [thm])
  val regs = case reg of
      Free _ => thm::regs
    | Const(\<^const_name>\<open>cregister_pair\<close>,_) $ _ $ _ =>
        regs |> register_thms_of (@{thm distinct_cvarsR} OF [thm])
             |> register_thms_of (@{thm distinct_cvarsL} OF [thm])
    | Const(\<^const_name>\<open>qregister_pair\<close>,_) $ _ $ _ =>
        regs |> register_thms_of (@{thm distinct_qvarsR} OF [thm])
             |> register_thms_of (@{thm distinct_qvarsL} OF [thm])
    | t => raise TERM ("register_thms_of: expecting a fact of the form \<open>c/register ...\<close> where ... is a register tuple of free variables. Got:", [t])
  in regs end

fun register_compats_of thm compats = case Thm.prop_of thm of
      \<^Const>\<open>Trueprop\<close> $ (\<^Const>\<open>cregister _ _\<close> $ (\<^Const>\<open>cregister_pair _ _ _\<close> $ (\<^Const>\<open>cregister_pair _ _ _\<close> $ _ $ _) $ _)) =>
        compats |> register_compats_of (@{thm ccompatible3[THEN iffD1, THEN conjunct2, THEN conjunct2]} OF [thm])
                |> register_compats_of (@{thm ccompatible3[THEN iffD1, THEN conjunct2, THEN conjunct1]} OF [thm])
                |> register_compats_of (@{thm ccompatible3[THEN iffD1, THEN conjunct1]} OF [thm])
    | \<^Const>\<open>Trueprop\<close> $ (\<^Const>\<open>qregister _ _\<close> $ (\<^Const>\<open>qregister_pair _ _ _\<close> $ (\<^Const>\<open>qregister_pair _ _ _\<close> $ _ $ _) $ _)) =>
        compats |> register_compats_of (@{thm qcompatible3[THEN iffD1, THEN conjunct2, THEN conjunct2]} OF [thm])
                |> register_compats_of (@{thm qcompatible3[THEN iffD1, THEN conjunct2, THEN conjunct1]} OF [thm])
                |> register_compats_of (@{thm qcompatible3[THEN iffD1, THEN conjunct1]} OF [thm])
    | \<^Const>\<open>Trueprop\<close> $ (\<^Const>\<open>cregister _ _\<close> $ (\<^Const>\<open>cregister_pair _ _ _\<close> $ _ $ (\<^Const>\<open>cregister_pair _ _ _\<close> $ _ $ _))) =>
        compats |> register_compats_of (@{thm ccompatible3'[THEN iffD1, THEN conjunct2, THEN conjunct2]} OF [thm])
                |> register_compats_of (@{thm ccompatible3'[THEN iffD1, THEN conjunct2, THEN conjunct1]} OF [thm])
                |> register_compats_of (@{thm ccompatible3'[THEN iffD1, THEN conjunct1]} OF [thm])
    | \<^Const>\<open>Trueprop\<close> $ (\<^Const>\<open>qregister _ _\<close> $ (\<^Const>\<open>qregister_pair _ _ _\<close> $ _ $ (\<^Const>\<open>qregister_pair _ _ _\<close> $ _ $ _))) =>
        compats |> register_compats_of (@{thm qcompatible3'[THEN iffD1, THEN conjunct2, THEN conjunct2]} OF [thm])
                |> register_compats_of (@{thm qcompatible3'[THEN iffD1, THEN conjunct2, THEN conjunct1]} OF [thm])
                |> register_compats_of (@{thm qcompatible3'[THEN iffD1, THEN conjunct1]} OF [thm])
    | \<^Const>\<open>Trueprop\<close> $ (\<^Const>\<open>cregister _ _\<close> $ (\<^Const>\<open>cregister_pair _ _ _\<close> $ _ $ _)) =>
        thm :: (@{thm ccompatible_sym} OF [thm]) :: compats
    | \<^Const>\<open>Trueprop\<close> $ (\<^Const>\<open>qregister _ _\<close> $ (\<^Const>\<open>qregister_pair _ _ _\<close> $ _ $ _)) =>
        thm :: (@{thm qcompatible_sym} OF [thm]) :: compats
    | \<^Const>\<open>Trueprop\<close> $ (\<^Const>\<open>cregister _ _\<close> $ Free _) => compats
    | \<^Const>\<open>Trueprop\<close> $ (\<^Const>\<open>qregister _ _\<close> $ Free _) => compats
    | _ => raise THM ("register_compats_of: expecting a fact of the form \<open>c/qregister \<dots>\<close> or \<open>c/qcompatible \<dots>\<close>", 0, [thm])


fun declare_register_simps_from_thm thm = let
  val vars = register_thms_of thm []
  val compats = register_compats_of thm []
  val simp_vars = fold (fn thm => Simplifier.map_ss (Simplifier.add_simp thm)) vars
  val simp_compats = fold (fn thm => Simplifier.map_ss (Simplifier.add_simp thm)) compats
  in simp_vars #> simp_compats end

fun dest_qregisterT_ct ctyp = let
  val _ = case Thm.typ_of ctyp of \<^Type>\<open>qregister _ _\<close> => ()
             | T => raise TYPE ("dest_qregisterT_ct: not a qregister type", [T], [])
  val [T,U] = Thm.dest_ctyp ctyp
in (T,U) end

(* Returns a theorem `qregister_le lhs rhs` if possible *)
(* TODO: support cregisters as well *)
fun qregister_le_prove ctxt lhs rhs = let
  val (rhs_inT, rhs_outT) = dest_qregisterT_ct (Thm.ctyp_of_cterm rhs)
  val (lhs_inT, lhs_outT) = dest_qregisterT_ct (Thm.ctyp_of_cterm lhs)
  val _ = \<^assert> (Thm.eq_ctyp (rhs_outT, lhs_outT))
  val less_eq_goal = \<^instantiate>\<open>lhs and rhs and 'a=lhs_inT and 'b=rhs_inT and 'c=lhs_outT
          in cprop \<open>qregister_le (lhs::('a,'c) qregister) (rhs::('b,'c) qregister)\<close>\<close>
in
  Goal.prove_internal ctxt [] less_eq_goal (K (qregister_le_tac ctxt 1))
end

(* Rewrites `apply_qregister F A` into `apply_qregister target (apply_qregister (qregister_conversion \<dots>) A)`
  for suitable \<dots>
  Analogously for apply_qregister_space. *)
fun apply_qregister_conversion_conv ctxt target ct = let
  val thm = case Thm.term_of ct of 
              \<^Const_>\<open>apply_qregister _ _\<close> $ _ $ _ => @{thm qregister_apply_conversion[THEN eq_reflection]}
            | \<^Const_>\<open>apply_qregister_space _ _\<close> $ _ $ _ => @{thm apply_qregister_space_conversion[THEN eq_reflection]}
            | _ => raise CTERM ("apply_qregister_conversion_conv: term should be of the form `apply_qregister F A`", [ct])
  val source = Thm.dest_arg1 ct
  val argument = Thm.dest_arg ct
  val less_eq_thm = qregister_le_prove ctxt source target
in
  (infer_instantiate ctxt [(("x",1), argument)] thm) OF [less_eq_thm]
end

(* Returns true if argument is a (quantum) index-register *)
fun is_index_qregister (Const(\<^const_name>\<open>qregister_pair\<close>,_) $ t $ u) = is_index_qregister t andalso is_index_qregister u
  | is_index_qregister (Const(\<^const_name>\<open>qregister_chain\<close>,_) $ t $ u) = is_index_qregister t andalso is_index_qregister u
  | is_index_qregister (Const(\<^const_name>\<open>qFst\<close>,_)) = true
  | is_index_qregister (Const(\<^const_name>\<open>qSnd\<close>,_)) = true
  | is_index_qregister \<^Const_>\<open>qregister_id _\<close> = true
  | is_index_qregister \<^Const_>\<open>empty_qregister _ _\<close> = true
  | is_index_qregister _ = false
(* Returns true if argument is a (classical) index-register *)
fun is_index_cregister (Const(\<^const_name>\<open>cregister_pair\<close>,_) $ t $ u) = is_index_cregister t andalso is_index_cregister u
  | is_index_cregister (Const(\<^const_name>\<open>cregister_chain\<close>,_) $ t $ u) = is_index_cregister t andalso is_index_cregister u
  | is_index_cregister (Const(\<^const_name>\<open>cFst\<close>,_)) = true
  | is_index_cregister (Const(\<^const_name>\<open>cSnd\<close>,_)) = true
  | is_index_cregister \<^Const_>\<open>cregister_id _\<close> = true
  | is_index_cregister \<^Const_>\<open>empty_cregister _ _\<close> = true
  | is_index_cregister _ = false




end
