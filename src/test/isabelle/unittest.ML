
fun assert_equal mk_string y x =
  if x=y then () else
  error ("Expected "^mk_string y^", got "^mk_string x)

fun string_of_term_gl t = Syntax.string_of_term_global (Context.the_global_context ()) t

fun aconv' check_types t u =
  if check_types then t aconv u
  else let val t' = map_types (K dummyT) t
           val u' = map_types (K dummyT) u
    in t' aconv u' end

fun assert_aconv check_types expected y = let
  (* val _ = \<^print> expected *)
  (* val _ = \<^print> y *)
  in
  if aconv' check_types expected y then () else
  if Envir.beta_norm expected aconv Envir.beta_norm y then
    error ("Expected: "^ string_of_term_gl expected^"\nGot:      the same up to beta equivalence")
  else error ("Expected: "^ string_of_term_gl expected^"\nGot:      "^ string_of_term_gl y)
  end

fun assert_aconv_cterm check_types x y = assert_aconv check_types (Thm.term_of x) (Thm.term_of y)

fun assert_aconv_thm check_types y x =
  if aconv' check_types (Thm.prop_of x) y then () else
  error ("Expected "^ string_of_term_gl y^" (up to aconv), got "^ @{make_string} x)

fun assert_aconv_conv check_types conv input expected =
  let val thm = conv input
      val _ = Thm.proof_body_of thm (* Makes sure that all proofs are executed and succeed *)
      val (lhs,rhs) = Logic.dest_equals (Thm.prop_of thm)
      val _ = if lhs aconv (Thm.term_of input) then () else error ("Conversion returned wrong lhs")
  in
    if aconv' check_types rhs expected then () else
    error ("Expected (up to aconv): "^ string_of_term_gl expected^"\nGot: "^ string_of_term_gl rhs)
  end

fun assert_schematic_aconv check_types (goal : {context: Proof.context, facts: thm list, goal: thm}) i expected = let
  val terms = goal |> #goal |> Thm.concl_of |> Logic.unprotect |> Logic.dest_conjunctions 
              |> map_filter (fn \<^Const_>\<open>Pure.term _\<close> $ t => SOME t | _ => NONE)
  val term = nth terms (i-1) |> \<^print>
  val _ = aconv' check_types term expected
      orelse error ("Expected (up to aconv): "^ string_of_term_gl expected^"\nGot: "^ string_of_term_gl term)
in () end
