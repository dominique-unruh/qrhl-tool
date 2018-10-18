
fun assert_equal mk_string y x =
  if x=y then () else
  error ("Expected "^mk_string y^", got "^mk_string x)

fun string_of_term_gl t = Syntax.string_of_term_global (Context.the_global_context ()) t

fun assert_aconv expected y =
  if expected aconv y then () else
  if Envir.beta_norm expected aconv Envir.beta_norm y then
    error ("Expected: "^ string_of_term_gl expected^"\nGot:      the same up to beta equivalence")
  else error ("Expected: "^ string_of_term_gl expected^"\nGot:      "^ string_of_term_gl y)

fun assert_aconv_cterm x y = assert_aconv (Thm.term_of x) (Thm.term_of y)

fun assert_aconv_thm y x =
  if Thm.prop_of x aconv y then () else
  error ("Expected "^ string_of_term_gl y^" (up to aconv), got "^ @{make_string} x)

fun assert_aconv_conv conv input expected =
  let val thm = conv input
      val _ = Thm.proof_body_of thm (* Makes sure that all proofs are executed and succeed *)
      val (lhs,rhs) = Logic.dest_equals (Thm.prop_of thm)
      val _ = if lhs aconv (Thm.term_of input) then () else error ("Conversion returned wrong lhs")
  in
    if rhs aconv expected then () else
    error ("Expected (up to aconv): "^ string_of_term_gl expected^"\nGot: "^ string_of_term_gl rhs)
  end
