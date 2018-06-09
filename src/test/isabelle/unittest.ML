
fun assert_equal mk_string y x =
  if x=y then () else
  error ("Expected "^mk_string y^", got "^mk_string x)

fun string_of_term_gl t = Syntax.string_of_term_global (Context.the_global_context ()) t ^ " -- " ^ @{make_string} t

fun assert_aconv x y =
  if x aconv y then () else
  error ("Expected: "^ string_of_term_gl x^"\nGot:      "^ string_of_term_gl y)

fun assert_aconv_cterm x y = assert_aconv (Thm.term_of x) (Thm.term_of y)

fun assert_aconv_thm y x =
  if Thm.prop_of x aconv y then () else
  error ("Expected "^ string_of_term_gl y^" (up to aconv), got "^ @{make_string} x)

fun assert_aconv_conv conv input expected =
  let val thm = conv input
      val (lhs,rhs) = Logic.dest_equals (Thm.prop_of thm)
      val _ = if lhs aconv (Thm.term_of input) then () else error ("Conversion returned wrong lhs")
  in
    if rhs aconv expected then () else
    error ("Expected (up to aconv): "^ string_of_term_gl expected^"\nGot: "^ string_of_term_gl rhs)
  end
