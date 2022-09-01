theory Test_Strongest_Postcondition
  imports QRHL.Strongest_Postcondition UnitTest
begin


ML \<open>
fun test_get_sp ctxt left prog pre expected =
let val (sp,thm,side) = Strongest_Postcondition.get_sp left prog pre ctxt
    val _ = tracing ("Side conditions: " ^ String.concatWith ";" (map (Syntax.string_of_term ctxt) side))
    val sp' = sp |> Thm.cterm_of ctxt |> Conv.try_conv (Expressions.clean_expression_conv ctxt)
                 |> Thm.rhs_of |> Thm.term_of |> Envir.beta_norm
    val _ = assert_aconv expected sp'
    val (A,_,_,B) = Relational_Hoare.dest_qrhl_goal (Thm.prop_of thm)
    val _ = assert_aconv sp B
    val _ = assert_aconv pre A
in () end
\<close>

declare [[show_consts, show_types]]

(* print_translation \<open>[(\<^const_syntax>\<open>expression\<close>, fn ctxt => fn [vars,t] => 
      Const(\<^const_syntax>\<open>undefined\<close>, dummyT) $ vars $ t)]\<close> *)

(* TEST CASE: assign *)
variables classical x :: nat and classical y :: nat begin
ML \<open>
test_get_sp \<^context> true
            \<^term>\<open>assign \<lbrakk>var_x\<rbrakk> Expr[5]\<close> (* program *)
            \<^term>\<open>Expr[Cla[x+x = y]]\<close> (* pre *)
            \<^term>\<open>expression \<lbrakk>var_x1::nat variable, var_x::nat variable, var_y::nat variable\<rbrakk>
                   (\<lambda>(var_x1::nat, var_x::nat, var_y::nat).
                   SUP z::nat. \<CC>\<ll>\<aa>[var_x + var_x = var_y] \<sqinter> \<CC>\<ll>\<aa>[var_x1 = (5::nat)])\<close> (* expected *)
\<close>
end

end
