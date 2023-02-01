theory Test_Weakest_Precondition
  imports QRHL.Weakest_Precondition UnitTest
begin

declare [[show_types,show_sorts,show_consts,eta_contract=false]]

ML \<open>open Weakest_Precondition\<close>

ML \<open>
fun test_get_wp ctxt left prog post expected =
let val (wp,thm) = Weakest_Precondition.get_wp left prog post ctxt
(*     val wp' = wp |> Thm.cterm_of ctxt |> Conv.try_conv (Expressions.clean_expression_conv ctxt)
                 |> Thm.rhs_of |> Thm.term_of |> Envir.beta_norm *)
    val wp' = Envir.beta_norm wp
    val _ = assert_aconv true expected wp'
    val (A,_,_,B) = Relational_Hoare.dest_qrhl_goal (Thm.prop_of thm)
    val _ = assert_aconv true wp A
    val _ = assert_aconv true post B
in () end
\<close>


experiment
  fixes a b x :: \<open>bit cvariable\<close> and A X Y :: \<open>bit qvariable\<close>
    and h :: \<open>(bit \<Rightarrow> bit) cvariable\<close>
  assumes [register]: \<open>cregister \<lbrakk>a,b,h,x\<rbrakk>\<^sub>c\<close>
  assumes [register]: \<open>qregister \<lbrakk>A,X,Y\<rbrakk>\<close>
begin

(* TEST CASE: get_wp of "if true then skip else skip" *)
ML \<open>
test_get_wp \<^context> true 
            \<^term>\<open>ifthenelse Expr[True] [] []\<close> (* program *)
            \<^term>\<open>Expr[top] :: predicate expression2\<close> (* post *)
            \<^term>\<open>Expr[ ((\<CC>\<ll>\<aa>[\<not> True] + top) \<sqinter> (\<CC>\<ll>\<aa>[True] + top)) ] :: predicate expression2\<close> (* expected *)
\<close>

(* TEST CASE: get_wp of "measure a A computational_basis" *)
ML \<open>
test_get_wp \<^context> true 
            \<^term>\<open>measurement \<lbrakk>a\<rbrakk> \<lbrakk>A\<rbrakk> Expr[computational_basis]\<close> (* program *)
            \<^term>\<open>Expr[top] :: predicate expression2\<close> (* post *)
            \<^term>\<open>Expr[ (let M = computational_basis
                  in \<CC>\<ll>\<aa>[mtotal M] \<sqinter> (INF z. let P = mproj M z\<guillemotright>\<lbrakk>A1\<rbrakk> \<cdot> top in top \<sqinter> P + - P))] :: predicate expression2\<close> (* expected *)
\<close>

(* TEST CASE: get_wp (right) of "if (true) b:=1" *)
ML \<open>
test_get_wp \<^context> false
            \<^term>\<open>ifthenelse Expr[True] [assign \<lbrakk>b\<rbrakk> Expr[1] ] []\<close> (* program *)
            \<^term>\<open>Expr[top] :: predicate expression2\<close> (* post *)
            \<^term>\<open>Expr[(\<CC>\<ll>\<aa>[\<not> True] + top) \<sqinter> (\<CC>\<ll>\<aa>[True] + top)] :: predicate expression2\<close> (* expected *)
\<close>

ML \<open>
test_get_wp \<^context> true
            \<^term>\<open>qapply X Expr[hadamard]\<close>
            \<^term>\<open>Expr[top] :: predicate expression2\<close>
            \<^term>\<open>Expr[\<CC>\<ll>\<aa>[isometry hadamard] \<sqinter> ((hadamard\<guillemotright>\<lbrakk>X1\<rbrakk>)* \<cdot> (top \<sqinter> (hadamard\<guillemotright>\<lbrakk>X1\<rbrakk> \<cdot> top)))] :: predicate expression2\<close>
\<close>

ML \<open>
test_get_wp \<^context> false
            \<^term>\<open>sample \<lbrakk>x\<rbrakk> Expr[undefined]\<close>
            \<^term>\<open>Expr[top] :: predicate expression2\<close>
            \<^term>\<open>Expr[\<CC>\<ll>\<aa>[weight (undefined::bit distr) = (1::real)] 
                 \<sqinter> (INF z::bit\<in>supp undefined. (top::predicate))] :: predicate expression2\<close>
\<close>

end (* experiment *)

end (* theory *)
