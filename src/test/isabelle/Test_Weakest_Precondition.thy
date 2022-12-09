theory Test_Weakest_Precondition
  imports QRHL.Weakest_Precondition UnitTest
begin

declare[[show_types,show_sorts,show_consts,eta_contract=false]]

ML \<open>
fun test_get_wp ctxt left prog post expected =
let val (wp,thm) = Weakest_Precondition.get_wp left prog post ctxt
    val wp' = wp |> Thm.cterm_of ctxt |> Conv.try_conv (Programs.clean_expression_conv ctxt)
                 |> Thm.rhs_of |> Thm.term_of |> Envir.beta_norm
    val _ = assert_aconv expected wp'
    val (A,_,_,B) = Relational_Hoare.dest_qrhl_goal (Thm.prop_of thm)
    val _ = assert_aconv wp A
    val _ = assert_aconv post B
in () end
\<close>


(* TEST CASE: get_wp of "if true then skip else skip" *)
ML \<open>
test_get_wp \<^context> true 
            \<^term>\<open>ifthenelse Expr[True] [] []\<close> (* program *)
            \<^term>\<open>Expr[top] :: predicate expression2\<close> (* post *)
            \<^term>\<open>Expr[ ((\<CC>\<ll>\<aa>[\<not> True] + top) \<sqinter> (\<CC>\<ll>\<aa>[True] + top)) ] :: _ expression2\<close> (* expected *)
\<close>

(* TEST CASE: get_wp of "measure a A computational_basis" *)
experiment
  fixes a :: \<open>bit cvariable\<close> and A :: \<open>bit qvariable\<close>
  assumes [register]: \<open>cregister a\<close> \<open>qregister A\<close>
begin
ML \<open>
test_get_wp \<^context> true 
            \<^term>\<open>measurement \<lbrakk>a\<rbrakk> \<lbrakk>A\<rbrakk> Expr[computational_basis]\<close> (* program *)
            \<^term>\<open>Expr[top] :: predicate expression2\<close> (* post *)
            \<^term>\<open>Expr[ (let M = computational_basis
                  in \<CC>\<ll>\<aa>[mtotal M] \<sqinter> (INF z. let P = mproj M z\<guillemotright>\<lbrakk>A1\<rbrakk> \<cdot> top in top \<sqinter> P + - P))] :: _ expression2\<close> (* expected *)
\<close>
end

(* TEST CASE: get_wp (right) of "if (true) b:=1" *)
experiment
  fixes b :: \<open>bit cvariable\<close>
  assumes [register]: \<open>cregister b\<close>
begin
ML \<open>
test_get_wp \<^context> false
            \<^term>\<open>ifthenelse Expr[True] [assign \<lbrakk>b\<rbrakk> Expr[1] ] []\<close> (* program *)
            \<^term>\<open>Expr[top] :: predicate expression2\<close> (* post *)
            \<^term>\<open>Expr[(\<CC>\<ll>\<aa>[\<not> True] + top) \<sqinter> (\<CC>\<ll>\<aa>[True] + top)] :: _ expression2\<close> (* expected *)
\<close>
end

experiment
  fixes x y :: \<open>bit qvariable\<close> and h :: \<open>(bit \<Rightarrow> bit) cvariable\<close>
  assumes [register]: \<open>qregister \<lbrakk>x,y\<rbrakk>\<close> \<open>cregister \<lbrakk>h\<rbrakk>\<close>
begin
ML \<open>
test_get_wp \<^context> true
            \<^term>\<open>qapply x Expr[hadamard]\<close>
            \<^term>\<open>Expr[top] :: predicate expression2\<close>
            \<^term>\<open>Expr[\<CC>\<ll>\<aa>[isometry hadamard] \<sqinter> ((hadamard\<guillemotright>\<lbrakk>x1\<rbrakk>)* \<cdot> (top \<sqinter> (hadamard\<guillemotright>\<lbrakk>x1\<rbrakk> \<cdot> top)))] :: _ expression2\<close>
\<close>
end

experiment
  fixes x :: \<open>bit cvariable\<close>
  assumes [register]: \<open>cregister x\<close>
begin
ML \<open>
test_get_wp \<^context> false
            \<^term>\<open>sample \<lbrakk>x\<rbrakk> Expr[undefined]\<close>
            \<^term>\<open>Expr[top] :: predicate expression2\<close>
            \<^term>\<open>Expr[\<CC>\<ll>\<aa>[weight (undefined::bit distr) = (1::real)] 
                 \<sqinter> (INF z::bit\<in>supp undefined. (top::predicate))] :: _ expression2\<close>
\<close>
end

(* variables classical b :: int begin
ML \<open>
local
val t = \<^term>\<open>qrhl Expr[top] [assign var_b Expr[1]] [assign var_b Expr[2]] Expr[top]\<close>
val t' = Weakest_Precondition.wp_tac_on_term true \<^context> t |> the |> the_single
val _ = assert_aconv \<^term>\<open>qrhl Expr[top] [] [assign var_b Expr[2]] Expr[top]\<close> t'
in end
\<close>
end *)

end
