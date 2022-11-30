theory Test_Weakest_Precondition
  imports QRHL.Weakest_Precondition UnitTest
begin


ML \<open>
fun test_get_wp ctxt left prog post expected =
let val (wp,thm) = Weakest_Precondition.get_wp left prog post ctxt
    val wp' = wp |> Thm.cterm_of ctxt |> Conv.try_conv (Expressions.clean_expression_conv ctxt)
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
            \<^term>\<open>Expr[top::predicate]\<close> (* post *)
            \<^term>\<open>const_expression ((\<CC>\<ll>\<aa>[\<not> True] + top) \<sqinter> (\<CC>\<ll>\<aa>[True] + top))\<close> (* expected *)
\<close>

declare[[show_types,show_sorts,show_consts,eta_contract=false]]

(* TEST CASE: get_wp of "measure a A computational_basis" *)
variables classical a :: bit and quantum A :: bit begin
ML \<open>
test_get_wp \<^context> true 
            \<^term>\<open>measurement \<lbrakk>var_a\<rbrakk> \<lbrakk>A\<rbrakk> (const_expression computational_basis)\<close> (* program *)
            \<^term>\<open>const_expression (top::predicate)\<close> (* post *)
            \<^term>\<open>const_expression
                 (let M::(bit, bit) measurement = computational_basis
                  in \<CC>\<ll>\<aa>[mtotal M] \<sqinter> (INF z::bit. let P::mem2 subspace = mproj M z\<guillemotright>\<lbrakk>A1::bit variable\<rbrakk> \<cdot> top in top \<sqinter> P + - P))\<close> (* expected *)
\<close>
end

(* TEST CASE: get_wp (right) of "if (true) b:=1" *)
variables classical b :: bit begin
ML \<open>
test_get_wp \<^context> false
            \<^term>\<open>ifthenelse Expr[True] [assign \<lbrakk>var_b\<rbrakk> Expr[1] ] []\<close> (* program *)
            \<^term>\<open>Expr[top::predicate]\<close> (* post *)
            \<^term>\<open>const_expression ((\<CC>\<ll>\<aa>[\<not> True] + top) \<sqinter> (\<CC>\<ll>\<aa>[True] + top))\<close> (* expected *)
\<close>
end

variables quantum x :: bit and quantum y :: bit and classical h :: "bit \<Rightarrow> bit" begin
ML \<open>
test_get_wp \<^context> true
            \<^term>\<open>qapply \<lbrakk>x\<rbrakk> Expr[hadamard]\<close>
            \<^term>\<open>Expr[top::predicate]\<close>
            \<^term>\<open>Expr[\<CC>\<ll>\<aa>[isometry hadamard] \<sqinter> ((hadamard\<guillemotright>\<lbrakk>x1::bit variable\<rbrakk>)* \<cdot> (top \<sqinter> (hadamard\<guillemotright>\<lbrakk>x1\<rbrakk> \<cdot> top)))]\<close>
\<close>
end


variables classical x :: bit begin
declare [[show_types,show_consts]]
ML \<open>
test_get_wp \<^context> false
            \<^term>\<open>sample \<lbrakk>var_x\<rbrakk> Expr[undefined]\<close>
            \<^term>\<open>Expr[top::predicate]\<close>
            \<^term>\<open>Expr[\<CC>\<ll>\<aa>[weight (undefined::bit distr) = (1::real)] \<sqinter> (INF z::bit\<in>supp undefined. (top::predicate))]\<close>
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
