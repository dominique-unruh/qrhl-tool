theory Test_Tactics
  imports UnitTest "QRHL.Tactics"
begin

ML \<open>
fun test_get_wp ctxt left prog post expected =
let val (wp,thm) = Tactics.get_wp left prog post ctxt
    val _ = assert_aconv expected wp
    val (A,_,_,B) = Encoding.dest_qrhl_goal (Thm.prop_of thm)
    val _ = assert_aconv expected A
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
            \<^term>\<open>measurement var_a \<lbrakk>A\<rbrakk> (const_expression computational_basis)\<close> (* program *)
            \<^term>\<open>const_expression (top::predicate)\<close> (* post *)
            \<^term>\<open>const_expression
                 (let M::(bit, bit) measurement = computational_basis
                  in \<CC>\<ll>\<aa>[mtotal M] \<sqinter> (INF z::bit. let P::mem2 subspace = mproj M z\<guillemotright>\<lbrakk>A1::bit variable\<rbrakk> \<cdot> top in top \<sqinter> P + ortho P))\<close> (* expected *)
\<close>
end

(* TEST CASE: get_wp (right) of "if (true) b:=1" *)
variables classical b :: bit begin
ML \<open>
test_get_wp \<^context> false
            \<^term>\<open>ifthenelse Expr[True] [assign var_b Expr[1] ] []\<close> (* program *)
            \<^term>\<open>Expr[top::predicate]\<close> (* post *)
            \<^term>\<open>const_expression ((\<CC>\<ll>\<aa>[\<not> True] + top) \<sqinter> (\<CC>\<ll>\<aa>[True] + top))\<close> (* expected *)
\<close>
end

end
