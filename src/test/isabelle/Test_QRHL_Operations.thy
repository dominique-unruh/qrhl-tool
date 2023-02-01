theory Test_QRHL_Operations
  imports UnitTest "QRHL.QRHL_Operations"
begin

ML \<open>open QRHL_Operations\<close>

experiment
  fixes q r :: \<open>int qvariable\<close>
  fixes x y :: \<open>int cvariable\<close>
  assumes [register]: \<open>qregister \<lbrakk>q, r\<rbrakk>\<close>
  assumes [register]: \<open>cregister \<lbrakk>x, y\<rbrakk>\<^sub>c\<close>
begin

declare [[eta_contract=false]]

ML \<open>
assert_aconv true \<^term>\<open>\<forall>x::int. Cla[x = 1] \<le> Cla[x \<le> 1]\<close>
  (expression_leq (\<^context>, \<^term>\<open>Expr[Cla[x = 1]]\<close>, \<^term>\<open>Expr[Cla[x \<le> 1]]\<close>))
\<close>

end

end
