theory Test_Programs
  imports UnitTest "QRHL.Programs"
begin


experiment
  fixes q r :: \<open>int qvariable\<close>
  fixes x y :: \<open>int cvariable\<close>
  assumes [register]: \<open>qregister \<lbrakk>q, r\<rbrakk>\<close>
  assumes [register]: \<open>cregister \<lbrakk>x, y\<rbrakk>\<^sub>c\<close>
begin

(* Parsing test *)
ML \<open>
assert_aconv true \<^term>\<open>Pr[b=1 : left(rho)]\<close> \<^term>\<open>probability (\<lambda>mem. b = 1) left rho\<close>
\<close>

end



end
