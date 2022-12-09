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
assert_aconv \<^term>\<open>Expr[x1+1]\<close> \<^term>\<open>\<lambda>mem::cl2. getter (cregister_chain cFst x) mem + 1\<close>
\<close>

(* Parsing test *)
ML \<open>
assert_aconv \<^term>\<open>Pr[b=1 : left(rho)]\<close> \<^term>\<open>probability (\<lambda>mem. b = 1) left rho\<close>
\<close>

ML \<open>
assert_aconv_conv (Programs.clean_expression_conv \<^context>)
                  \<^cterm>\<open>getter x (setter x 1 mm)\<close>
                  \<^term>\<open>1 :: int\<close>
\<close>

ML \<open>
assert_aconv_conv (Programs.clean_expression_conv \<^context>)
                  \<^cterm>\<open>getter x (setter y 1 mm)\<close>
                  \<^term>\<open>getter x mm\<close>
\<close>

end



end
