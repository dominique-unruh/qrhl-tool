theory Test_Expressions
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
assert_aconv true \<^term>\<open>Expr[x1+1]\<close> \<^term>\<open>\<lambda>mem::cl2. getter (cregister_chain cFst x) mem + 1\<close>
\<close>

ML \<open>
assert_aconv_conv true (Expressions.clean_expression_conv \<^context>)
                  \<^cterm>\<open>getter x (setter x 1 mm)\<close>
                  \<^term>\<open>1 :: int\<close>
\<close>

ML \<open>
assert_aconv_conv true (Expressions.clean_expression_conv \<^context>)
                  \<^cterm>\<open>getter x (setter y 1 mm)\<close>
                  \<^term>\<open>getter x mm\<close>
\<close>

ML \<open>
assert_aconv true (Expressions.expression_to_term \<^context> \<^term>\<open>\<lambda>mem::cl2. getter (cregister_chain cFst x) mem + 1\<close>)
             \<^term>\<open>(x1::int)+1\<close> 
\<close>

ML \<open>
assert_aconv true (Expressions.expression_to_term \<^context> \<^term>\<open>\<lambda>mem::cl. getter x mem + 1\<close>)
             (Syntax.read_term_global \<^theory> "(x::int)+1") 
\<close>

ML \<open>
assert_aconv true (Expressions.expression_to_term \<^context> \<^term>\<open>\<lambda>mem::cl2. qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q q \<equiv>\<qq> qregister_chain \<lbrakk>#2.\<rbrakk>\<^sub>q q\<close>)
             \<^term>\<open>(q1::(int,qu2) qregister) \<equiv>\<qq> q2\<close> 
\<close>

end

end