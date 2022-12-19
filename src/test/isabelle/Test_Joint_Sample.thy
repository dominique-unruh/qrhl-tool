theory Test_Joint_Sample
  imports UnitTest "QRHL.Joint_Sample"
begin

experiment
  fixes x :: \<open>bit cvariable\<close> and y :: \<open>bit cvariable\<close>
  assumes [register]: \<open>cregister x\<close> \<open>cregister y\<close>
begin

schematic_goal "qrhl ?e [sample \<lbrakk>x\<rbrakk> Expr[uniform UNIV]] [sample \<lbrakk>y\<rbrakk> Expr[uniform UNIV]] Expr[Cla[x1=y2]]" and \<open>?e = (\<lambda>_. \<top>)\<close>
   apply (tactic \<open>Joint_Sample.joint_sample_equal_tac \<^context> 1\<close>)
  by simp

schematic_goal
  assumes [simp]: \<open>map_distr fst (uniform X) = uniform A\<close> \<open>map_distr snd (uniform X) = uniform B\<close>
    \<open>\<forall>x\<in>supp (uniform X). fst x = snd x\<close>
  shows "qrhl ?e [sample \<lbrakk>x\<rbrakk> Expr[uniform A]] [sample \<lbrakk>y\<rbrakk> Expr[uniform B]] Expr[Cla[x1=y2]]" and \<open>?e = (\<lambda>_. \<top>)\<close>
   apply (tactic \<open>Joint_Sample.joint_sample_tac \<^context> \<^cterm>\<open>\<lambda>m::cl2. uniform X :: (bit*bit) distr\<close> 1\<close>)
  by simp

end


end