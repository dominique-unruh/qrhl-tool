theory Test_Squash_Sampling
  imports QRHL.Squash_Sampling UnitTest
begin

variables
quantum q :: int and
quantum r :: int and
quantum s :: int and
classical x :: int and
classical y :: int and
classical z :: int
begin

lemma 
  assumes  \<open>qrhl A [qinit \<lbrakk>q\<rbrakk> Expr[U *\<^sub>V \<psi>]] [] B\<close>
  shows \<open>qrhl A [qinit \<lbrakk>q\<rbrakk> Expr[\<psi>], qapply \<lbrakk>q\<rbrakk> Expr[U]] [] B\<close>
  apply (tactic \<open>Squash_Sampling.squash_sampling_tac true \<^context> 1\<close>)
  using assms
  by simp

lemma \<open>qrhl A [qinit \<lbrakk>q,s,r\<rbrakk> Expr[ket (x,y,z)], qapply \<lbrakk>q,r\<rbrakk> Expr[U x \<otimes>\<^sub>o id_cblinfun]] [] B\<close>
  apply (tactic \<open>Squash_Sampling.squash_sampling_tac true \<^context> 1\<close>)
  oops

end



end