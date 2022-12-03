theory Test_Prog_Variables
  imports UnitTest "QRHL.Prog_Variables"
begin

declare [[show_types, show_consts]]

lemma 
  assumes [register]: \<open>qregister \<lbrakk>q, r\<rbrakk>\<close>
  shows \<open>\<lbrakk>r \<le> qregister_id\<rbrakk>\<^sub>q\<close>
  by (tactic \<open>Prog_Variables.qregister_le_tac \<^context> 1\<close>)

schematic_goal 
  assumes [register]: \<open>qregister \<lbrakk>q, r\<rbrakk>\<close>
  shows \<open>\<lbrakk>qregister_chain \<lbrakk>q\<rbrakk>\<^sub>q qregister_id \<le> \<lbrakk>q, r\<rbrakk>\<^sub>q\<rbrakk>\<^sub>q\<close>
  by (tactic \<open>Prog_Variables.qregister_le_tac \<^context> 1\<close>)

schematic_goal 
  assumes [register]: \<open>qregister \<lbrakk>q, r\<rbrakk>\<close>
  shows \<open>\<lbrakk>qregister_id \<le> (?F::(?'a,'b) qregister)\<rbrakk>\<^sub>q \<and> \<lbrakk>r \<le> ?F\<rbrakk>\<^sub>q\<close>
  by (tactic \<open>Prog_Variables.qregister_lub_tac \<^context> 1\<close>)

experiment
  fixes q r :: \<open>int qvariable\<close>
  assumes [register]: \<open>qregister \<lbrakk>q, r\<rbrakk>\<close>
begin

ML \<open>
val ct = \<^cterm>\<open>\<lbrakk>qregister_chain \<lbrakk>q\<rbrakk>\<^sub>q qregister_id \<mapsto> \<lbrakk>q,r\<rbrakk>\<rbrakk>\<^sub>q\<close>
val _ = assert_aconv_conv (Prog_Variables.qregister_conversion_to_register_conv \<^context>) ct 
    \<^term>\<open>qFst :: (_, int * int) qregister\<close>
\<close>

ML \<open>
val ct = \<^cterm>\<open>\<lbrakk>q \<mapsto> q\<rbrakk>\<^sub>q\<close>
val _ = assert_aconv_conv (Prog_Variables.qregister_conversion_to_register_conv \<^context>) ct 
    \<^term>\<open>qregister_id :: (_, int) qregister\<close>
\<close>

ML \<open>
val ct = \<^cterm>\<open>\<lbrakk>q \<mapsto> qregister_id\<rbrakk>\<^sub>q\<close>
val _ = assert_aconv_conv (Prog_Variables.qregister_conversion_to_register_conv \<^context>) ct 
    \<^term>\<open>q\<close>
\<close>

end



end
