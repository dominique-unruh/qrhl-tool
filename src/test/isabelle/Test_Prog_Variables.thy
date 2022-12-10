theory Test_Prog_Variables
  imports UnitTest "QRHL.Prog_Variables"
begin


experiment
  fixes q r :: \<open>int qvariable\<close>
  assumes [register]: \<open>qregister \<lbrakk>q, r\<rbrakk>\<close>
begin

declare [[show_types, show_consts]]

lemma 
  shows \<open>\<lbrakk>r \<le> qregister_id\<rbrakk>\<^sub>q\<close>
  by (tactic \<open>Prog_Variables.qregister_le_tac \<^context> 1\<close>)

schematic_goal 
  shows \<open>\<lbrakk>qregister_chain \<lbrakk>q\<rbrakk>\<^sub>q qregister_id \<le> \<lbrakk>q, r\<rbrakk>\<^sub>q\<rbrakk>\<^sub>q\<close>
  by (tactic \<open>Prog_Variables.qregister_le_tac \<^context> 1\<close>)

schematic_goal 
  shows \<open>\<lbrakk>qregister_id \<le> (?F::(?'a,qu) qregister)\<rbrakk>\<^sub>q \<and> \<lbrakk>r \<le> ?F\<rbrakk>\<^sub>q\<close>
  by (tactic \<open>Prog_Variables.qregister_lub_tac \<^context> 1\<close>)

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

(* Check whether Prog_Variables.declare_variable properly declares quantum variables *)
ML \<open>
local
val ctxt = Prog_Variables.declare_variable \<^context> \<^binding>\<open>qvar\<close> \<^typ>\<open>int\<close> Prog_Variables.Quantum [("q",\<^typ>\<open>int\<close>)]
in
val _ = assert_aconv (Syntax.read_term ctxt "qvar") \<^term>\<open>qvar :: int qvariable\<close>
val _ = assert_aconv_conv (Simplifier.rewrite ctxt) \<^cterm>\<open>qregister \<lbrakk>qvar::int qvariable, q\<rbrakk>\<^sub>q\<close> \<^term>\<open>True\<close>
end
\<close>

end



end
