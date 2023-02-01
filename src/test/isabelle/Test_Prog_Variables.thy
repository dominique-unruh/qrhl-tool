theory Test_Prog_Variables
  imports UnitTest "QRHL.Prog_Variables"
begin


experiment
  fixes q r :: \<open>int qvariable\<close> and b :: \<open>bit qvariable\<close>
  assumes [register]: \<open>qregister \<lbrakk>q, r, b\<rbrakk>\<close>
begin
abbreviation \<open>q1 \<equiv> qregister_chain qFst q :: _ q2variable\<close> 
abbreviation \<open>q2 \<equiv> qregister_chain qSnd q :: _ q2variable\<close>
abbreviation \<open>r1 \<equiv> qregister_chain qFst r :: _ q2variable\<close> 
abbreviation \<open>r2 \<equiv> qregister_chain qSnd r :: _ q2variable\<close>
ML \<open>open Prog_Variables\<close>


declare [[show_types, show_consts]]

lemma 
  shows \<open>\<lbrakk>r \<le> qregister_id\<rbrakk>\<^sub>q\<close>
  by (tactic \<open>Prog_Variables.qregister_le_tac \<^context> 1\<close>)

lemma \<open>\<lbrakk>empty_qregister \<le> r\<rbrakk>\<^sub>q\<close>
  by (tactic \<open>Prog_Variables.qregister_le_tac \<^context> 1\<close>)

lemma 
  shows \<open>\<lbrakk>qregister_chain \<lbrakk>q\<rbrakk>\<^sub>q qregister_id \<le> \<lbrakk>q, r\<rbrakk>\<^sub>q\<rbrakk>\<^sub>q\<close>
  by (tactic \<open>Prog_Variables.qregister_le_tac \<^context> 1\<close>)

schematic_goal 
  shows \<open>\<lbrakk>qregister_id \<le> (?F::(?'a,qu) qregister)\<rbrakk>\<^sub>q \<and> \<lbrakk>r \<le> ?F\<rbrakk>\<^sub>q\<close>
  by (tactic \<open>Prog_Variables.qregister_lub_tac \<^context> 1\<close>)

schematic_goal 
  shows \<open>\<lbrakk>empty_qregister \<le> (?F::(?'a,qu) qregister)\<rbrakk>\<^sub>q \<and> \<lbrakk>r \<le> ?F\<rbrakk>\<^sub>q\<close>
  by (tactic \<open>Prog_Variables.qregister_lub_tac \<^context> 1\<close>)

ML \<open>
val ct = \<^cterm>\<open>\<lbrakk>qregister_chain \<lbrakk>q\<rbrakk>\<^sub>q qregister_id \<mapsto> \<lbrakk>q,r\<rbrakk>\<rbrakk>\<^sub>q\<close>
val _ = assert_aconv_conv true (Prog_Variables.qregister_conversion_to_register_conv \<^context>) ct 
    \<^term>\<open>qFst :: (_, int * int) qregister\<close>
\<close>

ML \<open>
val ct = \<^cterm>\<open>\<lbrakk>q \<mapsto> q\<rbrakk>\<^sub>q\<close>
val _ = assert_aconv_conv true (Prog_Variables.qregister_conversion_to_register_conv \<^context>) ct 
    \<^term>\<open>qregister_id :: (_, int) qregister\<close>
\<close>

ML \<open>
val ct = \<^cterm>\<open>\<lbrakk>q \<mapsto> qregister_id\<rbrakk>\<^sub>q\<close>
val _ = assert_aconv_conv true (Prog_Variables.qregister_conversion_to_register_conv \<^context>) ct 
    \<^term>\<open>q\<close>
\<close>

ML \<open>
assert_aconv_conv true (qregister_conversion_to_register_conv \<^context>)
  \<^cterm>\<open>\<lbrakk>q1, r1 \<mapsto> q1, r1, q2, r2\<rbrakk>\<^sub>q\<close>
  \<^term>\<open>\<lbrakk>\<lbrakk>#1\<rbrakk>\<^sub>q, \<lbrakk>#2\<rbrakk>\<^sub>q\<rbrakk>\<^sub>q :: (int \<times> int, int \<times> int \<times> int \<times> int) qregister\<close>
\<close>

(* Check whether Prog_Variables.declare_variable properly declares quantum variables *)
ML \<open>
local
val ctxt = Prog_Variables.declare_variable \<^context> \<^binding>\<open>qvar\<close> \<^typ>\<open>bool\<close> Prog_Variables.Quantum [("q",\<^typ>\<open>int\<close>)]
in
val _ = assert_aconv true (Syntax.read_term ctxt "qvar") \<^term>\<open>qvar :: bool qvariable\<close>
val _ = assert_aconv_conv true (Simplifier.rewrite ctxt) \<^cterm>\<open>qregister \<lbrakk>qvar::bool qvariable, q\<rbrakk>\<^sub>q\<close> \<^term>\<open>True\<close>
end
\<close>

lemma \<open>\<lbrakk>q1, r1 \<le> q1, r1, q2\<rbrakk>\<^sub>q\<close>
  by (tactic \<open>Prog_Variables.qregister_le_tac \<^context> 1\<close>)

ML \<open>
assert_aconv_conv false (translate_to_index_registers_conv \<^context>)
  \<^cterm>\<open>apply_qregister b hadamard *\<^sub>S top\<close>
  \<^term>\<open>apply_qregister_space b
      (apply_qregister qregister_id (apply_qregister qregister_id hadamard) *\<^sub>S
       apply_qregister_space empty_qregister \<top>)\<close>
\<close>

ML \<open>
assert_aconv_conv false (translate_to_index_registers_conv \<^context>)
  \<^cterm>\<open>- (apply_qregister_space b X) \<sqinter> top\<close>
  \<^term>\<open>TODO\<close>
\<close>

end



end
