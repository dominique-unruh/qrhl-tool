theory Test_Registers_Automation
  imports UnitTest Registers2.Registers_Automation Registers2.Register_Syntax
begin

ML \<open>open Registers_Automation\<close>

experiment
  fixes C :: "(bit, string) qregister" and A :: "(bit, string) qregister" and B :: "(bit, string) qregister"
  assumes [register]: \<open>qregister \<lbrakk>C, A, B\<rbrakk>\<close>
begin

(* ML \<open>
Registers.quick_norm_register
\<^term>\<open>qregister_chain \<lbrakk>qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q A, qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q B, qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q C, qregister_chain \<lbrakk>#2.\<rbrakk>\<^sub>q A\<rbrakk>\<^sub>q \<lbrakk>#3.\<rbrakk>\<^sub>q
:: (_,string * string) qregister\<close>
|> Thm.cterm_of \<^context>
\<close>

ML \<open>
Registers.quick_norm_register
\<^term>\<open>qregister_chain \<lbrakk>qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q A, qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q B, qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q C, qregister_chain \<lbrakk>#2.\<rbrakk>\<^sub>q A\<rbrakk>\<^sub>q \<lbrakk>#3.\<rbrakk>\<^sub>q
:: (_,string * string) qregister\<close>
|> Thm.cterm_of \<^context>
\<close> *)


ML \<open>
local
val t1 = \<^term>\<open>\<lbrakk>qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q C, qregister_chain \<lbrakk>#2.\<rbrakk>\<^sub>q A\<rbrakk>\<^sub>q\<close>
val t2 = \<^term>\<open>qregister_chain \<lbrakk>qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q A, qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q B, qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q C, qregister_chain \<lbrakk>#2.\<rbrakk>\<^sub>q A\<rbrakk>\<^sub>q \<lbrakk>#3.\<rbrakk>\<^sub>q\<close>
in
val _ = assert_aconv true t1
(join_registers \<^context> t1 t2 |> the)
end
\<close>
end


end


