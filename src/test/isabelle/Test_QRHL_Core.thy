theory Test_QRHL_Core
  imports  UnitTest "QRHL.QRHL_Core"
begin

(* TEST CASE: sort_lift_conv (A\<guillemotright>(variable_concat  \<lbrakk>a\<rbrakk> \<lbrakk>\<rbrakk>)) *)
variables quantum a :: int begin
ML \<open>
local
val ct = \<^cterm>\<open>(A::(_,_)bounded) \<guillemotright> variable_concat \<lbrakk>a\<rbrakk> \<lbrakk>\<rbrakk>\<close>
val ct' = QRHL.sort_lift_conv \<^context> ct |> Thm.rhs_of |> \<^print>
val (_,_,Q') = QRHL.dest_lift (Thm.term_of ct')
val () = assert_aconv \<^term>\<open>\<lbrakk>a\<rbrakk>\<close> Q'
in end
\<close>
end


end
