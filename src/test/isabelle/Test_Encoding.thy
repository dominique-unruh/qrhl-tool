theory Test_Encoding
  imports UnitTest "QRHL.Encoding"
begin

variables classical b :: int begin
ML \<open>
local
val ct = \<^cterm>\<open>expression (variable_concat \<lbrakk>var_b\<rbrakk> (variable_concat (variable_concat variable_unit variable_unit) variable_unit)) e\<close>
val ct' = Encoding.clean_expression_conv_varlist \<^context> ct |> Thm.rhs_of |> \<^print>
val varlist = ct' |> Thm.dest_fun |> Thm.dest_arg |> \<^print>
val () = assert_aconv_cterm \<^cterm>\<open>\<lbrakk>var_b\<rbrakk>\<close> varlist
in end
\<close>
end

variables classical x :: int begin
ML \<open>
local
val ct = \<^cterm>\<open>expression (variable_concat variable_unit \<lbrakk>var_x2\<rbrakk>) (\<lambda>(x1,x2). x2)\<close>
val () = assert_aconv_conv (Encoding.clean_expression_conv \<^context>)
        ct \<^term>\<open>expression \<lbrakk>var_x2\<rbrakk> (\<lambda>x1. x1)\<close> : unit
in end
\<close>
end


variables classical x :: int begin
ML \<open>
local
val ct = \<^cterm>\<open>subst_expression (substitute1 var_x1 (const_expression z))
                   (expression \<lbrakk>var_x1, var_x2\<rbrakk> (\<lambda>(x1::int, x2::int). (x1,x2)))\<close>
val () = assert_aconv_conv (Encoding.subst_expression_conv \<^context>) ct 
            \<^term>\<open>expression \<lbrakk>var_x2\<rbrakk> (%x. (z::int,x))\<close>
in end
\<close>
end

end
