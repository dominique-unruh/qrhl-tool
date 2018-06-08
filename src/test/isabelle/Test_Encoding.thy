theory Test_Encoding
  imports UnitTest "../../main/isabelle/Encoding"
begin

variables classical b :: int begin
ML \<open>
local
val ct = @{cterm "expression (variable_concat \<lbrakk>var_b\<rbrakk> (variable_concat (variable_concat variable_unit variable_unit) variable_unit)) e"}
val ct' = Encoding.clean_expression_conv_varlist @{context} ct |> Thm.rhs_of |> @{print}
val varlist = ct' |> Thm.dest_fun |> Thm.dest_arg |> @{print}
val _ = assert_aconv_cterm @{cterm "\<lbrakk>var_b\<rbrakk>"} varlist
in end
\<close>
end


end
