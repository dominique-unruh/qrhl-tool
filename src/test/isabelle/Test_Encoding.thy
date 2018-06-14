theory Test_Encoding
  imports UnitTest "../../main/isabelle/Encoding"
begin

variables classical b :: int begin
ML \<open>
local
val ct = @{cterm "expression (variable_concat \<lbrakk>var_b\<rbrakk> (variable_concat (variable_concat variable_unit variable_unit) variable_unit)) e"}
val ct' = Encoding.clean_expression_conv_varlist @{context} ct |> Thm.rhs_of |> @{print}
val varlist = ct' |> Thm.dest_fun |> Thm.dest_arg |> @{print}
val () = assert_aconv_cterm @{cterm "\<lbrakk>var_b\<rbrakk>"} varlist
in end
\<close>
end

variables classical x :: int begin
ML \<open>
local
val ct = @{cterm "expression (variable_concat variable_unit \<lbrakk>var_x2\<rbrakk>) (\<lambda>(x1,x2). x2)"}
val () = assert_aconv_conv (Encoding.clean_expression_conv @{context})
        ct @{term "expression \<lbrakk>var_x2\<rbrakk> (\<lambda>x1. x1)"} : unit
in end
\<close>
end


variables classical x :: int begin
ML \<open>
local
val ct = @{cterm "subst_expression (substitute1 var_x1 (const_expression z))
                   (expression \<lbrakk>var_x1, var_x2\<rbrakk> (\<lambda>(x1::int, x2::int). (x1,x2)))"}
val () = assert_aconv_conv (Encoding.subst_expression_conv @{context}) ct 
            @{term "expression \<lbrakk>var_x2\<rbrakk> (%x. (z::int,x))"}
in end
\<close>
end

end
