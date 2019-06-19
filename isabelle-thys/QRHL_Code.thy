theory QRHL_Code
  imports Complex_Inner_Product
begin

definition [code del]: "SPAN = (undefined :: complex list \<Rightarrow> 'a linear_space)"
code_datatype SPAN

end
