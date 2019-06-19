theory A
  imports Bot
begin

definition [code del]: "SPAN = (undefined :: complex list \<Rightarrow> 'a linear_space)"
code_datatype SPAN

end
