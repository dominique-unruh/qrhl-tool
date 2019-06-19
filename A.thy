theory A
  imports Bot
begin

definition [code del]: "SPAN = (undefined :: int \<Rightarrow> 'a t)"
code_datatype SPAN

end
