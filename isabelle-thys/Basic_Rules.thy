theory Basic_Rules
  imports Complex_Inner_Product Complex_Main
begin

lift_definition index_flip_subspace :: "int linear_space \<Rightarrow> int linear_space" is
  "\<lambda>S. (undefined :: int \<Rightarrow> int) ` S"
  by simp

end
