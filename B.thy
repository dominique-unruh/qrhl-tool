theory B
  imports Bot
begin

lift_definition index_flip_subspace :: "int t \<Rightarrow> int t" is
  "\<lambda>S. (undefined :: int \<Rightarrow> int) ` S"
  by simp

end
