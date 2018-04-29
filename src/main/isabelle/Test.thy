theory Test
  imports "HOL-Library.Adhoc_Overloading" Main Test3
begin

lemma a: "x+(x::nat) = 2*x" by auto
lemma b: "(1::nat)+(1::nat) = 2" 
  apply (subst a)
  by simp

end
