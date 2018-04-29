theory Test
  imports Main Test3 "HOL-Library.Adhoc_Overloading" Main
begin

lemma a: "x+(x::nat) = 2*x" by auto
lemma b: "(1::nat)+(1::nat) = 2" 
  apply (subst a)
  by simp

end
