theory Test
  imports 
    "HOL-Library.Rewrite" 
    "HOL-Library.Adhoc_Overloading"
begin

lemma "(0::nat) = (1::nat)"
  apply (rewrite One_nat_def)

