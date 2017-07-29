theory PrgEnc
  imports QRHL_Protocol
begin

declare[[quick_and_dirty]]
  
typedecl key
typedecl msg
  
instantiation key :: finite begin instance sorry end
instantiation msg :: finite begin instance sorry end
instantiation msg :: group_add begin instance sorry end
axiomatization where xor_cancel[simp]: "a+a=0" for a::msg

axiomatization 
  G :: "key \<Rightarrow> msg" 
  
definition enc :: "key * msg \<Rightarrow> msg"
  where [simp]: "enc = (\<lambda>(k,x). G(k)+x)"
  
lemma my_simp: "G k1 + x = x + G k1 + m2 + m2"
  by (metis add.assoc add.left_cancel xor_cancel)

lemma aux_bij: "bij (\<lambda>xb::msg. xb + Gx + xa)"
  apply (rule bij_betw_byWitness[where f'="\<lambda>xb::msg. xb + Gx + xa"], auto)
  apply (metis add.assoc add.left_cancel xor_cancel)
  by (metis add.assoc add.left_cancel xor_cancel)
    
  

    
declare[[show_types,show_sorts]]
  
    
end
  