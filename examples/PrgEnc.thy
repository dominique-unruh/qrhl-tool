theory PrgEnc
  imports QRHL.QRHL
begin

typedecl key
typedecl msg

(* The types of keys and messages must be declared finite, otherwise uniform sampling is not defined *)
instantiation key :: finite begin instance sorry end
instantiation msg :: finite begin instance sorry end

(* The type of messages is declared as an additive group,
   + stands for the bitwise XOR on messages *)
instantiation msg :: group_add begin instance sorry end
axiomatization where xor_cancel[simp]: "a+a=0" for a::msg

(* G is an unspecified pseudo-random generator *)
axiomatization 
  G :: "key \<Rightarrow> msg" 

(* Encryption is defined in terms of G *)
definition enc :: "key * msg \<Rightarrow> msg"
  where [simp]: "enc = (\<lambda>(k,x). G(k)+x)"

(* Three lemmas that we use in the *.qrhl files *)
lemma my_simp: "G k1 + x = x + G k1 + m2 + m2"
  by (metis add.assoc add.left_cancel xor_cancel)

lemma mysimp2: "x+m11+m22+m22 = x+m11" for x::msg
  by (metis add.assoc add.left_cancel xor_cancel)

lemma aux_bij: "bij (\<lambda>xb::msg. xb + Gx + xa)"
  apply (rule bij_betw_byWitness[where f'="\<lambda>xb::msg. xb + Gx + xa"], auto)
  apply (metis add.assoc add.left_cancel xor_cancel)
  by (metis add.assoc add.left_cancel xor_cancel)
    
end
