theory PrgEnc
  imports QRHL.QRHL
begin

(* The types of keys and messages must be declared finite, otherwise uniform sampling is not defined *)
(* The type of messages is declared as an additive group,
   + stands for the bitwise XOR on messages *)
declare_variable_type key :: finite
declare_variable_type msg :: "{finite,xor_group}"

(* G is an unspecified pseudo-random generator *)
axiomatization 
  G :: "key \<Rightarrow> msg" 

(* Encryption is defined in terms of G *)
definition enc :: "key * msg \<Rightarrow> msg"
  where [simp]: "enc = (\<lambda>(k,x). G(k)+x)"

(* A lemma that we use in the *.qrhl files *)
lemma aux_bij: "bij (\<lambda>xb::msg. xb + Gx + xa)"
  apply (rule bij_betw_byWitness[where f'="\<lambda>xb::msg. xb + Gx + xa"], auto)
  by (metis Groups.add_ac(1) xor_cancel)+
    
end
