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
  
lemma my_simp: "G k1 + x = x + G k1 + m2 + m2 == True"
  by (smt add.assoc add.left_cancel xor_cancel)
  
    declare[[show_types,show_sorts]]

axiomatization where bad: "a+b=0" for a :: msg
  
ML{*
QRHL.simp @{term "\<CC>\<ll>\<aa>[undefined] \<sqinter> (INF x. \<CC>\<ll>\<aa>[G k1 + x = x + G k1 + m2 + m2 \<and> m1 = m2 \<and> cglobA1 = cglobA2 \<and> b1 = b2] \<sqinter> \<lbrakk>qglobA1\<rbrakk> \<equiv>\<qq> \<lbrakk>qglobA2\<rbrakk>)
"} ["bad"] @{context}
|> Thm.cterm_of @{context}
*}
  
    
end
  