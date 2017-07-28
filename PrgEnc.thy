theory PrgEnc
  imports QRHL_Protocol
begin

declare[[quick_and_dirty]]
  
typedecl key
typedecl msg
  
instantiation key :: finite begin instance sorry end
instantiation msg :: finite begin instance sorry end
instantiation msg :: group_add begin instance sorry end
  
axiomatization 
  G :: "key \<Rightarrow> msg" 
  
definition enc :: "key * msg \<Rightarrow> msg"
  where [simp]: "enc = (\<lambda>(k,x). G(k)+x)"
  
end

