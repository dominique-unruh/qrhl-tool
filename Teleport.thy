theory Teleport
  imports QRHL_Protocol
begin
  
axiomatization "tensorIso" :: "('a,'b) isometry \<Rightarrow> ('c,'d) isometry \<Rightarrow> ('a*'c,'b*'d) isometry"
axiomatization where idIso_tensor_idIso[simp]: "tensorIso idIso idIso = idIso"
axiomatization "assoc_op" :: "('a*'b*'c, ('a*'b)*'c) isometry"
axiomatization "assoc_op'" :: "(('a*'b)*'c, 'a*'b*'c) isometry"
axiomatization "comm_op" :: "('a*'b, 'b*'a) isometry"
  
consts tensor :: "'a \<Rightarrow> 'b \<Rightarrow> 'c" (infix "\<otimes>" 71)
adhoc_overloading tensor tensorIso
  
axiomatization "addState" :: "'a state \<Rightarrow> ('b,'b*'a) isometry"
axiomatization where (* TODO: some disjointness conditions *)
  quantum_eq_add_state: "quantum_equality_full U Q V R \<sqinter> span {\<psi>}\<guillemotright>T
             = quantum_equality_full (tensorIso U idIso) (qvariables_concat Q T) (addState \<psi> \<cdot> V) R"
    for U :: "('a,'c) isometry" and V :: "('b,'c) isometry" and \<psi> :: "'d state"
    and Q :: "'a qvariables"    and R :: "'b qvariables"    and T :: "'d qvariables"
  
  
end
  