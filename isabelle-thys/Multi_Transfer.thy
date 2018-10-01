theory Multi_Transfer
  imports Main
  keywords "save_transfer_rules" :: thy_decl
begin

ML_file "multi_transfer.ML"

(* typedef t1 = "UNIV::bool set" by simp
setup_lifting type_definition_t1
typedef t2 = "UNIV::t1 set" by simp
setup_lifting type_definition_t2
lift_definition x :: t1 is "undefined::bool" .
lift_definition y :: t2 is x . *)

(* ML \<open>
fun transfer_del_type tyco context = 
  let val matching_thms = Transfer.get_transfer_raw (Context.proof_of context)
        |> filter (fn thm => thm |> Thm.prop_of |> 
              Term.exists_type (Term.exists_subtype (fn Type(n,_) => n=tyco | _ => false)))
|> map @{print}
      val context' = fold_rev (Transfer.transfer_raw_del) matching_thms context
in
  context'
end

val _ = Attrib.setup @{binding transfer_del_type}
  (Scan.lift (Parse.type_const)
    >> (fn tyco => Thm.declaration_attribute (fn _ => fn context =>
      let val tyco' = Proof_Context.read_type_name {proper=true,strict=true} (Context.proof_of context) tyco
                      |> dest_Type |> fst
      in transfer_del_type tyco' context end)))
  "Deletes all transfer rules containing a given type" 
  |> Theory.setup
\<close> *)

(* term "()"
lemma "y = y"
  using [[transfer_del_const pcr_t1]]
  apply transfer
  apply transfer
 *)

end
