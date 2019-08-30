structure Multi_Transfer = struct

fun transfer_del_const const context = 
  let val ctxt = Context.proof_of context
      val matching_thms = Transfer.get_transfer_raw ctxt
        |> filter (fn thm => thm |> Thm.prop_of |> 
              Term.exists_Const (fn (n,_) => n=const))
      val _ = tracing ("Deleting transfer rules:\n  " ^ String.concatWith "\n  " 
              (map (Syntax.string_of_term ctxt o Thm.prop_of) matching_thms))
      val context' = fold_rev (Transfer.transfer_raw_del) matching_thms context
in
  context'
end

val _ = Attrib.setup @{binding transfer_del_const}
  (Scan.lift (Parse.const)
    >> (fn tyco => Thm.declaration_attribute (fn _ => fn context =>
      let val tyco' = Proof_Context.read_const {proper=true,strict=true} (Context.proof_of context) tyco
                      |> dest_Const |> fst
      in transfer_del_const tyco' context end)))
  "Deletes all transfer rules containing a given constant" 
  |> Theory.setup

end