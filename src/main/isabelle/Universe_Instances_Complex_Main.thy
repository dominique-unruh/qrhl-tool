theory Universe_Instances_Complex_Main
  imports Complex_Main Universe 
begin

derive universe real
derive universe complex

ML \<open> (* Lists all types that are not declared as sort universe *)
\<^context>
|> Proof_Context.tsig_of
|> Type.rep_tsig
|> #log_types
|> app (fn tn => (Proof_Context.arity_sorts \<^context> tn @{sort universe}; ()) 
    handle ERROR _ => tracing ("NO: "^Syntax.string_of_typ \<^context> (Type(tn,[]))^"    "^tn))
\<close>

end
