theory Universe_Instances_CryptHOL
  imports Universe_Instances_Complex_Main CryptHOL.Misc_CryptHOL
begin

no_notation HLD_nxt (infixr "\<cdot>" 65)

derive universe nlist
derive universe blinfun
derive universe bcontfun
derive universe vec
derive universe ereal
derive universe ennreal
derive universe 1
derive universe 0
derive universe enat
derive universe topology
derive universe Monomorphic_Monad.id
derive universe measure
derive universe pmf
derive universe discrete
derive universe tree
derive universe fps
derive universe cset
derive universe llist
derive universe bit1
derive universe bit0
derive universe multiset
derive universe stream
derive universe fset
derive universe optionT
derive universe nondetT
derive universe stateT
derive universe contT
derive universe envT
derive universe phantom
derive universe Old_Datatype.node
derive universe mapping
derive universe fmap
derive universe tllist
derive universe writerT
derive universe resumption

ML \<open> (* Lists all types that are not declared as sort universe *)
\<^context>
|> Proof_Context.tsig_of
|> Type.rep_tsig
|> #log_types
|> app (fn tn => (Proof_Context.arity_sorts \<^context> tn @{sort universe}; ()) 
    handle ERROR _ => tracing ("NO: "^Syntax.string_of_typ \<^context> (Type(tn,[]))^"    "^tn))
\<close>


end