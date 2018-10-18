theory Extended_Sorry
  imports Main
begin

definition sorry_marker :: "int \<Rightarrow> prop \<Rightarrow> prop" where "sorry_marker n P == P"

ML_file "extended_sorry.ML"

method_setup cheat = \<open>Scan.lift (Parse.position Parse.text) >> (fn (txt,pos) => fn _ => CONTEXT_METHOD (fn _ => fn (ctxt, st) =>
    Method.CONTEXT ctxt (Extended_Sorry.marked_sorry_tac ctxt {position=pos, comment=txt} 1 st)))\<close>

lemma test: "1=3 \<and> 2=3"
  apply rule
  by (cheat xxx)+

ML \<open>
Extended_Sorry.show_oracles @{thm test}
\<close>


end