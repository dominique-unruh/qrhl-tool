theory Extended_Sorry
  imports Main
begin

definition sorry_marker :: "int \<Rightarrow> prop \<Rightarrow> prop" where "sorry_marker n P == P"

ML_file "extended_sorry.ML"

method_setup cheat = \<open>Scan.lift (Parse.position Parse.text) >> (fn (txt,pos) => fn _ => CONTEXT_METHOD (fn _ => fn (ctxt, st) =>
    Method.CONTEXT ctxt (CHANGED (Extended_Sorry.marked_sorry_tac ctxt {position=pos, comment=txt}) st)))\<close>

(* lemma test: "((!x. applyOp A (ket x) = applyOp B (ket x)) \<longrightarrow> A = B) \<and> abc"
  apply auto
  by (cheat xxxx) *)

end