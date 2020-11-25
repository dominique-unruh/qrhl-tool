section \<open>\<open>Extended_Sorry\<close> -- An alternative to @{theory_text sorry}\<close>

theory Extended_Sorry
  imports Main
  keywords "print_oracles" (* "print_instance_oracles" *) :: diag
begin

definition sorry_marker :: "int \<Rightarrow> prop \<Rightarrow> prop" where "sorry_marker n P == P"

ML_file "extended_sorry.ML"

method_setup cheat = \<open>Scan.lift (Parse.position Parse.text) >> (fn (txt,pos) => fn _ => CONTEXT_METHOD (fn _ => fn (ctxt, st) =>
    CONTEXT_TACTIC (CHANGED (Extended_Sorry.marked_sorry_tac ctxt {position=pos, comment=txt})) (ctxt, st)))\<close>

(* lemma test: "((!x. applyOp A (ket x) = applyOp B (ket x)) \<longrightarrow> A = B) \<and> abc"
  apply auto
  by (cheat xxxx) *)

end