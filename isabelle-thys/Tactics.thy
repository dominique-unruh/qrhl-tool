(* TODO: distribute in separate theories *)
theory Tactics
  imports (* Expressions *) Relational_Hoare
begin



lemma seq_rule:
  assumes "qrhl A c1 d1 B"
  and "qrhl B c2 d2 C"
  shows "qrhl A (c1@c2) (d1@d2) C"
  by (cheat seq_rule)

lemma seqREMOVE:
  assumes "c = c1@c2" and "d = d1@d2"
  assumes "qrhl A c1 d1 B"
    and "qrhl B c2 d2 C"
  shows "qrhl A c d C"
  using assms using seq_rule by auto


ML_file "tactics.ML"

method_setup seq = {*
  Scan.lift Parse.nat -- Scan.lift Parse.nat -- Scan.lift Parse.term >> (fn ((i,j),B) => fn ctx =>
    SIMPLE_METHOD (Tactics.seq_tac i j (Relational_Hoare.read_predicate ctx B) ctx 1))
*}

experiment
  fixes x :: \<open>int cvariable\<close>
  assumes [variable,simp]: \<open>cregister x\<close>
begin
  lemma
    assumes \<open>qrhl A [hello] [bye] C\<close> and \<open>qrhl C [test] [test2] B\<close>
    shows "qrhl A [hello, test] [bye, test2] B"
    apply (tactic \<open>Tactics.seq_tac ~2 ~2 \<^term>\<open>C :: cl2 \<Rightarrow> predicate\<close> \<^context> 1\<close>)
    using assms by auto
  
  lemma
    assumes \<open>qrhl A [hello] [bye] Expr[Cla[x1=x2]]\<close> and \<open>qrhl Expr[Cla[x1=x2]] [test] [test2] B\<close>
    shows "qrhl A [hello, test] [bye, test2] B"
    apply (seq 1 1 \<open>Cla[x1=x2]\<close>)
    using assms by auto
  end
end
