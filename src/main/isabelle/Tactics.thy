theory Tactics
  imports Encoding Weakest_Precondition
begin


ML_file "tactics.ML"

method_setup seq = {*
  Scan.lift Parse.nat -- Scan.lift Parse.nat -- Scan.lift Parse.term >> (fn ((i,j),B) => fn ctx =>
    SIMPLE_METHOD (Tactics.seq_tac i j (Encoding.read_predicate ctx B) ctx 1))
*}


variables classical x :: nat begin

schematic_goal "qrhl ?pre [block [assign var_x Expr[x+2], assign var_x Expr[0], assign var_x Expr[x+1] ] ] [] Expr[ Cla[x1=1] ]"
  apply (tactic \<open>Tactics.wp_tac \<^context> true 1\<close>)
  apply simp
  oops

end

end
