theory Multi_Transfer
  imports Main
begin

definition "transfer_hint  (t::'a itself) b = b"
syntax "_transfer_hint" :: "'a \<Rightarrow> type => 'a" ("_ ::: _")
translations "a ::: 't" == "CONST transfer_hint TYPE('t) a"
lemma [transfer_rule]: 
  includes lifting_syntax
  shows "(R ===> R) (\<lambda>x::'a. x) (transfer_hint TYPE('a))"
  unfolding transfer_hint_def by transfer_prover

ML_file "multi_transfer.ML"

end
