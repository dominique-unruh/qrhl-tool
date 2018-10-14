theory Hashed_Terms
  imports Main
    "HOL-Protocol.Protocol_Main"
begin

ML_file "hashed_terms.ML"


ML \<open>
val _ = \<^term>\<open>1+3\<close> |> Codec.encode Hashed_Terms.term_codec |> \<^print>
\<close>

end
