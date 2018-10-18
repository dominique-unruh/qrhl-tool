theory Scratch
  imports Main
begin

lemma l: "B x \<Longrightarrow> B y" sorry

ML \<open>
Thm.instantiate ([((("'a",0),\<^sort>\<open>type\<close>),\<^ctyp>\<open>int\<close>)], [((("B",0),\<^typ>\<open>int\<Rightarrow>bool\<close>),\<^cterm>\<open>(%x::int. True)\<close>)]) @{thm l}
|> Thm.prop_of
\<close>

ML asm_rl

ML \<open>
infer_instantiate' \<^context> [SOME \<^cterm>\<open>(%x. True)\<close>] @{thm l}
|> Thm.prop_of
\<close>


ML \<open>
\<^term>\<open>STR ''
''\<close> (* |> HOLogic.dest_literal *)
\<close>

ML Lexicon.tokenize

typ str_position

find_theorems String.Literal

ML \<open>
\<^term>\<open>STR ''
'' = STR ''\<newline>''\<close>
\<close>


definition "message = STR ''Line
Line''"
thm message_def
export_code message in Haskell


lemma "STR ''
'' = STR 0x10"
  apply (tactic \<open>Tactical.no_tac\<close>)
  apply code_simp