theory ML_Term_Antiquot
imports Pure
begin

ML_file "ml_term_antiquot.ML"

setup \<open>
  ML_Antiquotation.inline \<^binding>\<open>ml_term\<close> ML_Term_Antiquot.ml_term_antiquot
  #>
  ML_Antiquotation.inline \<^binding>\<open>ml_typ\<close> ML_Term_Antiquot.ml_typ_antiquot \<close>

(* setup {* ML_Antiquotation.inline @{binding typx} TermX_Antiquot.typx_antiquot *} *)
(* 
(* From Isabelle Cookbook *)
setup {* let val parser = Args.context -- Scan.lift Args.name
             fun term_pat (ctxt, str) = str |> Proof_Context.read_term_pattern ctxt
                                            |> ML_Syntax.print_term
                                            |> ML_Syntax.atomic
         in
           ML_Antiquotation.inline @{binding "term_pat"} (parser >> term_pat)
         end *}
 *)

(* ML \<open>
  val bla = \<^typ>\<open>prop=>prop\<close>
  val tmp = \<^term>\<open>bla::prop\<Rightarrow>prop\<close>
  val res = @{ml_term "x==y" for x=tmp 'a=bla} |> Thm.cterm_of \<^context>
  (* val res2 = @{ml_typ "prop\<Rightarrow>'a" for 'a=\<open>@{typ prop}\<close>} *)
\<close>
 *)


(*
ML {*
local
val src = "@{ml_term \"hd (?l::?'l.1)\" where \"?'l.1\<Rightarrow>?'a list\"}"
val ((_,body),_) = ML_Context.eval_antiquotes (ML_Lex.read @{here} src, @{here}) (SOME (Context.Proof @{context}))
in
(*val _ = writeln (ML_Lex.flatten env) *)
val _ = writeln (ML_Lex.flatten body)
end
*}
 *)


end
