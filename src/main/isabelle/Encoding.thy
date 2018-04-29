theory Encoding
  imports QRHL_Core
begin

(* TODO: should rename "qvariables" to "variables" *)

typedecl 'a expression
axiomatization
  expression :: "'a qvariables \<Rightarrow> ('a\<Rightarrow>'b) \<Rightarrow> 'b expression"

typedecl program
axiomatization
  skip :: "program" and
  sequence :: "program \<Rightarrow> program \<Rightarrow> program" and
  assign :: "'a qvariable \<Rightarrow> 'a expression \<Rightarrow> program"

axiomatization fv_expression :: "'a expression \<Rightarrow> string set" where
  fv_expression_def: "fv_expression (expression v e) = set (qvariable_names v)" 
    for v :: "'a qvariables"

axiomatization fv_program :: "program \<Rightarrow> string set" where
  fv_program_sequence: "fv_program (sequence p1 p2) = fv_program p1 \<union> fv_program p2"
and fv_program_assign: "fv_program (assign x e) = {variable_name x} \<union> fv_expresson e"
and fv_program_skip: "fv_program skip = {}"
for p1 p2 :: program and e :: "'a expression"

axiomatization qrhl :: "predicate expression \<Rightarrow> program \<Rightarrow> program \<Rightarrow> predicate expression \<Rightarrow> bool"

axiomatization probability2 :: "bool expression \<Rightarrow> program \<Rightarrow> program_state \<Rightarrow> real"

ML {*
fun term_to_expression ctx t =
  let val lookup_var = QRHL.lookup_variable ctx
      val frees = Term.add_frees t [] |> filter (fn (v,_) => lookup_var v = SOME QRHL.Classical) |> rev
      val (vars,varsT) = 
        frees |> map (fn (v,T) => (v^"_var",T)) |> QRHL.varterm_from_list |> QRHL.mk_varterm
      val pattern = HOLogic.mk_tuple (map Free frees) |> @{print}
      val e = HOLogic.tupled_lambda pattern t
  in
    Const(@{const_name expression}, QRHL.mk_qvariablesT varsT --> (varsT --> dummyT) --> @{typ "dummy expression"})
      $ vars $ e
  end
*}

ML {*
val ctx = QRHL.declare_variable @{context} "x" @{typ int} QRHL.Classical
val e = term_to_expression ctx (HOLogic.mk_eq (Free("x",dummyT),Free("y",dummyT)))
   |> Syntax.check_term ctx 
*}


ML_file "encoding.ML"

ML {*
val e' = Encoding.add_index_to_expression e false
val t = Encoding.expression_to_term e' |> Thm.cterm_of ctx
*}

syntax "_expression" :: "'a \<Rightarrow> 'a expression" ("Expr[_]")
parse_translation \<open>[("_expression", fn ctx => fn [e] => term_to_expression ctx e)]\<close>

syntax "_probability2" :: "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> real" ("Pr2[_:_'(_')]")
translations "_probability2 a b c" \<rightleftharpoons> "CONST probability2 (_expression a) b c"

syntax "_qrhl" :: "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> bool" ("QRHL {_} _ _ {_}")
translations "_qrhl a b c d" \<rightleftharpoons> "CONST qrhl (_expression a) b c (_expression d)"

syntax "_rhl" :: "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> bool" ("RHL {_} _ _ {_}")
translations "_rhl a b c d" \<rightleftharpoons> "_qrhl (classical_subspace a) b c (classical_subspace d)"

(* consts x_var :: "int qvariable" *)

(* local_setup {*
  fn lthy => QRHL.declare_variable lthy "x" @{typ bit} QRHL.Classical
*}

term x_var

ML {*
  QRHL.lookup_variable @{context} "x"
*} *)

term \<open> QRHL {Cla[x=1]} skip skip {Cla[x=1]} \<close>
term \<open> RHL {x=1} skip skip {x=1} \<close>


term \<open>Pr[x:p(rho)] <= Pr[x:p(rho)]\<close>

term \<open>
  Expr[x+1]
\<close>

term \<open>
  Pr2[x=1:p(rho)]
\<close>

term \<open>
Pr2[x=1:p(rho)] <= Pr2[x=1:p(rho)]
\<close>


end
