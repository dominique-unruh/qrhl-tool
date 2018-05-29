theory Encoding
  imports QRHL_Core
begin

(* TODO: should rename "qvariables" to "variables" *)

type_synonym 'a cvariable = "'a qvariable"

typedecl 'a expression
axiomatization
  expression :: "'a qvariables \<Rightarrow> ('a\<Rightarrow>'b) \<Rightarrow> 'b expression"

abbreviation "const_expression z \<equiv> expression \<lbrakk>\<rbrakk> (\<lambda>_. z)"

axiomatization map_expression :: "(('z \<Rightarrow> 'e) \<Rightarrow> 'f) \<Rightarrow> ('z \<Rightarrow> 'e expression) \<Rightarrow> 'f expression" where 
  map_expression_def[simp]: "map_expression f (\<lambda>z. expression Q (e z)) = expression Q (\<lambda>a. f (\<lambda>z. e z a))"
for Q :: "'a qvariables" and e :: "'z \<Rightarrow> 'a \<Rightarrow> 'e" and f :: "('z \<Rightarrow> 'e) \<Rightarrow> 'f"

axiomatization pair_expression where
  pair_expression_def[simp]: "pair_expression (expression Q1 e1) (expression Q2 e2)
    = expression (qvariable_concat Q1 Q2) (\<lambda>(z1,z2). (e1 z1, e2 z2))"

definition map_expression2' :: "('e1 \<Rightarrow> ('z \<Rightarrow> 'e2) \<Rightarrow> 'f) \<Rightarrow> ('e1 expression) \<Rightarrow> ('z \<Rightarrow> 'e2 expression) \<Rightarrow> 'f expression" where
  "map_expression2' f e1 e2 = map_expression (\<lambda>x12. let x1 = fst (x12 undefined) in
                                                    let x2 = \<lambda>z. snd (x12 z) in
                                                    f x1 x2) (\<lambda>z. pair_expression e1 (e2 z))"

lemma map_expression2'[simp]:
  "map_expression2' f (expression Q1 e1) (\<lambda>z. expression Q2 (e2 z))
     = expression (qvariable_concat Q1 Q2) (\<lambda>(x1,x2). f (e1 x1) (\<lambda>z. e2 z x2))"
  unfolding map_expression2'_def pair_expression_def map_expression_def
  apply (tactic \<open>cong_tac @{context} 1\<close>) by auto


axiomatization index_var :: "bool \<Rightarrow> 'a qvariable \<Rightarrow> 'a qvariable" where
  index_var1[simp]: "variable_name (index_var True x) = variable_name x @ ''1''" and
  index_var2[simp]: "variable_name (index_var False x) = variable_name x @ ''2''"

axiomatization index_vars :: "bool \<Rightarrow> 'a qvariables \<Rightarrow> 'a qvariables"
axiomatization where
  index_vars_singleton[simp]: "index_vars left \<lbrakk>x\<rbrakk> = \<lbrakk>index_var left x\<rbrakk>" and
  index_vars_concat[simp]: "index_vars left (qvariable_concat Q R) = qvariable_concat (index_vars left Q) (index_vars left R)" and
  index_vars_unit[simp]: "index_vars left \<lbrakk>\<rbrakk> = \<lbrakk>\<rbrakk>"
for x :: "'a qvariable" and Q :: "'b qvariables" and R :: "'c qvariables"

axiomatization index_expression :: "bool \<Rightarrow> 'a expression \<Rightarrow> 'a expression" where
  index_expression_def[simp]: "index_expression left (expression Q e) = expression (index_vars left Q) e"
for Q :: "'b qvariables" and e :: "'b \<Rightarrow> 'a"

typedecl substitution
axiomatization substitute1 :: "'a qvariable \<Rightarrow> 'a expression \<Rightarrow> substitution"
axiomatization subst_expression :: "substitution \<Rightarrow> 'b expression \<Rightarrow> 'b expression"

typedecl program
axiomatization
  block :: "program list \<Rightarrow> program" and
  assign :: "'a cvariable \<Rightarrow> 'a expression \<Rightarrow> program" and
  sample :: "'a cvariable \<Rightarrow> 'a distr expression \<Rightarrow> program" and
  ifthenelse :: "bool expression \<Rightarrow> program list \<Rightarrow> program list \<Rightarrow> program" and
  while :: "bool expression \<Rightarrow> program list \<Rightarrow> program" and
  qinit :: "'a qvariables \<Rightarrow> 'a vector expression \<Rightarrow> program" and
  qapply :: "'a qvariables \<Rightarrow> ('a,'a) bounded expression \<Rightarrow> program" and
  measurement :: "'a cvariable \<Rightarrow> 'b qvariables \<Rightarrow> ('a,'b) measurement expression \<Rightarrow> program"


axiomatization fv_expression :: "'a expression \<Rightarrow> string set" where
  fv_expression_def: "fv_expression (expression v e) = set (qvariable_names v)" 
    for v :: "'a qvariables"

axiomatization fv_program :: "program \<Rightarrow> string set" where
  fv_program_sequence: "fv_program (block b) = (\<Union>s\<in>set b. fv_program s)"
and fv_program_assign: "fv_program (assign x e) = {variable_name x} \<union> fv_expression e"
and fv_program_sample: "fv_program (sample x e2) = {variable_name x} \<union> fv_expression e2"
and fv_program_ifthenelse: "fv_program (ifthenelse c p1 p2) =
  fv_expression c \<union> (\<Union>s\<in>set p1. fv_program s) \<union> (\<Union>s\<in>set p2. fv_program s)"
and fv_program_while: "fv_program (while c b) = fv_expression c \<union> (\<Union>s\<in>set b. fv_program s)"
and fv_program_qinit: "fv_program (qinit Q e3) = set (qvariable_names Q) \<union> fv_expression e3"
and fv_program_qapply: "fv_program (qapply Q e4) = set (qvariable_names Q) \<union> fv_expression e4"
and fv_program_measurement: "fv_program (measurement x R e5) = {variable_name x} \<union> set (qvariable_names R) \<union> fv_expression e5"

for b p1 p2 :: "program list" and x :: "'a qvariable" and e :: "'a expression"
and e2 :: "'a distr expression" and e3 :: "'a vector expression" and e4 :: "('a,'a) bounded expression"
and e5 :: "('a,'b) measurement expression" and Q :: "'a qvariables" and R :: "'b qvariables"

axiomatization qrhl :: "predicate expression \<Rightarrow> program list \<Rightarrow> program list \<Rightarrow> predicate expression \<Rightarrow> bool"

axiomatization probability2 :: "bool expression \<Rightarrow> program \<Rightarrow> program_state \<Rightarrow> real"

ML_file "encoding.ML"


(*
ML {*
val ctx = QRHL.declare_variable @{context} "x" @{typ int} QRHL.Classical
val e = Encoding.term_to_expression ctx (HOLogic.mk_eq (Free("x",dummyT),Free("y",dummyT)))
   |> Syntax.check_term ctx 
*}

ML {*
val e' = Encoding.add_index_to_expression e false
val t = Encoding.expression_to_term e' |> Thm.cterm_of ctx
*}
*)

syntax "_expression" :: "'a \<Rightarrow> 'a expression" ("Expr[_]")
parse_translation \<open>[("_expression", fn ctx => fn [e] => Encoding.term_to_expression_untyped ctx e)]\<close>

(* syntax "_predicate" :: "'a \<Rightarrow> predicate expression" ("Pred[_]")
parse_translation \<open>[("_predicate", fn ctx => fn [e] => 
  Encoding.term_to_predicate_expression_untyped ctx e)]\<close> *)

term "Pred[ Cla[True] ]"

syntax "_probability2" :: "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> real" ("Pr2[_:_'(_')]")
translations "_probability2 a b c" \<rightleftharpoons> "CONST probability2 (_expression a) b c"

syntax "_qrhl" :: "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> bool" ("QRHL {_} _ _ {_}")
translations "_qrhl a b c d" \<rightleftharpoons> "CONST qrhl (_expression a) b c (_expression d)"

syntax "_rhl" :: "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> bool" ("RHL {_} _ _ {_}")
translations "_rhl a b c d" \<rightleftharpoons> "_qrhl (classical_subspace a) b c (classical_subspace d)"


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
