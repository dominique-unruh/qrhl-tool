theory Encoding
  imports QRHL_Core Expressions
begin

type_synonym 'a cvariable = "'a variable"




typedecl program
typedecl oracle_program
axiomatization
  block :: "program list \<Rightarrow> program" and
  assign :: "'a::universe cvariable \<Rightarrow> 'a expression \<Rightarrow> program" and
  sample :: "'a cvariable \<Rightarrow> 'a distr expression \<Rightarrow> program" and
  ifthenelse :: "bool expression \<Rightarrow> program list \<Rightarrow> program list \<Rightarrow> program" and
  while :: "bool expression \<Rightarrow> program list \<Rightarrow> program" and
  qinit :: "'a variables \<Rightarrow> 'a vector expression \<Rightarrow> program" and
  qapply :: "'a variables \<Rightarrow> ('a,'a) bounded expression \<Rightarrow> program" and
  measurement :: "'a cvariable \<Rightarrow> 'b variables \<Rightarrow> ('a,'b) measurement expression \<Rightarrow> program" and
  instantiateOracles :: "oracle_program \<Rightarrow> program list \<Rightarrow> program"

axiomatization fv_program :: "program \<Rightarrow> string set" where
  fv_program_sequence: "fv_program (block b) = (\<Union>s\<in>set b. fv_program s)"
and fv_program_assign: "fv_program (assign x e) = {variable_name x} \<union> fv_expression e"
and fv_program_sample: "fv_program (sample x e2) = {variable_name x} \<union> fv_expression e2"
and fv_program_ifthenelse: "fv_program (ifthenelse c p1 p2) =
  fv_expression c \<union> (\<Union>s\<in>set p1. fv_program s) \<union> (\<Union>s\<in>set p2. fv_program s)"
and fv_program_while: "fv_program (while c b) = fv_expression c \<union> (\<Union>s\<in>set b. fv_program s)"
and fv_program_qinit: "fv_program (qinit Q e3) = set (variable_names Q) \<union> fv_expression e3"
and fv_program_qapply: "fv_program (qapply Q e4) = set (variable_names Q) \<union> fv_expression e4"
and fv_program_measurement: "fv_program (measurement x R e5) = {variable_name x} \<union> set (variable_names R) \<union> fv_expression e5"

for b p1 p2 :: "program list" and x :: "'a::universe variable" and e :: "'a expression"
and e2 :: "'a distr expression" and e3 :: "'a vector expression" and e4 :: "('a,'a) bounded expression"
and e5 :: "('a,'b::universe) measurement expression" and Q :: "'a variables" and R :: "'b variables"

axiomatization qrhl :: "predicate expression \<Rightarrow> program list \<Rightarrow> program list \<Rightarrow> predicate expression \<Rightarrow> bool"

typedecl program_state

(* TODO remove *)
axiomatization probability_old :: "string \<Rightarrow> program \<Rightarrow> program_state \<Rightarrow> real"
syntax "_probability_old" :: "ident \<Rightarrow> program \<Rightarrow> program_state \<Rightarrow> real" ("PrOld[_:(_'(_'))]")
parse_translation \<open>[("_probability_old", fn ctx => fn [Const(v,_),p,rho] =>
  \<^const>\<open>probability_old\<close> $ HOLogic.mk_string v $ p $ rho)]\<close>

(* Must come after loading qrhl.ML *)                                                                          
print_translation \<open>[(\<^const_syntax>\<open>probability_old\<close>, fn ctx => fn [str,p,rho] =>
  Const(\<^syntax_const>\<open>_probability_old\<close>,dummyT) $ Const(QRHL.dest_string_syntax str,dummyT) $ p $ rho)]\<close>

axiomatization probability :: "bool expression \<Rightarrow> program \<Rightarrow> program_state \<Rightarrow> real"


lemma subst_expression_unit_aux: \<comment> \<open>Helper for ML function subst_expression_conv\<close>
  "subst_expression (substitute1 x f) (expression \<lbrakk>\<rbrakk> e') \<equiv> (expression \<lbrakk>\<rbrakk> e')" sorry

lemma subst_expression_singleton_same_aux: \<comment> \<open>Helper for ML function subst_expression_conv\<close>
  "subst_expression (substitute1 x (expression R f')) (expression \<lbrakk>x\<rbrakk> e') \<equiv> (expression R (\<lambda>r. e' (f' r)))" sorry

lemma subst_expression_singleton_notsame_aux: \<comment> \<open>Helper for ML function subst_expression_conv\<close>
  assumes "variable_name x \<noteq> variable_name y"
  shows "subst_expression (substitute1 x f) (expression \<lbrakk>y\<rbrakk> e') \<equiv> expression \<lbrakk>y\<rbrakk> e'" sorry

lemma subst_expression_concat_id_aux: \<comment> \<open>Helper for ML function subst_expression_conv\<close>
  assumes "subst_expression (substitute1 x f) (expression Q1 (\<lambda>x. x)) \<equiv> expression Q1' e1"
  assumes "subst_expression (substitute1 x f) (expression Q2 (\<lambda>x. x)) \<equiv> expression Q2' e2"
  shows "subst_expression (substitute1 x f) (expression (variable_concat Q1 Q2) (\<lambda>x. x)) \<equiv>
    expression (variable_concat Q1' Q2') (\<lambda>(x1,x2). (e1 x1, e2 x2))"
  sorry

lemma subst_expression_id_comp_aux: \<comment> \<open>Helper for ML function subst_expression_conv\<close>
  assumes "subst_expression (substitute1 x f) (expression Q (\<lambda>x. x)) \<equiv> expression Q' g"
  shows "subst_expression (substitute1 x f) (expression Q e) \<equiv> expression Q' (\<lambda>x. e (g x))"
  sorry


ML_file "encoding.ML"

(* TODO move *)
hide_fact (open) expression_clean_assoc_aux
          expression_clean_singleton_aux
          expression_clean_cons_unit_aux
          expression_clean_unit_cons_aux
          expression_clean_var_cons_aux
          expression_id_comp_aux
          index_var_conv1_aux
          index_var_conv2_aux
          subst_expression_unit_aux
          subst_expression_singleton_same_aux
          subst_expression_singleton_notsame_aux
          subst_expression_concat_id_aux
          subst_expression_id_comp_aux

(* TODO move *)
simproc_setup index_var ("index_var lr v") = Prog_Variables.index_var_simproc

(* TODO move *)
simproc_setup clean_expression ("expression Q e") = Encoding.clean_expression_simproc


(* TODO move *)
consts "expression_syntax" :: "'a \<Rightarrow> 'a expression" ("Expr[_]")
parse_translation \<open>[(\<^const_syntax>\<open>expression_syntax\<close>, fn ctx => fn [e] => Expressions.term_to_expression_untyped ctx e)]\<close>
hide_const expression_syntax

term "Expr[x]"

consts "probability_syntax" :: "bool \<Rightarrow> program \<Rightarrow> program_state \<Rightarrow> real" ("Pr[_:(_'(_'))]")
translations "CONST probability_syntax a b c" \<rightleftharpoons> "CONST probability (Expr[a]) b c"
hide_const probability_syntax

consts "qrhl_syntax" :: "bool expression \<Rightarrow> program list \<Rightarrow> program list \<Rightarrow> bool expression \<Rightarrow> bool" ("QRHL {_} _ _ {_}")
translations "CONST qrhl_syntax a b c d" \<rightleftharpoons> "CONST qrhl (Expr[a]) b c (Expr[d])"
hide_const qrhl_syntax

consts "rhl_syntax" :: "bool \<Rightarrow> program list \<Rightarrow> program list \<Rightarrow> bool \<Rightarrow> bool" ("RHL {_} _ _ {_}")
translations "CONST rhl_syntax a b c d" \<rightleftharpoons> "QRHL {classical_subspace a} b c {classical_subspace d}"
hide_const rhl_syntax

term \<open> QRHL {Cla[x=1]} skip skip {Cla[x=1]} \<close>
term \<open> RHL {x=1} skip skip {x=1} \<close>

term \<open>PrOld[x:p(rho)] <= PrOld[x:p(rho)]\<close>

term \<open>
  Expr[x+1]
\<close>

term \<open>
  Pr[x=1:p(rho)]
\<close>

term \<open>
  Pr[x=1:p(rho)] <= Pr[x=1:p(rho)]
\<close>


end
