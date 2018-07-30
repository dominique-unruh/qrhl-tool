theory Encoding
  imports QRHL_Core
begin

type_synonym 'a cvariable = "'a variable"

typedecl 'a expression
axiomatization
  expression :: "'a variables \<Rightarrow> ('a\<Rightarrow>'b) \<Rightarrow> 'b expression"
and expression_eval :: "'b expression \<Rightarrow> mem2 \<Rightarrow> 'b"

text \<open>
Some notation, used mainly in the documentation of the ML code:
\<^item> A term of type \<^typ>\<open>'a variables\<close> is an \<^emph>\<open>explicit variable list\<close> if it is of the form
  \<^term>\<open>\<lbrakk>x\<^sub>1,x\<^sub>2,dots,x\<^sub>n\<rbrakk>\<close> where the \<^term>\<open>x\<^sub>i\<close> are free variables.

\<^item> A term of type \<^typ>\<open>'a variables\<close> is an \<^emph>\<open>explicit variable term\<close> if it is built from
  \<^const>\<open>variable_concat\<close>, \<^const>\<open>variable_unit\<close>, \<^const>\<open>variable_singleton\<close> and free variables.

\<^item> An expression is \<^emph>\<open>well-formed explicit\<close> iff it is of the form \<^term>\<open>expression \<lbrakk>x\<^sub>1,x\<^sub>2,dots,x\<^sub>n\<rbrakk> (\<lambda>(z\<^sub>1,z\<^sub>2,dots,z\<^sub>n). e (z\<^sub>1,z\<^sub>2,dots,z\<^sub>n))\<close>
  where the \<^term>\<open>x\<^sub>i\<close> are free variables.

\<^item> An expression is \<^emph>\<open>varlist explicit\<close> iff it is of the form \<^term>\<open>expression \<lbrakk>x\<^sub>1,x\<^sub>2,dots,x\<^sub>n\<rbrakk> e\<close>
  where the \<^term>\<open>x\<^sub>i\<close> are free variables.

\<^item> An expression is \<^emph>\<open>explicit\<close> iff it is of the form \<^term>\<open>expression Q e\<close> where \<^term>\<open>Q\<close> is an explicit variable term.
\<close>


abbreviation "const_expression z \<equiv> expression \<lbrakk>\<rbrakk> (\<lambda>_. z)"

axiomatization map_expression' :: "(('z \<Rightarrow> 'e) \<Rightarrow> 'f) \<Rightarrow> ('z \<Rightarrow> 'e expression) \<Rightarrow> 'f expression" where 
  map_expression'_def[simp]: "map_expression' f (\<lambda>z. expression Q (e z)) = expression Q (\<lambda>a. f (\<lambda>z. e z a))"
for Q :: "'a variables" and e :: "'z \<Rightarrow> 'a \<Rightarrow> 'e" and f :: "('z \<Rightarrow> 'e) \<Rightarrow> 'f"

axiomatization pair_expression where
  pair_expression_def[simp]: "pair_expression (expression Q1 e1) (expression Q2 e2)
    = expression (variable_concat Q1 Q2) (\<lambda>(z1,z2). (e1 z1, e2 z2))"
for Q1 :: "'q1 variables" and Q2 :: "'q2 variables" 
and e1 :: "'q1 \<Rightarrow> 'e1" and e2 :: "'q2 \<Rightarrow> 'e2"


definition map_expression :: "('e \<Rightarrow> 'f) \<Rightarrow> ('e expression) \<Rightarrow> 'f expression" where
  "map_expression f e = map_expression' (\<lambda>e. f (e ())) (\<lambda>_. e)"

lemma map_expression[simp]:
  "map_expression f (expression Q e) = expression Q (\<lambda>x. f (e x))"
  unfolding map_expression_def map_expression'_def
  apply (tactic \<open>cong_tac \<^context> 1\<close>) by auto

definition map_expression2' :: "('e1 \<Rightarrow> ('z \<Rightarrow> 'e2) \<Rightarrow> 'f) \<Rightarrow> ('e1 expression) \<Rightarrow> ('z \<Rightarrow> 'e2 expression) \<Rightarrow> 'f expression" where
  "map_expression2' f e1 e2 = map_expression' (\<lambda>x12. let x1 = fst (x12 undefined) in
                                                    let x2 = \<lambda>z. snd (x12 z) in
                                                    f x1 x2) (\<lambda>z. pair_expression e1 (e2 z))"

lemma map_expression2'[simp]:
  "map_expression2' f (expression Q1 e1) (\<lambda>z. expression Q2 (e2 z))
     = expression (variable_concat Q1 Q2) (\<lambda>(x1,x2). f (e1 x1) (\<lambda>z. e2 z x2))"
  unfolding map_expression2'_def pair_expression_def map_expression'_def
  apply (tactic \<open>cong_tac \<^context> 1\<close>) by auto

definition map_expression2 :: "('e1 \<Rightarrow> 'e2 \<Rightarrow> 'f) \<Rightarrow> 'e1 expression \<Rightarrow> 'e2 expression \<Rightarrow> 'f expression" where
  "map_expression2 f e1 e2 = map_expression (\<lambda>(x1,x2). f x1 x2) (pair_expression e1 e2)"

lemma map_expression2[simp]:
  "map_expression2 f (expression Q1 e1) (expression Q2 e2)
     = expression (variable_concat Q1 Q2) (\<lambda>(x1,x2). f (e1 x1) (e2 x2))"
  unfolding map_expression2_def pair_expression_def apply simp
  apply (tactic \<open>cong_tac \<^context> 1\<close>) by auto

definition map_expression3 :: "('e1 \<Rightarrow> 'e2 \<Rightarrow> 'e3 \<Rightarrow> 'f) \<Rightarrow> 'e1 expression \<Rightarrow> 'e2 expression \<Rightarrow> 'e3 expression \<Rightarrow> 'f expression" where
  "map_expression3 f e1 e2 e3 = map_expression (\<lambda>(x1,x2,x3). f x1 x2 x3)
    (pair_expression e1 (pair_expression e2 e3))"

lemma map_expression3[simp]:
  "map_expression3 f (expression Q1 e1) (expression Q2 e2) (expression Q3 e3)
     = expression (variable_concat Q1 (variable_concat Q2 Q3)) (\<lambda>(x1,x2,x3). f (e1 x1) (e2 x2) (e3 x3))"
  unfolding map_expression3_def pair_expression_def apply simp
  apply (tactic \<open>cong_tac \<^context> 1\<close>) by auto

axiomatization index_var :: "bool \<Rightarrow> 'a::value variable \<Rightarrow> 'a::value variable" where
  index_var1: "y = index_var True x \<longleftrightarrow> variable_name y = variable_name x @ ''1''" and
  index_var2: "y = index_var False x \<longleftrightarrow> variable_name y = variable_name x @ ''2''"

lemma index_var1I: "variable_name y = variable_name x @ ''1'' \<Longrightarrow> index_var True x = y"
  using index_var1 by metis
lemma index_var2I: "variable_name y = variable_name x @ ''2'' \<Longrightarrow> index_var False x = y"
  using index_var2 by metis

lemma index_var1_simp[simp]: "variable_name (index_var True x) = variable_name x @ ''1''" 
  using index_var1 by metis

lemma index_var2_simp[simp]: "variable_name (index_var False x) = variable_name x @ ''2''"
  using index_var2 by metis

axiomatization index_vars :: "bool \<Rightarrow> 'a variables \<Rightarrow> 'a variables"
axiomatization where
  index_vars_singleton[simp]: "index_vars left \<lbrakk>x\<rbrakk> = \<lbrakk>index_var left x\<rbrakk>" and
  index_vars_concat[simp]: "index_vars left (variable_concat Q R) = variable_concat (index_vars left Q) (index_vars left R)" and
  index_vars_unit[simp]: "index_vars left \<lbrakk>\<rbrakk> = \<lbrakk>\<rbrakk>"
for x :: "'a::value variable" and Q :: "'b::value variables" and R :: "'c::value variables"

axiomatization index_expression :: "bool \<Rightarrow> 'a expression \<Rightarrow> 'a expression" where
  index_expression_def[simp]: "index_expression left (expression Q e) = expression (index_vars left Q) e"
for Q :: "'b variables" and e :: "'b \<Rightarrow> 'a"

typedecl substitution
axiomatization substitute1 :: "'a variable \<Rightarrow> 'a expression \<Rightarrow> substitution"
axiomatization subst_expression :: "substitution \<Rightarrow> 'b expression \<Rightarrow> 'b expression"

typedecl program
axiomatization
  block :: "program list \<Rightarrow> program" and
  assign :: "'a cvariable \<Rightarrow> 'a expression \<Rightarrow> program" and
  sample :: "'a cvariable \<Rightarrow> 'a distr expression \<Rightarrow> program" and
  ifthenelse :: "bool expression \<Rightarrow> program list \<Rightarrow> program list \<Rightarrow> program" and
  while :: "bool expression \<Rightarrow> program list \<Rightarrow> program" and
  qinit :: "'a variables \<Rightarrow> 'a vector expression \<Rightarrow> program" and
  qapply :: "'a variables \<Rightarrow> ('a,'a) bounded expression \<Rightarrow> program" and
  measurement :: "'a cvariable \<Rightarrow> 'b variables \<Rightarrow> ('a,'b) measurement expression \<Rightarrow> program"


axiomatization fv_expression :: "'a expression \<Rightarrow> string set" where
  fv_expression_def: "fv_expression (expression v e) = set (variable_names v)"
    for v :: "'a variables"

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

for b p1 p2 :: "program list" and x :: "'a::value variable" and e :: "'a expression"
and e2 :: "'a distr expression" and e3 :: "'a vector expression" and e4 :: "('a,'a) bounded expression"
and e5 :: "('a,'b) measurement expression" and Q :: "'a variables" and R :: "'b variables"

axiomatization qrhl :: "predicate expression \<Rightarrow> program list \<Rightarrow> program list \<Rightarrow> predicate expression \<Rightarrow> bool"

typedecl program_state

axiomatization probability_old :: "string \<Rightarrow> program \<Rightarrow> program_state \<Rightarrow> real"
syntax "_probability_old" :: "ident \<Rightarrow> program \<Rightarrow> program_state \<Rightarrow> real" ("PrOld[_:(_'(_'))]")
parse_translation \<open>[("_probability_old", fn ctx => fn [Const(v,_),p,rho] =>
  \<^const>\<open>probability_old\<close> $ HOLogic.mk_string v $ p $ rho)]\<close>

(* Must come after loading qrhl.ML *)                                                                          
print_translation \<open>[(\<^const_syntax>\<open>probability_old\<close>, fn ctx => fn [str,p,rho] =>
  Const(\<^syntax_const>\<open>_probability_old\<close>,dummyT) $ Const(QRHL.dest_string_syntax str,dummyT) $ p $ rho)]\<close>

axiomatization probability :: "bool expression \<Rightarrow> program \<Rightarrow> program_state \<Rightarrow> real"

lemma expression_clean_assoc_aux: \<comment> \<open>Helper for ML function clean_expression_conv_varlist\<close>
  assumes "expression (variable_concat Q (variable_concat R S)) (\<lambda>(q,(r,s)). e ((q,r),s)) \<equiv> e'"
  shows "expression (variable_concat (variable_concat Q R) S) e \<equiv> e'"
  sorry

lemma expression_clean_singleton_aux: \<comment> \<open>Helper for ML function clean_expression_conv_varlist\<close>
  shows "expression \<lbrakk>x\<rbrakk> e \<equiv> expression \<lbrakk>x\<rbrakk> e"
  sorry

lemma expression_clean_cons_unit_aux: \<comment> \<open>Helper for ML function clean_expression_conv_varlist\<close>
  assumes "expression Q (\<lambda>q. e (q,())) \<equiv> expression Q' e'"
  shows "expression (variable_concat Q variable_unit) e \<equiv> expression Q' e'"
  sorry

lemma expression_clean_unit_cons_aux: \<comment> \<open>Helper for ML function clean_expression_conv_varlist\<close>
  assumes "expression Q (\<lambda>q. e ((),q)) \<equiv> expression Q' e'"
  shows "expression (variable_concat variable_unit Q) e \<equiv> expression Q' e'"
  sorry

lemma expression_clean_var_cons_aux: \<comment> \<open>Helper for ML function clean_expression_conv_varlist\<close>
  assumes "expression Q (\<lambda>x. x) \<equiv> expression Q' e'"
  shows "expression (variable_concat \<lbrakk>x\<rbrakk> Q) (\<lambda>x. x) \<equiv> expression (variable_concat \<lbrakk>x\<rbrakk> Q') (\<lambda>(x,q). (x, e' q))"
  sorry

lemma expression_clean_unit_aux: \<comment> \<open>Helper for ML function clean_expression_conv_varlist\<close>
  shows "expression \<lbrakk>\<rbrakk> e \<equiv> expression \<lbrakk>\<rbrakk> (\<lambda>_. e ())"
  by simp

lemma expression_id_comp_aux: \<comment> \<open>Helper for ML function clean_expression_conv_varlist\<close>
  assumes "expression Q (\<lambda>x. x) \<equiv> expression Q' g"
  shows "expression Q e \<equiv> expression Q' (\<lambda>x. e (g x))"
  sorry

lemma index_var_conv1_aux: \<comment> \<open>Helper for ML function index_var_conv\<close>
  assumes "variable_name v \<equiv> vname"
  assumes "variable_name v1 \<equiv> v1name"
  assumes "vname @ ''1'' \<equiv> v1name"
  shows "index_var True v \<equiv> v1"
  using assms index_var1I by smt

lemma index_var_conv2_aux: \<comment> \<open>Helper for ML function index_var_conv\<close>
  assumes "variable_name v \<equiv> vname"
  assumes "variable_name v2 \<equiv> v2name"
  assumes "vname @ ''2'' \<equiv> v2name"
  shows "index_var False v \<equiv> v2"
  using assms index_var2I by smt

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

hide_fact expression_clean_assoc_aux
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

simproc_setup index_var ("index_var lr v") = Encoding.index_var_simproc

simproc_setup clean_expression ("expression Q e") = Encoding.clean_expression_simproc


consts "expression_syntax" :: "'a \<Rightarrow> 'a expression" ("Expr[_]")
parse_translation \<open>[(\<^const_syntax>\<open>expression_syntax\<close>, fn ctx => fn [e] => Encoding.term_to_expression_untyped ctx e)]\<close>
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
