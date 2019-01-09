theory Expressions
  imports Prog_Variables Misc_Missing Extended_Sorry Multi_Transfer
begin

typedef 'a expression = "{(vs,f::_\<Rightarrow>'a). finite vs \<and> (\<forall>m1 m2. (\<forall>v\<in>vs. Rep_mem2 m1 v = Rep_mem2 m2 v) \<longrightarrow> f m1 = f m2)}"
  apply (rule exI[of _ "({},(\<lambda>x. undefined))"]) by auto
setup_lifting type_definition_expression

lift_definition rel_expression :: "(variable_raw \<Rightarrow> variable_raw \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a expression \<Rightarrow> 'b expression \<Rightarrow> bool"
  is "\<lambda>(rel_v::variable_raw \<Rightarrow> variable_raw \<Rightarrow> bool) (rel_result::'a \<Rightarrow> 'b \<Rightarrow> bool). 
      (rel_prod (rel_set rel_v) (rel_fun (rel_mem2 rel_v) rel_result)
        :: variable_raw set * (mem2 => 'a) => variable_raw set * (_ => 'b) => bool)".

lemma rel_expression_eq: "rel_expression (=) (=) = (=)"
  unfolding rel_expression.rep_eq rel_set_eq rel_mem2_eq rel_fun_eq prod.rel_eq Rep_expression_inject by rule

lift_definition expression :: "'a::universe variables \<Rightarrow> ('a\<Rightarrow>'b) \<Rightarrow> 'b expression" is
  "\<lambda>(vs::'a variables) (f::'a\<Rightarrow>'b). (set (raw_variables vs), (f o eval_variables vs) :: mem2\<Rightarrow>'b)"
  using eval_variables_footprint by fastforce

lifting_forget mem2.lifting
lift_definition expression_eval :: "'b expression \<Rightarrow> mem2 \<Rightarrow> 'b" is "\<lambda>(vs,f) m. f m" .
setup_lifting type_definition_mem2

lemma expression_eval: "expression_eval (expression X e) m = e (eval_variables X m)"
  unfolding expression_eval.rep_eq expression.rep_eq by auto

lift_definition expression_vars :: "'a expression \<Rightarrow> variable_raw set" is "\<lambda>(vs::variable_raw set,f). vs" .
lemma expression_vars[simp]: "expression_vars (expression X e) = set (raw_variables X)"
  by (simp add: expression.rep_eq expression_vars.rep_eq)

lemma Rep_expression_components: "Rep_expression e = (expression_vars e, expression_eval e)"
  apply transfer by auto

lemma expression_eqI: "expression_vars e = expression_vars e' \<Longrightarrow> expression_eval e = expression_eval e' \<Longrightarrow> e = e'"
  apply transfer by auto

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

lift_definition fv_expression :: "'a expression \<Rightarrow> string set" is "\<lambda>(vs,f). variable_raw_name ` vs" .
lemma fv_expression: "fv_expression (expression v e) = set (variable_names v)"
  apply transfer unfolding variable_names_def by auto

section \<open>Constructing expressions\<close>

abbreviation "const_expression z \<equiv> expression \<lbrakk>\<rbrakk> (\<lambda>_. z)"

lift_definition map_expression' :: "(('z \<Rightarrow> 'e) \<Rightarrow> 'f) \<Rightarrow> ('z \<Rightarrow> 'e expression) \<Rightarrow> 'f expression" is
  "\<lambda>F ez. if (\<forall>z. fst (ez z) = fst (ez undefined)) 
          then (fst (ez undefined), (\<lambda>m. F (\<lambda>z. snd (ez z) m)))
          else Rep_expression (const_expression undefined)" 
  apply (rename_tac F ez)
proof -
  fix F :: "('z \<Rightarrow> 'e) \<Rightarrow> 'f" and ez :: "'z \<Rightarrow> variable_raw set \<times> (mem2 \<Rightarrow> 'e)"
  assume assm: "(\<And>x. ez x \<in> {(vs, f). finite vs \<and> (\<forall>m1 m2. (\<forall>v\<in>vs. Rep_mem2 m1 v = Rep_mem2 m2 v) \<longrightarrow> f m1 = f m2)})"
  show "(if \<forall>z. fst (ez z) = fst (ez undefined) then (fst (ez undefined), \<lambda>m. F (\<lambda>z. snd (ez z) m)) else Rep_expression (const_expression undefined))
       \<in> {(vs, f). finite vs \<and> (\<forall>m1 m2. (\<forall>v\<in>vs. Rep_mem2 m1 v = Rep_mem2 m2 v) \<longrightarrow> f m1 = f m2)}"
  proof (cases "\<forall>z. fst (ez z) = fst (ez undefined)")
    case True
    then show ?thesis using assm apply (auto simp: split_beta) by metis
  next
    case False
    then show ?thesis using Rep_expression by metis
  qed
qed

lemma map_expression'[simp]: "map_expression' f (\<lambda>z. expression Q (e z)) = expression Q (\<lambda>a. f (\<lambda>z. e z a))"
  apply transfer by auto

lift_definition pair_expression :: "'a expression \<Rightarrow> 'b expression \<Rightarrow> ('a \<times> 'b) expression" is
  "\<lambda>(vs1,e1) (vs2,e2). (vs1 \<union> vs2, \<lambda>m. (e1 m, e2 m))"
  by auto


lemma pair_expression[simp]: "pair_expression (expression Q1 e1) (expression Q2 e2)
    = expression (variable_concat Q1 Q2) (\<lambda>(z1,z2). (e1 z1, e2 z2))"
  apply (subst Rep_expression_inject[symmetric])
  unfolding pair_expression.rep_eq expression.rep_eq
  by auto 

definition map_expression :: "('e \<Rightarrow> 'f) \<Rightarrow> ('e expression) \<Rightarrow> 'f expression" where
  "map_expression f e = map_expression' (\<lambda>e. f (e ())) (\<lambda>_. e)"

lemma map_expression[simp]:
  "map_expression f (expression Q e) = expression Q (\<lambda>x. f (e x))"             
  unfolding map_expression_def map_expression'
  apply (tactic \<open>cong_tac \<^context> 1\<close>) by auto

definition map_expression2' :: "('e1 \<Rightarrow> ('z \<Rightarrow> 'e2) \<Rightarrow> 'f) \<Rightarrow> ('e1 expression) \<Rightarrow> ('z \<Rightarrow> 'e2 expression) \<Rightarrow> 'f expression" where
  "map_expression2' f e1 e2 = map_expression' (\<lambda>x12. let x1 = fst (x12 undefined) in
                                                    let x2 = \<lambda>z. snd (x12 z) in
                                                    f x1 x2) (\<lambda>z. pair_expression e1 (e2 z))"

lemma map_expression2'[simp]:
  "map_expression2' f (expression Q1 e1) (\<lambda>z. expression Q2 (e2 z))
     = expression (variable_concat Q1 Q2) (\<lambda>(x1,x2). f (e1 x1) (\<lambda>z. e2 z x2))"
  unfolding map_expression2'_def pair_expression map_expression'
  apply (tactic \<open>cong_tac \<^context> 1\<close>) by auto

definition map_expression2 :: "('e1 \<Rightarrow> 'e2 \<Rightarrow> 'f) \<Rightarrow> 'e1 expression \<Rightarrow> 'e2 expression \<Rightarrow> 'f expression" where
  "map_expression2 f e1 e2 = map_expression (\<lambda>(x1,x2). f x1 x2) (pair_expression e1 e2)"

lemma map_expression2[simp]:
  "map_expression2 f (expression Q1 e1) (expression Q2 e2)
     = expression (variable_concat Q1 Q2) (\<lambda>(x1,x2). f (e1 x1) (e2 x2))"
  unfolding map_expression2_def pair_expression apply simp
  apply (tactic \<open>cong_tac \<^context> 1\<close>) by auto

definition map_expression3 :: "('e1 \<Rightarrow> 'e2 \<Rightarrow> 'e3 \<Rightarrow> 'f) \<Rightarrow> 'e1 expression \<Rightarrow> 'e2 expression \<Rightarrow> 'e3 expression \<Rightarrow> 'f expression" where
  "map_expression3 f e1 e2 e3 = map_expression (\<lambda>(x1,x2,x3). f x1 x2 x3)
    (pair_expression e1 (pair_expression e2 e3))"

lemma map_expression3[simp]:
  "map_expression3 f (expression Q1 e1) (expression Q2 e2) (expression Q3 e3)
     = expression (variable_concat Q1 (variable_concat Q2 Q3)) (\<lambda>(x1,x2,x3). f (e1 x1) (e2 x2) (e3 x3))"
  unfolding map_expression3_def pair_expression apply simp
  apply (tactic \<open>cong_tac \<^context> 1\<close>) by auto

definition map_expression3' ::
 "('e1 \<Rightarrow> 'e2 \<Rightarrow> ('z \<Rightarrow> 'e3) \<Rightarrow> 'f) \<Rightarrow> ('e1 expression) \<Rightarrow> ('e2 expression) \<Rightarrow> ('z \<Rightarrow> 'e3 expression) \<Rightarrow> 'f expression" where
  "map_expression3' f e1 e2 e3 = map_expression'
           (\<lambda>x123. let x1 = fst (x123 undefined) in
              let x2 = fst (snd (x123 undefined)) in
              let x3 = \<lambda>z. snd (snd (x123 z)) in
              f x1 x2 x3)
         (\<lambda>z. (pair_expression e1 (pair_expression e2 (e3 z))))"

lemma map_expression3'[simp]:
  "map_expression3' f (expression Q1 e1) (expression Q2 e2) (\<lambda>z. expression Q3 (e3 z))
     = expression (variable_concat Q1 (variable_concat Q2 Q3)) (\<lambda>(x1,x2,x3). f (e1 x1) (e2 x2) (\<lambda>z. e3 z x3))"
  unfolding map_expression3'_def pair_expression map_expression'
  apply (tactic \<open>cong_tac \<^context> 1\<close>) by auto

lemma range_cases[case_names 1]: "x : range f \<Longrightarrow> (\<And>y. P (f y)) \<Longrightarrow> P x"
  unfolding image_def by auto 

lift_definition index_expression :: "bool \<Rightarrow> 'a expression \<Rightarrow> 'a expression" is
  "\<lambda>left (vs,e). (index_var_raw left ` vs, \<lambda>m. e (unindex_mem2 left m))"
  by auto

lemma index_expression[simp]: "index_expression left (expression Q e) = expression (index_vars left Q) e"
  for Q :: "'b::universe variables" and e :: "'b \<Rightarrow> 'a"
  using [[transfer_del_const index_vars]]
  apply transfer by auto

lift_definition index_flip_expression :: "'a expression \<Rightarrow> 'a expression" is
  "\<lambda>(vs,e). (index_flip_var_raw ` vs, \<lambda>m. e (index_flip_mem2 m))"
  by auto

lemma index_flip_expression[simp]: "index_flip_expression (expression Q e) = expression (index_flip_vars Q) e"
  for Q :: "'b::universe variables" and e :: "'b \<Rightarrow> 'a"
  using [[transfer_del_const index_flip_vars]]
  apply transfer by auto

lemma index_flip_expression_vars[simp]: "expression_vars (index_flip_expression e) = index_flip_var_raw ` expression_vars e"
  by (simp add: expression_vars.rep_eq index_flip_expression.rep_eq split_beta)

lemma index_flip_expression_twice[simp]: "index_flip_expression (index_flip_expression e) = e"
  apply transfer by (auto simp: image_iff)

section \<open>Substitutions\<close>

(* TODO move *)
lemma variable_raw_domain_Rep_variable[simp]: "variable_raw_domain (Rep_variable (v::'a::universe variable)) = range (embedding::'a\<Rightarrow>_)"
  apply transfer by simp

typedef substitution1 = "{(v::variable_raw, vs, e::mem2\<Rightarrow>universe). 
  finite vs \<and>
  (\<forall>m. e m \<in> variable_raw_domain v) \<and>
  (\<forall>m1 m2. (\<forall>w\<in>vs. Rep_mem2 m1 w = Rep_mem2 m2 w) \<longrightarrow> e m1 = e m2)}"
  by (rule exI[of _ "(Rep_variable (undefined::unit variable), {}, \<lambda>_. embedding ())"], auto)
setup_lifting type_definition_substitution1

lift_definition substitute1 :: "'a::universe variable \<Rightarrow> 'a expression \<Rightarrow> substitution1" is
  "\<lambda>(v::variable_raw) (vs,e). (v, vs, \<lambda>m. embedding (e m))" 
  by auto 

lift_definition substitution1_footprint :: "substitution1 \<Rightarrow> variable_raw set" is "\<lambda>(_,vs::variable_raw set,_). vs" .
lift_definition substitution1_variable :: "substitution1 \<Rightarrow> variable_raw" is "\<lambda>(v::variable_raw,_,_). v" .
lift_definition substitution1_function :: "substitution1 \<Rightarrow> mem2 \<Rightarrow> universe" is "\<lambda>(_,_,f::mem2\<Rightarrow>universe). f" .

lemma Rep_substitution1_components: "Rep_substitution1 s = (substitution1_variable s, substitution1_footprint s, substitution1_function s)"
  apply transfer by auto

lemma substitution1_function_domain: "substitution1_function s m \<in> variable_raw_domain (substitution1_variable s)"
  apply transfer by auto

lemma substitute1_variable[simp]: "substitution1_variable (substitute1 x e) = Rep_variable x"
  apply transfer by auto
lemma substitute1_function: "substitution1_function (substitute1 x e) m = embedding (expression_eval e m)"
  apply transfer by auto

lift_definition index_flip_substitute1 :: "substitution1 \<Rightarrow> substitution1" 
  is "\<lambda>(v,vs,f). (index_flip_var_raw v, index_flip_var_raw ` vs, f o index_flip_mem2)"
  by auto

lemma index_flip_substitute1: "index_flip_substitute1 (substitute1 x e) = 
  substitute1 (index_flip_var x) (index_flip_expression e)"
  apply transfer by auto

(* definition rel_substitute1 :: "(variable_raw\<Rightarrow>variable_raw\<Rightarrow>bool) \<Rightarrow> ('a expression\<Rightarrow>'a expression\<Rightarrow>bool) \<Rightarrow> (substitution1\<Rightarrow>substitution1\<Rightarrow>bool)" where
  "rel_substitute1 rel_v rel_e s1 s2 = 
    (rel_v (substitution1_variable s1) (substitution1_variable s2)
   \<and> rel_e (inv embedding o substitution1_function s1) (substitution1_function s2))"
 *)


lift_definition rel_substitute1 :: "(variable_raw\<Rightarrow>variable_raw\<Rightarrow>bool) \<Rightarrow> ('a::universe expression\<Rightarrow>'b::universe expression\<Rightarrow>bool) \<Rightarrow> (substitution1\<Rightarrow>substitution1\<Rightarrow>bool)" is
  "\<lambda>(rel_v::variable_raw\<Rightarrow>variable_raw\<Rightarrow>bool) 
    (rel_exp :: (variable_raw set * (mem2 \<Rightarrow> 'a)) \<Rightarrow> (variable_raw set * (mem2 \<Rightarrow> 'b)) \<Rightarrow> bool). 
    rel_prod rel_v (%(vs1,f1) (vs2,f2). range f1 \<subseteq> range (embedding::'a\<Rightarrow>_) \<and> range f2 \<subseteq> range (embedding::'b\<Rightarrow>_) \<and>
                                        rel_exp (vs1, inv embedding o f1 :: mem2 \<Rightarrow> 'a) 
                                                (vs2, inv embedding o f2 :: mem2 \<Rightarrow> 'b))"
proof (rename_tac rel_v rel_exp1 rel_exp2 prod1 prod2)
  fix rel_v and rel_exp1 rel_exp2 :: "variable_raw set \<times> (mem2 \<Rightarrow> 'a)
   \<Rightarrow> variable_raw set \<times> (mem2 \<Rightarrow> 'b) \<Rightarrow> bool" and prod1 prod2 :: "variable_raw \<times> variable_raw set \<times> (mem2 \<Rightarrow> universe)"
  obtain v1 vs1 f1 where prod1: "prod1 = (v1,vs1,f1)" apply atomize_elim by (meson prod_cases3)
  obtain v2 vs2 f2 where prod2: "prod2 = (v2,vs2,f2)" apply atomize_elim by (meson prod_cases3)
  assume eq: "vsf1 \<in> {(vs, f). finite vs \<and> (\<forall>m1 m2. (\<forall>v\<in>vs. Rep_mem2 m1 v = Rep_mem2 m2 v) \<longrightarrow> f m1 = f m2)} \<Longrightarrow>
              vsf2 \<in> {(vs, f). finite vs \<and> (\<forall>m1 m2. (\<forall>v\<in>vs. Rep_mem2 m1 v = Rep_mem2 m2 v) \<longrightarrow> f m1 = f m2)} \<Longrightarrow>
              rel_exp1 vsf1 vsf2 = rel_exp2 vsf1 vsf2" for vsf1 vsf2
  assume p1: "prod1 \<in> {(v, vs, e).
           finite vs \<and> (\<forall>m. e m \<in> variable_raw_domain v) \<and> (\<forall>m1 m2. (\<forall>w\<in>vs. Rep_mem2 m1 w = Rep_mem2 m2 w) \<longrightarrow> e m1 = e m2)} "
  assume p2: "prod2 \<in> {(v, vs, e).
           finite vs \<and> (\<forall>m. e m \<in> variable_raw_domain v) \<and> (\<forall>m1 m2. (\<forall>w\<in>vs. Rep_mem2 m1 w = Rep_mem2 m2 w) \<longrightarrow> e m1 = e m2)}"
  have "rel_exp1 (vs1, inv embedding \<circ> f1) (vs2, inv embedding \<circ> f2) \<longleftrightarrow>
        rel_exp2 (vs1, inv embedding \<circ> f1) (vs2, inv embedding \<circ> f2)"
    apply (rule eq)
    using p1 p2 unfolding prod1 prod2 apply auto by presburger+
  then
  show "rel_prod rel_v (\<lambda>(vs1, f1) (vs2, f2). range f1 \<subseteq> range (embedding::'a\<Rightarrow>_) \<and> range f2 \<subseteq> range (embedding::'b\<Rightarrow>_) \<and> rel_exp1 (vs1, inv embedding \<circ> f1) (vs2, inv embedding \<circ> f2)) prod1 prod2 =
        rel_prod rel_v (\<lambda>(vs1, f1) (vs2, f2). range f1 \<subseteq> range (embedding::'a\<Rightarrow>_) \<and> range f2 \<subseteq> range (embedding::'b\<Rightarrow>_) \<and> rel_exp2 (vs1, inv embedding \<circ> f1) (vs2, inv embedding \<circ> f2)) prod1 prod2"
    by (simp add: case_prod_beta prod1 prod2)
qed

(* TODO remove *)
lift_definition rel_substitute1' :: "(variable_raw\<Rightarrow>variable_raw\<Rightarrow>bool) \<Rightarrow> ('a::universe expression\<Rightarrow>'b::universe expression\<Rightarrow>bool) \<Rightarrow> (substitution1\<Rightarrow>substitution1\<Rightarrow>bool)" is
  "\<lambda>(rel_v::variable_raw\<Rightarrow>variable_raw\<Rightarrow>bool) 
    (rel_exp :: (variable_raw set * (mem2 \<Rightarrow> 'a)) \<Rightarrow> (variable_raw set * (mem2 \<Rightarrow> 'b)) \<Rightarrow> bool). 
    rel_prod rel_v (%(vs1,f1) (vs2,f2). rel_exp (vs1, inv embedding o f1 :: mem2 \<Rightarrow> 'a) 
                                                (vs2, inv embedding o f2 :: mem2 \<Rightarrow> 'b))"
proof (rename_tac rel_v rel_exp1 rel_exp2 prod1 prod2)
  fix rel_v and rel_exp1 rel_exp2 :: "variable_raw set \<times> (mem2 \<Rightarrow> 'a)
   \<Rightarrow> variable_raw set \<times> (mem2 \<Rightarrow> 'b) \<Rightarrow> bool" and prod1 prod2 :: "variable_raw \<times> variable_raw set \<times> (mem2 \<Rightarrow> universe)"
  obtain v1 vs1 f1 where prod1: "prod1 = (v1,vs1,f1)" apply atomize_elim by (meson prod_cases3)
  obtain v2 vs2 f2 where prod2: "prod2 = (v2,vs2,f2)" apply atomize_elim by (meson prod_cases3)
  assume eq: "vsf1 \<in> {(vs, f). finite vs \<and> (\<forall>m1 m2. (\<forall>v\<in>vs. Rep_mem2 m1 v = Rep_mem2 m2 v) \<longrightarrow> f m1 = f m2)} \<Longrightarrow>
              vsf2 \<in> {(vs, f). finite vs \<and> (\<forall>m1 m2. (\<forall>v\<in>vs. Rep_mem2 m1 v = Rep_mem2 m2 v) \<longrightarrow> f m1 = f m2)} \<Longrightarrow>
              rel_exp1 vsf1 vsf2 = rel_exp2 vsf1 vsf2" for vsf1 vsf2
  assume p1: "prod1 \<in> {(v, vs, e).
           finite vs \<and> (\<forall>m. e m \<in> variable_raw_domain v) \<and> (\<forall>m1 m2. (\<forall>w\<in>vs. Rep_mem2 m1 w = Rep_mem2 m2 w) \<longrightarrow> e m1 = e m2)} "
  assume p2: "prod2 \<in> {(v, vs, e).
           finite vs \<and> (\<forall>m. e m \<in> variable_raw_domain v) \<and> (\<forall>m1 m2. (\<forall>w\<in>vs. Rep_mem2 m1 w = Rep_mem2 m2 w) \<longrightarrow> e m1 = e m2)}"
  have "rel_exp1 (vs1, inv embedding \<circ> f1) (vs2, inv embedding \<circ> f2) \<longleftrightarrow>
        rel_exp2 (vs1, inv embedding \<circ> f1) (vs2, inv embedding \<circ> f2)"
    apply (rule eq)
    using p1 p2 unfolding prod1 prod2 apply auto by presburger+
  then
  show "rel_prod rel_v (\<lambda>(vs1, f1) (vs2, f2). rel_exp1 (vs1, inv embedding \<circ> f1) (vs2, inv embedding \<circ> f2)) prod1 prod2 =
        rel_prod rel_v (\<lambda>(vs1, f1) (vs2, f2). rel_exp2 (vs1, inv embedding \<circ> f1) (vs2, inv embedding \<circ> f2)) prod1 prod2"
    by (simp add: case_prod_beta prod1 prod2)
qed

lemma rel_substitute1_expression_eq: "rel_substitute1 R (rel_expression S T) s1 s2 = 
        (R (substitution1_variable s1) (substitution1_variable s2) \<and>
        rel_set S (substitution1_footprint s1) (substitution1_footprint s2) \<and>
        range (substitution1_function s1) \<subseteq> range EMBEDDING('a) \<and> 
        range (substitution1_function s2) \<subseteq> range EMBEDDING('b) \<and> 
        rel_fun (rel_mem2 S) T (inv EMBEDDING('a) \<circ> substitution1_function s1)
                               (inv EMBEDDING('b) \<circ> substitution1_function s2))"
  apply transfer by force




lift_definition subst_mem2 :: "substitution1 list \<Rightarrow> mem2 \<Rightarrow> mem2" is
  "\<lambda>(\<sigma>::substitution1 list) (m::mem2) (v::variable_raw). 
    case find (\<lambda>s. substitution1_variable s=v) \<sigma> of None \<Rightarrow> Rep_mem2 m v | Some s \<Rightarrow> substitution1_function s m"
proof (rename_tac \<sigma> m v)
  fix \<sigma> m v
  show "(case find (\<lambda>s. substitution1_variable s = v) \<sigma> of None \<Rightarrow> Rep_mem2 m v | Some s \<Rightarrow> substitution1_function s m) \<in> variable_raw_domain v" 
  proof (cases "find (\<lambda>s. substitution1_variable s = v) \<sigma> = None")
    case True
    then show ?thesis using Rep_mem2 by auto
  next
    case False
    then obtain s where find: "find (\<lambda>s. substitution1_variable s = v) \<sigma> = Some s" by auto
    have "s \<in> set \<sigma>" and "substitution1_variable s = v"
      using find apply (subst (asm) find_Some_iff) using nth_mem apply force
      using find apply (subst (asm) find_Some_iff) using nth_mem by force
    then have "substitution1_function s m \<in> variable_raw_domain v"
      using substitution1_function_domain by metis
    with find show ?thesis by auto
  qed
qed


(* lemma
  includes lifting_syntax
  fixes R
  defines "subR == rel_substitute1 R (rel_expression R (=))"
  shows "(subR ===> rel_prod R (rel_prod (rel_set R) (rel_mem2 R ===> (=)))) Rep_substitution1 Rep_substitution1"
  apply (rule rel_funI)
  apply (simp add: subR_def rel_substitute1_expression_eq[abs_def] rel_fun_def Rep_substitution1_components rel_prod_conv)
  by (meson inv_into_injective rangeI set_rev_mp)
 *)

(* lemma rel_substitute1_Rep_substitution1:
  includes lifting_syntax
  fixes R S
  defines "subR == rel_substitute1 R (rel_expression R S)"
  defines "S' == BNF_Greatest_Fixpoint.image2p embedding embedding S"
  shows "(subR ===> rel_prod R (rel_prod (rel_set R) (rel_mem2 R ===> S'))) Rep_substitution1 Rep_substitution1"
  apply (rule rel_funI)
  apply (simp add: S'_def subR_def rel_substitute1_expression_eq[abs_def] rel_fun_def Rep_substitution1_components rel_prod_conv BNF_Greatest_Fixpoint.image2p_def)
  apply auto
  by (meson contra_subsetD f_inv_into_f rangeI) *)

lemma rel_substitute1_Rep_substitution1:
  includes lifting_syntax
  fixes R S S'
  defines "subR == rel_substitute1 R (rel_expression R S)"
  assumes "\<And>x y. S x y \<longleftrightarrow> S' (embedding x) (embedding y)"
  shows "(subR ===> rel_prod R (rel_prod (rel_set R) (rel_mem2 R ===> S'))) Rep_substitution1 Rep_substitution1"
  apply (rule rel_funI)
  apply (simp add: subR_def rel_substitute1_expression_eq[abs_def] rel_fun_def Rep_substitution1_components rel_prod_conv BNF_Greatest_Fixpoint.image2p_def)
  using assms by (auto simp: f_inv_into_f image_subset_iff) 

lemma rel_substitute1_substitution1_variable: 
  includes lifting_syntax
  fixes R S
  defines "subR == rel_substitute1 R (rel_expression R S)"
  shows "(subR ===> R) substitution1_variable substitution1_variable"
proof -
  define S' where S': "S' == BNF_Greatest_Fixpoint.image2p embedding embedding S"
  have [unfolded subR_def, transfer_rule]: "(subR ===> rel_prod R (rel_prod (rel_set R) (rel_mem2 R ===> S'))) Rep_substitution1 Rep_substitution1"
    unfolding subR_def apply (rule rel_substitute1_Rep_substitution1) by (simp add: S' image2p_def)
  show ?thesis
    unfolding subR_def substitution1_variable_def map_fun_def
    by transfer_prover
qed


lemma rel_substitute1_substitution1_footprint:
  includes lifting_syntax
  fixes R
  defines "subR == rel_substitute1 R (rel_expression R (=))"
  shows "(subR ===> rel_set R) substitution1_footprint substitution1_footprint"
proof -
  have [unfolded subR_def, transfer_rule]: "(subR ===> rel_prod R (rel_prod (rel_set R) (rel_mem2 R ===> (=)))) Rep_substitution1 Rep_substitution1"
    unfolding subR_def apply (rule rel_substitute1_Rep_substitution1) by simp
  show ?thesis
    unfolding subR_def substitution1_footprint_def map_fun_def
    by transfer_prover
qed

lemma subst_mem2_empty[simp]: "subst_mem2 [] = id"
  apply (rule ext) apply (subst Rep_mem2_inject[symmetric]) 
  by (simp add: subst_mem2.rep_eq)

(* 
definition subst_expression :: "substitution list \<Rightarrow> 'b expression \<Rightarrow> 'b expression" where
  "subst_expression \<sigma> e =  *)


lemma finite_substitution1_footprint[simp]: "finite (substitution1_footprint \<sigma>)"
  apply transfer by auto

(* TODO move *)
lemma find_map: "find p (map f l) = map_option f (find (\<lambda>x. p (f x)) l)"
  by (induction l, auto)

definition "subst_expression_footprint (\<sigma>::substitution1 list) (vs::variable_raw set) =
  (Union {substitution1_footprint s | s v. 
      Some s = find (\<lambda>s. substitution1_variable s = v) \<sigma> \<and> substitution1_variable s \<in> vs})
    \<union> (vs - substitution1_variable ` set \<sigma>)"

lemma finite_subst_expression_footprint: "finite vs \<Longrightarrow> finite (subst_expression_footprint \<sigma> vs)"
proof -
  assume "finite vs"
  have "subst_expression_footprint \<sigma> vs 
      \<subseteq> (Union {substitution1_footprint s | s. s\<in>set \<sigma> \<and> substitution1_variable s \<in> vs})
        \<union> (vs - substitution1_variable ` set \<sigma>)"
    unfolding subst_expression_footprint_def apply auto
    by (metis (full_types) find_Some_iff nth_mem)+
  moreover 
  from \<open>finite vs\<close> have "finite \<dots>" by auto
  ultimately show ?thesis
    by (meson finite_subset)
qed

lemma subst_expression_footprint_union:
  "subst_expression_footprint \<sigma> (X \<union> Y) = subst_expression_footprint \<sigma> X \<union> subst_expression_footprint \<sigma> Y"
  unfolding subst_expression_footprint_def by blast

lemma subst_mem2_footprint:
  fixes \<sigma> vs
  assumes meq: "\<And>v. v\<in>subst_expression_footprint \<sigma> vs \<Longrightarrow> Rep_mem2 m1 v = Rep_mem2 m2 v"
  assumes "v \<in> vs"
  shows "Rep_mem2 (subst_mem2 \<sigma> m1) v = Rep_mem2 (subst_mem2 \<sigma> m2) v"
proof (cases "find (\<lambda>s. substitution1_variable s=v) \<sigma>")
  case None
  then have unmod: "Rep_mem2 (subst_mem2 \<sigma> m) v = Rep_mem2 m v" for m
    unfolding subst_mem2.rep_eq by simp
  from None have "v \<notin> substitution1_variable ` set \<sigma>"
    apply transfer by (auto simp: find_None_iff)
  with \<open>v \<in> vs\<close> have "v \<in> subst_expression_footprint \<sigma> vs"
    unfolding subst_expression_footprint_def by simp 
  with unmod and meq show ?thesis by metis
next
  case (Some s)
  then have s_v: "substitution1_variable s = v"
    by (metis (mono_tags, lifting) find_Some_iff)
  from Some have Rep_sf: "Rep_mem2 (subst_mem2 \<sigma> m) v = substitution1_function s m" for m
    unfolding subst_mem2.rep_eq by auto 
  have sf_eq: "(\<forall>w\<in>substitution1_footprint s. Rep_mem2 m1 w = Rep_mem2 m2 w) \<Longrightarrow> substitution1_function s m1 = substitution1_function s m2"
    apply transfer by auto
  from Some \<open>v\<in>vs\<close> s_v have "Some s = find (\<lambda>s. substitution1_variable s = v) \<sigma> \<and> substitution1_variable s \<in> vs"
    by auto
  then have "substitution1_footprint s \<subseteq> subst_expression_footprint \<sigma> vs"
    unfolding subst_expression_footprint_def by auto
  with sf_eq meq have "substitution1_function s m1 = substitution1_function s m2" by auto
  with sf_eq show ?thesis
    by (simp add: Rep_sf)
qed

lift_definition subst_expression :: "substitution1 list \<Rightarrow> 'b expression \<Rightarrow> 'b expression" is
  "\<lambda>(\<sigma>::substitution1 list) (vs,e).
       (subst_expression_footprint \<sigma> vs,
        e o subst_mem2 \<sigma>)"
proof (auto simp: finite_subst_expression_footprint)
  fix \<sigma> and vs :: "variable_raw set" and e :: "mem2\<Rightarrow>'b" and m1 m2
  assume "finite vs"
  assume "\<forall>m1 m2. (\<forall>v\<in>vs. Rep_mem2 m1 v = Rep_mem2 m2 v) \<longrightarrow> e m1 = e m2"
  then have e_footprint: "e m1 = e m2" if "\<forall>v\<in>vs. Rep_mem2 m1 v = Rep_mem2 m2 v" for m1 m2 using that by simp
  assume meq: "\<forall>v\<in>subst_expression_footprint \<sigma> vs.
          Rep_mem2 m1 v = Rep_mem2 m2 v"
  then have "Rep_mem2 (subst_mem2 \<sigma> m1) v = Rep_mem2 (subst_mem2 \<sigma> m2) v" if "v \<in> vs" for v
      using meq subst_mem2_footprint that by metis 
  then show "e (subst_mem2 \<sigma> m1) = e (subst_mem2 \<sigma> m2)" 
    by (rule_tac e_footprint, simp)
qed

lemma subst_expression_footprint: "expression_vars (subst_expression \<sigma> e) = subst_expression_footprint \<sigma> (expression_vars e)"
  apply transfer by auto
lemma subst_expression_eval: "expression_eval (subst_expression \<sigma> e) = expression_eval e o subst_mem2 \<sigma>"
  apply (rule ext) unfolding o_def expression_eval.rep_eq subst_expression.rep_eq case_prod_beta by simp

lemma subst_expression_unit_tac:
  shows "expression variable_unit E = subst_expression s (expression variable_unit E)"
  apply (subst Rep_expression_inject[symmetric])
  unfolding expression.rep_eq subst_expression.rep_eq subst_expression_footprint_def
  by auto

lemma subst_expression_singleton_same_tac:
  fixes x :: "'x::universe variable"
  shows "expression R (\<lambda>r. E (F r)) = subst_expression (substitute1 x (expression R F) # s) (expression \<lbrakk>x\<rbrakk> E)"
proof (subst Rep_expression_inject[symmetric], simp add: expression.rep_eq subst_expression.rep_eq, rule conjI)
  define x' where "x' = Rep_variable x"
  have aux: "((\<exists>v. (x' = v \<longrightarrow> sa = substitute1 x (expression R F)) \<and>
          (x' \<noteq> v \<longrightarrow> Some sa = find (\<lambda>s. substitution1_variable s = v) s)) \<and>
           substitution1_variable sa = x')
      =
         (sa = substitute1 x (expression R F) \<and> substitution1_variable sa = x')" for sa
    apply auto by (metis (mono_tags) find_Some_iff)
  have "subst_expression_footprint (substitute1 x (expression R F) # s) {x'} = substitution1_footprint (substitute1 x (expression R F))"
    unfolding subst_expression_footprint_def by (simp add: x'_def[symmetric] aux)
  also have "\<dots> = set (raw_variables R)"
    by (simp add: substitution1_footprint.rep_eq substitute1.rep_eq case_prod_beta expression.rep_eq)
  finally
  show "set (raw_variables R) = subst_expression_footprint (substitute1 x (expression R F) # s) {x'}" by simp
next
  have eval_x: "(embedding::'x\<Rightarrow>_) (eval_variables \<lbrakk>x\<rbrakk> m) = (Rep_mem2 m (Rep_variable x))" for m
    apply (simp add: variable_singleton.rep_eq eval_variables.rep_eq)
    apply (rule f_inv_into_f)
    by (metis (no_types, lifting) Rep_mem2 mem_Collect_eq variable_raw_domain_Rep_variable)
  have "F (eval_variables R m) = eval_variables \<lbrakk>x\<rbrakk> (subst_mem2 (substitute1 x (expression R F) # s) m)" for m
    apply (subst embedding_inv[symmetric])
    apply (simp add: eval_x subst_mem2.rep_eq substitute1_function)
    apply transfer by auto
  then
  show "(\<lambda>r. E (F r)) \<circ> eval_variables R = E \<circ> eval_variables \<lbrakk>x\<rbrakk> \<circ> subst_mem2 (substitute1 x (expression R F) # s)"
    by auto
qed

lemma subst_expression_singleton_empty_tac:
  shows "expression \<lbrakk>x\<rbrakk> E = subst_expression [] (expression \<lbrakk>x\<rbrakk> E)"
  apply (subst Rep_expression_inject[symmetric])
  unfolding expression.rep_eq subst_expression.rep_eq subst_expression_footprint_def
  by simp

lemma subst_expression_singleton_notsame_tac:
  fixes x :: "'x::universe variable" and y :: "'y::universe variable"
  assumes neq: "variable_name x \<noteq> variable_name y"
  assumes e_def: "e = subst_expression \<sigma> (expression \<lbrakk>y\<rbrakk> E)"
  shows "e = subst_expression (substitute1 x f # \<sigma>) (expression \<lbrakk>y\<rbrakk> E)"
proof (unfold e_def, subst Rep_expression_inject[symmetric], simp add: expression.rep_eq subst_expression.rep_eq, rule conjI)
  define x' y' where "x' = Rep_variable x" and "y' = Rep_variable y"
  from neq have [simp]: "x' \<noteq> y'"
    by (metis variable_name.rep_eq x'_def y'_def)
  then have aux1: "Some s = find (\<lambda>s. substitution1_variable s = v) (substitute1 x f # \<sigma>) \<and> substitution1_variable s \<in> {y'}
          \<longleftrightarrow> Some s = find (\<lambda>s. substitution1_variable s = v) \<sigma> \<and> substitution1_variable s \<in> {y'}"
    for v s
    by (metis (mono_tags) find.simps(2) find_Some_iff singletonD substitute1_variable x'_def)
  from \<open>x' \<noteq> y'\<close> 
  have aux2: "{y'} - substitution1_variable ` set (substitute1 x f # \<sigma>)
            = {y'} - substitution1_variable ` set (\<sigma>)"
    using x'_def by auto
  show "subst_expression_footprint \<sigma> {y'} = subst_expression_footprint (substitute1 x f # \<sigma>) {y'}"
    unfolding subst_expression_footprint_def aux1 aux2 by simp

  have eval_y: "(embedding::'y\<Rightarrow>_) (eval_variables \<lbrakk>y\<rbrakk> m) = (Rep_mem2 m (Rep_variable y))" for m
    apply (simp add: variable_singleton.rep_eq eval_variables.rep_eq)
    apply (rule f_inv_into_f)
    by (metis (no_types, lifting) Rep_mem2 mem_Collect_eq variable_raw_domain_Rep_variable)
  have "eval_variables \<lbrakk>y\<rbrakk> (subst_mem2 \<sigma> m) = eval_variables \<lbrakk>y\<rbrakk> (subst_mem2 (substitute1 x f # \<sigma>) m)" for m
    apply (subst embedding_inv[symmetric])
    by (simp add: eval_y subst_mem2.rep_eq substitute1_function del: embedding_inv flip: x'_def y'_def)
  then show "E \<circ> eval_variables \<lbrakk>y\<rbrakk> \<circ> subst_mem2 \<sigma> = E \<circ> eval_variables \<lbrakk>y\<rbrakk> \<circ> subst_mem2 (substitute1 x f # \<sigma>)"
    by auto
qed

lemma subst_expression_concat_id_tac:
  assumes "expression Q1' e1 = subst_expression s (expression Q1 (\<lambda>x. x))"
  assumes "expression Q2' e2 = subst_expression s (expression Q2 (\<lambda>x. x))"
  shows "expression (variable_concat Q1' Q2') (\<lambda>(x1,x2). (e1 x1, e2 x2)) = subst_expression s (expression (variable_concat Q1 Q2) (\<lambda>x. x))"
proof (subst Rep_expression_inject[symmetric], simp add: expression.rep_eq subst_expression.rep_eq, rule conjI)
  show "set (raw_variables Q1') \<union> set (raw_variables Q2') =
        subst_expression_footprint s (set (raw_variables Q1) \<union> set (raw_variables Q2))"
    apply (subst subst_expression_footprint_union)
    using assms by (metis expression_vars subst_expression_footprint)
next
  have 1: "e1 (eval_variables Q1' m) = eval_variables Q1 (subst_mem2 s m)" for m
    using assms(1)[THEN arg_cong[where f=expression_eval]]
    unfolding subst_expression_eval o_def expression_eval
    by metis
  have 2: "e2 (eval_variables Q2' m) = eval_variables Q2 (subst_mem2 s m)" for m
    using assms(2)[THEN arg_cong[where f=expression_eval]]
    unfolding subst_expression_eval o_def expression_eval
    by metis
  from 1 2
  show "(\<lambda>(x1, x2). (e1 x1, e2 x2)) \<circ> eval_variables (variable_concat Q1' Q2') =
    (\<lambda>x. x) \<circ> eval_variables (variable_concat Q1 Q2) \<circ> subst_mem2 s"
    by auto
qed

lemma subst_expression_id_comp_tac:
  assumes "expression Q' g = subst_expression s (expression Q (\<lambda>x. x))"
  shows "expression Q' (\<lambda>x. E (g x)) = subst_expression s (expression Q E)"
proof (subst Rep_expression_inject[symmetric], simp add: expression.rep_eq subst_expression.rep_eq, rule conjI)
  have "set (raw_variables Q') = expression_vars (expression Q' g)"
    by simp
  also have "\<dots> = expression_vars (subst_expression s (expression Q (\<lambda>x. x)))"
    using assms by simp
  also have "\<dots> = subst_expression_footprint s (expression_vars (expression Q (\<lambda>x. x)))"
    unfolding subst_expression_footprint by rule
  also have "\<dots> = subst_expression_footprint s (set (raw_variables Q))"
    by simp
  finally
  show "set (raw_variables Q') = subst_expression_footprint s (set (raw_variables Q))"
    by assumption


  from assms have "expression_eval (expression Q' g) m = expression_eval (subst_expression s (expression Q (\<lambda>x. x))) m" for m
    by simp
  then have "g (eval_variables Q' m) = expression_eval (subst_expression s (expression Q (\<lambda>x. x))) m" for m
    by (simp add: expression_eval)
  also have "\<dots> m = eval_variables Q (subst_mem2 s m)" for m
    unfolding expression_eval.rep_eq subst_expression.rep_eq case_prod_beta expression.rep_eq
    by simp
  finally have "g (eval_variables Q' m) = eval_variables Q (subst_mem2 s m)" for m
    by assumption
  then show "(\<lambda>x. E (g x)) \<circ> eval_variables Q' = E \<circ> eval_variables Q \<circ> subst_mem2 s"
    by auto
qed



section \<open>ML code\<close>

lemma expression_clean_assoc_aux: \<comment> \<open>Helper for ML function clean_expression_conv_varlist\<close>
  assumes "expression (variable_concat Q (variable_concat R S)) (\<lambda>(q,(r,s)). e ((q,r),s)) \<equiv> e'"
  shows "expression (variable_concat (variable_concat Q R) S) e \<equiv> e'"
  unfolding assms[symmetric]
  apply (rule eq_reflection)
  apply (subst Rep_expression_inject[symmetric])
  apply (simp add: expression.rep_eq)
  apply (rule ext)
  by simp

lemma expression_clean_singleton_aux: \<comment> \<open>Helper for ML function clean_expression_conv_varlist\<close>
  shows "expression \<lbrakk>x\<rbrakk> e \<equiv> expression \<lbrakk>x\<rbrakk> e"
  by simp


lemma expression_clean_cons_unit_aux: \<comment> \<open>Helper for ML function clean_expression_conv_varlist\<close>
  assumes "expression Q (\<lambda>q. e (q,())) \<equiv> expression Q' e'"
  shows "expression (variable_concat Q variable_unit) e \<equiv> expression Q' e'"
  unfolding assms[symmetric]
  apply (rule eq_reflection)
  apply (subst Rep_expression_inject[symmetric])
  apply (simp add: expression.rep_eq)
  apply (rule ext)
  by simp

lemma expression_clean_unit_cons_aux: \<comment> \<open>Helper for ML function clean_expression_conv_varlist\<close>
  assumes "expression Q (\<lambda>q. e ((),q)) \<equiv> expression Q' e'"
  shows "expression (variable_concat variable_unit Q) e \<equiv> expression Q' e'"
  unfolding assms[symmetric]
  apply (rule eq_reflection)
  apply (subst Rep_expression_inject[symmetric])
  apply (simp add: expression.rep_eq)
  apply (rule ext)
  by simp

lemma expression_vars_inject: "expression Q e = expression Q' e' \<Longrightarrow> set (raw_variables Q) = set (raw_variables Q')"
  by (metis expression.rep_eq prod.sel(1))

lemma expression_clean_var_cons_aux: \<comment> \<open>Helper for ML function clean_expression_conv_varlist\<close>
  assumes "expression Q (\<lambda>x. x) \<equiv> expression Q' e'"
  shows "expression (variable_concat \<lbrakk>x\<rbrakk> Q) (\<lambda>x. x) \<equiv> expression (variable_concat \<lbrakk>x\<rbrakk> Q') (\<lambda>(x,q). (x, e' q))"
  apply (rule eq_reflection)
  apply (subst Rep_expression_inject[symmetric])
  apply (simp add: expression.rep_eq)
  using expression_vars_inject[OF assms[THEN meta_eq_to_obj_eq]] apply auto
  apply (rule ext)
  apply auto
  by (metis assms comp_apply expression.rep_eq prod.inject)

lemma expression_clean_unit_aux: \<comment> \<open>Helper for ML function clean_expression_conv_varlist\<close>
  shows "expression \<lbrakk>\<rbrakk> e \<equiv> expression \<lbrakk>\<rbrakk> (\<lambda>_. e ())"
  by simp

lemma expression_id_comp_aux: \<comment> \<open>Helper for ML function clean_expression_conv_varlist\<close>
  assumes "expression Q (\<lambda>x. x) \<equiv> expression Q' g"
  shows "expression Q e \<equiv> expression Q' (\<lambda>x. e (g x))"
  apply (rule eq_reflection)
  using assms[THEN meta_eq_to_obj_eq] apply transfer
  by (auto simp add: o_def)
  
section "Orderings on expressions"

instantiation expression :: (ord) ord begin
definition "less_eq_expression e f \<longleftrightarrow> expression_eval e \<le> expression_eval f"
definition "less_expression e f \<longleftrightarrow> expression_eval e \<le> expression_eval f \<and> \<not> (expression_eval f \<le> expression_eval e)"
instance by intro_classes                   
end

instantiation expression :: (preorder) preorder begin
instance apply intro_classes
  unfolding less_expression_def less_eq_expression_def 
  using order_trans by auto
end


ML_file "expressions.ML"

simproc_setup clean_expression ("expression Q e") = Expressions.clean_expression_simproc

consts "expression_syntax" :: "'a \<Rightarrow> 'a expression" ("Expr[_]")
parse_translation \<open>[(\<^const_syntax>\<open>expression_syntax\<close>, fn ctx => fn [e] => Expressions.term_to_expression_untyped ctx e)]\<close>
hide_const expression_syntax

end
