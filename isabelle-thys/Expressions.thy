theory Expressions
  imports Prog_Variables Misc_Missing Extended_Sorry Multi_Transfer
begin

typedef 'a expression = "{(vs,f::_\<Rightarrow>'a). finite vs \<and> (\<forall>m1 m2. (\<forall>v\<in>vs. Rep_mem2 m1 v = Rep_mem2 m2 v) \<longrightarrow> f m1 = f m2)}"
  apply (rule exI[of _ "({},(\<lambda>x. undefined))"]) by auto
setup_lifting type_definition_expression

lift_definition expression :: "'a::universe variables \<Rightarrow> ('a\<Rightarrow>'b) \<Rightarrow> 'b expression" is
  "\<lambda>(vs::'a variables) (f::'a\<Rightarrow>'b). (set (raw_variables vs), (f o eval_variables vs) :: mem2\<Rightarrow>'b)"
  using eval_variables_footprint by fastforce

lifting_forget mem2.lifting
lift_definition expression_eval :: "'b expression \<Rightarrow> mem2 \<Rightarrow> 'b" is "\<lambda>(vs,f) m. f m" .
setup_lifting type_definition_mem2

lemma expression_eval: "expression_eval (expression X e) m = e (eval_variables X m)"
  unfolding expression_eval.rep_eq expression.rep_eq by auto

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
  "\<lambda>F ez. if (\<forall>z. fst (ez z) = fst (ez undefined)) then (fst (ez undefined), (\<lambda>m. F (\<lambda>z. snd (ez z) m)))
          else Rep_expression undefined" 
  apply (rename_tac F ez)
proof -
  fix F :: "('z \<Rightarrow> 'e) \<Rightarrow> 'f" and ez :: "'z \<Rightarrow> variable_raw set \<times> (mem2 \<Rightarrow> 'e)"
  assume assm: "(\<And>x. ez x \<in> {(vs, f). finite vs \<and> (\<forall>m1 m2. (\<forall>v\<in>vs. Rep_mem2 m1 v = Rep_mem2 m2 v) \<longrightarrow> f m1 = f m2)})"
  show "(if \<forall>z. fst (ez z) = fst (ez undefined) then (fst (ez undefined), \<lambda>m. F (\<lambda>z. snd (ez z) m)) else Rep_expression undefined)
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

section \<open>Substitutions\<close>

typedecl substitution
axiomatization substitute1 :: "'a::universe variable \<Rightarrow> 'a expression \<Rightarrow> substitution"
(* TODO remove *)
consts subst_expression :: "substitution \<Rightarrow> 'b expression \<Rightarrow> 'b expression"

consts subst_expression' :: "substitution list \<Rightarrow> 'b expression \<Rightarrow> 'b expression"

 
lemma subst_expression'_unit_tac:
  shows "expression variable_unit E = subst_expression' s (expression variable_unit E)"
  sorry

lemma subst_expression'_singleton_same_tac:
  shows "expression R (\<lambda>r. E (F r)) = subst_expression' (substitute1 x (expression R F) # s) (expression \<lbrakk>x\<rbrakk> E)"
  sorry

lemma subst_expression'_singleton_empty_tac:
  shows "expression \<lbrakk>x\<rbrakk> E = subst_expression' [] (expression \<lbrakk>x\<rbrakk> E)"
  sorry

lemma subst_expression'_singleton_notsame_tac:
  assumes "variable_name x \<noteq> variable_name y"
  assumes "e = subst_expression' s (expression \<lbrakk>y\<rbrakk> E)"
  shows "e = subst_expression' (substitute1 x f # s) (expression \<lbrakk>y\<rbrakk> E)"
  sorry

lemma subst_expression'_concat_id_tac:
  assumes "expression Q1' e1 = subst_expression' s (expression Q1 (\<lambda>x. x))"
  assumes "expression Q2' e2 = subst_expression' s (expression Q2 (\<lambda>x. x))"
  shows "expression (variable_concat Q1' Q2') (\<lambda>(x1,x2). (e1 x1, e2 x2)) = subst_expression' s (expression (variable_concat Q1 Q2) (\<lambda>x. x))"
  sorry

lemma subst_expression'_id_comp_tac:
  assumes "expression Q' g = subst_expression' s (expression Q (\<lambda>x. x))"
  shows "expression Q' (\<lambda>x. E (g x)) = subst_expression' s (expression Q E)"
  sorry



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
  

ML_file "expressions.ML"

end
