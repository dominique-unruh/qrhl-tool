theory Expressions
  imports Prog_Variables Misc_Missing Extended_Sorry Multi_Transfer
begin

(* TODO: are expressions actually necessary?

   Why can't we just use terms of the form (\<lambda>m. ... (eval_variable x m))?

   (We won't have the guarantee that the set of variables used by an expression
   is finite, or even well-defined, but do we ever use those facts?)
*)

typedef 'a expression = "{(vs,f::_\<Rightarrow>'a). finite vs \<and> (\<forall>m1 m2. (\<forall>v\<in>vs. Rep_mem2 m1 v = Rep_mem2 m2 v) \<longrightarrow> f m1 = f m2)}"
  apply (rule exI[of _ "({},(\<lambda>x. undefined))"]) by auto
setup_lifting type_definition_expression

lift_definition rel_expression :: "(variable_raw \<Rightarrow> variable_raw \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a expression \<Rightarrow> 'b expression \<Rightarrow> bool"
  is "\<lambda>(rel_v::variable_raw \<Rightarrow> variable_raw \<Rightarrow> bool) (rel_result::'a \<Rightarrow> 'b \<Rightarrow> bool). 
      (rel_prod (rel_set rel_v) (rel_fun (rel_mem2 rel_v) rel_result)
        :: variable_raw set * (mem2 => 'a) => variable_raw set * (_ => 'b) => bool)".

lemma rel_expression_eq: "rel_expression (=) (=) = (=)"
  unfolding rel_expression.rep_eq rel_set_eq rel_mem2_eq rel_fun_eq prod.rel_eq Rep_expression_inject by rule

lemma left_unique_rel_expression[transfer_rule]:
  assumes "left_unique R" and "left_unique S" and "right_total R" and "type_preserving_var_rel R"
  shows "left_unique (rel_expression R S)"
proof -
  have "e = f" if "rel_expression R S e g" and "rel_expression R S f g" for e f g
  proof -
    obtain vse E where e: "Rep_expression e = (vse,E)" by (atomize_elim, auto)
    obtain vsf F where f: "Rep_expression f = (vsf,F)" by (atomize_elim, auto)
    obtain vsg G where g: "Rep_expression g = (vsg,G)" by (atomize_elim, auto)
    from that have "rel_prod (rel_set R) (rel_fun (rel_mem2 R) S) (vse,E) (vsg,G)"
      unfolding rel_expression.rep_eq e g by simp
    then have vseg: "rel_set R vse vsg" and EG: "(rel_fun (rel_mem2 R) S) E G" by auto

    from that have "rel_prod (rel_set R) (rel_fun (rel_mem2 R) S) (vsf,F) (vsg,G)"
      unfolding rel_expression.rep_eq f g by simp
    then have vsfg: "rel_set R vsf vsg" and FG: "(rel_fun (rel_mem2 R) S) F G" by auto

    from vseg vsfg have "vse = vsf"
      using \<open>left_unique R\<close>
      by (meson left_uniqueD left_unique_rel_set) 

    have left_unique_fun: "left_unique (rel_fun (rel_mem2 R) S)"
      apply (rule left_unique_fun)
       apply (rule left_total_rel_mem2)
      using assms by auto
    from EG FG have "E = F"
      using left_unique_fun
      by (meson left_uniqueD)

    from \<open>vse = vsf\<close> \<open>E = F\<close>
    show "e = f"
      using Rep_expression_inject e f by fastforce
    qed
  then show ?thesis
    unfolding left_unique_def by simp
qed

lemma rel_expression_flip[simp]: "(rel_expression R S)^--1 = rel_expression R^--1 S^--1"
  apply (rule ext)+ unfolding conversep_iff apply transfer
  using rel_mem2_flip[unfolded conversep_iff]
  apply (auto simp: rel_fun_def rel_set_def)
  by (metis (full_types))+

lemma right_unique_rel_expression[transfer_rule]:
  assumes "right_unique R" and "right_unique S" and "left_total R" and "type_preserving_var_rel R"
  shows "right_unique (rel_expression R S)"
  apply (subst conversep_conversep[of R, symmetric])
  apply (subst conversep_conversep[of S, symmetric])
  apply (subst rel_expression_flip[symmetric])
  apply (simp del: rel_expression_flip)
  apply (rule left_unique_rel_expression)
  using assms by auto

lemma bi_unique_rel_expression[transfer_rule]:
  assumes "bi_unique R" and "bi_unique S" and "bi_total R" and "type_preserving_var_rel R"
  shows "bi_unique (rel_expression R S)"
  using assms by (meson bi_total_alt_def bi_unique_alt_def left_unique_rel_expression right_unique_rel_expression)


lift_definition expression :: "'a::universe variables \<Rightarrow> ('a\<Rightarrow>'b) \<Rightarrow> 'b expression" is
  "\<lambda>(vs::'a variables) (f::'a\<Rightarrow>'b). (set (raw_variables vs), (f o eval_variables vs) :: mem2\<Rightarrow>'b)"
  using eval_variables_footprint by fastforce

(* lifting_forget mem2.lifting *)
lift_definition expression_eval :: "'b expression \<Rightarrow> mem2 \<Rightarrow> 'b" is "\<lambda>(vs::variable_raw set,f::mem2\<Rightarrow>'b) m. f m" .
(* setup_lifting type_definition_mem2 *)

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

abbreviation (input) "const_expression z \<equiv> expression \<lbrakk>\<rbrakk> (\<lambda>_. z)"

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


definition map_expression3'' ::
 "('e1 \<Rightarrow> ('z \<Rightarrow> 'e2) \<Rightarrow> ('z \<Rightarrow> 'e3) \<Rightarrow> 'f) \<Rightarrow> ('e1 expression) \<Rightarrow> ('z \<Rightarrow> 'e2 expression) \<Rightarrow> ('z \<Rightarrow> 'e3 expression) \<Rightarrow> 'f expression" where
  "map_expression3'' f e1 e2 e3 = map_expression'
           (\<lambda>x123. let x1 = fst (x123 undefined) in
              let x2 = \<lambda>z. fst (snd (x123 z)) in
              let x3 = \<lambda>z. snd (snd (x123 z)) in
              f x1 x2 x3)
         (\<lambda>z. (pair_expression e1 (pair_expression (e2 z) (e3 z))))"

lemma map_expression3''[simp]:
  "map_expression3'' f (expression Q1 e1) (\<lambda>z. expression Q2 (e2 z)) (\<lambda>z. expression Q3 (e3 z))
     = expression (variable_concat Q1 (variable_concat Q2 Q3)) (\<lambda>(x1,x2,x3). f (e1 x1) (\<lambda>z. e2 z x2) (\<lambda>z. e3 z x3))"
  unfolding map_expression3''_def pair_expression map_expression'
  apply (tactic \<open>cong_tac \<^context> 1\<close>) by auto

definition map_expression4' ::
 "('e1 \<Rightarrow> 'e2 \<Rightarrow> 'e3 \<Rightarrow> ('z \<Rightarrow> 'e4) \<Rightarrow> 'f) \<Rightarrow> ('e1 expression) \<Rightarrow> ('e2 expression) \<Rightarrow> ('e3 expression) \<Rightarrow> ('z \<Rightarrow> 'e4 expression) \<Rightarrow> 'f expression" where
  "map_expression4' f e1 e2 e3 e4 = map_expression'
           (\<lambda>x1234. let x1 = fst (x1234 undefined) in
              let x2 = fst (snd (x1234 undefined)) in
              let x3 = fst (snd (snd (x1234 undefined))) in
              let x4 = \<lambda>z. snd (snd (snd (x1234 z))) in
              f x1 x2 x3 x4)
         (\<lambda>z. (pair_expression e1 (pair_expression e2 (pair_expression e3 (e4 z)))))"

lemma map_expression4'[simp]:
  "map_expression4' f (expression Q1 e1) (expression Q2 e2) (expression Q3 e3) (\<lambda>z. expression Q4 (e4 z))
     = expression (variable_concat Q1 (variable_concat Q2 (variable_concat Q3 Q4))) (\<lambda>(x1,x2,x3,x4). f (e1 x1) (e2 x2) (e3 x3) (\<lambda>z. e4 z x4))"
  unfolding map_expression4'_def pair_expression map_expression'
  apply (tactic \<open>cong_tac \<^context> 1\<close>) by auto

lemma expression_eval_map_expression':
  assumes "\<And>z. expression_vars (e z) = expression_vars (e undefined)"
  shows "expression_eval (map_expression' f e) x = f (\<lambda>z. expression_eval (e z) x)"
  using assms
  apply (transfer fixing: f x)
  by (simp add: case_prod_beta)

lemma expression_eval_map_expression[simp]:
  shows "expression_eval (map_expression f e) x = f (expression_eval e x)"
  unfolding map_expression_def
  by (rule expression_eval_map_expression', simp)

lemma expression_eval_pair_expression[simp]:
  shows "expression_eval (pair_expression e g) x = (expression_eval e x, expression_eval g x)"
  apply (transfer fixing: x)
  by (simp add: case_prod_beta)


lemma expression_eval_map_expression2[simp]:
  shows "expression_eval (map_expression2 f e g) x = f (expression_eval e x) (expression_eval g x)"
  unfolding map_expression2_def
  apply (subst expression_eval_map_expression)
  apply (subst expression_eval_pair_expression)
  by simp

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


lemma index_flip_expression_index_expression:
  "index_flip_expression (index_expression left x) = index_expression (\<not>left) x"
  apply transfer apply auto
  using image_iff by fastforce

(* lemma expression_vars_index_flip_expression: "expression_vars (index_flip_expression e) = index_flip_var_raw ` expression_vars e"
  by (simp add: expression_vars.rep_eq index_flip_expression.rep_eq split_beta) *)

lemma expression_eval_index_flip_expression: "expression_eval (index_flip_expression e) = 
  expression_eval e o index_flip_mem2"
  unfolding o_def
  by (simp add: expression_eval.rep_eq index_flip_expression.rep_eq split_beta)

lemma index_flip_expression_pair_expression: "index_flip_expression (pair_expression e1 e2)
  = pair_expression (index_flip_expression e1) (index_flip_expression e2)"
  apply transfer by auto

lemma index_flip_expression_map_expression': "index_flip_expression (map_expression' f ez)
  = map_expression' f (index_flip_expression o ez)"
proof (cases "\<forall>z. expression_vars (ez z) = expression_vars (ez undefined)")
  case True
  then have True': "expression_vars (index_flip_expression (ez z)) = expression_vars (index_flip_expression (ez undefined))" for z
    apply transfer
    apply simp
    by (metis (mono_tags, lifting) fst_conv split_beta)

  from True have "expression_vars (map_expression' f ez) = expression_vars (ez undefined)"
    apply transfer by (simp add: fst_def)
  hence "expression_vars (index_flip_expression (map_expression' f ez)) 
       = index_flip_var_raw ` expression_vars (ez undefined)"
    unfolding index_flip_expression_vars by simp
  moreover from True' have "expression_vars (map_expression' f (index_flip_expression o ez)) 
      = expression_vars (index_flip_expression (ez undefined))"
    unfolding o_def apply transfer by (auto simp: fst_def)
  moreover have "expression_vars (index_flip_expression (ez undefined))
      = index_flip_var_raw ` expression_vars (ez undefined)"
    unfolding index_flip_expression_vars by simp
  ultimately have vars: "expression_vars (index_flip_expression (map_expression' f ez))
                 = expression_vars (map_expression' f (index_flip_expression o ez))"
    by simp

  from True have "expression_eval (map_expression' f ez) = (\<lambda>m. f (\<lambda>z. expression_eval (ez z) m))"
    apply transfer by (auto simp: fst_def snd_def)
  hence "expression_eval (index_flip_expression (map_expression' f ez)) 
       = (\<lambda>m. f (\<lambda>z. expression_eval (ez z) (index_flip_mem2 m)))"
    unfolding expression_eval_index_flip_expression by (simp add: o_def)
  moreover from True' have "expression_eval (map_expression' f (index_flip_expression o ez)) 
      = (\<lambda>m. f (\<lambda>z. expression_eval (index_flip_expression (ez z)) m))"
    unfolding o_def apply transfer by (auto simp: fst_def snd_def)
  moreover have "expression_eval (ez z) (index_flip_mem2 m) = expression_eval (index_flip_expression (ez z)) m" for m z
    apply transfer by (simp add: split_beta)
  ultimately have eval: "expression_eval (index_flip_expression (map_expression' f ez))
                 = expression_eval (map_expression' f (index_flip_expression o ez))"
    by simp
  
  from vars eval show ?thesis
    by (rule expression_eqI)
next
  case False
  then have False': "\<not> (\<forall>z. expression_vars (index_flip_expression (ez z)) = expression_vars (index_flip_expression (ez undefined)))"
    apply transfer
    apply (simp add: case_prod_beta)
    using index_flip_var_raw_inject by blast

  have "map_expression' f ez = const_expression undefined"
    apply (subst Rep_expression_inject[symmetric])
    using False by (auto simp: map_expression'.rep_eq expression_vars.rep_eq case_prod_beta)
  then have "index_flip_expression (map_expression' f ez) = const_expression undefined"
    by simp
  also from False' have "map_expression' f (index_flip_expression o ez) = const_expression undefined"
    apply (subst Rep_expression_inject[symmetric])
    using False by (auto simp: map_expression'.rep_eq expression_vars.rep_eq case_prod_beta)
  finally show ?thesis by metis
qed

lemma index_flip_expression_map_expression: "index_flip_expression (map_expression f e)
  = map_expression f (index_flip_expression e)"
  unfolding map_expression_def
  apply (subst index_flip_expression_map_expression') 
  by (simp add: o_def)

lemma index_flip_map_expression2': "index_flip_expression (map_expression2' f e1 e2) = 
  map_expression2' f (index_flip_expression e1) (index_flip_expression o e2)"
  unfolding map_expression2'_def by (simp add: index_flip_expression_pair_expression index_flip_expression_map_expression' o_def)

lemma index_flip_map_expression3'': "index_flip_expression (map_expression3'' f e1 e2 e3) = 
  map_expression3'' f (index_flip_expression e1) (index_flip_expression o e2) (index_flip_expression o e3)"
  unfolding map_expression3''_def by (simp add: index_flip_expression_pair_expression index_flip_expression_map_expression' o_def)

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

lemma substitution1_variable_index_flip: "substitution1_variable (index_flip_substitute1 s) = 
  index_flip_var_raw (substitution1_variable s)"
  apply transfer by auto

lemma substitution1_function_index_flip: "substitution1_function (index_flip_substitute1 s) = 
  substitution1_function s \<circ> index_flip_mem2"
  apply (cases "Rep_substitution1 s")
  by (simp add: substitution1_function.rep_eq index_flip_substitute1.rep_eq)

lemma index_flip_var_raw_substitution1_footprint: "index_flip_var_raw ` substitution1_footprint s =
  substitution1_footprint (index_flip_substitute1 s)"
  apply (cases "Rep_substitution1 s")
  by (simp add: substitution1_footprint.rep_eq index_flip_substitute1.rep_eq)

lemma index_flip_substitute1_twice[simp]: "index_flip_substitute1 (index_flip_substitute1 s) = s"
  apply transfer by (auto simp: image_iff)


definition rel_substitute1x :: "(variable_raw\<Rightarrow>variable_raw\<Rightarrow>bool) \<Rightarrow> (variable_raw\<Rightarrow>variable_raw\<Rightarrow>bool) \<Rightarrow> (substitution1\<Rightarrow>substitution1\<Rightarrow>bool)"
  where "rel_substitute1x R S s1 s2 \<longleftrightarrow> R (substitution1_variable s1) (substitution1_variable s2) \<and>
    (rel_set R (substitution1_footprint s1) (substitution1_footprint s2)) \<and>
    (rel_fun (rel_mem2 S) (=)) (substitution1_function s1) (substitution1_function s2)"


(* Remove? *)
lift_definition rel_substitute1 :: 
  "(variable_raw\<Rightarrow>variable_raw\<Rightarrow>bool) \<Rightarrow> ('a::universe expression\<Rightarrow>'b::universe expression\<Rightarrow>bool) 
          \<Rightarrow> (substitution1\<Rightarrow>substitution1\<Rightarrow>bool)" is
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

lemma rel_substitute1_flip[simp]: "(rel_substitute1 R S)^--1 = rel_substitute1 R^--1 S^--1"
  apply (rule ext)+ unfolding conversep_iff apply transfer by auto

lemma rel_substitute1x_flip[simp]: "(rel_substitute1x R S)^--1 = rel_substitute1x R^--1 S^--1"
  apply (rule ext)+ unfolding rel_substitute1x_def by (auto simp: rel_fun_def simp flip: rel_mem2_flip)

lemma left_unique_rel_substitute1x[transfer_rule]: 
  assumes "left_unique R"
  assumes "left_unique S"
    and "right_total S"
    and "type_preserving_var_rel S"
  shows "left_unique (rel_substitute1x R S)"
proof (unfold rel_substitute1x_def, rule left_uniqueI, auto)
  fix x y z
  assume "R (substitution1_variable x) (substitution1_variable z)"
    and "R (substitution1_variable y) (substitution1_variable z)"
  with \<open>left_unique R\<close> have "substitution1_variable x = substitution1_variable y"
    by (rule left_uniqueD)
  moreover
  assume "rel_set R (substitution1_footprint x) (substitution1_footprint z)"
    and "rel_set R (substitution1_footprint y) (substitution1_footprint z)"
  with \<open>left_unique R\<close> have "substitution1_footprint x = substitution1_footprint y"
    by (meson left_uniqueD left_unique_rel_set)
  moreover
  assume "rel_fun (rel_mem2 S) (=) (substitution1_function x) (substitution1_function z)"
    and "rel_fun (rel_mem2 S) (=) (substitution1_function y) (substitution1_function z)"
  with assms have "substitution1_function x = substitution1_function y"
    by (meson left_total_rel_mem2 left_uniqueD left_unique_eq left_unique_fun)
  ultimately
  show "x = y"
    using Rep_substitution1_components Rep_substitution1_inject by auto
qed

lemma left_unique_rel_substitute1[transfer_rule]: 
  assumes "left_unique R"
  assumes "left_unique S"
  shows "left_unique (rel_substitute1 R S)"
proof -
  have "s1 = s2" if "rel_substitute1 R S s1 t" and "rel_substitute1 R S s2 t" for s1 s2 t
  proof -
    obtain xs1 vss1 es1 where s1: "Rep_substitution1 s1 = (xs1,vss1,es1)" by (meson prod_cases3)
    then have "finite vss1" and foot1: "(\<forall>w\<in>vss1. Rep_mem2 m1 w = Rep_mem2 m2 w) \<longrightarrow> es1 m1 = es1 m2" for m1 m2
      using Rep_substitution1[of s1] by auto
    obtain xs2 vss2 es2 where s2: "Rep_substitution1 s2 = (xs2,vss2,es2)" by (meson prod_cases3)
    then have "finite vss2" and foot2: "(\<forall>w\<in>vss2. Rep_mem2 m1 w = Rep_mem2 m2 w) \<longrightarrow> es2 m1 = es2 m2" for m1 m2
      using Rep_substitution1[of s2] by auto
    obtain xt vst et where t: "Rep_substitution1 t = (xt,vst,et)" by (meson prod_cases3)

    from that have "rel_prod R
     (\<lambda>(vss1, es1) (vst, et).
         range es1 \<subseteq> range EMBEDDING('a) \<and>
         range et \<subseteq> range EMBEDDING('b) \<and>
         S (Abs_expression (vss1, inv EMBEDDING('a) \<circ> es1)) (Abs_expression (vst, inv EMBEDDING('b) \<circ> et)))
     (xs1, vss1, es1) (xt, vst, et)"
      unfolding rel_substitute1.rep_eq s1 t by simp
    then have R1: "R xs1 xt" and range_es1: "range es1 \<subseteq> range EMBEDDING('a)" and "range et \<subseteq> range EMBEDDING('b)" 
      and S1: "S (Abs_expression (vss1, inv EMBEDDING('a) \<circ> es1)) (Abs_expression (vst, inv EMBEDDING('b) \<circ> et))"
      by auto

    from that have "rel_prod R
     (\<lambda>(vss2, es2) (vst, et).
         range es2 \<subseteq> range EMBEDDING('a) \<and>
         range et \<subseteq> range EMBEDDING('b) \<and>
         S (Abs_expression (vss2, inv EMBEDDING('a) \<circ> es2)) (Abs_expression (vst, inv EMBEDDING('b) \<circ> et)))
     (xs2, vss2, es2) (xt, vst, et)"
      unfolding rel_substitute1.rep_eq s2 t by simp
    then have R2: "R xs2 xt" and range_es2: "range es2 \<subseteq> range EMBEDDING('a)" and "range et \<subseteq> range EMBEDDING('b)" 
      and S2: "S (Abs_expression (vss2, inv EMBEDDING('a) \<circ> es2)) (Abs_expression (vst, inv EMBEDDING('b) \<circ> et))"
      by auto

    from R1 R2 have "xs1 = xs2"
      using \<open>left_unique R\<close>
      by (meson left_uniqueD)

    from S1 S2 have AbsS: "Abs_expression (vss1, inv EMBEDDING('a) \<circ> es1) = Abs_expression (vss2, inv EMBEDDING('a) \<circ> es2)"
      using \<open>left_unique S\<close>
      by (meson left_uniqueD)
    have "(vss1, inv EMBEDDING('a) \<circ> es1) = (vss2, inv EMBEDDING('a) \<circ> es2)"
      apply (rule Abs_expression_inject[THEN iffD1, OF _ _ AbsS])
      using foot1 foot2 \<open>finite vss1\<close> \<open>finite vss2\<close> by force+
    then have "vss1 = vss2" and inv: "inv EMBEDDING('a) o es1 = inv EMBEDDING('a) o es2" by auto
    with range_es1 range_es2 have "es1 = es2"
      by (smt fun.inj_map_strong inv_into_injective subsetCE) 

    from \<open>xs1 = xs2\<close> and \<open>vss1 = vss2\<close> and \<open>es1 = es2\<close>
    show "s1 = s2"
      using Rep_substitution1_inject s1 s2 by fastforce
    qed
  then show ?thesis
    unfolding left_unique_def by simp
qed

lemma right_unique_rel_substitute1[transfer_rule]:
  assumes "right_unique R" and "right_unique S"
  shows "right_unique (rel_substitute1 R S)"
  apply (subst conversep_conversep[of R, symmetric])
  apply (subst conversep_conversep[of S, symmetric])
  apply (subst rel_substitute1_flip[symmetric])
  apply (simp del: rel_substitute1_flip)
  apply (rule left_unique_rel_substitute1)
  using assms by auto

lemma right_unique_rel_substitute1x[transfer_rule]:
  assumes "right_unique R" and "right_unique S" and "left_total S" and "type_preserving_var_rel S"
  shows "right_unique (rel_substitute1x R S)"
  apply (subst conversep_conversep[of R, symmetric])
  apply (subst conversep_conversep[of S, symmetric])
  apply (subst rel_substitute1x_flip[symmetric])
  apply (simp del: rel_substitute1x_flip)
  apply (rule left_unique_rel_substitute1x)
  using assms by auto

lemma bi_unique_rel_substitute1[transfer_rule]:
  assumes "bi_unique R" and "bi_unique S"
  shows "bi_unique (rel_substitute1 R S)"
  using assms by (meson bi_total_alt_def bi_unique_alt_def left_unique_rel_substitute1 right_unique_rel_substitute1)

lemma bi_unique_rel_substitute1x[transfer_rule]:
  assumes "bi_unique R" and "bi_unique S" and "bi_total S" and "type_preserving_var_rel S"
  shows "bi_unique (rel_substitute1x R S)"
  using assms by (meson bi_total_alt_def bi_unique_alt_def left_unique_rel_substitute1x right_unique_rel_substitute1x)


lemma rel_substitute1_expression_eq: "rel_substitute1 R (rel_expression S T) s1 s2 = 
        (R (substitution1_variable s1) (substitution1_variable s2) \<and>
        rel_set S (substitution1_footprint s1) (substitution1_footprint s2) \<and>
        range (substitution1_function s1) \<subseteq> range EMBEDDING('a) \<and> 
        range (substitution1_function s2) \<subseteq> range EMBEDDING('b) \<and> 
        rel_fun (rel_mem2 S) T (inv EMBEDDING('a) \<circ> substitution1_function s1)
                               (inv EMBEDDING('b) \<circ> substitution1_function s2))"
  using [[transfer_del_const pcr_mem2]]
  apply transfer by force


lemma rel_substitution1x_function:
  includes lifting_syntax
  fixes R S
  defines "subR == rel_substitute1x R S"
  shows "(subR ===> rel_mem2 S ===> (=)) substitution1_function substitution1_function"
  unfolding subR_def rel_substitute1x_def apply (rule rel_funI)+ unfolding rel_fun_def
  apply transfer by auto

lemma rel_substitution1_function:
  includes lifting_syntax
  fixes R
  defines "subR == rel_substitute1 R (rel_expression R (=))"
  shows "(subR ===> rel_mem2 R ===> (=)) substitution1_function substitution1_function"
proof (rule rel_funI, rule rel_funI, rename_tac s1 s2 m1 m2)
  fix s1 s2 m1 m2
  assume s12: "subR s1 s2"
  assume m12: "rel_mem2 R m1 m2"
  show "substitution1_function s1 m1 = substitution1_function s2 m2"
    using s12 m12 unfolding subR_def 
    apply transfer unfolding rel_fun_def rel_set_def apply auto
    by (metis UNIV_I image_subset_iff inv_into_injective)
qed

(* TODO define *)

(* Note: substitute_vars adds variables from varterm right-to-left to the substition1 list.
   This means, right variables have priority in case of name clashes *)
axiomatization substitute_vars :: "'a variables \<Rightarrow> 'a expression \<Rightarrow> substitution1 list"
axiomatization where substitute_vars_unit: "substitute_vars variable_unit e = []"
axiomatization where substitute_vars_concat: "substitute_vars (variable_concat v1 v2) e
   = (substitute_vars v2 (map_expression snd e)) @ (substitute_vars v1 (map_expression fst e))" for e :: "('a::universe*'b::universe) expression"
axiomatization where substitute_vars_singleton: "substitute_vars (variable_singleton v) e = [substitute1 v e]" for e :: "('a::universe) expression"


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


lemma rel_substitute1_Rep_substitution1:
  includes lifting_syntax
  fixes R S S'
  defines "subR == rel_substitute1 R (rel_expression R S)"
  assumes "\<And>x y. S x y \<longleftrightarrow> S' (embedding x) (embedding y)"
  shows "(subR ===> rel_prod R (rel_prod (rel_set R) (rel_mem2 R ===> S'))) Rep_substitution1 Rep_substitution1"
  apply (rule rel_funI)
  apply (simp add: subR_def rel_substitute1_expression_eq[abs_def] rel_fun_def Rep_substitution1_components rel_prod_conv BNF_Greatest_Fixpoint.image2p_def)
  using assms by (auto simp: f_inv_into_f image_subset_iff) 

lemma rel_substitute1x_Rep_substitution1:
  includes lifting_syntax
  fixes R S S'
  defines "subR == rel_substitute1x R S"
  shows "(subR ===> rel_prod R (rel_prod (rel_set R) (rel_mem2 S ===> (=)))) Rep_substitution1 Rep_substitution1"
  apply (rule rel_funI)
  by (simp add: subR_def rel_substitute1x_def Rep_substitution1_components)

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

lemma rel_substitute1x_substitution1_variable: 
  includes lifting_syntax
  fixes R S
  defines "subR == rel_substitute1x R S"
  shows "(subR ===> R) substitution1_variable substitution1_variable"
  unfolding subR_def rel_substitute1x_def rel_fun_def by auto

lemma rel_substitute1x_substitution1_footprint:
  includes lifting_syntax
  fixes R S
  defines "subR == rel_substitute1x R S"
  shows "(subR ===> rel_set R) substitution1_footprint substitution1_footprint"
  unfolding subR_def rel_substitute1x_def rel_fun_def by auto

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


lemma rel_subst_mem2_x:
  includes lifting_syntax
  fixes R
  assumes [transfer_rule]: "bi_unique R"
  defines "subR == rel_substitute1x R R"
  shows "(list_all2 subR ===> rel_mem2 R ===> rel_mem2 R) subst_mem2 subst_mem2"
proof (rule rel_funI, rule rel_funI)
  fix s1 s2 m1 m2
  assume s12[unfolded subR_def, transfer_rule]: "list_all2 subR s1 s2"
  assume m12[transfer_rule]: "rel_mem2 R m1 m2"
  show "rel_mem2 R (subst_mem2 s1 m1) (subst_mem2 s2 m2)"
    unfolding rel_mem2.rep_eq subst_mem2.rep_eq 
  proof (rule rel_funI, rename_tac v1 v2) 
    fix v1 v2
    assume v12[transfer_rule]: "R v1 v2"
    note rel_substitute1x_substitution1_variable[transfer_rule]
    define find1 find2 
      where "find1 = find (\<lambda>s. substitution1_variable s = v1) s1" 
        and "find2 = find (\<lambda>s. substitution1_variable s = v2) s2"
    have find12: "(rel_option subR) find1 find2" 
      unfolding find1_def find2_def subR_def
      by transfer_prover
    show "(case find1 of None \<Rightarrow> Rep_mem2 m1 v1 | Some s \<Rightarrow> substitution1_function s m1) =
          (case find2 of None \<Rightarrow> Rep_mem2 m2 v2 | Some s \<Rightarrow> substitution1_function s m2)"
    proof (cases "find1")
      case None
      with find12 have None2: "find2 = None" by auto
      show ?thesis
        unfolding None None2 apply simp
        by (metis (full_types) v12 m12 rel_fun_def rel_mem2.rep_eq)
    next
      case (Some s1')
      with find12 obtain s2' where Some2: "find2 = Some s2'" and [transfer_rule]: "subR s1' s2'"
        by (meson option_rel_Some1)
      have [transfer_rule]: "(subR ===> rel_mem2 R ===> (=)) substitution1_function substitution1_function"
         unfolding subR_def by (rule rel_substitution1x_function)
      show ?thesis
        unfolding Some Some2 apply simp by transfer_prover
    qed
  qed
qed

lemma rel_subst_mem2:
  includes lifting_syntax
  fixes R
  assumes [transfer_rule]: "bi_unique R"
  defines "subR == rel_substitute1 R (rel_expression R (=))"
  shows "(list_all2 subR ===> rel_mem2 R ===> rel_mem2 R) subst_mem2 subst_mem2"
proof (rule rel_funI, rule rel_funI)
  fix s1 s2 m1 m2
  assume s12[unfolded subR_def, transfer_rule]: "list_all2 subR s1 s2"
  assume m12[transfer_rule]: "rel_mem2 R m1 m2"
  show "rel_mem2 R (subst_mem2 s1 m1) (subst_mem2 s2 m2)"
    unfolding rel_mem2.rep_eq subst_mem2.rep_eq 
  proof (rule rel_funI, rename_tac v1 v2) 
    fix v1 v2
    assume v12[transfer_rule]: "R v1 v2"
    note rel_substitute1_substitution1_variable[transfer_rule]
    define find1 find2 where "find1 = find (\<lambda>s. substitution1_variable s = v1) s1" and "find2 = find (\<lambda>s. substitution1_variable s = v2) s2"
    have find12: "(rel_option subR) find1 find2" 
      unfolding find1_def find2_def subR_def
      by transfer_prover
    show "(case find1 of None \<Rightarrow> Rep_mem2 m1 v1 | Some s \<Rightarrow> substitution1_function s m1) =
          (case find2 of None \<Rightarrow> Rep_mem2 m2 v2 | Some s \<Rightarrow> substitution1_function s m2)"
    proof (cases "find1")
      case None
      with find12 have None2: "find2 = None" by auto
      show ?thesis
        unfolding None None2 apply simp
        by (metis (full_types) v12 m12 rel_fun_def rel_mem2.rep_eq)
    next
      case (Some s1')
      with find12 obtain s2' where Some2: "find2 = Some s2'" and [transfer_rule]: "subR s1' s2'"
        by (meson option_rel_Some1)
      have [transfer_rule]: "(subR ===> rel_mem2 R ===> (=)) substitution1_function substitution1_function"
         unfolding subR_def by (rule rel_substitution1_function)
      show ?thesis
        unfolding Some Some2 apply simp by transfer_prover
    qed
  qed
qed


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

lemma rel_set_subst_expression_footprint_x:
  includes lifting_syntax
  assumes "bi_unique R" and "bi_total R" and "type_preserving_var_rel R"
  defines "subR == rel_substitute1x R R"
  assumes "list_all2 subR s1 s2"
  assumes "rel_set R vs1 vs2" 
  shows "rel_set R (subst_expression_footprint s1 vs1) (subst_expression_footprint s2 vs2)"
proof (rule rel_setI)

  have goal: "\<exists>y\<in>subst_expression_footprint s2 vs2. R x y" if "x \<in> subst_expression_footprint s1 vs1" 
    and [transfer_rule]: "list_all2 subR s1 s2"
    and [transfer_rule]: "rel_set R vs1 vs2"
    and [transfer_rule]: "bi_unique R"
    and [transfer_rule]: "bi_total R"
    and [transfer_rule]: "type_preserving_var_rel R"
    and subR_def: "subR = rel_substitute1x R R"
  for x s1 s2 vs1 vs2 R subR
  proof -
    have [transfer_rule]: "(subR ===> R) substitution1_variable substitution1_variable"
      unfolding subR_def by (rule rel_substitute1x_substitution1_variable)
    have [transfer_rule]: "(subR ===> rel_set R) substitution1_footprint substitution1_footprint"
      unfolding subR_def by (rule rel_substitute1x_substitution1_footprint)
    have [transfer_rule]: "bi_unique subR" 
      unfolding subR_def
      using \<open>bi_unique R\<close> apply (rule bi_unique_rel_substitute1x)
      using that bi_unique_eq by auto
    show ?thesis
    proof (cases "x \<in> vs1 - substitution1_variable ` set s1")
      case False
      with that obtain sx vx where x_sx: "x \<in> substitution1_footprint sx" 
        and Some1: "Some sx = find (\<lambda>s. substitution1_variable s = vx) s1" 
        and sx_vs1: "substitution1_variable sx \<in> vs1"
        unfolding subst_expression_footprint_def by auto
      from Some1 obtain i where s1i: "s1!i = sx" and lens1: "i < length s1"
        by (metis find_Some_iff) 
      define sy where "sy = s2!i"
      then have [transfer_rule]: "subR sx sy"
        using s1i lens1 \<open>list_all2 subR s1 s2\<close> list_all2_conv_all_nth by blast
      from Some1 have vx_def: "vx = substitution1_variable sx"
        by (metis (mono_tags) find_Some_iff)
      define vy where "vy = substitution1_variable sy"
      have [transfer_rule]: "R vx vy" unfolding vy_def vx_def
        by (meson \<open>(subR ===> R) substitution1_variable substitution1_variable\<close> \<open>subR sx sy\<close> rel_funD)
      from sx_vs1 have "vx : vs1"
        by (simp add: vx_def)
      have Some2: "Some sy = find (\<lambda>s. substitution1_variable s = vy) s2"
        apply (transfer fixing: sy vy s1) 
        by (fact Some1)
      have sy_vs2: "substitution1_variable sy \<in> vs2"
        apply (transfer fixing: sy vs2)
        by (fact sx_vs1)
      have "rel_set R (substitution1_footprint sx) (substitution1_footprint sy)"
        by (meson \<open>(subR ===> rel_set R) substitution1_footprint substitution1_footprint\<close> \<open>subR sx sy\<close> rel_funD)
      with x_sx obtain y where Rxy: "R x y" and y_sy: "y \<in> substitution1_footprint sy"
        by (meson rel_set_def)
      from Some2 sy_vs2 y_sy have "y\<in>subst_expression_footprint s2 vs2"
        unfolding subst_expression_footprint_def by auto
      with Rxy show ?thesis by auto
    next
      case True
      have "rel_set R (vs1 - substitution1_variable ` set s1) (vs2 - substitution1_variable ` set s2)"
        by transfer_prover
      with True obtain y where "y \<in> vs2 - substitution1_variable ` set s2" and Rxy: "R x y"
        by (meson rel_set_def)
      then have "y\<in>subst_expression_footprint s2 vs2"
        unfolding subst_expression_footprint_def by auto
      with Rxy show ?thesis by auto 
    qed
  qed
  show "\<exists>y\<in>subst_expression_footprint s2 vs2. R x y" if "x \<in> subst_expression_footprint s1 vs1" for x
    apply (rule goal) using assms that by simp_all
  show "\<exists>x\<in>subst_expression_footprint s1 vs1. R x y" if "y \<in> subst_expression_footprint s2 vs2" for y
    apply (subst conversep_iff[of R, symmetric])
    apply (rule goal[where R="conversep R" and subR="conversep subR"]) 
          apply (simp_all add: list.rel_flip)
    using that assms by (simp_all add: subR_def)
qed

lemma rel_set_subst_expression_footprint:
  includes lifting_syntax
  assumes "bi_unique R" and "bi_total R" and "type_preserving_var_rel R"
  defines "subR == rel_substitute1 R (rel_expression R (=))"
  assumes "list_all2 subR s1 s2"
  assumes "rel_set R vs1 vs2" 
  shows "rel_set R (subst_expression_footprint s1 vs1) (subst_expression_footprint s2 vs2)"
proof (rule rel_setI)

  have goal: "\<exists>y\<in>subst_expression_footprint s2 vs2. R x y" if "x \<in> subst_expression_footprint s1 vs1" 
    and [transfer_rule]: "list_all2 subR s1 s2"
    and [transfer_rule]: "rel_set R vs1 vs2"
    and [transfer_rule]: "bi_unique R"
    and [transfer_rule]: "bi_total R"
    and [transfer_rule]: "type_preserving_var_rel R"
    and subR_def: "subR = rel_substitute1 R (rel_expression R (=))"
  for x s1 s2 vs1 vs2 R subR
  proof -
    have [transfer_rule]: "(subR ===> R) substitution1_variable substitution1_variable"
      unfolding subR_def by (rule rel_substitute1_substitution1_variable)
    have [transfer_rule]: "(subR ===> rel_set R) substitution1_footprint substitution1_footprint"
      unfolding subR_def by (rule rel_substitute1_substitution1_footprint)
    have [transfer_rule]: "bi_unique subR" 
      unfolding subR_def
      using \<open>bi_unique R\<close> apply (rule bi_unique_rel_substitute1)
      apply (rule bi_unique_rel_expression)
      using that bi_unique_eq by auto
    show ?thesis
    proof (cases "x \<in> vs1 - substitution1_variable ` set s1")
      case False
      with that obtain sx vx where x_sx: "x \<in> substitution1_footprint sx" 
        and Some1: "Some sx = find (\<lambda>s. substitution1_variable s = vx) s1" 
        and sx_vs1: "substitution1_variable sx \<in> vs1"
        unfolding subst_expression_footprint_def by auto
      from Some1 obtain i where s1i: "s1!i = sx" and lens1: "i < length s1"
        by (metis find_Some_iff) 
      define sy where "sy = s2!i"
      then have [transfer_rule]: "subR sx sy"
        using s1i lens1 \<open>list_all2 subR s1 s2\<close> list_all2_conv_all_nth by blast
      from Some1 have vx_def: "vx = substitution1_variable sx"
        by (metis (mono_tags) find_Some_iff)
      define vy where "vy = substitution1_variable sy"
      have [transfer_rule]: "R vx vy" unfolding vy_def vx_def
        by (meson \<open>(subR ===> R) substitution1_variable substitution1_variable\<close> \<open>subR sx sy\<close> rel_funD)
      from sx_vs1 have "vx : vs1"
        by (simp add: vx_def)
      have Some2: "Some sy = find (\<lambda>s. substitution1_variable s = vy) s2"
        apply (transfer fixing: sy vy s1) 
        by (fact Some1)
      have sy_vs2: "substitution1_variable sy \<in> vs2"
        apply (transfer fixing: sy vs2)
        by (fact sx_vs1)
      have "rel_set R (substitution1_footprint sx) (substitution1_footprint sy)"
        by (meson \<open>(subR ===> rel_set R) substitution1_footprint substitution1_footprint\<close> \<open>subR sx sy\<close> rel_funD)
      with x_sx obtain y where Rxy: "R x y" and y_sy: "y \<in> substitution1_footprint sy"
        by (meson rel_set_def)
      from Some2 sy_vs2 y_sy have "y\<in>subst_expression_footprint s2 vs2"
        unfolding subst_expression_footprint_def by auto
      with Rxy show ?thesis by auto
    next
      case True
      have "rel_set R (vs1 - substitution1_variable ` set s1) (vs2 - substitution1_variable ` set s2)"
        by transfer_prover
      with True obtain y where "y \<in> vs2 - substitution1_variable ` set s2" and Rxy: "R x y"
        by (meson rel_set_def)
      then have "y\<in>subst_expression_footprint s2 vs2"
        unfolding subst_expression_footprint_def by auto
      with Rxy show ?thesis by auto 
    qed
  qed
  show "\<exists>y\<in>subst_expression_footprint s2 vs2. R x y" if "x \<in> subst_expression_footprint s1 vs1" for x
    apply (rule goal) using assms that by simp_all
  show "\<exists>x\<in>subst_expression_footprint s1 vs1. R x y" if "y \<in> subst_expression_footprint s2 vs2" for y
    apply (subst conversep_iff[of R, symmetric])
    apply (rule goal[where R="conversep R" and subR="conversep subR"]) 
          apply (simp_all add: list.rel_flip)
    using that assms by (simp_all add: subR_def)
qed

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


lemma rel_expression_subst_expression [transfer_rule]: 
  includes lifting_syntax
  assumes [transfer_rule]: "bi_unique R" and [transfer_rule]: "bi_total R" and [transfer_rule]: "type_preserving_var_rel R"
  defines "subR == rel_substitute1 R (rel_expression R (=))"
  shows "(list_all2 subR ===> rel_expression R (=) ===> rel_expression R (=)) 
         subst_expression subst_expression"
proof -
  have "rel_expression R (=) (subst_expression s1 e1) (subst_expression s2 e2)" 
    if subR_s1_s2[transfer_rule]: "list_all2 subR s1 s2" and R_e1_e2: "rel_expression R (=) e1 e2" 
    for s1 s2 and e1 e2 :: "'b expression"
  proof -
    define vs1 E1 vs2 E2 where "vs1 = expression_vars e1" and "E1 = expression_eval e1"
      and "vs2 = expression_vars e2" and "E2 = expression_eval e2"
    have [unfolded subR_def, transfer_rule]: "(subR ===> rel_prod R (rel_prod (rel_set R) (rel_mem2 R ===> (=)))) Rep_substitution1 Rep_substitution1"
      unfolding subR_def apply (rule rel_substitute1_Rep_substitution1) by simp
    have [transfer_rule]: "(subR ===> R) substitution1_variable substitution1_variable"
      unfolding subR_def by (rule rel_substitute1_substitution1_variable)
    have [transfer_rule]: "bi_unique subR" 
      unfolding subR_def
      using \<open>bi_unique R\<close> apply (rule bi_unique_rel_substitute1)
      apply (rule bi_unique_rel_expression)
      using assms bi_unique_eq by auto
    have [transfer_rule]: "(subR ===> rel_set R) substitution1_footprint substitution1_footprint"
      unfolding subR_def by (rule rel_substitute1_substitution1_footprint)
    have R_vs1_vs2[transfer_rule]: "rel_set R vs1 vs2"
      unfolding vs1_def vs2_def using R_e1_e2 apply transfer by auto
    have foot: "rel_set R (subst_expression_footprint s1 vs1) (subst_expression_footprint s2 vs2)"
      apply (rule rel_set_subst_expression_footprint)
      using assms R_vs1_vs2 subR_s1_s2 unfolding subR_def by auto
    have E1E2: "(rel_mem2 R ===> (=)) E1 E2" 
      unfolding E1_def E2_def apply (rule rel_funI)
      using R_e1_e2 apply transfer 
      unfolding rel_mem2.rep_eq rel_fun_def by auto
    have subst_mem2_s1_s2: "(rel_mem2 R ===> rel_mem2 R) (subst_mem2 s1) (subst_mem2 s2)"
      using rel_subst_mem2 subR_s1_s2 \<open>bi_unique R\<close>
      by (metis rel_fun_def subR_def)
    from E1E2 subst_mem2_s1_s2 have subst: "(rel_mem2 R ===> (=)) (E1 \<circ> subst_mem2 s1) (E2 \<circ> subst_mem2 s2)"
      by (smt comp_def rel_funD rel_funI)
    show ?thesis
      unfolding rel_expression.rep_eq subst_expression.rep_eq using foot subst
      by (simp add: Rep_expression_components E1_def E2_def vs1_def vs2_def)
  qed

  then show ?thesis
     unfolding subR_def
    apply (rule_tac rel_funI)+ by assumption
qed

lemma rel_expression_subst_expression_x [transfer_rule]: 
  includes lifting_syntax
  fixes R
  assumes [transfer_rule]: "bi_unique R" and [transfer_rule]: "bi_total R" and [transfer_rule]: "type_preserving_var_rel R"
  defines "subR == rel_substitute1x R R"
  shows "(list_all2 subR ===> rel_expression R (=) ===> rel_expression R (=)) 
         subst_expression subst_expression"
proof -
  have "rel_expression R (=) (subst_expression s1 e1) (subst_expression s2 e2)" 
    if subR_s1_s2[transfer_rule]: "list_all2 subR s1 s2" and R_e1_e2: "rel_expression R (=) e1 e2" 
    for s1 s2 and e1 e2 :: "'b expression"
  proof -
    define vs1 E1 vs2 E2 where "vs1 = expression_vars e1" and "E1 = expression_eval e1"
      and "vs2 = expression_vars e2" and "E2 = expression_eval e2"
    have [unfolded subR_def, transfer_rule]: 
      "(subR ===> rel_prod R (rel_prod (rel_set R) (rel_mem2 R ===> (=)))) Rep_substitution1 Rep_substitution1"
      unfolding subR_def by (rule rel_substitute1x_Rep_substitution1)
    have [transfer_rule]: "(subR ===> R) substitution1_variable substitution1_variable"
      unfolding subR_def by (rule rel_substitute1x_substitution1_variable)
    have [transfer_rule]: "bi_unique subR" 
      unfolding subR_def
      using \<open>bi_unique R\<close> apply (rule bi_unique_rel_substitute1x)
      by (auto simp: assms)
    have [transfer_rule]: "(subR ===> rel_set R) substitution1_footprint substitution1_footprint"
      unfolding subR_def by (rule rel_substitute1x_substitution1_footprint)
    have R_vs1_vs2[transfer_rule]: "rel_set R vs1 vs2"
      unfolding vs1_def vs2_def using R_e1_e2 apply transfer by auto
    have foot: "rel_set R (subst_expression_footprint s1 vs1) (subst_expression_footprint s2 vs2)"
      apply (rule rel_set_subst_expression_footprint_x)
      using assms R_vs1_vs2 subR_s1_s2 unfolding subR_def by auto
    have E1E2: "(rel_mem2 R ===> (=)) E1 E2" 
      unfolding E1_def E2_def apply (rule rel_funI)
      using R_e1_e2 apply transfer 
      unfolding rel_mem2.rep_eq rel_fun_def by auto
    have subst_mem2_s1_s2: "(rel_mem2 R ===> rel_mem2 R) (subst_mem2 s1) (subst_mem2 s2)"
      using rel_subst_mem2_x subR_s1_s2 \<open>bi_unique R\<close>
      by (metis rel_fun_def subR_def)
    from E1E2 subst_mem2_s1_s2 have subst: "(rel_mem2 R ===> (=)) (E1 \<circ> subst_mem2 s1) (E2 \<circ> subst_mem2 s2)"
      by (smt comp_def rel_funD rel_funI)
    show ?thesis
      unfolding rel_expression.rep_eq subst_expression.rep_eq using foot subst
      by (simp add: Rep_expression_components E1_def E2_def vs1_def vs2_def)
  qed

  then show ?thesis
     unfolding subR_def
    apply (rule_tac rel_funI)+ by assumption
qed


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


lemma index_flip_subst_expression: 
  fixes \<sigma> :: "substitution1 list" and e :: "'a expression"
  shows "index_flip_expression (subst_expression \<sigma> e) 
        = subst_expression (map index_flip_substitute1 \<sigma>) (index_flip_expression e)"
proof -
  define subR where "subR = (rel_substitute1x rel_flip_index rel_flip_index)" 
  
  have rel_set_rel_flip_index: "rel_set rel_flip_index x y \<longleftrightarrow> index_flip_var_raw ` x = y" for x y
    unfolding rel_set_def rel_flip_index_def by auto

  include lifting_syntax
  note bi_unique_rel_flip_index[transfer_rule]
  note bi_total_rel_flip_index[transfer_rule]
  note type_preserving_rel_flip_index[transfer_rule]

  have rel_fun_flip[simp]: "(x ===> y)^--1 = (x^--1 ===> y^--1)" for x :: "'c\<Rightarrow>'d\<Rightarrow>bool" and y :: "'e\<Rightarrow>'f\<Rightarrow>bool" 
    unfolding rel_fun_def by auto

  have "rel_expression rel_flip_index (=) e (index_flip_expression e)" for e :: "'c expression"
  proof (unfold rel_expression.rep_eq index_flip_expression.rep_eq, cases "Rep_expression e", auto)
    fix vs f assume "Rep_expression e = (vs,f)"
    show "rel_set rel_flip_index vs (index_flip_var_raw ` vs)"
      by (rule rel_setI, unfold rel_flip_index_def, auto)
    show "(rel_mem2 rel_flip_index ===> (=)) f (\<lambda>m. f (index_flip_mem2 m))"
      apply (rule conversepD[of "(rel_mem2 rel_flip_index ===> (=))"])
      unfolding rel_fun_flip apply simp
      unfolding rel_fun_def rel_mem2.rep_eq rel_flip_index_def'
      unfolding rel_flip_index_def' apply transfer by auto
  qed
  then have [transfer_rule]: "((=) ===> rel_expression rel_flip_index (=)) (%x. x) index_flip_expression"
    unfolding rel_fun_def by auto

  have rel_flip_index_index_flip_var_raw: "rel_flip_index v (index_flip_var_raw v)" for v
    by (simp add: rel_flip_index_def)
  have rel_set_rel_flip_index_index_flip_var_raw: "rel_set rel_flip_index vs (index_flip_var_raw ` vs)" for vs
    by (subst rel_set_rel_flip_index, rule)
  have Fx: "F x = (F \<circ> index_flip_mem2) y" if "rel_mem2 rel_flip_index x y" for F::"mem2\<Rightarrow>'c" and x y
    using that apply transfer apply (auto simp: rel_flip_index_def[abs_def])
    by (metis (full_types) rel_fun_def)
  then have inv_embedding_index_flip_mem2: "(rel_mem2 rel_flip_index ===> (=)) (inv embedding \<circ> f) (inv embedding \<circ> (f \<circ> index_flip_mem2))" for f
    apply (rule_tac rel_funI) by simp

  have "rel_substitute1x rel_flip_index rel_flip_index s (index_flip_substitute1 s)" for s
    unfolding rel_substitute1x_def  
    using Fx
    by (metis (mono_tags, lifting) index_flip_var_raw_substitution1_footprint rel_flip_index_def rel_funI rel_set_rel_flip_index substitution1_function_index_flip substitution1_variable_index_flip)
  
  then have index_flip_substitute1_transfer [transfer_rule]:
    "((=) ===> subR) (%x. x) index_flip_substitute1"
    unfolding subR_def rel_fun_def by auto
  have "index_flip_expression e = f" if that[transfer_rule]: "rel_expression rel_flip_index (=) e f" for e f :: "'c expression"
    apply transfer by rule
  then have [transfer_rule]: "(rel_expression rel_flip_index (=) ===> rel_expression (=) (=)) index_flip_expression id"
    apply (rule_tac rel_funI) by (simp add: rel_expression_eq)

  have [transfer_rule]: "(list_all2 subR ===> rel_expression rel_flip_index (=) ===> rel_expression rel_flip_index (=))
   subst_expression subst_expression"
    unfolding subR_def
    by transfer_prover

  have "(rel_expression (=) (=))
        (index_flip_expression (subst_expression \<sigma> e))
        (id (subst_expression (map index_flip_substitute1 \<sigma>) (index_flip_expression e)))"
    apply transfer_prover_start
           apply transfer_step+
    by simp
  then
  show "index_flip_expression (subst_expression \<sigma> e) = subst_expression (map index_flip_substitute1 \<sigma>) (index_flip_expression e)"
    unfolding rel_expression_eq id_def by assumption
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

lemma subst_expression_convert_substitute_vars_tac: \<comment> \<open>Helper for ML function subst_expression_tac\<close>
  assumes "\<sigma> = substitute_vars xs e"
  assumes "g = subst_expression \<sigma> f"
  shows "g = subst_expression (substitute_vars xs e) f"
  using assms by simp

lemma substitute_vars_unit_tac: \<comment> \<open>Helper for ML function substitute_vars_tac\<close>
  shows "[] = substitute_vars \<lbrakk>\<rbrakk> e"
  by (simp add: substitute_vars_unit)

lemma substitute_vars_singleton_tac: \<comment> \<open>Helper for ML function substitute_vars_tac\<close>
  shows "[substitute1 x e] = substitute_vars \<lbrakk>x\<rbrakk> e"
  by (simp add: substitute_vars_singleton)

lemma substitute_vars_concat_tac: \<comment> \<open>Helper for ML function substitute_vars_tac\<close>
  assumes "e1 = map_expression fst e"
  assumes "e2 = map_expression snd e"
  assumes "lQ = substitute_vars Q e1"
  assumes "lR = substitute_vars R e2"
  assumes "lQR = lR @ lQ"
  shows "lQR = substitute_vars (variable_concat Q R) e"
  apply (subst substitute_vars_concat) unfolding assms by simp

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

print_translation \<open>[(\<^const_syntax>\<open>expression\<close>, fn ctxt => fn [vars,t] => 
  (Const(\<^const_syntax>\<open>expression_syntax\<close>, dummyT) $
      Expressions.expression_to_term_syntax (\<^Const>\<open>expression dummyT dummyT\<close> $ vars $ t))
  handle _ => raise Match)
]\<close>

hide_const expression_syntax

(* TODO remove *)
schematic_goal "?x = substitute_vars \<lbrakk>var_z,var_x\<rbrakk> Expr[x]" and "?x = xxx"
apply (tactic \<open>Expressions.substitute_vars_tac \<^context> 1\<close>)
print_theorems
  oops

end
