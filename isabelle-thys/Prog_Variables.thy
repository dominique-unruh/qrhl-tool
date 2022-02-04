theory Prog_Variables
  imports Universe Extended_Sorry Multi_Transfer
  keywords "variables" :: thy_decl_block
begin

typedef variable_raw = "{v :: string * universe set. snd v \<noteq> {}}" by auto
setup_lifting type_definition_variable_raw
(* TODO: use multi_transfer *)
lifting_forget universe.lifting
lift_definition variable_raw_domain :: "variable_raw \<Rightarrow> universe set" is "snd" .
lift_definition variable_raw_name :: "variable_raw \<Rightarrow> string" is "fst" .
declare [[lifting_restore Quotient_universe]]

(* TODO: remove in Isabelle2022 *)
declare More_List.no_leading_Cons[rule del]

(*setup {* Sign.add_const_constraint (\<^const_name>\<open>embedding\<close>,SOME \<^typ>\<open>'a=>universe\<close>) *}*)

(* a variable, refers to a location in a memory *)
(* typedef (overloaded) 'a::universe variable = "{v::variable_raw. range (embedding::'a=>universe) = snd (Rep_variable_raw v)}"  *)

(*setup {* Sign.add_const_constraint (@{const_name embedding},SOME @{typ "'a::universe=>universe"}) *}*)

(* a variable, refers to a location in a memory *)
typedef (overloaded) ('a::universe) variable = "{v::variable_raw. range (embedding::'a=>universe) = variable_raw_domain v}"
  apply (rule exI[where x="Abs_variable_raw (undefined, range embedding)"])
  apply (simp add: variable_raw_domain.rep_eq)
  apply (subst Abs_variable_raw_inverse)
  by auto
setup_lifting type_definition_variable

lift_definition variable_name :: "'a::universe variable \<Rightarrow> string" is "variable_raw_name" .

datatype 'a vtree = VTree_Singleton 'a | VTree_Concat "'a vtree" "'a vtree" | VTree_Unit

fun tree_domain where
  "tree_domain VTree_Unit = {VTree_Unit}"
| "tree_domain (VTree_Singleton v) = VTree_Singleton ` variable_raw_domain v"
| "tree_domain (VTree_Concat v w) = {VTree_Concat x y | x y. x \<in> tree_domain v \<and> y \<in> tree_domain w}"


fun flatten_tree where
  "flatten_tree VTree_Unit = []"
| "flatten_tree (VTree_Concat x y) = flatten_tree x @ flatten_tree y"
| "flatten_tree (VTree_Singleton z) = [z]"

typedef (overloaded) ('a::universe) "variables" = "{(v::variable_raw vtree, e::universe vtree\<Rightarrow>universe). 
  bij_betw e (tree_domain v) (range (embedding::'a\<Rightarrow>universe))}"
proof -
  fix x :: "'a variable" 
  let ?embedding = "embedding :: 'a \<Rightarrow> universe"
  define x_tree e where "x_tree = VTree_Singleton (Rep_variable x)" 
    and "e = (\<lambda>x. case x of VTree_Singleton v \<Rightarrow> (v::universe))"
  have x_tree_domain: "tree_domain x_tree = VTree_Singleton ` (range ?embedding)"
    unfolding x_tree_def apply simp
    using Rep_variable by auto
  have "bij_betw e (tree_domain x_tree) (range ?embedding)" 
    apply (rule bij_betwI') 
    unfolding x_tree_domain e_def
    by auto
  then show ?thesis
    by (rule_tac exI[of _ "(x_tree,e)"], auto)
qed
setup_lifting type_definition_variables

lift_definition raw_variables :: "'a::universe variables \<Rightarrow> variable_raw list" 
  is "\<lambda>(v::variable_raw vtree,e). flatten_tree v" .

definition "variable_names vs = map variable_raw_name (raw_variables vs)"

(* lift_definition variable_names :: "'a::universe variables \<Rightarrow> string list" 
  is "\<lambda>(v,e). map variable_raw_name (flatten_tree v)" . *)

lift_definition variable_concat :: "'a::universe variables \<Rightarrow> 'b::universe variables \<Rightarrow> ('a * 'b) variables"
  is "\<lambda>(v1,e1) (v2,e2). (VTree_Concat v1 v2,
                         (\<lambda>x. case x of VTree_Concat x1 x2 \<Rightarrow> embedding (inv embedding (e1 x1) :: 'a, inv embedding (e2 x2) :: 'b)))"
proof auto
  fix v1 v2 and e1 e2 :: "universe vtree \<Rightarrow> universe"
  define E dom emba embb emb where "E x = (case x of VTree_Concat x1 x2 \<Rightarrow> emb (inv emba (e1 x1), inv embb (e2 x2)))"
       and "dom = {VTree_Concat a b |a b. a \<in> tree_domain v1 \<and> b \<in> tree_domain v2}" 
       and "emba = (embedding :: 'a \<Rightarrow> _)" 
       and "embb = (embedding :: 'b \<Rightarrow> _)" 
       and "emb = (embedding :: ('a*'b) \<Rightarrow> _)" for x
  assume bij_e1: "bij_betw e1 (tree_domain v1) (range emba)"
    and  bij_e2: "bij_betw e2 (tree_domain v2) (range embb)"
  have xy: "x = y" if E: "E x = E y" and "x \<in> dom" and "y \<in> dom" for x y
  proof -
    from \<open>x \<in> dom\<close> obtain x1 x2 where x: "x = VTree_Concat x1 x2" unfolding dom_def by auto
    with \<open>x \<in> dom\<close> have x1v1: "x1 \<in> tree_domain v1" and x2v2: "x2 \<in> tree_domain v2" 
      unfolding dom_def by auto
    then have e1x1: "e1 x1 : range emba" and e2x2: "e2 x2 : range embb" and True
      apply auto using bij_e1 bij_e2 bij_betwE by force+
    from \<open>y \<in> dom\<close> obtain y1 y2 where y: "y = VTree_Concat y1 y2" unfolding dom_def by auto
    with \<open>y \<in> dom\<close> have y1v1: "y1 \<in> tree_domain v1" and y2v2: "y2 \<in> tree_domain v2" 
      unfolding dom_def by auto
    then have e1y1: "e1 y1 : range emba" and e2y2: "e2 y2 : range embb" and True
      apply auto using bij_e1 bij_e2 bij_betwE by force+

    from E have "(inv emba (e1 x1), inv embb (e2 x2))
               = (inv emba (e1 y1), inv embb (e2 y2))"
      unfolding E_def emb_def x y by auto
    then have "e1 x1 = e1 y1" and "e2 x2 = e2 y2"
      using e1x1 e1y1 e2x2 e2y2 inv_into_injective by force+

    then show "x = y"
      unfolding x y apply simp
      by (metis bij_betw_inv_into_left bij_e1 bij_e2 x1v1 x2v2 y1v1 y2v2)
  qed
  have yEx: "\<exists>x\<in>dom. y = E x" if "y \<in> range emb" for y
  proof -
    from that obtain a b where y: "y = emb (a,b)" by auto
    obtain x1 where x1: "a = inv emba (e1 x1)" and x1v1: "x1 \<in> tree_domain v1"
      by (metis bij_betw_imp_surj_on bij_e1 emba_def embedding_inv' imageE range_eqI)
    obtain x2 where x2: "b = inv embb (e2 x2)" and x2v2: "x2 \<in> tree_domain v2" 
      by (metis bij_betw_imp_surj_on bij_e2 embb_def embedding_inv' imageE range_eqI)
    have x12dom: "VTree_Concat x1 x2 \<in> dom"
      unfolding dom_def using x1v1 x2v2 by auto
    show ?thesis
      apply (rule bexI[of _ "VTree_Concat x1 x2"])
      unfolding E_def y x1 x2 using x12dom by auto
  qed

  show "bij_betw E dom (range emb)"
    apply (rule bij_betwI')
    using xy yEx 
    by (auto simp: dom_def E_def emb_def emba_def embb_def)
qed

lift_definition variable_singleton :: "'a::universe variable \<Rightarrow> 'a variables"
  is "\<lambda>v. (VTree_Singleton v, \<lambda>x. case x of VTree_Singleton y \<Rightarrow> y)"
  using [[show_consts]]
proof -
  fix v :: variable_raw
  define E emb where "E x = (case x of VTree_Singleton z \<Rightarrow> z)" and "emb = (embedding :: 'a \<Rightarrow> universe)"
    for x :: "universe vtree"
  assume range_emb: "range emb = variable_raw_domain v"
  have "bij_betw E (VTree_Singleton ` variable_raw_domain v) (range emb)"
    apply (rule bij_betwI')
    using range_emb by (auto simp: E_def)
  then show "(VTree_Singleton v, E)
          \<in> {(v, e). bij_betw e (tree_domain v) (range emb)}"
    by auto
qed

nonterminal variable_list_args
syntax
  "variable_unit"      :: "variable_list_args \<Rightarrow> 'a"        ("(1'[|'|])")
  "variable_unit"      :: "variable_list_args \<Rightarrow> 'a"        ("(1'\<lbrakk>'\<rbrakk>)")
  "_variables"      :: "variable_list_args \<Rightarrow> 'a"        ("(1'[|_'|])")
  "_variables"      :: "variable_list_args \<Rightarrow> 'a"        ("(1'\<lbrakk>_'\<rbrakk>)")
  "_variable_list_arg"  :: "'a \<Rightarrow> variable_list_args"                   ("_")
  "_variable_list_args" :: "'a \<Rightarrow> variable_list_args \<Rightarrow> variable_list_args"     ("_,/ _")

translations
  "_variables (_variable_list_args x y)" \<rightleftharpoons> "CONST variable_concat (CONST variable_singleton x) (_variables y)"
  "_variables (_variable_list_arg x)" \<rightleftharpoons> "CONST variable_singleton x"
  "_variables (_variable_list_args x y)" \<leftharpoondown> "CONST variable_concat (_variables (_variable_list_arg x)) (_variables y)"
  

lift_definition variable_unit :: "unit variables"
  is "(VTree_Unit, \<lambda>_. embedding ())"
  by (auto intro: bij_betwI')

lemma raw_variables_concat[simp]: "raw_variables (variable_concat Q1 Q2) = raw_variables Q1 @ raw_variables Q2"
  apply transfer by auto

lemma raw_variables_unit[simp]: "raw_variables variable_unit = []"
  apply transfer by simp

lemma raw_variables_singleton[simp]: "raw_variables \<lbrakk>x\<rbrakk> = [Rep_variable x]"
  apply transfer by simp

lemma variable_names_cons[simp]: "variable_names (variable_concat X Y) = variable_names X @ variable_names Y"
  unfolding variable_names_def by simp

lemma variable_singleton_name[simp]: "variable_names (variable_singleton x) = [variable_name x]"
  unfolding variable_names_def variable_name_def by simp

lemma variable_unit_name[simp]: "variable_names variable_unit = []"
  unfolding variable_names_def by simp

definition "type_preserving_var_rel R \<longleftrightarrow> (\<forall>v w. R v w \<longrightarrow> variable_raw_domain v = variable_raw_domain w)"

lemma type_preserving_var_rel_flip[simp]: "type_preserving_var_rel R\<inverse>\<inverse> \<longleftrightarrow> type_preserving_var_rel R"
  unfolding type_preserving_var_rel_def by auto

section \<open>Distinct variables\<close>

definition "distinct_qvars Q = distinct (raw_variables Q)"

lemma distinct_variable_names[simp]:
  "distinct (variable_names Q) \<Longrightarrow> distinct_qvars Q" 
  unfolding variable_names_def distinct_qvars_def
  by (subst (asm) distinct_map, simp)
  
lemma distinct_qvars_split1: 
  "distinct_qvars (variable_concat (variable_concat Q R) S) = (distinct_qvars (variable_concat Q R) \<and> distinct_qvars (variable_concat Q S) \<and> distinct_qvars (variable_concat R S))"
  unfolding distinct_qvars_def apply transfer by auto
lemma distinct_qvars_split2: "distinct_qvars (variable_concat S (variable_concat Q R)) = (distinct_qvars (variable_concat Q R) \<and> distinct_qvars (variable_concat Q S) \<and> distinct_qvars (variable_concat R S))"
  unfolding distinct_qvars_def apply transfer by auto
lemma distinct_qvars_swap: "distinct_qvars (variable_concat Q R) \<Longrightarrow> distinct_qvars (variable_concat R Q)" 
  unfolding distinct_qvars_def apply transfer by auto
lemma distinct_qvars_concat_unit1[simp]: "distinct_qvars (variable_concat Q \<lbrakk>\<rbrakk>) = distinct_qvars Q" for Q::"'a::universe variables" 
  unfolding distinct_qvars_def apply transfer by auto
lemma distinct_qvars_concat_unit2[simp]: "distinct_qvars (variable_concat \<lbrakk>\<rbrakk> Q) = distinct_qvars Q" for Q::"'a::universe variables" 
  unfolding distinct_qvars_def apply transfer by auto
lemma distinct_qvars_unit[simp]: "distinct_qvars \<lbrakk>\<rbrakk>" 
  unfolding distinct_qvars_def apply transfer by auto
lemma distinct_qvars_single[simp]: "distinct_qvars \<lbrakk>q\<rbrakk>" for q::"'a::universe variable"
  unfolding distinct_qvars_def apply transfer by auto

lemma distinct_qvarsL: "distinct_qvars (variable_concat Q R) \<Longrightarrow> distinct_qvars Q"
  unfolding distinct_qvars_def apply transfer by auto
lemma distinct_qvarsR: "distinct_qvars (variable_concat Q R) \<Longrightarrow> distinct_qvars R"
  unfolding distinct_qvars_def apply transfer by auto

typedef mem2 = "{f. \<forall>v::variable_raw. f v \<in> variable_raw_domain v}"
  apply auto apply (rule choice) apply transfer by auto
setup_lifting type_definition_mem2

lift_definition rel_mem2 :: "(variable_raw \<Rightarrow> variable_raw \<Rightarrow> bool) \<Rightarrow> mem2 \<Rightarrow> mem2 \<Rightarrow> bool"
  is "\<lambda>rel_v::variable_raw\<Rightarrow>variable_raw\<Rightarrow>bool. rel_fun rel_v (=)".

lemma rel_mem2_eq: "rel_mem2 (=) = (=)"
  apply (rule ext)+ unfolding rel_mem2.rep_eq rel_fun_def using Rep_mem2_inject by auto
lemma rel_mem2_mono: "A \<ge> B \<Longrightarrow> rel_mem2 A \<le> rel_mem2 B"
  unfolding rel_mem2.rep_eq rel_fun_def by auto

lemma left_unique_rel_mem2[transfer_rule]: assumes "left_total R" shows "left_unique (rel_mem2 R)"
proof -
  have left_unique_fun: "left_unique (rel_fun R ((=)))"
    apply (rule left_unique_fun)
    using assms left_unique_eq by auto
  have "m=m'" if "rel_mem2 R m m2" and "rel_mem2 R m' m2" for m m' m2
  proof -
    from that have "rel_fun R (=) (Rep_mem2 m) (Rep_mem2 m2)" by (simp add: rel_mem2.rep_eq)
    moreover from that have "rel_fun R (=) (Rep_mem2 m') (Rep_mem2 m2)" by (simp add: rel_mem2.rep_eq)
    ultimately have "Rep_mem2 m = Rep_mem2 m'"
      by (rule left_unique_fun[unfolded left_unique_def, rule_format])
    then show "m = m'"
      using Rep_mem2_inject by auto 
  qed
  then show ?thesis
    by (simp add: left_uniqueI)
qed

lemma rel_mem2_flip[simp]: "(rel_mem2 x)^--1 = (rel_mem2 x^--1)"
    apply (rule ext)+ unfolding conversep_iff apply transfer
    by (auto simp: rel_fun_def)

lemma right_unique_rel_mem2[transfer_rule]: assumes "right_total R" shows "right_unique (rel_mem2 R)"
  apply (subst conversep_conversep[of R, symmetric])
  apply (subst rel_mem2_flip[symmetric])
  apply (simp del: rel_mem2_flip)
  apply (rule left_unique_rel_mem2)
  using assms by simp

lemma bi_unique_rel_mem2[transfer_rule]: assumes "bi_total R" shows "bi_unique (rel_mem2 R)"
  using assms bi_total_alt_def bi_unique_alt_def left_unique_rel_mem2 right_unique_rel_mem2 by blast

lemma left_total_rel_mem2[transfer_rule]: 
  assumes "left_unique R" and "right_total R" and "type_preserving_var_rel R"
  shows "left_total (rel_mem2 R)"
proof -
  have "\<exists>m2. rel_mem2 R m1 m2" for m1
  proof (transfer fixing: R, auto)
    fix m1 
    assume m1v: "\<forall>v. m1 v \<in> variable_raw_domain v"
    have left_total_fun: "left_total (rel_fun R (=))"
      apply (rule left_total_fun)
      using \<open>left_unique R\<close> by (auto simp: left_total_eq)
    then obtain m2 where m2: "rel_fun R (=) m1 m2" 
      using left_totalE by auto
    have m2v: "m2 v \<in> variable_raw_domain v" for v
    proof -
      obtain w where "R w v"
        apply atomize_elim using \<open>right_total R\<close> unfolding right_total_def by simp
      with m2 have m1m2: "m1 w = m2 v"
        by (rule rel_funD)
      from \<open>R w v\<close> \<open>type_preserving_var_rel R\<close> have "variable_raw_domain v = variable_raw_domain w"
        unfolding type_preserving_var_rel_def by simp
      with m1v[rule_format, of w] m1m2 
      show ?thesis by auto
    qed
    from m2 m2v 
    show "\<exists>x. (\<forall>v. x v \<in> variable_raw_domain v) \<and> rel_fun R (=) m1 x"
      by auto
  qed
  then show ?thesis
    by (rule left_totalI)
qed

lemma right_total_rel_mem2[transfer_rule]: 
  assumes "right_unique R" and "left_total R" and "type_preserving_var_rel R"
  shows "right_total (rel_mem2 R)"
  apply (subst conversep_conversep[of R, symmetric])
  apply (subst rel_mem2_flip[symmetric])
  apply (simp del: rel_mem2_flip)
  apply (rule left_total_rel_mem2)
  using assms by auto

lemma bi_total_rel_mem2[transfer_rule]: 
  assumes "bi_unique R" and "bi_total R" and "type_preserving_var_rel R"
  shows "bi_total (rel_mem2 R)"
  by (meson assms bi_total_alt_def bi_unique_alt_def left_total_rel_mem2 right_total_rel_mem2)



fun eval_vtree :: "variable_raw Prog_Variables.vtree \<Rightarrow> mem2 \<Rightarrow> universe Prog_Variables.vtree" where
  "eval_vtree VTree_Unit m = VTree_Unit"
| "eval_vtree (VTree_Singleton v) m = VTree_Singleton (Rep_mem2 m v)"
| "eval_vtree (VTree_Concat t1 t2) m = VTree_Concat (eval_vtree t1 m) (eval_vtree t2 m)"

lemma eval_vtree_footprint: 
  assumes "\<And>v. v\<in>set (flatten_tree vs) \<Longrightarrow> Rep_mem2 m1 v = Rep_mem2 m2 v" 
  shows "eval_vtree vs m1 = eval_vtree vs m2" 
proof (insert assms, induction vs)
    case (VTree_Singleton x)
    then show ?case by auto
  next
    case (VTree_Concat vs1 vs2)
    have "v \<in> set (flatten_tree vs1) \<Longrightarrow> Rep_mem2 m1 v = Rep_mem2 m2 v" for v
      using VTree_Concat.prems by auto
    with VTree_Concat.IH have "eval_vtree vs1 m1 = eval_vtree vs1 m2" by simp
    moreover have "v \<in> set (flatten_tree vs2) \<Longrightarrow> Rep_mem2 m1 v = Rep_mem2 m2 v" for v
      using VTree_Concat.prems by auto
    with VTree_Concat.IH have "eval_vtree vs2 m1 = eval_vtree vs2 m2" by simp
    ultimately show ?case by simp
  next
    case VTree_Unit
    then show ?case by auto
  qed

lift_definition eval_variables :: "'a::universe variables \<Rightarrow> mem2 \<Rightarrow> 'a" is
 "\<lambda>(vtree,e) m. inv embedding (e (eval_vtree vtree m))" .

lemma eval_variables_footprint: 
  assumes "\<And>v. v\<in>set (raw_variables vs) \<Longrightarrow> Rep_mem2 m1 v = Rep_mem2 m2 v" 
  shows "eval_variables vs m1 = eval_variables vs m2" 
  using assms apply transfer apply auto apply (subst eval_vtree_footprint) by auto

lemma eval_variables_concat[simp]: "eval_variables (variable_concat Q1 Q2) m = (eval_variables Q1 m, eval_variables Q2 m)"
  apply transfer by auto

lemma eval_variables_unit: "eval_variables \<lbrakk>\<rbrakk> m = ()" (* Simp not needed, already simp'ed by unit_eq *)
  by simp

lemma eval_variables_singleton: "eval_variables \<lbrakk>x::'a::universe variable\<rbrakk> m = inv (embedding::'a\<Rightarrow>_) (Rep_mem2 m (Rep_variable x))"
  unfolding eval_variables.rep_eq variable_singleton.rep_eq by simp

section \<open>Indexed variables\<close>

fun index_var_name :: "bool \<Rightarrow> string \<Rightarrow> string" where
  "index_var_name True n = n @ ''1''"
| "index_var_name False n = n @ ''2''"

lift_definition index_var_raw :: "bool \<Rightarrow> variable_raw \<Rightarrow> variable_raw" is
  "\<lambda>left (n,dom). (index_var_name left n, dom)"
  by auto

lemma index_var_raw_inject: "index_var_raw left x = index_var_raw left y \<Longrightarrow> x = y"
  apply (cases left) by (transfer; auto)+

lemma variable_raw_domain_index_var_raw[simp]: "variable_raw_domain (index_var_raw left v) = variable_raw_domain v"
  apply transfer by auto

lemma variable_raw_name_index_var_left[simp]: "variable_raw_name (index_var_raw True v) = variable_raw_name v @ ''1''"
  apply transfer by auto
lemma variable_raw_name_index_var_right[simp]: "variable_raw_name (index_var_raw False v) = variable_raw_name v @ ''2''"
  apply transfer by auto

definition "index_flip_name n = (if n=[] then [] else (if last n = CHR ''1'' then butlast n @ ''2'' else if last n = CHR ''2'' then butlast n @ ''1'' else n))"
lift_definition index_flip_var_raw  :: "variable_raw \<Rightarrow> variable_raw" is
  "\<lambda>(n,dom). (index_flip_name n, dom)"
  by auto

lemma index_flip_name_twice[simp]: "index_flip_name (index_flip_name x) = x"
  apply (cases x rule: rev_cases) unfolding index_flip_name_def by auto

lemma index_flip_name_inject: "index_flip_name x = index_flip_name y \<Longrightarrow> x = y"
  using index_flip_name_twice by metis

lemma index_flip_var_twice[simp]: "index_flip_var_raw (index_flip_var_raw x) = x"
  apply transfer by auto

lemma index_flip_var_raw_inject: "index_flip_var_raw x = index_flip_var_raw y \<Longrightarrow> x = y"
  apply transfer by (auto simp: index_flip_name_inject)

lemma index_flip_name_index_var_name[simp]: "index_flip_name (index_var_name left x) = index_var_name (\<not> left) x"
  unfolding index_flip_name_def apply (cases left) by auto

lemma index_flip_var_index_var_raw[simp]: "index_flip_var_raw (index_var_raw left x) = index_var_raw (\<not> left) x"
  apply (transfer fixing: left)
  apply (cases left) 
  by (auto simp: index_flip_name_def)

lemma variable_raw_domain_index_flip_var_raw[simp]: "variable_raw_domain (index_flip_var_raw v) = variable_raw_domain v"
  apply transfer by auto

lemma variable_raw_name_index_flip_var[simp]: "variable_raw_name (index_flip_var_raw v) =  index_flip_name (variable_raw_name v)"
  apply transfer by auto


definition "rel_flip_index x y \<longleftrightarrow> index_flip_var_raw x = y"
lemma rel_flip_index_def': "rel_flip_index x y \<longleftrightarrow> x = index_flip_var_raw y"
    unfolding rel_flip_index_def by auto

lemma bi_unique_rel_flip_index: "bi_unique rel_flip_index" 
  apply (rule bi_uniqueI)
   apply (rule left_uniqueI, unfold rel_flip_index_def', auto)[1]
  by (rule right_uniqueI, unfold rel_flip_index_def, auto)[1]

lemma bi_total_rel_flip_index: "bi_total rel_flip_index"
  apply (rule bi_totalI)
   apply (rule left_totalI, unfold rel_flip_index_def, auto)[1]
  by (rule right_totalI, unfold rel_flip_index_def', auto)[1]

lemma type_preserving_rel_flip_index: "type_preserving_var_rel rel_flip_index"
    unfolding type_preserving_var_rel_def rel_flip_index_def by auto 

lemma rel_flip_index_conversep[simp]: "rel_flip_index\<inverse>\<inverse> = rel_flip_index"
  apply (rule ext)+ unfolding conversep_iff using rel_flip_index_def rel_flip_index_def' by auto


(* TODO move to different section *)
lemma variable_eqI: "variable_name x = variable_name y \<Longrightarrow> x = y"
  apply transfer apply transfer by auto

lift_definition index_var :: "bool \<Rightarrow> 'a::universe variable \<Rightarrow> 'a::universe variable" is index_var_raw
  by simp

lemma index_var1: "y = index_var True x \<longleftrightarrow> variable_name y = variable_name x @ ''1''"
  apply (rule iffI)
   apply (transfer, simp)
  by (rule variable_eqI, transfer, simp)

lemma index_var2: "y = index_var False x \<longleftrightarrow> variable_name y = variable_name x @ ''2''"
  apply (rule iffI)
   apply (transfer, simp)
  by (rule variable_eqI, transfer, simp)

lemma index_var1I: "variable_name y = variable_name x @ ''1'' \<Longrightarrow> index_var True x = y"
  using index_var1 by metis

lemma index_var2I: "variable_name y = variable_name x @ ''2'' \<Longrightarrow> index_var False x = y"
  using index_var2 by metis

lemma index_var1_simp[simp]: "variable_name (index_var True x) = variable_name x @ ''1''" 
  using index_var1 by metis

lemma index_var2_simp[simp]: "variable_name (index_var False x) = variable_name x @ ''2''"
  using index_var2 by metis

lift_definition index_flip_var :: "'a::universe variable \<Rightarrow> 'a::universe variable" is index_flip_var_raw
  by simp

lemma index_flip_var: "y = index_flip_var x \<longleftrightarrow> variable_name y = index_flip_name (variable_name x)"
  apply (rule iffI)
   apply (transfer, simp)
  by (rule variable_eqI, transfer, simp)

lemma index_flip_var_index_var[simp]: "index_flip_var (index_var left x) = index_var (\<not>left) x"
  apply transfer by simp

lemma index_flip_varI: "variable_name y = index_flip_name (variable_name x) \<Longrightarrow> index_flip_var x = y"
  using index_flip_var by metis

lemma index_flip_var_simp[simp]: "variable_name (index_flip_var x) = index_flip_name (variable_name x)" 
  using index_flip_var by metis


lift_definition unindex_mem2 :: "bool \<Rightarrow> mem2 \<Rightarrow> mem2" is
  "\<lambda>left (f::_\<Rightarrow>universe) v. f (index_var_raw left v)"
  apply transfer by (auto; blast)

lemma Rep_mem2_unindex_mem2[simp]: "Rep_mem2 (unindex_mem2 left m) v = Rep_mem2 m (index_var_raw left v)"
  unfolding unindex_mem2.rep_eq by auto

lemma eval_vtree_unindex_mem2[simp]: "eval_vtree vt (unindex_mem2 left m)
        = eval_vtree (map_vtree (index_var_raw left) vt) m"
  by (induction vt, auto)

lift_definition index_mem2 :: "bool \<Rightarrow> mem2 \<Rightarrow> mem2" is
  "\<lambda>left (f::_\<Rightarrow>universe) v. 
    if v \<in> range (index_var_raw left) then f (inv (index_var_raw left) v) else f v"
  by (auto, metis f_inv_into_f rangeI variable_raw_domain_index_var_raw)

lemma Rep_mem2_index_mem2[simp]: "Rep_mem2 (index_mem2 left m) (index_var_raw left v) = Rep_mem2 m v"
  apply transfer apply auto
  by (metis f_inv_into_f index_var_raw_inject rangeI)

lemma Rep_mem2_index_mem2_bad: "v \<notin> range (index_var_raw left) \<Longrightarrow> Rep_mem2 (index_mem2 left m) v = Rep_mem2 m v"
  unfolding index_mem2.rep_eq by auto

lift_definition index_flip_mem2 :: "mem2 \<Rightarrow> mem2" is
  "\<lambda>(f::_\<Rightarrow>universe) v. f (index_flip_var_raw v)"
  using variable_raw_domain_index_flip_var_raw by blast

(* TODO move *)
definition "transposition a b v = (if v=a then b else if v=b then a else v)"

lift_definition swap_variables_mem2 :: "'a::universe variable \<Rightarrow> 'a variable \<Rightarrow> mem2 \<Rightarrow> mem2" is
  "\<lambda>a b (f::_\<Rightarrow>universe) v. f (transposition a b v)"
  by (auto simp: transposition_def)

lemma Rep_mem2_index_flip_mem2[simp]: "Rep_mem2 (index_flip_mem2 m) v = Rep_mem2 m (index_flip_var_raw v)"
  unfolding index_flip_mem2.rep_eq by simp

definition "index_vartree left = map_vtree (index_var_raw left)"

lemma tree_domain_index_vartree[simp]: "tree_domain (index_vartree left vt) = tree_domain vt"
  unfolding index_vartree_def by (induction vt, auto)

definition "index_flip_vartree = map_vtree (index_flip_var_raw)"

definition "swap_variables_vartree v w = map_vtree (transposition v w)"

lemma tree_domain_index_flip_vartree[simp]: "tree_domain (index_flip_vartree vt) = tree_domain vt"
  unfolding index_flip_vartree_def by (induction vt, auto)

lift_definition index_vars :: "bool \<Rightarrow> 'a::universe variables \<Rightarrow> 'a variables" is
  "\<lambda>left (vt,e). (index_vartree left vt,e)" by auto

lemma eval_variables_unindex_mem2[simp]: 
  "eval_variables Q (unindex_mem2 left m) = eval_variables (index_vars left Q) m"
  apply transfer apply auto
  by (simp add: index_vartree_def)

(* TODO move *)
lemma flatten_tree_map_vtree: "flatten_tree (map_vtree f t) = map f (flatten_tree t)"
  by (induction t, auto)

lemma raw_variables_index_vars[simp]: "raw_variables (index_vars left vs) = map (index_var_raw left) (raw_variables vs)"
  unfolding raw_variables.rep_eq index_vars.rep_eq case_prod_beta index_vartree_def 
  by (simp add: flatten_tree_map_vtree)

lemma index_vars_singleton[simp]: "index_vars left \<lbrakk>x\<rbrakk> = \<lbrakk>index_var left x\<rbrakk>"
  apply transfer unfolding index_vartree_def by auto

lemma index_vars_concat[simp]: "index_vars left (variable_concat Q R) = variable_concat (index_vars left Q) (index_vars left R)"
  apply transfer unfolding index_vartree_def by auto
lemma index_vars_unit[simp]: "index_vars left \<lbrakk>\<rbrakk> = \<lbrakk>\<rbrakk>"
  for x :: "'a::universe variable" and Q :: "'b::universe variables" and R :: "'c::universe variables"
  apply transfer unfolding index_vartree_def by auto


lift_definition index_flip_vars :: "'a::universe variables \<Rightarrow> 'a variables" is
  "\<lambda>(vt,e). (index_flip_vartree vt,e)" by auto

lift_definition swap_variables_vars :: "'a::universe variable \<Rightarrow> 'a variable \<Rightarrow> 'b::universe variables \<Rightarrow> 'b variables" is
  "\<lambda>v w (vt,e). (swap_variables_vartree v w vt,e)" 
  by (cheat swap_variables_vars)

lemma eval_variables_index_flip_mem2[simp]: 
  "eval_variables Q (index_flip_mem2 m) = eval_variables (index_flip_vars Q) m"
proof (transfer, auto, rename_tac vt f Q)
  fix vt f Q
  assume bij: "bij_betw f (tree_domain vt) (range embedding)"
  have "(eval_vtree vt (index_flip_mem2 Q)) = (eval_vtree (index_flip_vartree vt) Q)"
    apply (induction vt)
    by (auto simp: index_flip_vartree_def)
  then show "inv embedding (f (eval_vtree vt (index_flip_mem2 Q))) = inv embedding (f (eval_vtree (index_flip_vartree vt) Q))"
    by simp
qed


lemma raw_variables_index_flip_vars[simp]: "raw_variables (index_flip_vars vs) = map (index_flip_var_raw) (raw_variables vs)"
  unfolding raw_variables.rep_eq index_vars.rep_eq case_prod_beta index_flip_vartree_def
  by (simp add: flatten_tree_map_vtree index_flip_vars.rep_eq index_flip_vartree_def split_beta)

lemma index_flip_vars_singleton[simp]: "index_flip_vars \<lbrakk>x\<rbrakk> = \<lbrakk>index_flip_var x\<rbrakk>"
  apply transfer unfolding index_flip_vartree_def by auto

lemma index_flip_vars_concat[simp]: "index_flip_vars (variable_concat Q R) = variable_concat (index_flip_vars Q) (index_flip_vars R)"
  apply transfer unfolding index_flip_vartree_def by auto

lemma index_flip_vars_unit[simp]: "index_flip_vars \<lbrakk>\<rbrakk> = \<lbrakk>\<rbrakk>"
  for x :: "'a::universe variable" and Q :: "'b::universe variables" and R :: "'c::universe variables"
  apply transfer unfolding index_flip_vartree_def by auto


section \<open>ML code\<close>


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

lemma index_flip_var_conv_aux1: "index_flip_var (index_var True v) \<equiv> index_var False v"
  by simp
lemma index_flip_var_conv_aux2: "index_flip_var (index_var False v) \<equiv> index_var True v"
  by simp

ML_file "prog_variables.ML"

section {* Simprocs *}

(* A simproc that utters warnings whenever the simplifier tries to prove a distinct_qvars statement with distinct, explicitly listed variables but can't *)
syntax "_declared_qvars" :: "variable_list_args \<Rightarrow> bool" ("declared'_qvars \<lbrakk>_\<rbrakk>")
syntax "_declared_qvars" :: "variable_list_args \<Rightarrow> bool" ("declared'_qvars [|_|]")
parse_translation \<open>[("_declared_qvars", Prog_Variables.declared_qvars_parse_tr)]\<close>

simproc_setup warn_declared_qvars ("variable_name q") = Prog_Variables.warn_declared_qvars_simproc

simproc_setup index_var ("index_var lr v") = Prog_Variables.index_var_simproc
simproc_setup index_flip_var ("index_flip_var v") = Prog_Variables.index_flip_var_simproc

section \<open>Cleanup\<close>

hide_type (open) vtree

end
