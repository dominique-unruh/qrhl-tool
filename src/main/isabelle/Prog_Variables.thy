theory Prog_Variables
  imports Universe
  keywords "variables" :: thy_decl_block
begin

typedef variable_raw = "{v :: string * universe set. snd v \<noteq> {}}" by auto
setup_lifting type_definition_variable_raw
(* TODO: use multi_transfer *)
lifting_forget universe.lifting
lift_definition variable_raw_domain :: "variable_raw \<Rightarrow> universe set" is "snd" .
lift_definition variable_raw_name :: "variable_raw \<Rightarrow> string" is "fst" .
declare [[lifting_restore Quotient_universe]]

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

lift_definition variable_names :: "'a::universe variables \<Rightarrow> string list" 
  is "\<lambda>(v,e). map variable_raw_name (flatten_tree v)" .

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

lift_definition variable_unit :: "unit variables"
  is "(VTree_Unit, \<lambda>_. embedding ())"
  by (auto intro: bij_betwI')

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
  

lemma variable_names_cons[simp]: "variable_names (variable_concat X Y) = variable_names X @ variable_names Y"
  by (transfer, auto)
lemma variable_singleton_name[simp]: "variable_names (variable_singleton x) = [variable_name x]"
  by (transfer, auto)
lemma variable_unit_name[simp]: "variable_names variable_unit = []"
  by (transfer, auto)

ML_file "prog_variables.ML"

section {* Simprocs *}

(* A simproc that utters warnings whenever the simplifier tries to prove a distinct_qvars statement with distinct, explicitly listed variables but can't *)
syntax "_declared_qvars" :: "variable_list_args \<Rightarrow> bool" ("declared'_qvars \<lbrakk>_\<rbrakk>")
syntax "_declared_qvars" :: "variable_list_args \<Rightarrow> bool" ("declared'_qvars [|_|]")
parse_translation \<open>[("_declared_qvars", Prog_Variables.declared_qvars_parse_tr)]\<close>

simproc_setup warn_declared_qvars ("variable_name q") = Prog_Variables.warn_declared_qvars_simproc

section \<open>Distinct variables\<close>

lift_definition distinct_qvars :: "'a::universe variables \<Rightarrow> bool" 
  is "\<lambda>(v,_). distinct (flatten_tree v)" .

lemma distinct_variable_names[simp]:
  "distinct (variable_names Q) \<Longrightarrow> distinct_qvars Q" 
  apply transfer using distinct_map by auto

lemma distinct_qvars_split1: 
  "distinct_qvars (variable_concat (variable_concat Q R) S) = (distinct_qvars (variable_concat Q R) \<and> distinct_qvars (variable_concat Q S) \<and> distinct_qvars (variable_concat R S))"
  apply transfer by auto
lemma distinct_qvars_split2: "distinct_qvars (variable_concat S (variable_concat Q R)) = (distinct_qvars (variable_concat Q R) \<and> distinct_qvars (variable_concat Q S) \<and> distinct_qvars (variable_concat R S))"
  apply transfer by auto
lemma distinct_qvars_swap: "distinct_qvars (variable_concat Q R) \<Longrightarrow> distinct_qvars (variable_concat R Q)" 
  apply transfer by auto
lemma distinct_qvars_concat_unit1[simp]: "distinct_qvars (variable_concat Q \<lbrakk>\<rbrakk>) = distinct_qvars Q" for Q::"'a::universe variables" 
  apply transfer by auto
lemma distinct_qvars_concat_unit2[simp]: "distinct_qvars (variable_concat \<lbrakk>\<rbrakk> Q) = distinct_qvars Q" for Q::"'a::universe variables" 
  apply transfer by auto
lemma distinct_qvars_unit[simp]: "distinct_qvars \<lbrakk>\<rbrakk>" 
  apply transfer by auto
lemma distinct_qvars_single[simp]: "distinct_qvars \<lbrakk>q\<rbrakk>" for q::"'a::universe variable"
  apply transfer by auto

lemma distinct_qvarsL: "distinct_qvars (variable_concat Q R) \<Longrightarrow> distinct_qvars Q"
  apply transfer by auto
lemma distinct_qvarsR: "distinct_qvars (variable_concat Q R) \<Longrightarrow> distinct_qvars R"
  apply transfer by auto

hide_type (open) vtree

end
