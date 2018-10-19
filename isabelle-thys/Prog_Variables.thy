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

lemma eval_variables_unit[simp]: "eval_variables \<lbrakk>\<rbrakk> m = ()"
  apply transfer by auto

(* lemma eval_variables_singleton[simp]: "eval_variables \<lbrakk>x\<rbrakk> m = ()"
  apply transfer by auto *)

section \<open>Indexed variables\<close>

lift_definition index_var_raw  :: "bool \<Rightarrow> variable_raw \<Rightarrow> variable_raw" is
  "\<lambda>left (n,dom). (n @ (if left then ''1'' else ''2''), dom)"
  by auto

lemma index_var_raw_inject: "index_var_raw left x = index_var_raw left y \<Longrightarrow> x = y"
  apply transfer by auto

lemma variable_raw_domain_index_var_raw[simp]: "variable_raw_domain (index_var_raw left v) = variable_raw_domain v"
  apply transfer by auto

lemma variable_raw_name_index_var_left[simp]: "variable_raw_name (index_var_raw True v) = variable_raw_name v @ ''1''"
  apply transfer by auto
lemma variable_raw_name_index_var_right[simp]: "variable_raw_name (index_var_raw False v) = variable_raw_name v @ ''2''"
  apply transfer by auto

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

definition "index_vartree left = map_vtree (index_var_raw left)"

lemma tree_domain_index_vartree[simp]: "tree_domain (index_vartree left vt) = tree_domain vt"
  unfolding index_vartree_def by (induction vt, auto)

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

ML_file "prog_variables.ML"

section {* Simprocs *}

(* A simproc that utters warnings whenever the simplifier tries to prove a distinct_qvars statement with distinct, explicitly listed variables but can't *)
syntax "_declared_qvars" :: "variable_list_args \<Rightarrow> bool" ("declared'_qvars \<lbrakk>_\<rbrakk>")
syntax "_declared_qvars" :: "variable_list_args \<Rightarrow> bool" ("declared'_qvars [|_|]")
parse_translation \<open>[("_declared_qvars", Prog_Variables.declared_qvars_parse_tr)]\<close>

simproc_setup warn_declared_qvars ("variable_name q") = Prog_Variables.warn_declared_qvars_simproc

section \<open>Cleanup\<close>

hide_type (open) vtree

end
