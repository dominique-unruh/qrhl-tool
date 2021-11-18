theory Prog_Variables
  imports Extended_Sorry Multi_Transfer Registers.Classical_Extra Registers.Quantum_Extra2
  (* keywords "variables" :: thy_decl_block *)
begin

hide_const (open) Classical_Extra.X Classical_Extra.Y Classical_Extra.x Classical_Extra.y

typedecl cl
typedecl qu
instance qu :: finite sorry
instance qu :: default sorry

type_synonym 'a cvariable = \<open>('a,cl) Axioms_Classical.preregister\<close>
type_synonym 'a qvariable = \<open>'a Axioms_Quantum.update \<Rightarrow> qu Axioms_Quantum.update\<close>

typedef QVARIABLE = \<open>UNIV :: qu Axioms_Quantum.update set set\<close>..
setup_lifting type_definition_QVARIABLE
(* TODO: Is this truely an equivalence class of classical variables? *)
typedef CVARIABLE = \<open>UNIV :: cl Axioms_Classical.update set set\<close>..
setup_lifting type_definition_CVARIABLE

lift_definition QVARIABLE_of :: \<open>'a::finite qvariable \<Rightarrow> QVARIABLE\<close> is
  \<open>\<lambda>x::'a::finite qvariable. range x\<close>.
axiomatization CVARIABLE_of :: \<open>'a cvariable \<Rightarrow> CVARIABLE\<close>

lift_definition QVARIABLE_unit :: \<open>QVARIABLE\<close> is
  \<open>{c *\<^sub>C (id_cblinfun) | c. True} :: 'qu Axioms_Quantum.update set\<close>.
axiomatization CVARIABLE_unit :: \<open>CVARIABLE\<close>

axiomatization QVARIABLE_pair :: \<open>QVARIABLE \<Rightarrow> QVARIABLE \<Rightarrow> QVARIABLE\<close>
axiomatization CVARIABLE_pair :: \<open>CVARIABLE \<Rightarrow> CVARIABLE \<Rightarrow> CVARIABLE\<close>

datatype 'a vtree = VTree_Singleton 'a | VTree_Concat "'a vtree" "'a vtree" | VTree_Unit

consts variable_concat :: \<open>'a \<Rightarrow> 'b \<Rightarrow> 'c\<close>
adhoc_overloading variable_concat Axioms_Quantum.register_pair Axioms_Classical.register_pair

consts variable_unit :: \<open>'a\<close>
adhoc_overloading variable_unit
  \<open>Quantum_Extra2.empty_var :: (unit Axioms_Quantum.update \<Rightarrow> _)\<close> 
  \<open>Classical_Extra.empty_var :: (unit Axioms_Classical.update \<Rightarrow> _)\<close>

abbreviation (input) "variable_singleton x \<equiv> x"


nonterminal variable_list_args
syntax
  "variable_unit"      :: "variable_list_args \<Rightarrow> 'a"        ("(1'[|'|])")
  "variable_unit"      :: "variable_list_args \<Rightarrow> 'a"        ("(1'\<lbrakk>'\<rbrakk>)")
  "_variables"      :: "variable_list_args \<Rightarrow> 'a"        ("(1'[|_'|])")
  "_variables"      :: "variable_list_args \<Rightarrow> 'a"        ("(1'\<lbrakk>_'\<rbrakk>)")
  "_variable_list_arg"  :: "'a \<Rightarrow> variable_list_args"                   ("_")
  "_variable_list_args" :: "'a \<Rightarrow> variable_list_args \<Rightarrow> variable_list_args"     ("_,/ _")

translations
  "_variables (_variable_list_args x y)" \<rightleftharpoons> "CONST variable_concat x (_variables y)"
  "_variables (_variable_list_arg x)" \<rightharpoonup> "x"
  "_variables (_variable_list_args x y)" \<leftharpoondown> "CONST variable_concat (_variables (_variable_list_arg x)) (_variables y)"

section \<open>Distinct variables\<close>

abbreviation (input) "distinct_qvars Q == Axioms_Quantum.register Q"
abbreviation (input) "distinct_cvars Q == Axioms_Classical.register Q"

lemma register_pair_is_register_iff: \<open>Axioms_Quantum.register (Q;R) \<longleftrightarrow> compatible Q R\<close>
  apply auto
  by (smt (verit, best) Axioms_Quantum.register_pair_def Laws_Quantum.compatibleI zero_not_register)

lemma distinct_qvars_split1: 
  "distinct_qvars (variable_concat (variable_concat Q R) S) = (distinct_qvars (variable_concat Q R) \<and> distinct_qvars (variable_concat Q S) \<and> distinct_qvars (variable_concat R S))"
  by (metis Laws_Quantum.compatible3 Laws_Quantum.compatible_comp_left Laws_Quantum.compatible_comp_right Laws_Quantum.compatible_sym Laws_Quantum.pair_is_register Laws_Quantum.register_Fst Laws_Quantum.register_Snd Laws_Quantum.register_pair_Fst Laws_Quantum.register_pair_Snd id_def register_pair_is_register_converse(1) register_pair_is_register_iff)
lemma distinct_qvars_swap: "distinct_qvars (variable_concat Q R) \<Longrightarrow> distinct_qvars (variable_concat R Q)" 
  by (meson Laws_Quantum.compatible_sym register_pair_is_register_iff)
lemma distinct_qvars_split2: "distinct_qvars (variable_concat S (variable_concat Q R)) = (distinct_qvars (variable_concat Q R) \<and> distinct_qvars (variable_concat Q S) \<and> distinct_qvars (variable_concat R S))"
  by (metis distinct_qvars_split1 distinct_qvars_swap)
lemma distinct_qvars_concat_unit1[simp]: "distinct_qvars (variable_concat Q \<lbrakk>\<rbrakk>) = distinct_qvars Q" for Q::"'a::finite qvariable" 
  using is_unit_register_empty_var register_pair_is_register_converse(1) register_pair_is_register_iff unit_register_compatible' by blast
lemma distinct_qvars_concat_unit2[simp]: "distinct_qvars (variable_concat \<lbrakk>\<rbrakk> Q) = distinct_qvars Q" for Q::"'a::finite qvariable" 
  using is_unit_register_empty_var register_pair_is_register_converse(2) register_pair_is_register_iff unit_register_compatible by blast
lemma distinct_qvars_unit[simp]: "distinct_qvars \<lbrakk>\<rbrakk>" 
  by simp
(* lemma distinct_qvars_single[simp]: "distinct_qvars \<lbrakk>q\<rbrakk>" for q::"'a::finite qvariable"
  unfolding distinct_qvars_def apply transfer by auto *)

lemma distinct_qvarsL: "distinct_qvars (variable_concat Q R) \<Longrightarrow> distinct_qvars Q"
  using register_pair_is_register_converse(1) by blast
lemma distinct_qvarsR: "distinct_qvars (variable_concat Q R) \<Longrightarrow> distinct_qvars R"
  using register_pair_is_register_converse(2) by blast

lemma distinct_cvars_split1: 
  "distinct_cvars (variable_concat (variable_concat Q R) S) = (distinct_cvars (variable_concat Q R) \<and> distinct_cvars (variable_concat Q S) \<and> distinct_cvars (variable_concat R S))"
  by x(metis Laws_Quantum.compatible3 Laws_Quantum.compatible_comp_left Laws_Quantum.compatible_comp_right Laws_Quantum.compatible_sym Laws_Quantum.pair_is_register Laws_Quantum.register_Fst Laws_Quantum.register_Snd Laws_Quantum.register_pair_Fst Laws_Quantum.register_pair_Snd id_def register_pair_is_register_converse(1) register_pair_is_register_iff)
lemma distinct_cvars_swap: "distinct_cvars (variable_concat Q R) \<Longrightarrow> distinct_cvars (variable_concat R Q)" 
  by (meson Laws_Quantum.compatible_sym register_pair_is_register_iff)
lemma distinct_cvars_split2: "distinct_cvars (variable_concat S (variable_concat Q R)) = (distinct_cvars (variable_concat Q R) \<and> distinct_cvars (variable_concat Q S) \<and> distinct_cvars (variable_concat R S))"
  by (metis distinct_cvars_split1 distinct_cvars_swap)
lemma distinct_cvars_concat_unit1[simp]: "distinct_cvars (variable_concat Q \<lbrakk>\<rbrakk>) = distinct_cvars Q" for Q::"'a::finite cvariable" 
  using is_unit_register_empty_var register_pair_is_register_converse(1) register_pair_is_register_iff unit_register_compatible' by blast x
lemma distinct_cvars_concat_unit2[simp]: "distinct_cvars (variable_concat \<lbrakk>\<rbrakk> Q) = distinct_cvars Q" for Q::"'a::finite cvariable" 
  using is_unit_register_empty_var register_pair_is_register_converse(2) register_pair_is_register_iff unit_register_compatible by blast x
lemma distinct_cvars_unit[simp]: "distinct_cvars \<lbrakk>\<rbrakk>" 
  by simp
(* lemma distinct_cvars_single[simp]: "distinct_cvars \<lbrakk>q\<rbrakk>" for q::"'a::finite cvariable"
  unfolding distinct_cvars_def apply transfer by auto *)

lemma distinct_cvarsL: "distinct_cvars (variable_concat Q R) \<Longrightarrow> distinct_cvars Q"
  sorry (* TODO: needs slightly changed definition of register pair *)
  (* using register_pair_is_register_converse(1) by blast *)
lemma distinct_cvarsR: "distinct_cvars (variable_concat Q R) \<Longrightarrow> distinct_cvars R"
  sorry
  (* using register_pair_is_register_converse(2) by blast *)

section \<open>Indexed variables\<close>

type_synonym cl2 = \<open>cl \<times> cl\<close>
type_synonym qu2 = \<open>qu \<times> qu\<close>

type_synonym 'a c2variable = \<open>('a,cl2) preregister\<close>
type_synonym 'a q2variable = \<open>'a Axioms_Quantum.update \<Rightarrow> qu2 Axioms_Quantum.update\<close>


definition index_cvar :: \<open>bool \<Rightarrow> 'a cvariable \<Rightarrow> 'a c2variable\<close> where
  \<open>index_cvar b x = (if b then Laws_Classical.Fst else Laws_Classical.Snd) o x\<close>
definition index_qvar :: \<open>bool \<Rightarrow> 'a qvariable \<Rightarrow> 'a q2variable\<close> where
  \<open>index_qvar b x = (if b then Laws_Quantum.Fst else Laws_Quantum.Snd) o x\<close>

definition index_flip_cvar :: \<open>'a c2variable \<Rightarrow> 'a c2variable\<close> where
  \<open>index_flip_cvar x = Laws_Classical.swap o x\<close>
definition index_flip_qvar :: \<open>'a q2variable \<Rightarrow> 'a q2variable\<close> where
  \<open>index_flip_qvar x = Laws_Quantum.swap o x\<close>

definition index_flip_mem2 :: "qu2 \<Rightarrow> qu2" where \<open>index_flip_mem2 = (\<lambda>(x,y). (y,x))\<close>
(*  "\<lambda>(f::_\<Rightarrow>universe) v. f (index_flip_var_raw v)"
  using variable_raw_domain_index_flip_var_raw by blast *)

definition swap_cvariables_mem2 :: "'a c2variable \<Rightarrow> 'a c2variable \<Rightarrow> (cl2 \<Rightarrow> cl2)" where
  \<open>swap_cvariables_mem2 x y m = register_apply (Axioms_Classical.register_pair x y) (\<lambda>(a,b). (b,a)) m\<close>

axiomatization swap_variables_qvars :: \<open>'a q2variable \<Rightarrow> 'a q2variable \<Rightarrow> 'b q2variable \<Rightarrow> 'b q2variable\<close>

section \<open>ML code\<close>

(* 
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
  by simp *)

ML_file "prog_variables.ML"

section {* Simprocs *}

(* A simproc that utters warnings whenever the simplifier tries to prove a distinct_qvars statement with distinct, explicitly listed variables but can't *)
syntax "_declared_qvars" :: "variable_list_args \<Rightarrow> bool" ("declared'_qvars \<lbrakk>_\<rbrakk>")
syntax "_declared_qvars" :: "variable_list_args \<Rightarrow> bool" ("declared'_qvars [|_|]")
(* parse_translation \<open>[("_declared_qvars", Prog_Variables.declared_qvars_parse_tr)]\<close> *)

(* simproc_setup warn_declared_qvars ("variable_name q") = Prog_Variables.warn_declared_qvars_simproc *)

(* simproc_setup index_var ("index_var lr v") = Prog_Variables.index_var_simproc *)
(* simproc_setup index_flip_var ("index_flip_var v") = Prog_Variables.index_flip_var_simproc *)

section \<open>Cleanup\<close>

hide_type (open) vtree

end
