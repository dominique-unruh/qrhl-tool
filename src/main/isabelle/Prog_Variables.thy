theory Prog_Variables
  imports Universe
  keywords "variables" :: thy_decl_block
begin

typedef variable_raw = "{v :: string * universe set. snd v \<noteq> {}}" by auto

(*setup {* Sign.add_const_constraint (\<^const_name>\<open>embedding\<close>,SOME \<^typ>\<open>'a=>universe\<close>) *}*)

(* a variable, refers to a location in a memory *)
(* typedef (overloaded) 'a::universe variable = "{v::variable_raw. range (embedding::'a=>universe) = snd (Rep_variable_raw v)}" sorry *)

(*setup {* Sign.add_const_constraint (@{const_name embedding},SOME @{typ "'a::universe=>universe"}) *}*)

(* a variable, refers to a location in a memory *)
typedef (overloaded) ('a::universe) variable = "{v::variable_raw. range (embedding::'a=>universe) = snd (Rep_variable_raw v)}"
  apply (rule exI[where x="Abs_variable_raw (undefined, range embedding)"])
  apply simp
  apply (subst Abs_variable_raw_inverse)
  by auto

definition variable_name :: "'a::universe variable \<Rightarrow> string" where "variable_name v = fst (Rep_variable_raw (Rep_variable v))"

typedecl 'a "variables" (* represents a tuple of variables, of joint type 'a *)

axiomatization
    variable_names :: "'a variables \<Rightarrow> string list"
and variable_concat :: "'a variables \<Rightarrow> 'b variables \<Rightarrow> ('a * 'b) variables"
and variable_singleton :: "'a variable \<Rightarrow> 'a variables"
and variable_unit :: "unit variables"

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
  

axiomatization where
  variable_names_cons[simp]: "variable_names (variable_concat X Y) = variable_names X @ variable_names Y"
  and variable_singleton_name[simp]: "variable_names (variable_singleton x) = [variable_name x]"
  and variable_unit_name[simp]: "variable_names variable_unit = []"
  for X::"'a::universe variables" and Y::"'b::universe variables" and x::"'c::universe variable"

ML_file "prog_variables.ML"

section {* Simprocs *}

(* A simproc that utters warnings whenever the simplifier tries to prove a distinct_qvars statement with distinct, explicitly listed variables but can't *)
syntax "_declared_qvars" :: "variable_list_args \<Rightarrow> bool" ("declared'_qvars \<lbrakk>_\<rbrakk>")
syntax "_declared_qvars" :: "variable_list_args \<Rightarrow> bool" ("declared'_qvars [|_|]")
parse_translation \<open>[("_declared_qvars", Prog_Variables.declared_qvars_parse_tr)]\<close>

simproc_setup warn_declared_qvars ("variable_name q") = Prog_Variables.warn_declared_qvars_simproc

end
