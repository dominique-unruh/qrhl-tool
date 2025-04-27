theory Prog_Variables
  imports
    (* Multi_Transfer *)
    HOL.Map
    Registers2.BOLegacy
    Registers.Classical_Extra
    Registers2.Quantum_Registers
    Registers2.Classical_Registers
    Registers2.Quantum_Reg_Ranges
    Registers2.Classical_Reg_Ranges
    Registers2.Quantum_Reg_Conversions
    Registers2.Quantum_From_Classical_Reg
    Registers2.Classical_Reg_Conversions
    Registers2.Register_Syntax
    Registers2.Registers_Unsorted
begin

unbundle cblinfun_syntax
unbundle no m_inv_syntax
hide_const (open) Order.top
no_notation Order.top ("\<top>\<index>")
hide_const (open) Axioms_Classical.getter
hide_const (open) Axioms_Classical.setter
declare [[simproc del: Laws_Quantum.compatibility_warn]]
declare [[simproc del: Laws_Classical.compatibility_warn]]
hide_const (open) Classical_Extra.X Classical_Extra.Y Classical_Extra.x Classical_Extra.y
hide_const (open) Coset.kernel

subsubsection \<open>Wrapper types around registers\<close>

typedecl cl
typedecl qu
instance qu :: default ..

type_synonym 'a cvariable = \<open>('a,cl) cregister\<close>
type_synonym 'a qvariable = \<open>('a,qu) qregister\<close>

type_synonym QVARIABLE = \<open>qu QREGISTER\<close>
type_synonym CVARIABLE = \<open>cl CREGISTER\<close>

(* datatype 'a vtree = VTree_Singleton 'a | VTree_Concat "'a vtree" "'a vtree" | VTree_Unit *)

section \<open>Distinct variables\<close>

abbreviation (input) "distinct_qvars Q == qregister Q" (* LEGACY *)
abbreviation (input) "distinct_cvars Q == cregister Q" (* LEGACY *)

lemma distinct_qvars_split1:
  "qregister (qregister_pair (qregister_pair Q R) S) = (qregister (qregister_pair Q R) \<and> qregister (qregister_pair Q S) \<and> distinct_qvars (qregister_pair R S))"
  using qcompatible3 by blast
lemma distinct_qvars_swap: "distinct_qvars (qregister_pair Q R) \<Longrightarrow> distinct_qvars (qregister_pair R Q)"
  using qcompatible_sym by auto
lemma distinct_qvars_split2: "distinct_qvars (qregister_pair S (qregister_pair Q R)) = (distinct_qvars (qregister_pair Q R) \<and> distinct_qvars (qregister_pair Q S) \<and> distinct_qvars (qregister_pair R S))"
  by (metis qcompatible3 qcompatible_sym)
lemma distinct_qvars_concat_unit1[simp]: "distinct_qvars (qregister_pair Q empty_qregister) = distinct_qvars Q" for Q::"'a qvariable"
  using qcompatible_QQcompatible qcompatible_empty by auto
lemma distinct_qvars_concat_unit2[simp]: "distinct_qvars (qregister_pair empty_qregister Q) = distinct_qvars Q" for Q::"'a::finite qvariable"
  using qcompatible_QQcompatible qcompatible_empty qcompatible_sym by blast
lemma distinct_qvars_unit[simp]: "distinct_qvars empty_qregister"
  by (simp add: )

lemma distinct_cvars_swap: "distinct_cvars (cregister_pair Q R) \<Longrightarrow> distinct_cvars (cregister_pair R Q)"
  using ccompatible_sym by blast

section \<open>Indexed variables\<close>

type_synonym cl2 = \<open>cl \<times> cl\<close>
type_synonym qu2 = \<open>qu \<times> qu\<close>

type_synonym 'a c2variable = \<open>('a,cl2) cregister\<close>
type_synonym 'a q2variable = \<open>('a,qu2) qregister\<close>

definition index_cvar :: \<open>bool \<Rightarrow> 'a cvariable \<Rightarrow> 'a c2variable\<close> where
  \<open>index_cvar b x = cregister_chain (if b then cFst else cSnd) x\<close>
definition index_qvar :: \<open>bool \<Rightarrow> 'a qvariable \<Rightarrow> 'a q2variable\<close> where
  \<open>index_qvar b x = qregister_chain (if b then qFst else qSnd) x\<close>

definition index_flip_cvar :: \<open>'a c2variable \<Rightarrow> 'a c2variable\<close> where
  \<open>index_flip_cvar x = cregister_chain cswap x\<close>
definition index_flip_qvar :: \<open>'a q2variable \<Rightarrow> 'a q2variable\<close> where
  \<open>index_flip_qvar x = qregister_chain qswap x\<close>

lemma index_flip_qvar_register_pair[simp]: \<open>index_flip_qvar (qregister_pair Q R) = qregister_pair (index_flip_qvar Q) (index_flip_qvar R)\<close>
  unfolding index_flip_qvar_def
  apply (cases \<open>qcompatible Q R\<close>)
  by (simp_all add: qregister_chain_pair)

lemma index_flip_qvar_chain[simp]: \<open>index_flip_qvar (qregister_chain Q R) = qregister_chain (index_flip_qvar Q) R\<close>
  unfolding index_flip_qvar_def
  by (simp add: qregister_chain_assoc)

lemma index_flip_qvar_Fst[simp]: \<open>index_flip_qvar qFst = qSnd\<close>
  unfolding index_flip_qvar_def
  by (simp add: qcompatible_Fst_Snd qcompatible_sym qregister_chain_pair_Fst qswap_def)

lemma index_flip_qvar_Snd[simp]: \<open>index_flip_qvar qSnd = qFst\<close>
  by (simp add: index_flip_qvar_def qcompatible_Fst_Snd qcompatible_sym qregister_chain_pair_Snd qswap_def)

definition index_flip_mem2 :: "qu2 \<Rightarrow> qu2" where \<open>index_flip_mem2 = (\<lambda>(x,y). (y,x))\<close>

definition swap_cvariables_mem2 :: "'a c2variable \<Rightarrow> 'a c2variable \<Rightarrow> (cl2 \<Rightarrow> cl2)" where
  \<open>swap_cvariables_mem2 x y m = apply_cregister_total (cregister_pair x y) (\<lambda>(a,b). (b,a)) m\<close>

definition swap_variables_qvars :: \<open>'a q2variable \<Rightarrow> 'a q2variable \<Rightarrow> 'b q2variable \<Rightarrow> 'b q2variable\<close> where
  \<open>swap_variables_qvars Q Q' R = 
    qregister_chain (transform_qregister (apply_qregister (qregister_pair Q Q') swap_ell2)) R\<close>

section \<open>Unsorted\<close>


(* axiomatization lift_pure_state :: \<open>('a,'b) qregister \<Rightarrow> 'a ell2 \<Rightarrow> 'b ell2\<close> *)


section \<open>ML code\<close>

ML_file "prog_variables.ML"


section \<open>Syntax\<close>


section \<open>Simprocs\<close>

(* A simproc that utters warnings whenever the simplifier tries to prove a distinct_qvars statement with distinct, explicitly listed variables but can't *)
(* syntax "_declared_qvars" :: "variable_list_args \<Rightarrow> bool" ("declared'_qvars \<lbrakk>_\<rbrakk>")
syntax "_declared_qvars" :: "variable_list_args \<Rightarrow> bool" ("declared'_qvars [|_|]") *)
(* LEGACY *)
abbreviation (input) \<open>declared_qvars Q \<equiv> qregister Q\<close>

(* parse_translation \<open>[("_declared_qvars", Prog_Variables.declared_qvars_parse_tr)]\<close> *)

(* simproc_setup warn_declared_qvars ("variable_name q") = Prog_Variables.warn_declared_qvars_simproc *)

(* simproc_setup index_var ("index_var lr v") = Prog_Variables.index_var_simproc *)
(* simproc_setup index_flip_var ("index_flip_var v") = Prog_Variables.index_flip_var_simproc *)

(* Simproc that rewrites a `qregister_conversion F G` into an index-register.
   (Index-registers are registers build from chain, pair, Fst, Snd.) *)

(* A hint to the simplifier with the meaning:
    - A is a term of the form x>>Q
    - Q,R are registers
    - Q \<le> R
    - The whole term should be rewritten into x'>>R for some x'
  Rewriting the term is done by the simproc TODO declared below.
*)
definition "register_conversion_hint R A = A" (* LEGACY *)
lemma register_conversion_hint_cong[cong]: "A=A' \<Longrightarrow> register_conversion_hint R A = register_conversion_hint R A'" by simp

(* Simproc that rewrites terms of the form `register_conversion_hint G (apply_qregister F a)` into
  `apply_qregister target (apply_qregister (qregister_conversion \<dots>) A)` for suitable \<dots> *)
simproc_setup register_conversion_hint (\<open>register_conversion_hint G (apply_qregister F a)\<close> | \<open>register_conversion_hint G (apply_qregister_space F S)\<close>) =
  \<open>fn m => fn ctxt => fn ct => let
    (* val _ = \<^print> ct *)
    val target = ct |> Thm.dest_arg1
    val conv = (Prog_Variables.apply_qregister_conversion_conv ctxt target |> Conv.arg_conv)
        then_conv Conv.rewr_conv @{thm register_conversion_hint_def[THEN eq_reflection]}
    in \<^try>\<open>SOME (conv ct) catch e => NONE\<close> end\<close>

(* lemma register_conversion_hint_solve[simp]: 
  \<open>register_conversion_hint R (apply_qregister Q x) = apply_qregister R (apply_qregister (qregister_conversion Q R) x)\<close>
  if \<open>REGISTER_SOLVE (qregister_le Q R)\<close>
   *)

section \<open>Cleanup\<close>

end
