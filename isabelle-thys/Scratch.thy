theory Scratch
  imports QRHL
 (* "HOL-ex.Sketch_and_Explore" *) 
(* "HOL-Eisbach.Eisbach" *)
QRHL_Operations 
begin

ML \<open>

\<close>

ML \<open>
\<close>


(* Adapted from Sketch_And_Explore *)
ML \<open>

val t = Syntax.read_term (Proof_Context.set_mode Proof_Context.mode_schematic \<^context>)
  "(1::?'a::{one}, undefined::('hello::finite \<times> 'huhu), undefined::'hello)"

val res = Print_Term_Reliably.print_term \<^context> t
val t2 = Syntax.read_term (Proof_Context.set_mode Proof_Context.mode_schematic \<^context>)
res
val eq = t = t2
\<close>


ML \<open>
val t = Syntax.parse_term (Proof_Context.set_mode Proof_Context.mode_schematic \<^context>)
  "(1::'a::{one}, 1::'a )"
val tf = Term.add_tfrees t []
|> map snd |> flat |> map writeln
\<close>


term \<open>\<bottom>\<close>

term Order.bottom








lemma lemma_724698:
  fixes C :: "(bit, qu) qregister" and A :: "(bit, qu) qregister" and B :: "(bit, qu) qregister"
  assumes [register]: \<open>declared_qvars \<lbrakk>C, A, B\<rbrakk>\<close>
  shows "qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q (C::(bit, qu) qregister) \<equiv>\<qq> qregister_chain \<lbrakk>#2.\<rbrakk>\<^sub>q A \<le> \<CC>\<ll>\<aa>[\<parallel>EPR\<parallel> = 1] \<sqinter> (\<CC>\<ll>\<aa>[isometry CNOT] \<sqinter> (apply_qregister \<lbrakk>qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q C, qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q A\<rbrakk>\<^sub>q CNOT* *\<^sub>S (\<CC>\<ll>\<aa>[isometry hadamard] \<sqinter> (apply_qregister (qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q C) hadamard* *\<^sub>S ((let M = computational_basis in \<CC>\<ll>\<aa>[mtotal M] \<sqinter> (\<Sqinter>z. let P = apply_qregister (qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q A) (mproj M z) *\<^sub>S \<top> in (let M = computational_basis in \<CC>\<ll>\<aa>[mtotal M] \<sqinter> (\<Sqinter>za. let P = apply_qregister (qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q C) (mproj M za) *\<^sub>S \<top> in (\<CC>\<ll>\<aa>[z \<noteq> 1] + \<CC>\<ll>\<aa>[isometry pauliX] \<sqinter> (apply_qregister (qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q B) pauliX* *\<^sub>S ((\<CC>\<ll>\<aa>[za \<noteq> 1] + \<CC>\<ll>\<aa>[isometry pauliZ] \<sqinter> (apply_qregister (qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q B) pauliZ* *\<^sub>S (qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q B \<equiv>\<qq> qregister_chain \<lbrakk>#2.\<rbrakk>\<^sub>q A \<sqinter> (apply_qregister (qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q B) pauliZ *\<^sub>S \<top>)))) \<sqinter> (\<CC>\<ll>\<aa>[za = 1] + qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q B \<equiv>\<qq> qregister_chain \<lbrakk>#2.\<rbrakk>\<^sub>q A) \<sqinter> (apply_qregister (qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q B) pauliX *\<^sub>S \<top>)))) \<sqinter> (\<CC>\<ll>\<aa>[z = 1] + (\<CC>\<ll>\<aa>[za \<noteq> 1] + \<CC>\<ll>\<aa>[isometry pauliZ] \<sqinter> (apply_qregister (qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q B) pauliZ* *\<^sub>S (qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q B \<equiv>\<qq> qregister_chain \<lbrakk>#2.\<rbrakk>\<^sub>q A \<sqinter> (apply_qregister (qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q B) pauliZ *\<^sub>S \<top>)))) \<sqinter> (\<CC>\<ll>\<aa>[za = 1] + qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q B \<equiv>\<qq> qregister_chain \<lbrakk>#2.\<rbrakk>\<^sub>q A)) \<sqinter> P + - P)) \<sqinter> P + - P)) \<sqinter> (apply_qregister (qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q C) hadamard *\<^sub>S \<top>))) \<sqinter> (apply_qregister \<lbrakk>qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q C, qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q A\<rbrakk>\<^sub>q CNOT *\<^sub>S \<top>)))) \<div> EPR\<guillemotright>\<lbrakk>qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q A, qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q B\<rbrakk>\<^sub>q"
  apply prepare_for_code

experiment
  fixes C :: "(bit, qu) qregister" and A :: "(bit, qu) qregister" and B :: "(bit, qu) qregister"
  assumes [register]: \<open>declared_qvars \<lbrakk>C, A, B\<rbrakk>\<close>
begin

ML \<open>
Prog_Variables.
\<close>


end


ML\<open>open QRHL_Operations\<close>

ML \<open>
get_thms \<^context> "refl"
\<close>


ML \<open>
QRHL_Operations.thms_as_subgoals (\<^context>, "refl")
\<close>


ML \<open>
val ctxt = \<^context> |> Config.put Printer.show_types true
val _ = Syntax.string_of_term ctxt \<^term>\<open>1=2\<close> |> writeln
\<close>

thm HOL.refl
thm refl
term refl

thm conjI
thm HOL.conjI

declare[[show_types]]


lemma xxx[simp]: \<open>is_Proj (selfbutterket c')\<close>
  sledgehammer
  by (simp add: butterfly_is_Proj)
  try0
  by -


lemma \<open>Proj (selfbutterket c' *\<^sub>S \<top>) = selfbutterket c'\<close>
  by (simp add: Proj_on_own_range)

  apply simp

lemma \<open>(SUP x\<in>Y. f x) \<le> (Z :: _ ell2 ccsubspace)\<close>

no_notation m_inv ("inv\<index> _" [81] 80)
unbundle no_vec_syntax
unbundle jnf_notation
hide_const (open) Finite_Cartesian_Product.mat
hide_const (open) Finite_Cartesian_Product.vec

derive (eq) ceq bit
derive (compare) ccompare bit
derive (dlist) set_impl bit


ML Sign.parse_translation

lemma
  fixes a b c
  assumes t[variable]: \<open>qregister (\<lbrakk>a,b,c\<rbrakk> :: (bit*bit*bit) qvariable)\<close>
  shows True
proof -
  define CNOT' where \<open>CNOT' = apply_qregister \<lbrakk>a,c \<mapsto> a,b,c\<rbrakk> CNOT\<close>

  have \<open>apply_qregister \<lbrakk>a,b\<rbrakk> CNOT o\<^sub>C\<^sub>L apply_qregister \<lbrakk>a,c\<rbrakk> CNOT = 
        apply_qregister \<lbrakk>a,c\<rbrakk> CNOT o\<^sub>C\<^sub>L apply_qregister \<lbrakk>a,b\<rbrakk> CNOT\<close>
    apply prepare_for_code
    by normalization

  have \<open>CNOT' *\<^sub>V ket (1,1,1) = (ket (1,1,0) :: (bit*bit*bit) ell2)\<close>
    unfolding CNOT'_def
    apply prepare_for_code
    by normalization


  oops



ML \<open>open Prog_Variables\<close>

(* TEST *)
lemma
  fixes a b c
  assumes t[variable]: \<open>qregister (\<lbrakk>a,b,c\<rbrakk> :: (bit*bit*bit) qvariable)\<close>
  shows True
proof -
  define CNOT' where \<open>CNOT' = apply_qregister \<lbrakk>a,c \<mapsto> a,b,c\<rbrakk> CNOT\<close>
  have \<open>apply_qregister \<lbrakk>a,b\<rbrakk> CNOT o\<^sub>C\<^sub>L apply_qregister \<lbrakk>a,c\<rbrakk> CNOT = 
        apply_qregister \<lbrakk>a,c\<rbrakk> CNOT o\<^sub>C\<^sub>L apply_qregister \<lbrakk>a,b\<rbrakk> CNOT\<close>
    apply (simp add: join_registers)
    oops


(* (* TODO keep? *)
lemma qregister_chain_unit_right[simp]: \<open>qregister F \<Longrightarrow> qregister_chain F qvariable_unit = qvariable_unit\<close>
  by (simp add: qvariable_unit_def)
lemma qregister_chain_unit_left[simp]: \<open>qregister F \<Longrightarrow> qregister_chain qvariable_unit F = qvariable_unit\<close>
  by (simp add: qvariable_unit_def) *)


(* TODO keep? *)
lemma qregister_conversion_chain:
  assumes \<open>qregister_le F G\<close> \<open>qregister_le G H\<close>
  shows \<open>qregister_chain (qregister_conversion G H) (qregister_conversion F G) = qregister_conversion F H\<close>
  using assms unfolding qregister_le_def apply (transfer fixing: F G H) apply transfer
  by (auto intro!: ext qregister_conversion_raw_register simp: f_inv_into_f range_subsetD)


(* TODO keep? *)
lemma permute_and_tensor1_cblinfun_butterfly: 
  fixes f :: \<open>_::finite \<Rightarrow> _::finite\<close>
  assumes [simp]: \<open>bij f\<close> \<open>\<And>x y. R x y\<close>
  shows \<open>permute_and_tensor1_cblinfun f R (butterket a b) = butterket (inv f a) (inv f b)\<close>
proof (rule equal_ket, rule Rep_ell2_inject[THEN iffD1], rule ext)
  fix i j
  have \<open>Rep_ell2 (permute_and_tensor1_cblinfun f R (butterket a b) \<cdot> ket i) j = 
          Rep_ell2 ((ket b \<bullet>\<^sub>C ket (f i)) *\<^sub>C ket a) (f j)\<close>
    by auto
  also have \<open>\<dots> = (if b=f i then 1 else 0) * (if a=f j then 1 else 0)\<close>
    by (auto simp add: scaleC_ell2.rep_eq ket.rep_eq)
  also have \<open>\<dots> = (if inv f b=i then 1 else 0) * (if inv f a=j then 1 else 0)\<close>
    by (smt (verit, del_insts) assms(1) assms(2) bij_inv_eq_iff)
  also have \<open>\<dots> = Rep_ell2 ((ket (inv f b) \<bullet>\<^sub>C ket i) *\<^sub>C ket (inv f a)) j\<close>
    by (simp add: scaleC_ell2.rep_eq ket.rep_eq)
  also have \<open>\<dots> = Rep_ell2 (butterket (inv f a) (inv f b) \<cdot> ket i) j\<close>
    by auto
  finally show \<open>Rep_ell2 (permute_and_tensor1_cblinfun f R (butterket a b) \<cdot> ket i) j
                   = Rep_ell2 (butterket (inv f a) (inv f b) \<cdot> ket i) j\<close>
    by -
qed

(* TODO: to bounded operators *)
declare enum_idx_correct[simp]


