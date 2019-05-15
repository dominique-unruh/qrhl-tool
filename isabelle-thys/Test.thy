theory Test
  imports 
  CryptHOL.Cyclic_Group "HOL-Eisbach.Eisbach_Tools"  
(* Cert_Codegen *)
(* Hashed_Terms Extended_Sorry *)
QRHL.QRHL
Main
(* TestEx2 *)
(*   keywords
    "relift_definition" :: thy_goal
 *)
begin

hide_const (open) Order.top

variables classical a :: bit and quantum A :: bit begin
ML \<open>
Weakest_Precondition.get_wp true 
            \<^term>\<open>measurement \<lbrakk>var_a\<rbrakk> \<lbrakk>A\<rbrakk> (const_expression computational_basis)\<close> (* program *)
            \<^term>\<open>const_expression (top::predicate)\<close> (* post *)
 \<^context>
\<close>
end


ML \<open>
fun check_func (t,cert) = let
  val thm = cert ()
  (* val _ = if Thm.term_of (Thm.rhs_of thm) <> t then raise TERM("check_func",[Thm.prop_of thm, t]) else () *)
  in (Thm.global_cterm_of (Thm.theory_of_thm thm) t, thm) end
\<close>






(* eta_proc bug *)
lemma "(\<lambda>(i, b, s). t (i, b, s)) == x"
  apply simp (* Becomes t = x *)
  oops
schematic_goal x: " (\<lambda>(i, b, s). ?t (i, b, s)) = xxxx"
  (* apply simp *)
  oops



declare[[show_abbrevs=false,eta_contract=false]]

text nothing


hide_const (open) Order.top Polynomial.order
hide_const (open) List_Fusion.generator.generator




(* ML {*
  fun subst_expression_simproc _ ctxt ct = SOME (Encoding.subst_expression_conv ctxt ct) handle CTERM _ => NONE
*} *)

(* simproc_setup subst_expression ("subst_expression (substitute1 x (expression R f')) (expression Q e')") = subst_expression_simproc *)



lemma qrhl_top: "qrhl A p1 p2 (expression Q (\<lambda>z. top))" by (cheat qrhl_top)
lemma qrhl_top': "f \<ge> top \<Longrightarrow> qrhl A p1 p2 (expression Q f)" 
  using qrhl_top
  by (metis (full_types) le_funI top.extremum top_le)

lemma skip:
  assumes "A \<le> B"
  shows "qrhl A [] [] B"
  using skip_rule conseq_rule assms by blast

ML \<open>
fun rename_tac_variant names = SUBGOAL (fn (goal,i) =>
  let val used = Term.add_free_names goal []
      val fresh = Name.variant_list used names
  in
    rename_tac fresh i
  end)
\<close>

method_setup rename_tac_eisbach = \<open>
  Args.term >> (fn name => fn ctxt => 
    case name of Free(name',_) => SIMPLE_METHOD' (rename_tac_variant [name'])
               | _ => (warning ("Could not convert "^Syntax.string_of_term ctxt name^" into a variable name. Not renaming."); Method.succeed)
    )\<close>

(* abbreviation "eval_variable v m \<equiv> eval_variables \<lbrakk>v\<rbrakk> m" *)

(* Converts a goal of the form "expression Q e \<le> expression R f :: 'a expression" 
   with Q,R explicit variable terms into "\<And>x1...xn. C x1...xn \<le> D x1...xn :: 'a" for some C,D. *)
method intro_expression_leq = 
  (rule less_eq_expression_def[THEN iffD2],
   rule le_fun_def[THEN iffD2],
   match conclusion in "\<forall>mem::mem2. C mem" for C \<Rightarrow>
      \<open>rule allI, rename_tac mem, 
       match conclusion in "C mem" for mem \<Rightarrow> 
         \<open>unfold expression_eval[where m=mem],
          (unfold eval_variables_concat[where m=mem] eval_variables_unit[where m=mem])?,
          (unfold case_prod_conv)?,
          ((match conclusion in "PROP (D (eval_variables \<lbrakk>v\<rbrakk> mem))" for D v \<Rightarrow> 
              \<open>rule meta_spec[where x="eval_variables \<lbrakk>v\<rbrakk> mem" and P=D], rename_tac_eisbach v\<close>)+)?
         \<close>
      \<close>
  )[1]

method print_goal = match conclusion in goal for goal \<Rightarrow> \<open>print_term goal\<close>

method skip = (rule skip, intro_expression_leq)

variables
  classical x :: int and
  classical a :: int and
  classical b :: int and 
  classical c :: int and
  quantum q :: int
begin

lemma
  assumes [simp]: "x\<ge>0"                                                  
  shows "qrhl D [s1,sample \<lbrakk>var_x\<rbrakk> Expr[uniform {0..max x 0}]] [t1,t2,assign \<lbrakk>var_x\<rbrakk> Expr[0]] Expr[Cla[x1\<ge>x2]]"
  using [[show_types]]
  apply (tactic \<open>Weakest_Precondition.wp_seq_tac 1 1 \<^context> 1\<close>)
  apply simp
  by (rule qrhl_top)

lemma test:
  (* assumes "\<And>x y. e x \<le> e' x y" *)
  (* fixes z::"_::preorder" *)
  shows "Expr[z] \<le> Expr[z+0*a]"
  (* apply (insert assms)   *)
  apply intro_expression_leq 
  by auto

lemma
  assumes [simp]: "x\<ge>0"
  shows "qrhl Expr[ Cla[x1=0 \<and> x2=1] ] [qinit \<lbrakk>q\<rbrakk> Expr[ ket 0 ]] [assign \<lbrakk>var_x\<rbrakk> Expr[x-1]] Expr[Cla[x1\<ge>x2]]"
  apply (tactic \<open>Weakest_Precondition.wp_seq_tac 1 1 \<^context> 1\<close>) 
  apply simp
  apply skip
  by simp

end

declare_variable_type G :: "{power,ab_semigroup_mult,inverse}"

axiomatization G::"G cyclic_group" and g::G

(* term "(^^)" *)
axiomatization powG :: "G \<Rightarrow> int \<Rightarrow> G" (infixr "\<^sup>^" 80)
(* locale group_G = cyclic_group G  *)
(* lemma group_G: group_G *)
(* abbreviation "g == generator G" *)

thm cyclic_group.carrier_conv_generator

(* Add to CryptHOL? *)
lemma (in cyclic_group) "finite (carrier G)"
proof -
  from generator obtain n::nat where "\<^bold>g [^] n = inv \<^bold>g" 
    apply atomize_elim by (metis generatorE generator_closed inv_closed)
  then have g1: "\<^bold>g [^] (Suc n) = \<one>"
    by auto
  then have mod: "\<^bold>g [^] m = \<^bold>g [^] (m mod Suc n)" for m
  proof -
    obtain k where "m mod Suc n + Suc n * k = m" apply atomize_elim
      by (metis mod_less_eq_dividend mod_mod_trivial nat_mod_eq_lemma)
    then have "\<^bold>g [^] m = \<^bold>g [^] (m mod Suc n + Suc n * k)" by simp
    also have "\<dots> = \<^bold>g [^] (m mod Suc n)" 
      apply (subst nat_pow_mult[symmetric], rule)
      apply (subst nat_pow_pow[symmetric], rule)
      unfolding g1 by simp
    finally show ?thesis .
  qed
  have "range ((([^])::_\<Rightarrow>nat\<Rightarrow>_) \<^bold>g) \<subseteq> (([^]) \<^bold>g) ` {..<Suc n}"
  proof -
    have "\<^bold>g [^] x \<in> ([^]) \<^bold>g ` {..<Suc n}" for x::nat
      apply (subst mod) by auto
    then show ?thesis by auto
  qed
  then have "finite (range ((([^])::_\<Rightarrow>nat\<Rightarrow>_) \<^bold>g))"
    using finite_surj by auto
  with generator show "finite (carrier G)"
    using finite_subset by blast
qed

lemma (in cyclic_group) m_comm:
  assumes "x : carrier G" and "y : carrier G"
  shows "x \<otimes> y = y \<otimes> x"
proof -
  from generator assms obtain n m :: nat where x:"x=\<^bold>g [^] n" and y:"y=\<^bold>g [^] m" 
    apply atomize_elim by auto
  show ?thesis
    unfolding x y by (simp add: add.commute nat_pow_mult)
qed

(* axiomatization where cyclic_group_G: "cyclic_group G" *)

interpretation G_group: cyclic_group G
  rewrites "x [^]\<^bsub>G\<^esub> n = x \<^sup>^ (n::int)" and "x \<otimes>\<^bsub>G\<^esub> y = x*y" and "\<one>\<^bsub>G\<^esub> = 1" and "generator G = g" 
    and "m_inv G = inverse" and "carrier G = UNIV"
  by (cheat G_group)

definition "keygen = uniform {(g \<^sup>^ x, x) | x::int. x\<in>{0..order G-1}}"
definition "enc h x = uniform {(g\<^sup>^r, h\<^sup>^r * x) | r::int. r\<in>{0..order G-1}}"
definition "dec x c = (let (c1,c2) = c in c2 * c1 \<^sup>^ (-x))"

lemma weight_enc: "weight (enc var_pk1 var_m1) = 1"
  unfolding enc_def
  apply (rule weight_uniform)
  by auto

lemma supp_enc: "supp (enc pk m) = {(g \<^sup>^ r, pk \<^sup>^ r * m) |r::int. r \<in> {0..order G-1}}"
  unfolding enc_def apply (rule supp_uniform) by auto
  (* find_theorems intro supp uniform *)

lemma weight_keygen: "weight keygen = 1"
  unfolding keygen_def
  apply (rule weight_uniform)
  by auto

lemma supp_keygen: "supp keygen = {(g \<^sup>^ x, x) |x::int. x \<in> {0..order G - 1}}"
  unfolding keygen_def apply (rule supp_uniform) by auto

lemma (in monoid) nat_pow_Suc_left: 
  assumes "x \<in> carrier G"
  shows "x [^] Suc n = x \<otimes> (x [^] n)"
  apply (induction n)
  using assms apply simp
  subgoal premises prems for n
    apply (subst nat_pow_Suc)
    apply (subst prems)
    apply (subst nat_pow_Suc)
    apply (subst m_assoc)
    using assms by auto
  done

lemma (in group) inv_nat_pow:
  assumes "x \<in> carrier G"
  shows "inv x [^] (n::nat) = inv (x [^] n)"
  apply (induction n) 
   apply simp
  apply (subst nat_pow_Suc)
  apply (subst nat_pow_Suc_left)
  using assms by (auto simp: inv_mult_group)

lemma (in group) inv_int_pow:
  assumes "x \<in> carrier G"
  shows "inv x [^] (n::int) = inv (x [^] n)"
  apply (cases n; hypsubst_thin)
   apply (subst int_pow_int)+
  using assms apply (rule inv_nat_pow)
  using assms apply (subst int_pow_neg, simp)+
  apply (subst int_pow_int)+
  by (subst inv_nat_pow, simp_all)


lemma (in cyclic_group) "(\<^bold>g [^] r) [^] -x = (\<^bold>g [^] (-r*x))" for r x :: int
  apply (subst int_pow_pow)
   apply (simp add: nat_pow_pow)
  by auto

(* lemma correct: "(g [^] x) [^] r \oti* m * (g \<^sup>^ r) \<^sup>^ -x = m"  *)

lemma correct: "(g \<^sup>^ x) \<^sup>^ r * m * (g \<^sup>^ r) \<^sup>^ -x = m" 
  apply (subst G_group.int_pow_pow) apply simp
  apply (subst G_group.int_pow_pow) apply simp
  apply (subst G_group.m_comm) 
    apply (auto simp: G_group.inv_int_pow )
  by (metis G_group.int_pow_neg G_group.inv_solve_left UNIV_I mult.commute)

variables classical c :: "G*G" and classical m :: G and classical pksk :: "G*int"
and classical pk :: G and classical sk :: int begin

definition "ElGamal = [sample \<lbrakk>var_pk,var_sk\<rbrakk> Expr[keygen],
           sample \<lbrakk>var_c\<rbrakk> Expr[enc pk m],
           assign \<lbrakk>var_m\<rbrakk> Expr[dec sk c]
          ]"

lemma elgamal_correct [simp]:
  fixes z
  shows "qrhl Expr[Cla[m1=z]] 
          ElGamal
         [] Expr[Cla[m1=z]]"
  unfolding ElGamal_def
  apply (tactic  \<open>Weakest_Precondition.wp_seq_tac 1 0 \<^context> 1\<close>)
  apply (simp add: case_prod_beta dec_def)
  apply (tactic  \<open>Weakest_Precondition.wp_seq_tac 1 0 \<^context> 1\<close>)
  (* unfolding enc_def *)
  (* unfolding  *)
  apply (simp add: weight_enc supp_enc)
  apply (tactic  \<open>Weakest_Precondition.wp_seq_tac 1 0 \<^context> 1\<close>)
  apply (simp add: weight_keygen supp_keygen)
  apply skip
  by (auto simp: correct)


lemma lem1:
  assumes "xxx 1"
  shows "xxx 2"
  by (cheat 1)

lemma lem2:
  assumes "xxx 2"
  shows "xxx 3"
  by (cheat 2)

lemma lem3:
  assumes "xxx 1"
  shows "xxx 3"
  ML_val \<open>@{Isar.goal} |> #goal |> Extended_Sorry.show_oracles\<close>
  apply (rule lem2)  
  ML_val \<open>@{Isar.goal} |> #goal |> Extended_Sorry.show_oracles\<close>
  apply (rule lem1)
  ML_val \<open>@{Isar.goal} |> #goal |> Extended_Sorry.show_oracles\<close>
  by (fact assms)

ML \<open>
(
@{thm lem1} RS @{thm lem2}
)
|>
Thm.proof_body_of (* |> Proofterm.all_oracles_of  *) 
\<close>

lemma skipREMOVE:
  assumes "A \<le> B"
  shows "qrhl A [] [] B"
  by (cheat 1)

lemma elgamal_correct2 [simp]:
  fixes z
  shows "qrhl Expr[Cla[m1=m2]] 
          ElGamal
         [] Expr[Cla[m1=m2]]"
  unfolding ElGamal_def
  apply (tactic  \<open>Weakest_Precondition.wp_seq_tac 1 0 \<^context> 1\<close>)
  apply (simp add: dec_def)
  apply (tactic  \<open>Weakest_Precondition.wp_seq_tac 1 0 \<^context> 1\<close>)
  apply (simp add: weight_enc supp_enc)
  apply (tactic  \<open>Weakest_Precondition.wp_seq_tac 1 0 \<^context> 1\<close>)
  apply (simp add: weight_keygen supp_keygen)
  apply skip
  by (auto simp: correct)
  
lemma elgamal_correct3 [simp]:
  fixes z
  shows "qrhl Expr[Cla[m1=m2]] 
         [] ElGamal Expr[Cla[m1=m2]]"
  unfolding ElGamal_def
  apply (tactic  \<open>Weakest_Precondition.wp_seq_tac 0 1 \<^context> 1\<close>)
  apply (simp add: dec_def case_prod_beta)
  apply (tactic  \<open>Weakest_Precondition.wp_seq_tac 0 1 \<^context> 1\<close>)
  apply (simp add: weight_enc supp_enc case_prod_beta)
  apply (tactic  \<open>Weakest_Precondition.wp_seq_tac 0 1 \<^context> 1\<close>)
  apply (simp add: weight_keygen supp_keygen)
  apply skip
  by (auto simp: correct)
  

ML \<open>
Extended_Sorry.show_oracles @{thm elgamal_correct3}
\<close>


term "variable_concat \<lbrakk>z\<rbrakk> \<lbrakk>x,y\<rbrakk>"

end
