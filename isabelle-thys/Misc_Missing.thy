theory Misc_Missing
  imports Main Universe "HOL-Library.Z2" "HOL-Library.FuncSet" "HOL-Library.Cardinality" Registers.Misc
begin

section \<open>Misc\<close>

lemma inj_comp[simp]: "inj ((\<circ>) f :: ('a\<Rightarrow>'b) \<Rightarrow> ('a\<Rightarrow>'c)) = inj f"
proof (rule; rule injI)
  assume inj: "inj ((\<circ>) f :: ('a\<Rightarrow>'b) \<Rightarrow> ('a\<Rightarrow>'c))"
  fix x y
  assume "f x = f y"
  then have "f o (\<lambda>_::'a. x) = f o (\<lambda>_. y)" by auto
  with inj have "(\<lambda>_::'a. x) = (\<lambda>_. y)" unfolding inj_def by auto
  then show "x = y" by metis
next
  assume inj: "inj f"
  fix x y  :: "'a\<Rightarrow>'b"
  assume "f \<circ> x = f \<circ> y"
  then have "f (x a) = f (y a)" for a
    unfolding o_def by metis
  with inj have "x a = y a" for a
    unfolding inj_def by auto
  then show "x = y" by auto
qed

lemma surj_comp[simp]: "surj ((\<circ>) f :: ('a\<Rightarrow>'b) \<Rightarrow> ('a\<Rightarrow>'c)) = surj f"
proof (rule)
  assume surj: "surj ((\<circ>) f :: ('a\<Rightarrow>'b) \<Rightarrow> ('a\<Rightarrow>'c))"
  {fix y :: 'c
  from surj obtain g :: "'a\<Rightarrow>'b" where "f o g = (\<lambda>_. y)"
    unfolding surj_def by metis
  then have "f (g undefined) = y" unfolding o_def by metis
  then have "\<exists>x. f x = y" by metis}
  then show "surj f" unfolding surj_def by metis
next
  assume "surj f"
  then have 1: "f \<circ> Hilbert_Choice.inv f = id"
    using surj_iff by auto
  {fix g :: "'a\<Rightarrow>'c"
    from 1 have "f \<circ> (Hilbert_Choice.inv f o g) = g" unfolding o_assoc by auto
    then have "\<exists>h. f o h = g" by auto}
  then show "surj ((\<circ>) f :: ('a\<Rightarrow>'b) \<Rightarrow> ('a\<Rightarrow>'c))"
    unfolding surj_def by metis
qed

lemma bij_comp[simp]: "bij ((\<circ>) f) = bij f" 
  unfolding bij_def by simp

class xor_group = ab_group_add +
  assumes xor_cancel[simp]: "x + x = 0" begin

lemma uminus_id[simp]: "-x = x"
  using xor_cancel
  by (metis group.left_cancel local.add.group_axioms local.right_minus)

lemma minus_is_plus[simp]: "x - y = x + y"
  using xor_cancel
  by (metis add_assoc local.add_0_right local.diff_add_cancel)

end


section \<open>Type bit\<close>


setup_lifting type_definition_bit

(* Needed after setup_lifting since otherwise code generation breaks, see the following "value" command *)
code_datatype "0::bit" "1::bit"
value [nbe] "0\<noteq>(1::bit)"

(* instantiation bit :: field begin
lift_definition times_bit :: "bit \<Rightarrow> bit \<Rightarrow> bit" is "(&)".
lift_definition plus_bit :: "bit \<Rightarrow> bit \<Rightarrow> bit" is "(\<noteq>)".
lift_definition zero_bit :: bit is "False".
lift_definition one_bit :: bit is "True".
definition[simp]: "uminus_bit (x::bit) = x"
definition[simp]: "minus_bit = ((+) :: bit\<Rightarrow>_\<Rightarrow>_)"
definition[simp]: "inverse_bit (x::bit) = x"
definition[simp]: "divide_bit = (( * ) :: bit\<Rightarrow>_\<Rightarrow>_)"
instance by intro_classes (transfer; auto)+
end *)

derive universe bit


(* lemma bit_cases[cases type:bit]: "(x=0 \<Longrightarrow> P) \<Longrightarrow> (x=1 \<Longrightarrow> P) \<Longrightarrow> P" for x :: bit (* bit.exhaust *)
  by (metis (full_types) Rep_bit_inverse one_bit.abs_eq zero_bit.abs_eq) *)
(* lemma bit_two[simp]: "(2::bit) = 0" (* bit_numeral_even *)
  by (metis add_cancel_left_right bit.exhaust one_add_one)  *)

(* This rule makes the simplifier loop in Isabelle2021-1. Check if that's still the case. If not, add [simp] and remove the special cases below. *)
lemma bit_eq_x: "((a=x) = (b=x)) = (a=b)" for a b x :: bit
  apply transfer by auto
(* These rules are a replacement for bit_eq_x[simp] in several important cases *)
lemma bit_eq_x_conj1[simp]: \<open>((a=x) = (b=x)) \<and> P \<longleftrightarrow> (a=b) \<and> P\<close> for a b x :: bit
  apply transfer by auto
lemma bit_eq_x_conj2[simp]: \<open>P \<and> ((a=x) = (b=x)) \<longleftrightarrow> P \<and> (a=b)\<close> for a b x :: bit
  apply transfer by auto
lemma bit_eq_x_not[simp]: \<open>\<not> ((a=x) = (b=x)) \<longleftrightarrow> \<not> (a=b)\<close> for a b x :: bit
  apply transfer by auto
lemma bit_eq_x_imp1[simp]: \<open>(((a=x) = (b=x)) \<longrightarrow> P) \<longleftrightarrow> ((a=b) \<longrightarrow> P)\<close> for a b x :: bit
  apply transfer by auto
lemma bit_eq_x_imp2[simp]: \<open>(P \<longrightarrow> ((a=x) = (b=x))) \<longleftrightarrow> (P \<longrightarrow> (a=b))\<close> for a b x :: bit
  apply transfer by auto
lemma bit_eq_x_iff1[simp]: \<open>(((a=x) = (b=x)) \<longleftrightarrow> P) \<longleftrightarrow> ((a=b) \<longleftrightarrow> P)\<close> for a b x :: bit
  apply transfer by auto
lemma bit_eq_x_iff2[simp]: \<open>(P \<longleftrightarrow> ((a=x) = (b=x))) \<longleftrightarrow> (P \<longleftrightarrow> (a=b))\<close> for a b x :: bit
  apply transfer by auto

(* To check whether we loop if we add [simp] to bit_eq_x *)
lemma \<open>a + b + b = a\<close> for a b :: bit
  apply simp?
  oops


lemma bit_neq: "(a \<noteq> b) = (a = b+1)" for a b :: bit
  apply (cases a rule:bit.exhaust; cases b rule:bit.exhaust) by auto

(* declare [[coercion "\<lambda>b::bit. if b=0 then (0::nat) else 1"]] *)

lemma bit_plus_1_eq[simp]: "(a+1=b) = (a=b+1)" for a b :: bit
  by auto

lemma bit_plus_2y[simp]: "(x + y) + y = x" for x :: bit
  apply (cases y) by auto

definition (in zero_neq_one) of_bit :: "bit \<Rightarrow> 'a"
  where "of_bit b = (if b=0 then 0 else 1)"

lemma UNIV_bit: "(UNIV::bit set) = {0,1}" by auto

(* Already defined in Registers.Misc *)
(* instantiation bit :: enum begin
definition "enum_bit = [0::bit,1]"
definition "enum_all_bit P \<longleftrightarrow> P (0::bit) \<and> P 1"
definition "enum_ex_bit P \<longleftrightarrow> P (0::bit) \<or> P 1"
instance apply intro_classes
  unfolding enum_bit_def enum_all_bit_def enum_ex_bit_def 
     apply auto
  using bit.exhaust apply metis
  using bit.exhaust by metis
end *)

(* instantiation bit :: equal begin
lift_definition equal_bit :: "bit \<Rightarrow> bit \<Rightarrow> bool" is "HOL.equal :: bool \<Rightarrow> bool \<Rightarrow> bool" .
instance apply intro_classes 
  apply transfer by (rule equal_eq)
end *)

instance bit :: xor_group
  apply intro_classes by auto

lemma SUP_UNIV_bit_expand: "(SUP b\<in>UNIV. A b) = A 0 \<squnion> A 1" for A :: \<open>bit \<Rightarrow> _ :: complete_lattice\<close>
  by (simp add: UNIV_bit sup_commute)

section \<open>Code\<close>

lemma pat_lambda_conv_aux: \<comment> \<open>Helper for ML function pat_lambda_conv\<close>
  shows "term \<equiv> (\<lambda>_. term ())"
  by simp

lemma eq_reflection_swap: "a = b \<Longrightarrow> b\<equiv>a" by auto

lemma append_list_tac_aux: \<comment> \<open>Helper lemma for append_list_tac\<close>
  assumes "x = b@c"
  shows "a#x = (a#b)@c"
  by (simp add: assms)

lemma match_list_tac_aux1: \<comment> \<open>Helper lemma for match_list_tac\<close>
  assumes "x = y"
  shows "a#x = a#y"
  using assms by simp

lemma match_list_tac_aux2: \<comment> \<open>Helper lemma for match_list_tac\<close>
  assumes "x@z = y"
  shows "(a#x)@z = a#y"
  using assms by simp

lemma match_list_tac_aux3: \<comment> \<open>Helper lemma for match_list_tac\<close>
  assumes "z = y"
  shows "[]@z = y"
  using assms by simp

ML_file "misc.ML"

(* TODO remove *)
schematic_goal xxx: "[] @ [?a,?b] @ ?c @ [?x,?y] = [1,2,4,5]"
  by (tactic \<open>Misc.match_list_tac \<^context> 1\<close>)
print_theorems

(* TODO remove *)
schematic_goal "?x = [1,2] @ [3,4]" and "?x = abc"
  apply (tactic \<open>Misc.append_list_tac \<^context> 1\<close>)
  oops


lemma sum_prod_swap:
  fixes g :: "'a\<Rightarrow>'b\<Rightarrow>'c::comm_ring_1"
  assumes "finite A"
  assumes "\<And>x. finite (B x)"
  shows "(\<Sum>f\<in>Pi\<^sub>E A B. \<Prod>x\<in>A. g x (f x)) = (\<Prod>x\<in>A. \<Sum>y\<in>B x. g x y)"
  using \<open>finite A\<close> 
proof induction
  case empty
  then show ?case by auto
next
  case (insert x F)
  define \<pi> where "\<pi> = (\<lambda>(y::'b,f). f(x:=y))"
  have \<pi>: "bij_betw \<pi> (B x \<times> Pi\<^sub>E F B) (Pi\<^sub>E (insert x F) B)"
    apply (rule bij_betwI[where g="\<lambda>f. (f x, f(x:=undefined))"])
    unfolding \<pi>_def
    (* Sledgehammer proofs *)
    using PiE_fun_upd apply fastforce
    apply (simp add: PiE_mem fun_upd_in_PiE local.insert(2))
    using local.insert(2) apply fastforce
    by simp
  have "(\<Sum>f\<in>Pi\<^sub>E (insert x F) B. \<Prod>x'\<in>insert x F. g x' (f x'))
      = (\<Sum>(y,f)\<in>B x \<times> Pi\<^sub>E F B. \<Prod>x'\<in>insert x F. g x' (if x'=x then y else f x'))"
    apply (subst sum.reindex_bij_betw[where h=\<pi>, symmetric])
     apply (fact \<pi>)
    by (simp add: \<pi>_def case_prod_beta fun_upd_def)
  also have "\<dots> = (\<Sum>(y,f)\<in>B x \<times> Pi\<^sub>E F B. 
                     g x y * (\<Prod>x'\<in>F. g x' (f x')))"
  proof -
    have *: "(\<Prod>x'\<in>F. g x' (if x' = x then y else f x')) = (\<Prod>x'\<in>F. g x' (f x'))" 
      for f y
      apply (rule prod.cong)
       apply simp
      using insert by auto
    show ?thesis
      apply (subst prod.insert)
      using insert * by auto
  qed
  also have "\<dots> = (\<Sum>y\<in>B x. \<Sum>f\<in>Pi\<^sub>E F B. g x y * (\<Prod>x'\<in>F. g x' (f x')))"
    by (rule sum.cartesian_product[symmetric])
  also have "\<dots> = (\<Sum>y\<in>B x. g x y * (\<Sum>f\<in>Pi\<^sub>E F B. \<Prod>x'\<in>F. g x' (f x')))"
    apply (subst sum_distrib_left) by (rule refl)
  also have "\<dots> = (\<Sum>y\<in>B x. g x y * (\<Prod>x'\<in>F. \<Sum>y'\<in>B x'. g x' y'))"
    using insert by simp
  also have "\<dots> = (\<Sum>y\<in>B x. g x y) * (\<Prod>x'\<in>F. \<Sum>y'\<in>B x'. g x' y')"
    by (rule sum_distrib_right[symmetric])
  also have "\<dots> = (\<Prod>x'\<in>insert x F. \<Sum>y\<in>B x'. g x' y)"
    apply (rule prod.insert[symmetric])
    using insert by simp_all
  finally show ?case
    by -
qed

definition "regular_betw_n f A B n \<longleftrightarrow> n\<noteq>0 \<and> f ` A = B \<and> (\<forall>y\<in>B. card (f -` {y} \<inter> A) = n)"
definition "regular_betw f A B \<longleftrightarrow> (\<exists>n. regular_betw_n f A B n)"

lemma regular_betwI:
  assumes "n\<noteq>0"
  assumes "f ` A = B"
  assumes "\<And>y. y\<in>B \<Longrightarrow> card (f -` {y} \<inter> A) = n"
  shows "regular_betw f A B"
  using assms unfolding regular_betw_n_def regular_betw_def by auto

lemma regular_betw_finite:
  assumes "regular_betw f A B"
  shows "finite A \<longleftrightarrow> finite B"
proof
  assume "finite A"
  then show "finite B"
    using assms unfolding regular_betw_def regular_betw_n_def by blast
next
  from assms obtain n where reg_n: "regular_betw_n f A B n"
    unfolding regular_betw_def by auto
  then have finite_y: "finite (f -` {y} \<inter> A)" if "y\<in>B" for y
    unfolding regular_betw_n_def using that apply auto
    by (metis card.infinite not_gr0)
  assume "finite B"
  have "A = (\<Union>y\<in>B. f -` {y} \<inter> A)"
    using reg_n unfolding regular_betw_n_def by auto
  moreover have "finite \<dots>"
    using \<open>finite B\<close> finite_y by (rule finite_UN_I)
  ultimately show "finite A"
    by simp
qed

lemma regular_betw_n_card:
  assumes "regular_betw_n f A B n"
  shows "card A = n * card B"
proof (cases "finite B")
  case True
  have "A = (\<Union>y\<in>B. f -` {y} \<inter> A)"
    using assms unfolding regular_betw_n_def by auto
  also have "card \<dots> = (\<Sum>y\<in>B. card (f -` {y} \<inter> A))"
    apply (rule card_UN_disjoint)
    using True assms apply (auto simp: regular_betw_n_def)
    using card.infinite by force
  also have "\<dots> = (\<Sum>y\<in>B. n)"
    using True assms by (auto simp: regular_betw_n_def)
  also have "\<dots> = n * card B"
    using True by simp
  finally show ?thesis .
next
  case False
  then have B: "card B = 0" by simp
  from False have "infinite A"
    using regular_betw_finite assms regular_betw_def by metis
  then have A: "card A = 0" by simp
  from A B show ?thesis by simp
qed

lemma card_extensional:
  assumes "finite X"
  shows "card (extensional X :: ('a\<Rightarrow>'b) set) = CARD('b) ^ card X"
  using assms
proof induction
  case empty
  then show ?case by simp
next
  case (insert x F)
  have "card (extensional (insert x F) :: ('a\<Rightarrow>'b) set) = card ((UNIV::'b set) \<times> (extensional F::('a\<Rightarrow>'b) set))"
    apply (rule bij_betw_same_card[where f="\<lambda>f. (f x, f(x:=undefined))"])
    apply (rule bij_betwI[where g="\<lambda>(y,f). f(x:=y)"])
    apply auto
    using extensional_arb local.insert(2) by fastforce
  also have "\<dots> = CARD('b) * card (extensional F::('a\<Rightarrow>'b) set)"
    using card_cartesian_product by blast
  also have "\<dots> = CARD('b) * CARD('b) ^ card F"
    unfolding insert by auto
  also have "\<dots> = CARD('b) ^ (card F + 1)"
    by auto
  also have "\<dots> = CARD('b) ^ card (insert x F)"
    using insert by auto
  finally show ?case
    by -
qed

lemma reindex_regular:
  fixes i :: "'x \<Rightarrow> 'y::finite"
  assumes [simp]: "inj i"
  shows "regular_betw (\<lambda>f x. (f (i x)) :: 'z::finite) UNIV UNIV"
proof (rule regular_betwI)
  show \<open>surj (\<lambda>f x. f (i x))\<close>
    by (rule surjI[where f="\<lambda>f y. f (Hilbert_Choice.inv i y)"], auto)
  define n where "n = CARD('z) ^ card (- range i)"
  show "n \<noteq> 0"
    unfolding n_def by auto
  fix g :: "'x \<Rightarrow> 'z"
  have "card ((\<lambda>f x. f (i x)) -` {g}) = card (extensional (- range i) :: ('y\<Rightarrow>'z) set)"
    apply (rule bij_betw_same_card[where f="(\<lambda>f::'y\<Rightarrow>'z. restrict f (- range i))"])
    apply (rule bij_betwI[where g="\<lambda>(f::'y\<Rightarrow>'z) (y::'y). if y\<in>range i then g (Hilbert_Choice.inv i y) else f y"])
    using ext[rule del]
       apply (auto intro!: ext)
    using extensional_arb by fastforce
  also have "\<dots> = n"
    apply (subst card_extensional) unfolding n_def by simp_all
  finally show "card ((\<lambda>f x. f (i x)) -` {g} \<inter> UNIV) = n"
    by simp
qed


lemma Collect_UNIV: "Collect P = UNIV \<longleftrightarrow> (\<forall>x. P x)"
  by auto

lemma local_defE: "(\<And>x. x=y \<Longrightarrow> P) \<Longrightarrow> P" by metis

end
