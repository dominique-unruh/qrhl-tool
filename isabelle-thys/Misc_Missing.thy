theory Misc_Missing
  imports Main "HOL-Library.Z2" "HOL-Library.FuncSet" "HOL-Library.Cardinality" 
    (* Missing_Bounded_Operators *) Registers.Misc
    Registers.Axioms_Classical
begin                                                                         

section \<open>Misc\<close>

unbundle lattice_syntax

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

(* derive universe bit *)


(* lemma bit_cases[cases type:bit]: "(x=0 \<Longrightarrow> P) \<Longrightarrow> (x=1 \<Longrightarrow> P) \<Longrightarrow> P" for x :: bit (* bit.exhaust *)
  by (metis (full_types) Rep_bit_inverse one_bit.abs_eq zero_bit.abs_eq) *)
(* lemma bit_two[simp]: "(2::bit) = 0" (* bit_numeral_even *)
  by (metis add_cancel_left_right bit.exhaust one_add_one)  *)

lemma bit_eq_x[simp]: "((a=x) = (b=x)) = (a=b)" for a b x :: bit
  apply transfer by auto

(* Check whether the simplifier loops if we add [simp] to bit_eq_x (was a problem in Isabelle2021-1). *)
lemma \<open>a + b + b = a\<close> for a b :: bit
  apply simp?
  oops

lemma bit_neq: "(a \<noteq> b) = (a = b+1)" for a b :: bit
  by simp

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

lemma inv_comp_eqI: \<open>inv f o g = h\<close> if \<open>inj f\<close> and \<open>g = f o h\<close> for f g
  using that(1) that(2) by fastforce


class eenum = enum +
  fixes enum_nth :: \<open>nat \<Rightarrow> 'a\<close>
  fixes enum_index :: \<open>'a \<Rightarrow> nat\<close>
  assumes enum_nth_enum[simp]: \<open>\<And>i. i < CARD('a) \<Longrightarrow> Enum.enum ! i = enum_nth i\<close>
  assumes enum_nth_invalid: \<open>\<And>i. i \<ge> CARD('a) \<Longrightarrow> enum_nth i = enum_nth 0\<close> (* To get enum_index_nth below *)
  assumes enum_nth_index[simp]: \<open>\<And>a. enum_nth (enum_index a) = a\<close>
  assumes enum_index_bound[simp]: \<open>\<And>a. enum_index a < CARD('a)\<close>

instantiation bit :: eenum begin
definition \<open>enum_index_bit (x::bit) = (if x=1 then 1 else 0 :: nat)\<close>
definition \<open>enum_nth_bit (i::nat) = (if i=1 then 1 else 0 :: bit)\<close>
instance
  apply standard
  by (auto simp: nth_Cons' enum_bit_def enum_index_bit_def enum_nth_bit_def)
end


lemma inj_enum_index[simp]: \<open>inj enum_index\<close>
  by (metis enum_nth_index injI)

lemma bij_betw_enum_index: \<open>bij_betw (enum_index :: 'a::eenum \<Rightarrow> nat) UNIV {..<CARD('a)}\<close>
proof -
  let ?f = \<open>enum_index :: 'a::eenum \<Rightarrow> nat\<close>
  have \<open>range ?f \<subseteq> {..<CARD('a)}\<close>
    by (simp add: image_subsetI)
  moreover have \<open>card (range ?f) = card {..<CARD('a)}\<close>
    by (simp add: card_image)
  moreover have \<open>finite {..<CARD('a)}\<close>
    by simp
  ultimately have \<open>range ?f = {..<CARD('a)}\<close>
    by (meson card_subset_eq)
  then show ?thesis
    by (simp add: bij_betw_imageI)
qed

lemma inj_on_enum_nth[simp]: \<open>inj_on (enum_nth :: _ \<Rightarrow> 'a::eenum) {..<CARD('a)}\<close>
  by (metis (mono_tags, opaque_lifting) bij_betw_enum_index enum_nth_index f_the_inv_into_f_bij_betw inj_on_inverseI)

lemma enum_index_nth: \<open>enum_index (enum_nth i :: 'a::eenum) = (if i < CARD('a) then i else 0)\<close>
  by (metis bij_betw_enum_index enum_nth_index enum_nth_invalid f_the_inv_into_f_bij_betw lessThan_iff linorder_not_le zero_less_card_finite)


instantiation bool :: eenum begin
definition \<open>enum_index_bool x = (if x then 1 else 0 :: nat)\<close>
definition \<open>enum_nth_bool (i::nat) = (i=1)\<close>
instance 
  apply standard
  apply (auto simp: enum_bool_def enum_index_bool_def enum_nth_bool_def)
  by (metis less_2_cases nth_Cons_0)
end

instantiation prod :: (eenum, eenum) eenum begin
definition \<open>enum_index_prod = (\<lambda>(i::'a,j::'b). enum_index i * CARD('b) + enum_index j)\<close>
definition \<open>enum_nth_prod ij = (let i = ij div CARD('b) in if i < CARD('a) then (enum_nth i, enum_nth (ij mod CARD('b))) else (enum_nth 0, enum_nth 0) :: 'a\<times>'b)\<close>
instance
proof standard
  show \<open>i < CARD('a \<times> 'b) \<Longrightarrow> (Enum.enum ! i :: 'a\<times>'b) = enum_nth i\<close> for i
    apply (auto simp: card_UNIV_length_enum[symmetric] enum_nth_enum enum_prod_def product_nth enum_nth_prod_def Let_def)
    using less_mult_imp_div_less by blast+
  show \<open>CARD('a \<times> 'b) \<le> i \<Longrightarrow> enum_nth i = (enum_nth 0 :: 'a\<times>'b)\<close> for i
    by (auto simp: div_less_iff_less_mult enum_nth_prod_def)
  show \<open>enum_nth (enum_index a) = a\<close> for a :: \<open>'a\<times>'b\<close>
    apply (cases a)
    by (auto simp: div_less_iff_less_mult enum_nth_prod_def enum_index_prod_def)
  show \<open>enum_index a < CARD('a \<times> 'b)\<close> for a :: \<open>'a\<times>'b\<close>
    apply (cases a)
    by (auto simp: enum_index_prod_def)
    (* by (metis (no_types, lifting) add_cancel_right_right div_less div_mult_self3 enum_index_bound less_eq_div_iff_mult_less_eq less_not_refl2 linorder_not_less zero_less_card_finite) *)
qed
end


lemma fst_enum_nth: \<open>fst (enum_nth ij :: 'a::eenum\<times>'b::eenum) = enum_nth (ij div CARD('b))\<close>
  by (auto simp: enum_nth_invalid enum_nth_prod_def Let_def)

lemma snd_enum_nth: \<open>snd (enum_nth ij :: 'a::eenum\<times>'b::eenum) = (if ij < CARD('a\<times>'b) then enum_nth (ij mod CARD('b)) else enum_nth 0)\<close>
  apply (auto simp: enum_nth_prod_def Let_def)
  using div_less_iff_less_mult zero_less_card_finite by blast+

lemma enum_index_fst: \<open>enum_index (fst x) = enum_index x div CARD('b)\<close> for x :: \<open>'a::eenum\<times>'b::eenum\<close>
  by (auto simp add: enum_index_prod_def case_prod_beta)
lemma enum_index_snd: \<open>enum_index (snd x) = enum_index x mod CARD('b)\<close> for x :: \<open>'a::eenum\<times>'b::eenum\<close>
  by (auto simp add: enum_index_prod_def case_prod_beta)


lemma enum_nth_injective: \<open>i < CARD('a) \<Longrightarrow> j < CARD('a) \<Longrightarrow> (enum_nth i :: 'a::eenum) = enum_nth j \<longleftrightarrow> i = j\<close>
  by (metis enum_index_nth)

lemma div_leq_simp: \<open>(i div n < m) \<longleftrightarrow> i < n*m\<close> if \<open>n \<noteq> 0\<close> for n m :: nat
  by (simp add: div_less_iff_less_mult ordered_field_class.sign_simps(5) that zero_less_iff_neq_zero)

(* TODO: optionally: specify method, specify which prem *)
attribute_setup remove_prem = \<open>
  Scan.succeed (Thm.rule_attribute [] (fn context => fn thm => let
    val ctxt = Context.proof_of context
    val tac = assume_tac ctxt 1
    in tac thm |> Seq.hd end))\<close>

lemma complement_injective: \<open>- A = - B \<Longrightarrow> A = B\<close> for A B :: \<open>_ :: orthocomplemented_lattice\<close>
  using orthocomplemented_lattice_class.ortho_involution by auto

definition \<open>partial_fun_compatible f g \<longleftrightarrow> (\<forall>x. f x = None \<or> g x = None \<or> f x = g x)\<close>

definition \<open>option_Sup X = the_default None (X-{None})\<close>
definition \<open>partial_fun_Sup F x = option_Sup ((\<lambda>f. f x) ` F)\<close>

lemma partial_fun_compatible_refl[simp]: \<open>partial_fun_compatible f f\<close>
  by (simp add: partial_fun_compatible_def)

lemma option_Sup_empty[simp]: \<open>option_Sup {} = None\<close>
  by (simp add: option_Sup_def)

lemma option_Sup_None[simp]: \<open>option_Sup {None} = None\<close>
  by (simp add: option_Sup_def)

lemma option_Sup_Some[simp]: \<open>option_Sup {Some x} = Some x\<close>
  by (simp add: option_Sup_def)

lemma map_option_option_Sup:
  assumes \<open>inj f\<close>
  shows \<open>map_option f (option_Sup X) = option_Sup (map_option f ` X)\<close>
proof -
  consider (empty) \<open>X = {}\<close> | (1) \<open>card X = 1\<close> | (2) \<open>card X = 2\<close> | (3) \<open>card X \<ge> 3\<close> | (infinite) \<open>infinite X\<close>
    by (metis One_nat_def Suc_1 card_seteq empty_subsetI le0 not_less_eq_eq numeral_nat(3) verit_la_disequality)
  then
  (* The following "easy" case distinction was a surprisingly tricky manual proof. Is there an easier way? *)
  consider (empty) \<open>X = {}\<close> | (none) \<open>X = {None}\<close>
    | (single) x where \<open>X = {Some x}\<close> | (single') x where \<open>X = {None, Some x}\<close> 
    | (multiple) x y where \<open>{Some x, Some y} \<subseteq> X\<close> and \<open>x \<noteq> y\<close>
  proof cases
    case empty
    moreover assume \<open>X = {} \<Longrightarrow> thesis\<close>
    ultimately show thesis
      by simp
  next
    case 1
    then obtain x where \<open>X = {x}\<close>
      using card_1_singletonE by blast
    moreover assume \<open>X = {None} \<Longrightarrow> thesis\<close>
    moreover assume \<open>X = {Some x} \<Longrightarrow> thesis\<close> for x
    ultimately show thesis
      by auto
  next
    case 2
    then obtain x y where X: \<open>X = {x,y}\<close> and \<open>x \<noteq> y\<close> and \<open>y \<noteq> None\<close>
      by (metis card_2_iff doubleton_eq_iff)
    assume single': \<open>X = {None, Some x} \<Longrightarrow> thesis\<close> for x
    assume multiple: \<open>{Some x', Some y'} \<subseteq> X \<Longrightarrow> x' \<noteq> y' \<Longrightarrow> thesis\<close> for x' y'
    show thesis
      apply (cases x; cases y)
      using X  single' multiple
      using \<open>x \<noteq> y\<close>
      by auto 
  next
    case 3
    then obtain x y z where \<open>x \<in> X\<close> and \<open>y \<in> X\<close> and \<open>z \<in> X\<close> and \<open>x \<noteq> y\<close> and \<open>x \<noteq> z\<close> and \<open>y \<noteq> z\<close>
      by (auto simp add: numeral_3_eq_3 card_le_Suc_iff)
    moreover assume multiple: \<open>{Some x', Some y'} \<subseteq> X \<Longrightarrow> x' \<noteq> y' \<Longrightarrow> thesis\<close> for x' y'
    ultimately show thesis
      apply (cases x; cases y; cases z)
      by auto
  next
    case infinite
    then obtain X' where \<open>card X' = 3\<close> and \<open>X' \<subseteq> X\<close>
      using infinite_arbitrarily_large by blast
    then obtain x y z where \<open>x \<in> X'\<close> and \<open>y \<in> X'\<close> and \<open>z \<in> X'\<close> and \<open>x \<noteq> y\<close> and \<open>x \<noteq> z\<close> and \<open>y \<noteq> z\<close>
      by (auto simp add: numeral_3_eq_3 card_Suc_eq)
    moreover assume multiple: \<open>{Some x', Some y'} \<subseteq> X \<Longrightarrow> x' \<noteq> y' \<Longrightarrow> thesis\<close> for x' y'
    then have \<open>{Some x', Some y'} \<subseteq> X' \<Longrightarrow> x' \<noteq> y' \<Longrightarrow> thesis\<close> for x' y'
      using \<open>X' \<subseteq> X\<close> by auto
    ultimately show thesis
      apply (cases x; cases y; cases z)
      by auto
  qed
  then show ?thesis
  proof cases
    case empty
    then show ?thesis by simp
  next
    case none
    then show ?thesis by simp
  next
    case single
    then show ?thesis by simp
  next
    case single'
    then show ?thesis by (simp add: option_Sup_def)
  next
    case multiple
    then have \<open>card (X - {None}) \<noteq> 1\<close>
      by (smt (verit) Diff_eq_empty_iff card_1_singletonE insert_Diff_if insert_absorb insert_iff insert_not_empty option.discI option.inject)
    then have 1: \<open>option_Sup X = None\<close>
      by (simp add: option_Sup_def the_default_def)
    have \<open>{Some (f x), Some (f y)} \<subseteq> map_option f ` X\<close>
      by (metis empty_subsetI imageI insert_subset multiple(1) option.map(2))
    moreover have \<open>f x \<noteq> f y\<close>
      by (simp add: assms inj_eq multiple(2))
    ultimately have \<open>card ((map_option f ` X) - {None}) \<noteq> 1\<close>
      by (smt (verit) Diff_empty Diff_insert0 card_1_singletonE insert_Diff insert_iff insert_subset option.discI option.inject singleton_insert_inj_eq')
    then have 2: \<open>option_Sup (map_option f ` X) = None\<close>
      by (simp add: option_Sup_def the_default_def)
    from 1 2 show ?thesis
      by simp
  qed
qed

definition pairwise_all :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> bool"
  where "pairwise_all R S \<longleftrightarrow> (\<forall>x \<in> S. \<forall>y \<in> S. R x y)"

definition \<open>map_commutant F = {x. \<forall>y\<in>F. x \<circ>\<^sub>m y = y \<circ>\<^sub>m x}\<close>

lemma map_commutant_mult: \<open>a \<circ>\<^sub>m b \<in> map_commutant X\<close> if \<open>a \<in> map_commutant X\<close> and \<open>b \<in> map_commutant X\<close>
  using that 
  apply (auto simp: map_commutant_def comp_update_assoc)
  by (simp flip: comp_update_assoc)

lemma map_commutant_antimono: \<open>X \<subseteq> Y \<Longrightarrow> map_commutant X \<supseteq> map_commutant Y\<close>
  by (auto simp add: map_commutant_def)

lemma double_map_commutant_grows: \<open>X \<subseteq> map_commutant (map_commutant X)\<close>
  by (auto simp add: map_commutant_def)

lemma triple_map_commutant[simp]: \<open>map_commutant (map_commutant (map_commutant X)) = map_commutant X\<close>
  by (auto simp: map_commutant_def)

lemma set_compr_4_image_collect: \<open>{f x y z w |x y z w. P x y z w} = (\<lambda>(x,y,z,w). f x y z w) ` Collect (\<lambda>(x,y,z,w). P x y z w)\<close>
  by (auto simp: image_def)

lemma closedin_vimage:
  assumes \<open>closedin U S\<close>
  assumes \<open>continuous_map T U f\<close>
  shows \<open>closedin T (topspace T \<inter> (f -` S))\<close>
  by (meson assms(1) assms(2) continuous_map_closedin_preimage_eq)

lemma join_forall: \<open>(\<forall>x. P x) \<and> (\<forall>x. Q x) \<longleftrightarrow> (\<forall>x. P x \<and> Q x)\<close>
  by auto

lemma closedin_singleton: 
  assumes \<open>hausdorff T\<close> and \<open>x \<in> topspace T\<close>
  shows \<open>closedin T {x}\<close>
proof -
  obtain U where openU: \<open>openin T (U y)\<close> and x_not_U: \<open>x \<notin> U y\<close> and yU: \<open>y \<in> U y\<close> if \<open>x \<noteq> y\<close> and \<open>y \<in> topspace T\<close> for y
    apply atomize_elim unfolding join_forall apply (rule choice)
    using assms(1)[unfolded hausdorff_def, rule_format, OF assms(2)]
    by auto
  have \<open>topspace T - {x} = (\<Union>y\<in>topspace T - {x}. U y)\<close>
    using yU openU x_not_U apply auto
    using openin_subset by fastforce
  also have \<open>openin T \<dots>\<close>
    using openU by fastforce
  finally have \<open>openin T (topspace T - {x})\<close>
    by -
  then show ?thesis
    using assms(2) closedin_def by blast
qed


lemma option_Sup_insert_None: \<open>{option_Sup {x, None}, None} = {x, None}\<close>
  apply (cases x)
  by (simp_all add: option_Sup_def insert_Diff_if)

lemma map_comp_partial_fun_Sup_right:
  fixes X :: \<open>('a \<rightharpoonup> 'b) set\<close> and a :: \<open>'b \<rightharpoonup> 'c\<close>
  assumes \<open>pairwise_all partial_fun_compatible X\<close>
  shows \<open>a \<circ>\<^sub>m partial_fun_Sup X = partial_fun_Sup (map_comp a ` X)\<close>
proof (rule ext, rename_tac b)
  fix b
  show \<open>(a \<circ>\<^sub>m partial_fun_Sup X) b = partial_fun_Sup ((\<circ>\<^sub>m) a ` X) b\<close>
  proof (cases \<open>(\<lambda>f. f b) ` X = {None} \<or> X = {}\<close>)
    case True
    have \<open>(a \<circ>\<^sub>m partial_fun_Sup X) b = None\<close>
      using True by (auto simp add: partial_fun_Sup_def)
    also have \<open>\<dots> = option_Sup ((a \<circ>\<^sub>m id) ` (\<lambda>f. f b) ` X)\<close>
      using True by auto
    also have \<open>\<dots> = partial_fun_Sup ((\<circ>\<^sub>m) a ` X) b\<close>
      by (simp add: partial_fun_Sup_def image_image map_comp_def)
    finally show ?thesis
      by -
  next
    case False
    then obtain x where \<open>x \<in> X\<close> and \<open>x b \<noteq> None\<close>
      apply atomize_elim apply auto
      by (metis imageI)
    then obtain c where \<open>x b = Some c\<close>
      by blast
    with assms \<open>x \<in> X\<close>
    have fbX: \<open>(\<lambda>f. f b) ` X - {None} = {Some c}\<close>
      apply (auto intro!: image_eqI[of _ _ x] simp: pairwise_all_def partial_fun_compatible_def)
      by fastforce

    have \<open>{(a \<circ>\<^sub>m partial_fun_Sup X) b, None} = (map_comp a id) ` {partial_fun_Sup X b, None}\<close>
      by (simp add: map_comp_def)
    also have \<open>\<dots> = (a \<circ>\<^sub>m id) ` {Some c, None}\<close>
      apply (rule arg_cong[where f=\<open>image (a \<circ>\<^sub>m id)\<close>])
      by (simp add: fbX partial_fun_Sup_def option_Sup_def)
    also have \<open>\<dots> = {a c, None}\<close>
      by simp
    also have \<open>\<dots> = {option_Sup ((a \<circ>\<^sub>m id) ` {Some c, None}), None}\<close>
      by (simp add: option_Sup_insert_None)
    also have \<open>\<dots> = {option_Sup ((a \<circ>\<^sub>m id) ` (insert None ((\<lambda>f. f b) ` X))), None}\<close>
      by (smt (verit, ccfv_threshold) fbX insert_Diff_single insert_commute)
    also have \<open>\<dots> = {option_Sup ((a \<circ>\<^sub>m id) ` (\<lambda>f. f b) ` X), None}\<close>
      by (simp add: option_Sup_def)
    also have \<open>\<dots> = {partial_fun_Sup ((\<circ>\<^sub>m) a ` X) b, None}\<close>
      by (simp add: partial_fun_Sup_def image_image map_comp_def)
    finally  show \<open>(a \<circ>\<^sub>m partial_fun_Sup X) b = partial_fun_Sup ((\<circ>\<^sub>m) a ` X) b\<close>
      by (metis doubleton_eq_iff)
  qed
qed

lemma option_Sup_map_empty_image[simp]: \<open>option_Sup (Map.empty ` X) = None\<close>
proof (cases \<open>X = {}\<close>)
  case True
  then show ?thesis
    by (simp add: option_Sup_def)
next
  case False
  then have \<open>Map.empty ` X = {None :: 'a option}\<close>
    by auto
  then show ?thesis
    by simp
qed

lemma map_comp_partial_fun_Sup_left:
  fixes X :: \<open>('a \<rightharpoonup> 'b) set\<close> and a :: \<open>'c \<rightharpoonup> 'a\<close>
  shows \<open>partial_fun_Sup X \<circ>\<^sub>m a = partial_fun_Sup ((\<lambda>x. x \<circ>\<^sub>m a) ` X)\<close>
proof (rule ext)
  fix b
  show \<open>(partial_fun_Sup X \<circ>\<^sub>m a) b = partial_fun_Sup ((\<lambda>x. x \<circ>\<^sub>m a) ` X) b\<close>
    apply (cases \<open>a b\<close>)
    by (simp_all add: partial_fun_Sup_def[abs_def] image_image)
qed

lemma map_commutant_Sup_closed:
  fixes X Z
  defines \<open>\<FF> \<equiv> map_commutant Z\<close>
  assumes \<open>X \<subseteq> \<FF>\<close>
  assumes compat: \<open>pairwise_all partial_fun_compatible X\<close>
  shows \<open>partial_fun_Sup X \<in> \<FF>\<close>
proof (unfold \<FF>_def map_commutant_def, intro CollectI ballI, rename_tac x)
  fix x
  assume \<open>x \<in> Z\<close>
  with \<open>X \<subseteq> \<FF>\<close>
  have \<open>(\<lambda>y. y \<circ>\<^sub>m x) ` X = (\<lambda>y. x \<circ>\<^sub>m y) ` X\<close>
    by (force simp add: \<FF>_def map_commutant_def)
  then show \<open>(partial_fun_Sup X \<circ>\<^sub>m x) = (x \<circ>\<^sub>m partial_fun_Sup X)\<close>
    by (simp add: map_comp_partial_fun_Sup_right[OF compat] map_comp_partial_fun_Sup_left)
qed

lemma partial_fun_Sup_update1: \<open>a = partial_fun_Sup {update1 x y | x y. a x = Some y}\<close>
proof (rule ext)
  fix w
  consider (empty) \<open>a = Map.empty\<close> 
    | (none) u v where \<open>a w = None\<close> \<open>a v = Some u\<close>
    | (only) z where \<open>a = update1 w z\<close>
    | (some) z u v where \<open>a w = Some z\<close> \<open>a v = Some u\<close> \<open>v \<noteq> w\<close>
  proof atomize_elim
    let ?thesis = \<open>a = Map.empty \<or> (\<exists>v u. a w = None \<and> a v = Some u) \<or> (\<exists>z. a = update1 w z)
                                 \<or> (\<exists>z v u. a w = Some z \<and> a v = Some u \<and> v \<noteq> w)\<close>
    consider (empty) \<open>a = Map.empty\<close> | (none) \<open>a \<noteq> Map.empty\<close> \<open>a w = None\<close>
      | (two_some) z where \<open>a w = Some z\<close> \<open>a \<noteq> update1 w z\<close>
      | (update1) z where \<open>a = update1 w z\<close>
      by auto
    then show ?thesis
    proof cases
      case empty
      then show ?thesis by simp
    next
      case none
      then show ?thesis by auto
    next
      case two_some
      then obtain v where \<open>a v \<noteq> None\<close> \<open>v \<noteq> w\<close>
        apply atomize_elim unfolding update1_def
        by fastforce
      with two_some show ?thesis
        by auto
    next
      case update1
      then show ?thesis by auto
    qed
  qed
  then show \<open>a w = partial_fun_Sup {update1 x y | x y. a x = Some y} w\<close>
  proof cases
    case empty
    then show \<open>a w = partial_fun_Sup {update1 x y | x y. a x = Some y} w\<close>
      by (auto intro!:  simp add: case_prod_beta partial_fun_Sup_def)
  next
    case (none u v)
    then have \<open>(\<lambda>(x,y). update1 x y w) ` {(x, y). a x = Some y} = {None}\<close>
      by (auto intro!: image_eqI simp add: case_prod_beta update1_def)
    then show \<open>a w = partial_fun_Sup {update1 x y | x y. a x = Some y} w\<close>
      by (simp add: none partial_fun_Sup_def image_image set_compr_2_image_collect case_prod_beta)
  next
    case (only z)
    then have \<open>(\<lambda>(x,y). update1 x y w) ` {(x, y). a x = Some y} = {Some z}\<close>
      by (auto intro!: image_eqI simp add: case_prod_beta update1_def)
    then show \<open>a w = partial_fun_Sup {update1 x y | x y. a x = Some y} w\<close>
      by (simp add: only partial_fun_Sup_def image_image case_prod_beta update1_def)
  next
    case (some z u v)
    then have \<open>(\<lambda>(x,y). update1 x y w) ` {(x, y). a x = Some y} = {None, Some z}\<close>
      by (auto intro: image_eqI[where x=\<open>(w,z)\<close>]
          simp add: case_prod_beta update1_def)
    then show \<open>a w = partial_fun_Sup {update1 x y | x y. a x = Some y} w\<close>
      by (simp add: some partial_fun_Sup_def image_image set_compr_2_image_collect case_prod_beta option_Sup_def)
  qed
qed

lemma partial_fun_compatible_update1:
  \<open>pairwise_all partial_fun_compatible {update1 x y | x y. a x = Some y}\<close>
  apply (auto simp: pairwise_all_def partial_fun_compatible_def update1_def)
  by (metis option.inject option.simps(3))


lemma Some_map_comp[simp]: \<open>Some \<circ>\<^sub>m f = f\<close>
  apply (rule ext, case_tac \<open>f x\<close>)
  by (auto simp: map_comp_def)

lemma map_comp_Some[simp]: \<open>f \<circ>\<^sub>m Some = f\<close>
  apply (rule ext, case_tac \<open>f x\<close>)
  by (auto simp: map_comp_def)

lemma compare_all_eqI: \<open>(\<And>x. a = x \<longleftrightarrow> b = x) \<Longrightarrow> a = b\<close>
  by auto

lemma has_sum_reindex_bij_betw:
  assumes "bij_betw g A B"
  shows   "has_sum (\<lambda>x. f (g x)) A l \<longleftrightarrow> has_sum f B l"
proof -
  have \<open>has_sum (\<lambda>x. f (g x)) A l \<longleftrightarrow> has_sum f (g ` A) l\<close>
    apply (rule has_sum_reindex[symmetric, unfolded o_def])
    using assms bij_betw_imp_inj_on by blast
  also have \<open>\<dots> \<longleftrightarrow> has_sum f B l\<close>
    using assms bij_betw_imp_surj_on by blast
  finally show ?thesis .
qed


end
