theory Misc_Missing
  imports Main Universe
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


typedef bit = "UNIV::bool set"..
setup_lifting type_definition_bit
instantiation bit :: field begin
lift_definition times_bit :: "bit \<Rightarrow> bit \<Rightarrow> bit" is "(&)".
lift_definition plus_bit :: "bit \<Rightarrow> bit \<Rightarrow> bit" is "(\<noteq>)".
lift_definition zero_bit :: bit is "False".
lift_definition one_bit :: bit is "True".
definition[simp]: "uminus_bit (x::bit) = x"
definition[simp]: "minus_bit = ((+) :: bit\<Rightarrow>_\<Rightarrow>_)"
definition[simp]: "inverse_bit (x::bit) = x"
definition[simp]: "divide_bit = (( * ) :: bit\<Rightarrow>_\<Rightarrow>_)"
instance by intro_classes (transfer; auto)+
end

derive universe bit


lemma bit_cases[cases type:bit]: "(x=0 \<Longrightarrow> P) \<Longrightarrow> (x=1 \<Longrightarrow> P) \<Longrightarrow> P" for x :: bit
  by (metis (full_types) Rep_bit_inverse one_bit.abs_eq zero_bit.abs_eq)
lemma bit_two[simp]: "(2::bit) = 0"
  by (metis add_cancel_left_right bit_cases one_add_one) 
lemma bit_eq_x[simp]: "((a=x) = (b=x)) = (a=b)" for a b x :: bit
  apply transfer by auto
lemma bit_neq[simp]: "(a \<noteq> b) = (a = b+1)" for a b :: bit
  apply (cases a rule:bit_cases; cases b rule:bit_cases) by auto

(* declare [[coercion "\<lambda>b::bit. if b=0 then (0::nat) else 1"]] *)

lemma bit_plus_1_eq[simp]: "(a+1=b) = (a=b+1)" for a b :: bit
  by auto

lemma bit_plus_2y[simp]: "(x + y) + y = x" for x :: bit
  apply (cases y) by auto

definition (in zero_neq_one) of_bit :: "bit \<Rightarrow> 'a"
  where "of_bit b = (if b=0 then 0 else 1)"

lemma UNIV_bit: "(UNIV::bit set) = {0,1}" by auto

instantiation bit :: enum begin
definition "enum_bit = [0::bit,1]"
definition "enum_all_bit P \<longleftrightarrow> P (0::bit) \<and> P 1"
definition "enum_ex_bit P \<longleftrightarrow> P (0::bit) \<or> P 1"
instance apply intro_classes
  unfolding enum_bit_def enum_all_bit_def enum_ex_bit_def 
     apply auto
  using bit_cases apply metis
  using bit_cases by metis
end

instantiation bit :: equal begin
lift_definition equal_bit :: "bit \<Rightarrow> bit \<Rightarrow> bool" is "HOL.equal :: bool \<Rightarrow> bool \<Rightarrow> bool" .
instance apply intro_classes 
  apply transfer by (rule equal_eq)
end

instance bit :: xor_group
  apply intro_classes by auto

section \<open>Code\<close>

lemma pat_lambda_conv_aux: \<comment> \<open>Helper for ML function pat_lambda_conv\<close>
  shows "term \<equiv> (\<lambda>_. term ())"
  by simp

ML_file "misc.ML"



end
