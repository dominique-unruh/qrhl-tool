theory Misc_Missing
  imports Main
begin

lemma inj_comp[simp]: "inj (op\<circ> f :: ('a\<Rightarrow>'b) \<Rightarrow> ('a\<Rightarrow>'c)) = inj f"
proof (rule; rule injI)
  assume inj: "inj (op\<circ> f :: ('a\<Rightarrow>'b) \<Rightarrow> ('a\<Rightarrow>'c))"
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

lemma surj_comp[simp]: "surj (op\<circ> f :: ('a\<Rightarrow>'b) \<Rightarrow> ('a\<Rightarrow>'c)) = surj f"
proof (rule)
  assume surj: "surj (op\<circ> f :: ('a\<Rightarrow>'b) \<Rightarrow> ('a\<Rightarrow>'c))"
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
  then show "surj (op\<circ> f :: ('a\<Rightarrow>'b) \<Rightarrow> ('a\<Rightarrow>'c))"
    unfolding surj_def by metis
qed

lemma bij_comp[simp]: "bij (op\<circ> f) = bij f" 
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

end
