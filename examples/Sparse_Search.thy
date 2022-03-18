theory Sparse_Search
  imports QRHL.QRHL
begin

lemma ortho_compl_ccspan_ket: \<open>- ccspan (ket ` X) = ccspan (ket ` (- X))\<close>
  by -

lemma ccspan_ket_leq_ortho[simp]: \<open>ccspan {ket x} \<le> - ccspan {ket y} \<longleftrightarrow> x \<noteq> y\<close>
proof (intro iffI notI)
  assume \<open>x \<noteq> y\<close>
  then show \<open>ccspan { |x\<rangle> } \<le> - ccspan { |y\<rangle> }\<close>
    by (metis ccspan_leq_ortho_ccspan orthogonal_ket singletonD)
next
  assume \<open>ccspan { |x\<rangle> } \<le> - ccspan { |y\<rangle> }\<close>
  moreover assume \<open>x = y\<close>
  ultimately have \<open>ccspan { |x\<rangle> } \<le> - ccspan { |x\<rangle> }\<close>
    by simp
  then have \<open>|x\<rangle> \<in> space_as_set (- ccspan { |x\<rangle> })\<close>
    by (meson ccspan_superset less_eq_ccsubspace.rep_eq singletonI subsetD)
  then have \<open>is_orthogonal |x\<rangle> |x\<rangle>\<close>
    apply -
    apply auto
      sorry
  then show False
    by auto
qed

axiomatization p :: real where p0: "p \<ge> 0" and p1: "p \<le> 1"

definition "sparse_fun_distr = (product_distr' (\<lambda>_. bernoulli p))"

lemma weight_sparse_fun_distr[simp]: \<open>weight sparse_fun_distr = 1\<close>
  by (simp add: sparse_fun_distr_def total_product_distr'I)

definition "o2h_distr = map_distr (\<lambda>g. ({x. g x = 1}, (\<lambda>_. 0), g, ())) sparse_fun_distr"

lemma weight_o2h_distr[simp]: \<open>weight o2h_distr = 1\<close>
  by (simp add: o2h_distr_def)

end
