theory TestEx
  imports QRHL.QRHL QRHL.QRHL_Operations
begin

lemma bind_distr_point[simp]: "bind_distr (uniform {x}) f = f x"
  apply transfer
  sorry

lemma bind_distr_point2[simp]: "bind_distr \<mu> (\<lambda>z. uniform {f z}) = map_distr f \<mu>"
  apply transfer
  sorry

lemma map_distr_point[simp]: "map_distr f (uniform {x}) = uniform {f x}"
  apply transfer
  sorry

lemma "undefined (\<CC>\<ll>\<aa>[uniform {(1, 2)} = bind_distr (uniform {1, 3}) (\<lambda>z. map_distr (Pair z) (uniform {2}))] \<sqinter> (\<Sqinter>z\<in>supp (uniform {(1, 2)}). \<CC>\<ll>\<aa>[undefined (fst z) (fst z) (snd z) (snd z)]))"
  apply simp
  oops

ML \<open>
QRHL.simp 
\<^term>\<open>\<top> \<le> \<CC>\<ll>\<aa>[uniform {(1, 2)} = bind_distr (uniform {1, 3}) (\<lambda>z. map_distr (Pair z) (uniform {2}))] \<sqinter> (\<Sqinter>z\<in>supp (uniform {(1, 2)}). \<CC>\<ll>\<aa>[fst z = fst z])\<close>
[]
\<^context>
|>
fst
|>
Thm.cterm_of \<^context>
\<close>

lemma "\<top> \<le> \<CC>\<ll>\<aa>[uniform {(1, 2)} = bind_distr (uniform {1, 3}) (\<lambda>z. map_distr (Pair z) (uniform {2}))] \<sqinter> (\<Sqinter>z\<in>supp (uniform {(1, 2)}). \<CC>\<ll>\<aa>[fst z = fst z])"
  apply simp
  oops

end
