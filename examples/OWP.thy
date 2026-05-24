theory OWP
  imports QRHL.QRHL
begin

declare_variable_type X

axiomatization f :: \<open>X \<Rightarrow> X\<close> where bij_f: \<open>bij f\<close>
definition g where \<open>g = f \<circ> f\<close>

lemma [iff]: \<open>f x = f y \<longleftrightarrow> x = y\<close>
  by (metis UNIV_I bij_betw_iff_bijections bij_f)

end
