theory Chsh
  imports CryptHOL
begin

locale chsh =
  fixes S :: "('a\<times>'b) spmf"
    and A :: "'a\<Rightarrow>bool\<Rightarrow>bool spmf"
    and B :: "'b\<Rightarrow>bool\<Rightarrow>bool spmf"
begin

definition chsh_game :: "bool spmf" where
"chsh_game = do {
  (\<sigma>\<^sub>a,\<sigma>\<^sub>b) <- S;
  x <- coin_spmf;
  y <- coin_spmf;
  (a::bool) <- A \<sigma>\<^sub>a x;
  b <- B \<sigma>\<^sub>b y;
  return_spmf (x\<and>y \<longleftrightarrow> a\<noteq>b)
}"

lemma spmf_bind_finite: "spmf (p \<bind> f) y = (\<Sum>(x::_::finite)\<in>UNIV. spmf p x * spmf (f x) y)"
proof -
  have "pmf p None * spmf (case None of None \<Rightarrow> return_pmf None | Some x \<Rightarrow> f x) y = 0"
    by auto
  have Some_None: "Some`UNIV \<union> {None} = UNIV" using notin_range_Some by blast
  have "(\<Sum>a\<in>UNIV. pmf p a * spmf (case a of None \<Rightarrow> return_pmf None | Some x \<Rightarrow> f x) y)
      = (\<Sum>a\<in>Some`UNIV. pmf p a * spmf (case a of None \<Rightarrow> return_pmf None | Some x \<Rightarrow> f x) y)"
    apply (subst Some_None[symmetric]) by simp
  also have "\<dots> = (\<Sum>x\<in>UNIV. pmf p (Some x) * spmf (case (Some x) of None \<Rightarrow> return_pmf None | Some x \<Rightarrow> f x) y)" 
    apply (subst sum.reindex) by auto
  also have "\<dots> = (\<Sum>x\<in>UNIV. spmf p x * spmf (f x) y)"
    by auto
  also 
  show ?thesis
    unfolding bind_spmf_def pmf_bind 
    apply (subst integral_measure_pmf[where A=UNIV])
    by (auto simp: calculation)
qed

lemma spmf_sum_leq1: "(\<Sum>x\<in>(M::_::finite). spmf p x) \<le> 1" (is "?lhs \<le> _")
proof -
  have "?lhs = (\<Sum>x\<in>Some`M. pmf p x)"
    apply (subst sum.reindex) by auto
  also have "\<dots> \<le> (\<Sum>x\<in>UNIV. pmf p x)"
    apply (rule sum_mono2)
    by auto
  also have "\<dots> = 1"
    apply (rule sum_pmf_eq_1)
    by auto
  finally show ?thesis by simp
qed

lemma coin_spmf_bind: "spmf (bind_spmf coin_spmf p) x = (\<Sum>z\<in>UNIV. spmf (p z) x) / 2"
  apply (subst bind_spmf_of_set)
    apply auto[2]
  apply (subst pmf_bind_pmf_of_set)
  by auto

lemma sum_bool: "(\<Sum>x\<in>UNIV. P x) = P False + P True"
  unfolding UNIV_bool by simp
  


lemma "spmf chsh_game True \<le> 3/4"
proof -
  define pr1 where "pr1 \<sigma> = spmf (do { x <- coin_spmf; y <- coin_spmf; (a::bool) <- A (fst \<sigma>) x; b <- B (snd \<sigma>) y; return_spmf (x\<and>y \<longleftrightarrow> a\<noteq>b) }) True" for \<sigma>

  have pr1_34: "pr1 \<sigma> \<le> 3/4" for \<sigma>
  proof -
    define prA where "prA x a = spmf (A (fst \<sigma>) x) a" for a x
    define prB where "prB y b = spmf (B (snd \<sigma>) y) b" for b y
    define prxy where "prxy x y = spmf (do { (a::bool) <- A (fst \<sigma>) x; b <- B (snd \<sigma>) y; return_spmf (x\<and>y \<longleftrightarrow> a\<noteq>b) }) True" for x y
    define prA' where "prA' x a = (if a then prA x True else 1 - prA x True)" for x a

    have prxy_win: "prxy x y = prA x True * prB y (\<not> (x\<and>y)) + prA x False * prB y (x\<and>y)" for x y
      unfolding prxy_def spmf_bind_finite sum_bool prA_def prB_def
      apply (cases x; cases y)
      by auto
    define prxy' where "prxy' x y = prA' x True * prB y (\<not> (x\<and>y)) + prA' x False * prB y (x\<and>y)" for x y

    have pr1: "pr1 \<sigma> = (\<Sum>a\<in>UNIV. \<Sum>b\<in>UNIV. prxy a b) / 4"
      unfolding pr1_def coin_spmf_bind prxy_def 
      apply (subst sum_divide_distrib[symmetric])
      by simp

    have prABsum: "\<forall>x. (\<Sum>a\<in>UNIV. prA x a) \<le> 1 \<and> (\<Sum>a\<in>UNIV. prB x a) \<le> 1"
      unfolding prA_def prB_def 
      using spmf_sum_leq1 by auto
    have prABpos: "\<forall>x a. prA x a \<ge> 0 \<and> prB x a \<ge> 0"
      unfolding prA'_def prA_def prB_def by simp_all

    from prABsum have prAA': "prA x y \<le> prA' x y" for x y unfolding prA_def prA'_def apply (cases y, auto)
      by (simp add: chsh.sum_bool le_diff_eq)
    have prxy': "prxy x y \<le> prxy' x y" for x y
      unfolding prxy'_def prxy_win 
      using prAA' prABpos by (simp add: add_mono landau_o.R_mult_right_mono)

    have prA'B01: "\<forall>x a. prA' x a \<ge> 0 (* \<and> prA x a \<le> 1 *) \<and> prB x a \<ge> 0 (* \<and> prB x a \<le> 1 *)"
      unfolding prA'_def prA_def prB_def by (simp_all add: pmf_le_1)
    from prABsum have prA'Bsum: "\<forall>x. (\<Sum>a\<in>UNIV. prA' x a) = 1 \<and> (\<Sum>a\<in>UNIV. prB x a) \<le> 1"
      unfolding prA'_def sum_bool by auto

    define pA00 pA01 pA10 pA11 pB00 pB01 pB10 pB11
      where "pA00 = prA' False False" "pA01 = prA' False True"
        "pA10 = prA' True False" "pA11 = prA' True True"
        "pB00 = prB False False" "pB01 = prB False True"
        "pB10 = prB True False" "pB11 = prB True True"
    note pXxx_def = this    

    have "pr1 \<sigma> \<le> (\<Sum>a\<in>UNIV. sum (prxy' a) UNIV) / 4"
      unfolding pr1 apply simp
      apply (rule sum_mono)+
      by (rule prxy')
    also have "\<dots> \<le> 3/4"
      unfolding sum_bool prxy'_def apply simp
      apply (insert prA'B01 prA'Bsum) unfolding all_bool_eq sum_bool
      unfolding pXxx_def[symmetric]
      by (sos "(((A<0 * R<1) + (((A<=9 * R<1) * (R<4 * [1]^2)) + (((A<=8 * R<1) * ((R<11/6 * [5/11*pA01__ + 5/11*pA11__ + 1]^2) + (R<4/33 * [pA01__ + pA11__]^2))) + (((A<=4 * (A<=6 * (A<=8 * R<1))) * (R<1/2 * [1]^2)) + (((A<=2 * (A<=6 * (A<=8 * R<1))) * (R<5/6 * [1]^2)) + (((A<=2 * (A<=4 * (A<=9 * R<1))) * (R<4 * [1]^2)) + (((A<=2 * (A<=4 * (A<=5 * R<1))) * (R<8 * [1]^2)) + (((A<=1 * (A<=2 * (A<=6 * R<1))) * (R<8 * [1]^2)) + (((A<=0 * (A<=6 * (A<=9 * R<1))) * (R<4 * [1]^2)) + (((A<=0 * (A<=6 * (A<=7 * R<1))) * (R<8 * [1]^2)) + (((A<=0 * (A<=4 * (A<=8 * R<1))) * (R<37/6 * [1]^2)) + (((A<=0 * (A<=3 * (A<=4 * R<1))) * (R<8 * [1]^2)) + ((A<=0 * (A<=2 * (A<=8 * R<1))) * (R<1/2 * [1]^2)))))))))))))))")

    finally show ?thesis .
  qed

  have pr1_0: "pr1 \<sigma> \<ge> 0" for \<sigma>
    unfolding pr1_def by simp

  have pr1_norm: "norm (pr1 \<sigma>) \<le> 3/4" for \<sigma>
    using pr1_0 pr1_34 by auto
    
  have int_pr1: "integrable (measure_spmf S) pr1"
    apply (rule measure_spmf.integrable_const_bound[where B="3/4"])
    apply (subst pr1_norm) by auto

  have "spmf chsh_game True = (\<integral>\<sigma>. pr1 \<sigma> \<partial>measure_spmf S)"
    unfolding chsh_game_def case_prod_unfold
    apply (subst spmf_bind)
    unfolding pr1_def by rule
  also have "\<dots> \<le> (\<integral>\<sigma>. 3/4 \<partial>measure_spmf S)"
    apply (rule integral_mono)
    using int_pr1 pr1_34 by auto
  also have "\<dots> \<le> 3/4"
    apply (subst lebesgue_integral_const)
    using weight_spmf_le_1 by auto
  finally show ?thesis .
qed

end


