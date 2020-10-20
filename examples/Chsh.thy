theory Chsh
  imports CryptHOL.CryptHOL
begin

(* TODO Update to Isabelle 2020 *)

(* To run this file, open it in Isabelle 2019,
   select "CryptHOL" in the dropdown in the Theories panel and, 
   if needed, restart Isabelle.

   This assumes that the AFP is properly installed and configured in Isabelle.
   (https://www.isa-afp.org/index.html) *)



(* Declaring the CHSH adversary: The adversary consists of three algorithms S,A,B.
The internal state of A and B has types 'a,'b, respectively.
Hence the setup S outputs a pair 'a,'b consisting of the states of A and B.
A takes two inputs, the state of type 'a, and a bit.
Analogously, B takes two inputs, the state of type 'b, and a bit.
A and B both output a bit. 

(The "spmf" denotes that they are probabilistic functions.) *)

locale chsh =
  fixes S :: "('a\<times>'b) spmf"
    and A :: "'a\<Rightarrow>bool\<Rightarrow>bool spmf"
    and B :: "'b\<Rightarrow>bool\<Rightarrow>bool spmf"
begin

(* The CHSH game itself. The setup S picks the initial states \<sigma>\<^sub>a,\<sigma>\<^sub>b of A,B.
Two uniformly random bits x,y are chosen. A produces bit a given input x,
B produces bit b given input y. (The states of A,B are also given as explicit inputs
because CryptHOL does not model persistent state.) The game returns True iff 
"x\<and>y \<longleftrightarrow> a\<noteq>b" (which is the "Boolean" way of saying x\<cdot>y=a\<oplus>b). *)

section "Auxiliary lemmas"

definition chsh_game :: "bool spmf" where
"chsh_game = do {
  (\<sigma>\<^sub>a,\<sigma>\<^sub>b) <- S;
  x <- coin_spmf;
  y <- coin_spmf;
  (a::bool) <- A \<sigma>\<^sub>a x;
  b <- B \<sigma>\<^sub>b y;
  return_spmf (x\<and>y \<longleftrightarrow> a\<noteq>b)
}"

(* The following lemma is not specific to the CHSH analysis.
   It concerns the program p\<bind>f (i.e., run x\<leftarrow>p, and then f(x)).
   It says that the probability that p\<bind>f outputs y equals
   \<Sum>\<^sub>x Pr[p outputs x] * Pr[f x outputs y].
  
   (This is how \<bind> is usually defined for the spmf monad, but in CryptHOL the definition 
   of the spmf monad is by reduction to a different monad pmf, so the lemma needs to be 
   proven explicitly.) *)
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

(* Another simple general fact:
   For a program p, the sum of the probabilities of all possible outputs is at most 1 *)
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

(* The following lemma allows us to easily work with coin tosses.
   It says: The probability that p(b) outputs x where b is a uniformly random Boolean
   is (Pr[p True]+Pr[p False])/2. *)
lemma coin_spmf_bind: "spmf (bind_spmf coin_spmf p) x = (\<Sum>z\<in>UNIV. spmf (p z) x) / 2"
  apply (subst bind_spmf_of_set)
    apply auto[2]
  apply (subst pmf_bind_pmf_of_set)
  by auto

(* An auxiliary lemma to help rewriting later *)
lemma sum_bool: "(\<Sum>x\<in>UNIV. P x) = P False + P True"
  unfolding UNIV_bool by simp
  
section "The main result"

(* This lemma says that the probability that the CHSH game outputs True (i.e., the adversary wins)
   is at most 3/4. We know that this does not hold in the quantum setting. *)
lemma chsh: "spmf chsh_game True \<le> 3/4"
proof -
  (* "pr1 \<sigma>" is the probability that the CHSH game returns True if the initial state of A,B is \<sigma>.
     That is, we fix the output of S here. *)
  define pr1 where "pr1 \<sigma> = spmf (do { 
      x <- coin_spmf; y <- coin_spmf; 
      (a::bool) <- A (fst \<sigma>) x; b <- B (snd \<sigma>) y;
      return_spmf (x\<and>y \<longleftrightarrow> a\<noteq>b) }) True" for \<sigma>

  (* Main part of the proof: For any fixed initial state \<sigma> of A,B, the probability of winning
     is \<le> 3/4 *)
  have pr1_34: "pr1 \<sigma> \<le> 3/4" for \<sigma>
  proof -
    (* "prA x a" is the probability that A(x) outputs a *)
    define prA where "prA x a = spmf (A (fst \<sigma>) x) a" for a x
    (* "prB y b" is the probability that B(y) outputs b *)
    define prB where "prB y b = spmf (B (snd \<sigma>) y) b" for b y
    (* "prxy x y" is the probability of winning for fixed bits x,y (instead of uniformly random) *)
    define prxy where "prxy x y = spmf (do {
      (a::bool) <- A (fst \<sigma>) x; b <- B (snd \<sigma>) y;
      return_spmf (x\<and>y \<longleftrightarrow> a\<noteq>b) }) True" for x y
    (* "prA' x a" is the probability that A(x) outputs True (if a=True)
       or the probability that A(x) does not output True (if a=False). 
       This would be the same as prA if A terminates with probability 1.
       This definition simplifies some calculations.
    *)
    define prA' where "prA' x a = (if a then prA x True else 1 - prA x True)" for x a

    (* We can express the probability of winning in terms of prA and prB (for given x,y):
       This uses the fact that Pr[A(x)=a\<and>B(y)=b]=Pr[A(x)=a]\<cdot>Pr[B(y)=b] once the
       initial state \<sigma>=(\<sigma>\<^sub>a,\<sigma>\<^sub>b) is fixed.

       This step does not make sense in a quantum setting since an initial quantum state \<sigma> 
       cannot be interpreted as a pair of quantum states \<sigma>\<^sub>a,\<sigma>\<^sub>b (due to entanglement).
    *)
    have prxy_win: "prxy x y = prA x True * prB y (\<not> (x\<and>y)) + prA x False * prB y (x\<and>y)" for x y
      unfolding prxy_def spmf_bind_finite sum_bool prA_def prB_def
      apply (cases x; cases y)
      by auto
    (* The rhs of the previous fact, but using prA' instead of prA
       we abbreviate prxy' (recall that prA=prA' for terminating A) *)
    define prxy' where "prxy' x y = prA' x True * prB y (\<not> (x\<and>y)) + prA' x False * prB y (x\<and>y)" for x y

    (* pr1 \<sigma> (the probability of winning on initial state \<sigma>)
       is the average of the winning probabilities for all values x,y. *)
    have pr1: "pr1 \<sigma> = (\<Sum>x\<in>UNIV. \<Sum>y\<in>UNIV. prxy x y) / 4"
      unfolding pr1_def coin_spmf_bind prxy_def 
      apply (subst sum_divide_distrib[symmetric])
      by simp

    (* The total probability of all outputs of A(x) is bounded by 1. Same for B. *)
    have prABsum: "\<forall>x. (\<Sum>a\<in>UNIV. prA x a) \<le> 1 \<and> (\<Sum>a\<in>UNIV. prB x a) \<le> 1"
      unfolding prA_def prB_def 
      using spmf_sum_leq1 by auto
    (* Output probabilities are nonnegative *)
    have prABpos: "\<forall>x a. prA x a \<ge> 0 \<and> prB x a \<ge> 0"
      unfolding prA'_def prA_def prB_def by simp_all

    (* prA' upper bounds prA (recall: if A terminates with probability 1, they are the same) *)
    from prABsum have prAA': "prA x y \<le> prA' x y" for x y unfolding prA_def prA'_def apply (cases y, auto)
      by (simp add: chsh.sum_bool le_diff_eq)
    (* The relationship carries over to prxy vs. prxy' *)
    have prxy': "prxy x y \<le> prxy' x y" for x y
      unfolding prxy'_def prxy_win 
      using prAA' prABpos by (simp add: add_mono landau_o.R_mult_right_mono)

    (* Output probabilities are nonnegative (now with prA') *)
    have prA'Bpos: "\<forall>x a. prA' x a \<ge> 0 \<and> prB x a \<ge> 0"
      unfolding prA'_def prA_def prB_def by (simp_all add: pmf_le_1)
    (* Total probabilities are =1 and \<le>1, respectively. The =1 case we get since prA' "fills up"
       the probability in the non-terminating case. *)
    from prABsum have prA'Bsum: "\<forall>x. (\<Sum>a\<in>UNIV. prA' x a) = 1 \<and> (\<Sum>a\<in>UNIV. prB x a) \<le> 1"
      unfolding prA'_def sum_bool by auto

    (* Some appreviations. pXij is prX i j (where we identify 0=False, 1=True).
       We will need those below to simplify the terms to make them comprehensible
       for the sos-tactic *)
    define pA00 pA01 pA10 pA11 pA'00 pA'01 pA'10 pA'11 pB00 pB01 pB10 pB11
      where 
        "pA00 = prA False False" "pA01 = prA False True"
        "pA10 = prA True False" "pA11 = prA True True"
        "pA'00 = prA' False False" "pA'01 = prA' False True"
        "pA'10 = prA' True False" "pA'11 = prA' True True"
        "pB00 = prB False False" "pB01 = prB False True"
        "pB10 = prB True False" "pB11 = prB True True"
    note pXxx_def = this    

    (* Probability of winning is the sum over all prxy' a b for all a b, divided by 4 *)
    have "pr1 \<sigma> \<le> (\<Sum>a\<in>UNIV. sum (prxy' a) UNIV) / 4"
      unfolding pr1 apply simp
      apply (rule sum_mono)+
      by (rule prxy')
    (* And this is upper bounded by 3/4 *)
    also have "\<dots> \<le> 3/4"
      unfolding sum_bool prxy'_def apply simp
      apply (insert prA'Bpos prA'Bsum) unfolding all_bool_eq sum_bool
      unfolding pXxx_def[symmetric]
      by (sos "(((A<0 * R<1) + (((A<=9 * R<1) * (R<4 * [1]^2)) + (((A<=8 * R<1) * ((R<11/6 * [5/11*pA'01__ + 5/11*pA'11__ + 1]^2) + (R<4/33 * [pA'01__ + pA'11__]^2))) + (((A<=4 * (A<=6 * (A<=8 * R<1))) * (R<1/2 * [1]^2)) + (((A<=2 * (A<=6 * (A<=8 * R<1))) * (R<5/6 * [1]^2)) + (((A<=2 * (A<=4 * (A<=9 * R<1))) * (R<4 * [1]^2)) + (((A<=2 * (A<=4 * (A<=5 * R<1))) * (R<8 * [1]^2)) + (((A<=1 * (A<=2 * (A<=6 * R<1))) * (R<8 * [1]^2)) + (((A<=0 * (A<=6 * (A<=9 * R<1))) * (R<4 * [1]^2)) + (((A<=0 * (A<=6 * (A<=7 * R<1))) * (R<8 * [1]^2)) + (((A<=0 * (A<=4 * (A<=8 * R<1))) * (R<37/6 * [1]^2)) + (((A<=0 * (A<=3 * (A<=4 * R<1))) * (R<8 * [1]^2)) + ((A<=0 * (A<=2 * (A<=8 * R<1))) * (R<1/2 * [1]^2)))))))))))))))")

    (* So, altogether we have shown our subgoal (the fact pr1_34) *)
    finally show "pr1 \<sigma> \<le> 3/4" .
  qed

  (* Probability of winning is nonnegative for any initial state \<sigma> *)
  have pr1_0: "pr1 \<sigma> \<ge> 0" for \<sigma>
    unfolding pr1_def by simp

  (* Absolute value of the winning probability is also bounded by 3/4.
     This is needed to show integrability below. *)
  have pr1_norm: "norm (pr1 \<sigma>) \<le> 3/4" for \<sigma>
    using pr1_0 pr1_34 by auto

  (* pr1 is integrable with respect to the distribution of initial states. *)
  have int_pr1: "integrable (measure_spmf S) pr1"
    apply (rule measure_spmf.integrable_const_bound[where B="3/4"])
    apply (subst pr1_norm) by auto

  (* The probability of winning the CHSH game is the average over "pr1 \<sigma>" for all \<sigma>.
     Since \<sigma> does not necessarily come from a finite set, we need to formulate this using
     integrals. *)
  have "spmf chsh_game True = (\<integral>\<sigma>. pr1 \<sigma> \<partial>measure_spmf S)"
    unfolding chsh_game_def case_prod_unfold
    apply (subst spmf_bind)
    unfolding pr1_def by rule
  (* This is upper bounded by the average of 3/4 (since pr1 \<sigma> \<le> 3/4) *)
  also have "\<dots> \<le> (\<integral>\<sigma>. 3/4 \<partial>measure_spmf S)"
    apply (rule integral_mono)
    using int_pr1 pr1_34 by auto
  (* Which is upper bounded by 3/4.
     (Not equal because the distribution of initial states might not be total.) *)
  also have "\<dots> \<le> 3/4"
    apply (subst lebesgue_integral_const)
    using weight_spmf_le_1 by auto
  (* Altogether, we have shown that the probability of winning is at most 3/4. *)
  finally show "spmf chsh_game True \<le> 3/4" .
qed

end

end
