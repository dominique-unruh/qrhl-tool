theory Test
  imports Encoding Tactics QRHL_Code "HOL-Eisbach.Eisbach_Tools" CryptHOL.Cyclic_Group
  (* "HOL-Imperative_HOL.Imperative_HOL" *)
begin

ML \<open>
type sorry_location = { position : Position.T, comment : string }
val sorry_table = Synchronized.var "sorry" (Inttab.empty : sorry_location Inttab.table)
\<close>

definition sorry_marker :: "int \<Rightarrow> prop \<Rightarrow> prop" where "sorry_marker n P == P"

ML \<open>
Proofterm.proofs := 1
\<close>


oracle sorry_marker_oracle = \<open>fn (ctxt, (loc:sorry_location), t) => let
  val ser = serial ()
  val _ = Synchronized.change sorry_table (Inttab.update (ser, loc))
  val t' = \<^const>\<open>sorry_marker\<close> $ HOLogic.mk_number \<^typ>\<open>int\<close> ser $ t
  val ct = Thm.cterm_of ctxt t'
  in
    ct
  end
\<close>

ML \<open>
fun marked_sorry ctxt loc t = 
  sorry_marker_oracle (ctxt,loc,t) |> Conv.fconv_rule (Conv.rewr_conv @{thm sorry_marker_def});;
(* val thm1 = marked_sorry @{context} {position= @{here}} @{prop "1==1"}
val thm2 = marked_sorry @{context} {position= @{here}} @{prop "1==1"}
val thm = Thm.transitive thm1 thm2 *)
\<close>


ML \<open>
fun marked_sorry_tac ctxt loc = SUBGOAL (fn (goal,i) => let
  val thm = marked_sorry ctxt loc goal
  in
    solve_tac ctxt [thm] i
  end
) 
\<close>


ML \<open>
fun show_oracles thm = let
  val known_oracles = thm |> Thm.theory_of_thm |> Proof_Context.init_global
                          |> Thm.extern_oracles false |> map (fn (m as (_,props),name) => 
                              (Properties.get props "name" |> the,
                               Markup.markup m name))
                          |> Symtab.make
  val oracles = thm |> Thm.proof_body_of |> Proofterm.all_oracles_of
  fun show ("Test.sorry_marker_oracle",t) = let
        val ser = case t of \<^const>\<open>sorry_marker\<close> $ n $ _ => HOLogic.dest_number n |> snd
                          | t => raise (TERM ("show_oracles", [t]))
        val loc = Inttab.lookup (Synchronized.value sorry_table) ser |> the
        val pos = #position loc
        val comment = #comment loc
      in "\n  cheat method: " ^ comment ^ Position.here pos  end
    | show (name,_) = "\n  " ^ (Symtab.lookup known_oracles name |> the)
  in
    "Oracles used in theorem:" :: (map show oracles) |> Output.writelns
  end
\<close>


method_setup cheat = \<open>Scan.lift (Parse.position Parse.text) >> (fn (txt,pos) => fn _ => CONTEXT_METHOD (fn _ => fn (ctxt, st) =>
    Method.CONTEXT ctxt (marked_sorry_tac ctxt {position=pos, comment=txt} 1 st)))\<close>

declare[[smt_oracle=true]]

lemma theo: "1=1"
  apply (rule trans[of _ 1])
   apply (cheat 1)
  by smt

ML \<open>
val _ = show_oracles @{thm theo}
\<close>





(* 
ML \<open>
val (func,fut) = Active.dialog_text ()
val _ = func "hello" |> writeln
val _ = func "hullo" |> writeln
val _ = Future.join fut
\<close>
 *)

hide_const (open) Order.top


(* 
lemma "hadamard\<guillemotright>\<lbrakk>q1\<rbrakk> \<cdot> Qeq[q1=q2] = hadamard\<guillemotright>\<lbrakk>q2\<rbrakk> \<cdot> Qeq[q1=q2]"
  apply (auto simp: prepare_for_code)
  apply eval
  done

 *)  
  
  
  
(* lemma "space_div (span{ket 0}\<guillemotright>\<lbrakk>q\<rbrakk>) (ket 1) \<lbrakk>r\<rbrakk> = span{ket 0}\<guillemotright>\<lbrakk>q\<rbrakk>"
  apply (auto simp: prepare_for_code)
  by eval

lemma "space_div (span{ket (0,0), ket(1,1)}\<guillemotright>\<lbrakk>q,r\<rbrakk>) (ket 0) \<lbrakk>r\<rbrakk> = span{ket 0}\<guillemotright>\<lbrakk>q\<rbrakk>"
  apply (auto simp: prepare_for_code)
  by eval
 *)


axiomatization eval_variable :: "'a variable \<Rightarrow> mem2 \<Rightarrow> 'a"
axiomatization eval_variables :: "'a variables \<Rightarrow> mem2 \<Rightarrow> 'a"
axiomatization where
  eval_variables_unit: "eval_variables \<lbrakk>\<rbrakk> m = ()"
and eval_variables_singleton: "eval_variables \<lbrakk>q\<rbrakk> m = eval_variable q m"
and eval_variables_concat: "eval_variables (variable_concat Q R) m = (eval_variables Q m, eval_variables R m)"
for q :: "'a variable" and Q :: "'b variables" and R :: "'c variables" 


instantiation expression :: (ord) ord begin
definition "less_eq_expression e f \<longleftrightarrow> expression_eval e \<le> expression_eval f"
definition "less_expression e f \<longleftrightarrow> expression_eval e \<le> expression_eval f \<and> \<not> (expression_eval f \<le> expression_eval e)"
instance by intro_classes                   
end

axiomatization where expression_eval: "expression_eval (expression X e) m = e (eval_variables X m)"
  for X :: "'x variables" and e :: "'x \<Rightarrow> 'e" and m :: mem2

instantiation expression :: (preorder) preorder begin
instance apply intro_classes
  unfolding less_expression_def less_eq_expression_def 
  using order_trans by auto
end

(* ML {*
  fun subst_expression_simproc _ ctxt ct = SOME (Encoding.subst_expression_conv ctxt ct) handle CTERM _ => NONE
*} *)

(* simproc_setup subst_expression ("subst_expression (substitute1 x (expression R f')) (expression Q e')") = subst_expression_simproc *)



lemma qrhl_top: "qrhl A p1 p2 (expression Q (\<lambda>z. top))" sorry
lemma qrhl_top': "f \<ge> top \<Longrightarrow> qrhl A p1 p2 (expression Q f)" sorry

lemma skip:
  assumes "A \<le> B"
  shows "qrhl A [] [] B"
  sorry

(* 
lemma tmp: "(\<And>x. C x) \<Longrightarrow> (C x)" 
  by metis
 *)

term "[[y]]"
term "[(y)]"


(* lemma expression_leq:
  assumes "\<And>x. e x \<le> e' x"
  shows "expression X e \<le> expression X e'"
  using assms unfolding less_eq_expression_def expression_eval le_fun_def
  by auto *)

(* 
lemma expression_leq1:
  assumes "\<And>x. e x \<le> e' x"
  shows "expression \<lbrakk>v\<rbrakk> e \<le> expression \<lbrakk>v\<rbrakk> e'"
  using assms by (rule expression_leq) 

lemma expression_leq2:
  assumes "\<And>x y. e x y \<le> e' x y"
  shows "expression \<lbrakk>v,w\<rbrakk> (\<lambda>(x,y). e x y) \<le> expression \<lbrakk>v,w\<rbrakk> (\<lambda>(x,y). e' x y)"
  apply (rule expression_leq) using assms by auto
 *)

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

(* Converts a goal of the form "expression Q e \<le> expression R f :: 'a expression" 
   with Q,R explicit variable terms into "\<And>x1...xn. C x1...xn \<le> D x1...xn :: 'a" for some C,D. *)
method intro_expression_leq = 
  (rule less_eq_expression_def[THEN iffD2],
   rule le_fun_def[THEN iffD2],
   match conclusion in "\<forall>mem::mem2. C mem" for C \<Rightarrow>
      \<open>rule allI, rename_tac mem, 
       match conclusion in "C mem" for mem \<Rightarrow> 
         \<open>unfold expression_eval[where m=mem],
          (unfold eval_variables_concat[where m=mem] eval_variables_unit[where m=mem] eval_variables_singleton[where m=mem])?,
          (unfold case_prod_conv)?,
          ((match conclusion in "PROP (D (eval_variable v mem))" for D v \<Rightarrow> 
              \<open>rule meta_spec[where x="eval_variable v mem" and P=D], rename_tac_eisbach v\<close>)+)?
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
  shows "qrhl D [s1,sample var_x Expr[uniform {0..max x 0}]] [t1,t2,assign var_x Expr[0]] Expr[Cla[x1\<ge>x2]]"
  using [[method_error,show_types]]
  apply (tactic \<open>Tactics.wp_tac \<^context> true 1\<close>)
  apply (tactic \<open>Tactics.wp_tac \<^context> false 1\<close>)
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
  shows "qrhl Expr[ Cla[x1=0 \<and> x2=1] ] [qinit \<lbrakk>q\<rbrakk> Expr[ ket 0 ]] [assign var_x Expr[x-1]] Expr[Cla[x1\<ge>x2]]"
  using [[method_error]]
  apply (tactic \<open>Tactics.wp_tac \<^context> true 1\<close>) 
  apply (tactic \<open>Tactics.wp_tac \<^context> false 1\<close>)
  apply simp
  apply (rule skip)
  apply intro_expression_leq
  by simp

end

typedecl G
instance G::"{power,ab_semigroup_mult,inverse}" sorry
axiomatization G::"G cyclic_group" and g::G
(* term "(^^)" *)
axiomatization powG :: "G \<Rightarrow> int \<Rightarrow> G" (infixr "\<^sup>^" 80)
(* locale group_G = cyclic_group G  *)
(* axiomatization where group_G: group_G *)
(* abbreviation "g == generator G" *)

lemma (in cyclic_group) m_comm:
  assumes "x : carrier G" and "y : carrier G"
  shows "x \<otimes> y = y \<otimes> x"
proof -
  from generator assms obtain n m :: nat where x:"x=\<^bold>g [^] n" and y:"y=\<^bold>g [^] m" 
    apply atomize_elim by auto
  show ?thesis
    unfolding x y by (simp add: add.commute nat_pow_mult)
qed

interpretation G_group: cyclic_group G
  rewrites "x [^]\<^bsub>G\<^esub> n = x \<^sup>^ (n::int)" and "x \<otimes>\<^bsub>G\<^esub> y = x*y" and "\<one>\<^bsub>G\<^esub> = 1" and "generator G = g" 
    and "m_inv G = inverse" and "carrier G = UNIV"
  sorry


thm G_group.m_comm

(*(* From CryptHOL *)
record 'a cyclic_group = "'a monoid" + 
  generator :: 'a ("\<^bold>g\<index>")
locale cyclic_group = group G
  for G :: "('a, 'b) cyclic_group_scheme" (structure)
  +
  assumes generator_closed [intro, simp]: "generator G \<in> carrier G"
  and generator: "carrier G \<subseteq> range (\<lambda>n :: nat. generator G [^]\<^bsub>G\<^esub> n)"
*)

(*sublocale cyclic_group \<subseteq> comm_group
proof standard
  fix x y assume "x : carrier G" and "y : carrier G"
  with generator obtain n m :: nat where x:"x=\<^bold>g [^] n" and y:"y=\<^bold>g [^] m" 
    apply atomize_elim by auto
  show "x \<otimes> y = y \<otimes> x"
    unfolding x y by (simp add: add.commute nat_pow_mult)
qed*)


(* interpretation bool_cyclic: cyclic_group "\<lparr> carrier = UNIV, monoid.mult = (\<noteq>), one = False, generator = True \<rparr>"
  apply standard apply (auto simp: Units_def nat_pow_def image_def) 
  by (rule_tac x="if x then 1 else 0" in exI, simp)
 *)

definition "keygen = uniform {(g \<^sup>^ x, x) | x::int. x\<in>{0..order G-1}}"
(* thm cyclic_group.keygen_def *)
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


lemma (in group) int_pow_pow:
  assumes "x \<in> carrier G" shows "(x [^] n) [^] m = x [^] (n * m::int)"
proof (cases n; cases m)
  show ?thesis if "n=int n'" and "m=int m'" for n' m'
    unfolding that int_pow_int
    apply (subst nat_pow_pow)
     apply (fact assms)
    unfolding int_pow_int[symmetric]
    by simp

  show ?thesis if "n=-int n'" and "m=int m'" for n' m'
    unfolding that 
    apply (subst mult_minus_left)
    apply (subst int_pow_neg, simp add: assms)+
    unfolding that int_pow_int of_nat_mult[symmetric]
    apply (subst inv_nat_pow, simp add: assms)
    apply (subst nat_pow_pow)
    using assms by simp_all

  show ?thesis if "n=int n'" and "m=-int m'" for n' m'
    unfolding that 
    apply (subst mult_minus_right)
    apply (subst int_pow_neg, simp add: assms)+
    unfolding that int_pow_int of_nat_mult[symmetric]
    apply (subst nat_pow_pow)
    using assms by simp_all

  show ?thesis if "n=-int n'" and "m=-int m'" for n' m'
    unfolding that 
    apply (subst mult_minus_left)
    apply (subst mult_minus_right)
    apply (subst int_pow_neg, simp add: assms)+
    unfolding that int_pow_int of_nat_mult[symmetric]
    apply (subst inv_nat_pow, simp add: assms)
    apply (subst nat_pow_pow)
    using assms by simp_all
qed

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

definition "ElGamal = [sample var_pksk Expr[keygen],
           assign var_pk Expr[fst pksk],
           assign var_sk Expr[snd pksk],
           sample var_c Expr[enc pk m],
           assign var_m Expr[dec sk c]
          ]"

lemma elgamal_correct [simp]:
  fixes z
  shows "qrhl Expr[Cla[m1=z]] 
          ElGamal
         [] Expr[Cla[m1=z]]"
  unfolding ElGamal_def
  apply (tactic  \<open>Tactics.wp_tac \<^context> true 1\<close>)
  apply (simp add: dec_def)
  apply (tactic  \<open>Tactics.wp_tac \<^context> true 1\<close>)
  (* unfolding enc_def *)
  (* unfolding  *)
  apply (simp add: weight_enc supp_enc)
  apply (tactic  \<open>Tactics.wp_tac \<^context> true 1\<close>)
  apply (tactic  \<open>Tactics.wp_tac \<^context> true 1\<close>)
  apply (tactic  \<open>Tactics.wp_tac \<^context> true 1\<close>)
  apply (simp add: weight_keygen supp_keygen)
  apply skip
  by (auto simp: correct)

term "Pr[x:y(z)]"

lemma elgamal_correct2 [simp]:
  fixes z
  shows "qrhl Expr[Cla[m1=m2]] 
          ElGamal
         [] Expr[Cla[m1=m2]]"
  unfolding ElGamal_def
  apply (tactic  \<open>Tactics.wp_tac \<^context> true 1\<close>)
  apply (simp add: dec_def)
  apply (tactic  \<open>Tactics.wp_tac \<^context> true 1\<close>)
  (* unfolding enc_def *)
  (* unfolding  *)
  apply (simp add: weight_enc supp_enc)
  apply (tactic  \<open>Tactics.wp_tac \<^context> true 1\<close>)
  apply (tactic  \<open>Tactics.wp_tac \<^context> true 1\<close>)
  apply (tactic  \<open>Tactics.wp_tac \<^context> true 1\<close>)
  apply (simp add: weight_keygen supp_keygen)
  apply skip
  by (auto simp: correct)

end
