theory Test
  imports 
(* CryptHOL.Cyclic_Group QRHL.QRHL "HOL-Eisbach.Eisbach_Tools" *)
    QRHL.QRHL_Core  
(*   keywords
    "relift_definition" :: thy_goal
 *)
begin

value "0 = (1::bit)"

typedef stuff = "UNIV :: nat set" by simp

locale stuff1 begin
setup_lifting type_definition_stuff
(* ML \<open>

      val transfer_thms = Transfer.get_transfer_raw \<^context>
      |> filter (fn thm => thm |> Thm.prop_of |> Term.exists_type (Term.exists_subtype (fn Type(n,_) => n=\<^type_name>\<open>stuff\<close> | _ => false)))
val _ = transfer_thms |> map Thm.theory_of_thm |> map (Context.pretty_abbrev_thy) |> @{print}
\<close>
 *)
end

ML \<open>

\<close>


locale stuff2 begin
lemma type_definition_stuff': "type_definition (\<lambda>x. Rep_stuff x + 1) (\<lambda>x. Abs_stuff (x - 1)) {0<..}"
  apply (rule type_definition.intro)
  using Rep_stuff_inverse Abs_stuff_inverse by auto
setup_lifting type_definition_stuff'
ML \<open>Multi_Transfer.local_transfer_rules \<^context>\<close>
end

lift_definition test :: "int vector" is "undefined" sorry

lift_definition (in stuff1) all :: "stuff set" is UNIV .
lemma (in stuff1) all: "all = UNIV"
  unfolding all_def apply auto by (metis Rep_stuff_inverse rangeI)

lift_definition (in stuff2) all :: "stuff set" is "{0<..}" by simp
lemma (in stuff2) all: "all = stuff1.all"
  unfolding stuff1.all_def all_def apply auto
  using greaterThan_0 image_iff
  by fastforce

lemmas (in stuff2) [transfer_rule] = all.transfer[unfolded all]

context stuff2 begin
lift_definition test2 :: "int vector" is "undefined" sorry
ML \<open>Multi_Transfer.local_transfer_rules \<^context>\<close>
end


ML \<open>
\<close>

ML \<open>Multi_Transfer.Saved_Transfer_Rules.get (Context.Theory \<^theory>)\<close>


ML \<open>
(* fun save_transfer_rules locale tyco name lthy =
  let
      val lthy_locale = Named_Target.init' {conclude=I, setup=I} locale (Proof_Context.theory_of lthy)
      val transfer_thms = Transfer.get_transfer_raw lthy_locale
          |> filter (fn thm => thm |> Thm.prop_of |> Term.exists_type (Term.exists_subtype (fn Type(n,_) => n=tyco | _ => false)))
      val (transfer_thms_exported,thy) = Local_Theory.exit_result_global (fn m => map (Morphism.thm m)) (transfer_thms,lthy_locale)
      val lthy = Context.raw_transfer thy lthy
      val update = Saved_Transfer_Rules.map (Symtab.update (name,transfer_thms_exported))
      val lthy = Local_Theory.declaration {pervasive=true, syntax=false} (K update) lthy
                     (* TODO merge *)
  in
    lthy
  end
 *)
\<close>

save_transfer_rules stuff1
save_transfer_rules stuff2

ML \<open>Multi_Transfer.Saved_Transfer_Rules.get (Context.Theory \<^theory>)\<close>

lemma "card (UNIV :: stuff set) = 0"
  using [[transfer_import stuff1]]
  apply transfer
  by simp

lemma "x : stuff1.all"
  using [[transfer_import stuff1]]
  using [[transfer_import stuff2]]
  apply transfer
  by simp
  


(* ML \<open>
fun import_transfer_rules locale tyco context =
  let val thy = Context.theory_of context
      val _ = thy |> Context.pretty_abbrev_thy |> @{print}
      (* val lthy = Context.proof_of context *)
      val lthy_locale = Named_Target.init' {conclude=I, setup=I} locale thy
(* val _ = @{print} 1 *)
      val transfer_thms = Transfer.get_transfer_raw lthy_locale
      |> filter (fn thm => thm |> Thm.prop_of |> Term.exists_type (Term.exists_subtype (fn Type(n,_) => n=tyco | _ => false)))
val _ = transfer_thms |> hd |> Thm.theory_of_thm |> (Context.pretty_abbrev_thy) |> @{print}
      (* val transfer_thms_exported = Proof_Context.export lthy_locale (Context.proof_of context) transfer_thms *)
      val (transfer_thms_exported,thy') = Local_Theory.exit_result_global (fn m => map (Morphism.thm m)) (transfer_thms,lthy_locale)
      val context' = Context.mapping (K thy') (Context.raw_transfer thy') context
      (* val transfer_thms_exported' = Proof_Context.export lthy' lthy transfer_thms_exported *)
(* val _ = @{print} 2 *)
      (* val transfer_thms_exported = map (Thm.transfer'' context) transfer_thms_exported *)
(* val _ = @{print} 3 *)
      val add_transfers = fold (Transfer.transfer_raw_add) transfer_thms_exported
(* val _ = @{print} 4 *)
in 
  add_transfers context'
end

val _ = Attrib.setup @{binding import_transfer}
  (Scan.lift (Parse.position Parse.name) -- Scan.lift Parse.type_const
    >> (fn (locale,tyco) => Thm.declaration_attribute 
    (fn _ => fn context => 
      let val locale' = Locale.check (Context.theory_of context) locale
          val tyco' = Proof_Context.read_type_name {proper=true,strict=true} (Context.proof_of context) tyco 
                      |> dest_Type |> fst 
      in
      import_transfer_rules locale' tyco' context end)))
  "Imports transfer rules from locale" 
  |> Theory.setup
;;
(* import_transfer_rules \<^locale>\<open>stuff1\<close> \<^type_name>\<open>stuff\<close> \<^context> *)
\<close>
 *)
(* declare [[import_transfer stuff1 stuff]] *)

(* lemma "x : stuff1.all"
  using [[import_transfer stuff1 stuff]]
  apply transfer
  by simp
 *)

(* bundle stuff1 begin
lemmas [transfer_rule] = stuff1.all.transfer
lemmas [transfer_rule] = stuff1.stuff.bi_unique stuff1.stuff.pcr_cr_eq stuff1.stuff.rep_transfer
  stuff1.stuff.domain stuff1.stuff.left_unique
  stuff1.stuff.right_unique stuff1.stuff.right_total
lemmas [transfer_domain_rule] = stuff1.stuff.domain
end
 *)

(* lemma "x : stuff1.all"
  including stuff1
  apply transfer
  apply transfer_step
 *)

(* bundle stuff2 begin
lemmas [transfer_rule] = stuff2.all.transfer[unfolded stuff2.all]

lemmas [transfer_rule] = stuff2.stuff.bi_unique stuff2.stuff.pcr_cr_eq stuff2.stuff.rep_transfer (* stuff2.cr_stuff_def stuff2.pcr_stuff_def *)
 stuff2.stuff.domain stuff2.stuff.domain_eq  stuff2.stuff.domain_par stuff2.stuff.domain_par_left_total stuff2.stuff.left_unique
 stuff2.stuff.right_unique stuff2.stuff.right_total

lemmas [transfer_domain_rule] = stuff2.stuff.domain_eq
 *)

(* relift_definition stuff2.all stuff1.all
  apply (rule eq_reflection)
  unfolding stuff1.all_def stuff2.all_def apply auto
  using greaterThan_0 image_iff
  by fastforce
 *)

(* ML \<open>
Transfer.get_transfer_raw \<^context>
              |> filter (fn thm => thm |> Thm.prop_of |> Term.exists_Const (fn (name,_) => name=\<^const_name>\<open>stuff1.all\<close>))
\<close>
end
 *)

(* (* declare [[lifting_restore stuff2.Quotient_stuff]] *)
lemma "x : stuff1.all"
  including stuff2 
  apply transfer_start
     apply transfer_step
    apply transfer_step
   apply transfer_step
  apply transfer_end
  by simp
 *)
(* end *)

(* print_bundles!  *)


(* end *)
(* end *)

(* (* context bla begin
lifting_forget bla2.stuff.lifting *)
lemma "x : stuff1.all"
  (* using [[lifting_restore Quotient_stuff]] *)
  including lift2
  apply transfer_start
  apply transfer_step
  apply transfer_step
  apply transfer_step
  apply transfer_end

(* 
 1. Transfer.Rel (rel_fun ?Ra7 (rel_fun (rel_set pcr_stuff) (=))) ?aa7 (\<in>) *)

lemma (in bla) "bla.all = bla2.all2"
  unfolding bla.all_def bla2.all2_def apply auto
  using greaterThan_0 image_iff by fastforce

print_theorems
  (* parametric refl *) .
lemma (in bla2) "x : all2"
  apply transfer
  by simp

print_theorems
 *)

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

(* TODO move *)
setup_lifting type_definition_variable_raw
setup_lifting type_definition_variable
setup_lifting type_definition_mem2

(* thm type_definition_mem2
lemma type_definition_universe_class: 
  fixes embed
  defines "embed \<equiv> embedding::'a::universe\<Rightarrow>_"
  shows "type_definition embed (inv embed) (range embed)"
  apply (rule type_definition.intro)
  by (auto simp: embed_def)
setup_lifting type_definition_universe_class *)

lift_definition eval_variable :: "'a::universe variable \<Rightarrow> mem2 \<Rightarrow> 'a"
  is "\<lambda>v m. inv embedding (m v)" .
print_theorems

axiomatization eval_variables :: "'a variables \<Rightarrow> mem2 \<Rightarrow> 'a"

lemma eval_variables_unit: "eval_variables \<lbrakk>\<rbrakk> m = ()" sorry
lemma eval_variables_singleton: "eval_variables \<lbrakk>q\<rbrakk> m = eval_variable q m" sorry
lemma eval_variables_concat: "eval_variables (variable_concat Q R) m = (eval_variables Q m, eval_variables R m)" sorry


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
  apply skip
  by simp

end

declare_variable_type G :: "{power,ab_semigroup_mult,inverse}"

axiomatization G::"G cyclic_group" and g::G

(* term "(^^)" *)
axiomatization powG :: "G \<Rightarrow> int \<Rightarrow> G" (infixr "\<^sup>^" 80)
(* locale group_G = cyclic_group G  *)
(* axiomatization where group_G: group_G *)
(* abbreviation "g == generator G" *)

thm cyclic_group.carrier_conv_generator

(* Add to CryptHOL? *)
lemma (in cyclic_group) "finite (carrier G)"
proof -
  from generator obtain n::nat where "\<^bold>g [^] n = inv \<^bold>g" 
    apply atomize_elim by (metis generatorE generator_closed inv_closed)
  then have g1: "\<^bold>g [^] (Suc n) = \<one>"
    by auto
  then have mod: "\<^bold>g [^] m = \<^bold>g [^] (m mod Suc n)" for m
  proof -
    obtain k where "m mod Suc n + Suc n * k = m" apply atomize_elim
      by (metis mod_less_eq_dividend mod_mod_trivial nat_mod_eq_lemma)
    then have "\<^bold>g [^] m = \<^bold>g [^] (m mod Suc n + Suc n * k)" by simp
    also have "\<dots> = \<^bold>g [^] (m mod Suc n)" 
      apply (subst nat_pow_mult[symmetric], rule)
      apply (subst nat_pow_pow[symmetric], rule)
      unfolding g1 by simp
    finally show ?thesis .
  qed
  have "range ((([^])::_\<Rightarrow>nat\<Rightarrow>_) \<^bold>g) \<subseteq> (([^]) \<^bold>g) ` {..<Suc n}"
  proof -
    have "\<^bold>g [^] x \<in> ([^]) \<^bold>g ` {..<Suc n}" for x::nat
      apply (subst mod) by auto
    then show ?thesis by auto
  qed
  then have "finite (range ((([^])::_\<Rightarrow>nat\<Rightarrow>_) \<^bold>g))"
    using finite_surj by auto
  with generator show "finite (carrier G)"
    using finite_subset by blast
qed

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


definition "keygen = uniform {(g \<^sup>^ x, x) | x::int. x\<in>{0..order G-1}}"
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
