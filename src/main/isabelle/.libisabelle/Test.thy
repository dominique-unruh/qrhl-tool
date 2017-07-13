theory Test
  imports QRHL
begin

  
  
lemma "(H \<rightarrow> \<lbrakk>C1\<rbrakk>)* \<cdot> (\<lbrakk>B1\<rbrakk> \<equiv>\<qq> \<lbrakk>A2\<rbrakk> \<sqinter> imageIso (H \<rightarrow> \<lbrakk>C1\<rbrakk>)) =  H \<rightarrow> \<lbrakk>C1\<rbrakk> \<cdot> \<lbrakk>B1\<rbrakk> \<equiv>\<qq> \<lbrakk>A2\<rbrakk>"
  by simp
  
  
ML QRHL.qinitWp

  term "sup a b"
  
    ML " @{const_name sup} "
    
      
lemma "INF b2:supp (uniform {0, 1}). \<CC>\<ll>\<aa>[0 \<le> (b2::int)] \<sqinter> \<lbrakk>q1\<rbrakk> \<equiv>\<qq> \<lbrakk>q2\<rbrakk> = \<lbrakk>q1\<rbrakk> \<equiv>\<qq> \<lbrakk>q2\<rbrakk>"
  by simp
    
context fixes a1 b2::int begin
  
declare inf_assoc[symmetric, simp] 

ML {* @{type_name unit} *}
  
term "Inf (f ` A)"
  
ML \<open>
  (fn v => fn T => fn e => fn B =>
    let val distrT = Type(@{type_name distr},[T])
        val _ = if fastype_of e = distrT then () 
                else raise(TYPE("variable and expression, type mismatch",[T,fastype_of e],[e]))
        val _ = if fastype_of B = @{typ assertion} then ()
                else raise(TYPE("assertion has wrong type",[fastype_of B],[B]))
        val setT = Type(@{type_name set},[T])
        val supp = Const(@{const_name supp}, distrT --> setT) $ e
        val absB = Term.absfree (v,T) B
        val B2 = @{const Inf(assertion)} $ 
                      (Const(@{const_name image}, (T --> @{typ assertion}) --> setT -->  @{typ "assertion set"})
                         $ absB $ supp)
        val total = @{const classical_subspace} $ 
             HOLogic.mk_eq (Const(@{const_name weight}, distrT --> @{typ real}) $ e, @{term "1::real"})
    in
      @{term "inf::assertion=>assertion=>assertion"} $ total $ B2
    end)

"x1" @{typ int} @{term "uniform {x1::int}"}
@{term "Cla[(x1::int) <= 2]"}
|> Thm.cterm_of @{context}
(*|> Syntax.string_of_term @{context}
|> YXML.content_of*)
\<close>
  
ML \<open>
Term.abstract_over
\<close>
  
  ML \<open> @{term "Inf"}  \<close>
  
ML \<open>Term.dest_Type @{typ "'a set"}\<close>
  
find_theorems "Cla[_] \<sqinter> (Cla[_] \<sqinter> Cla[_])"

lemma "Cla[a1 = 1] \<sqinter> \<lbrakk>q1\<rbrakk> \<equiv>\<qq> \<lbrakk>q2\<rbrakk> \<sqinter> \<CC>\<ll>\<aa>[a1 = 0 \<and> b2 = 0] \<le> undefined"
  apply simp 
  apply auto
    apply (rule classical_simp2)
  done
oops    
    
  
lemma "sup (Cla[a1 = 0 \<and> b2 = 0]) Qeq[q1=q2] \<le> sup (Cla[1 = b2 + 0 + 1]) Qeq[q1=q2]" 
  apply simp
  
  oops
  
    syntax sup (infixl "\<sqinter>" 70)
    
    print_syntax
    
  term "a \<squnion> b"
  term "a \<sqinter> b"
    