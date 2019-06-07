theory Code_Hacks
  imports Main
begin

ML \<open>
fun make_context name aterm t = let
  fun make (t$u) i = make t i $ make u i
    | make (Abs(a,T,t)) i = Abs(a,T,make t (i+1))
    | make t i = if t=aterm then Bound i else t
in Abs(name, fastype_of aterm, make t 0) end
\<close>

ML \<open>
fun const_has_sorts ctxt (Const(name,_)) = let
    fun is_sort [] = false
      | is_sort \<^sort>\<open>type\<close> = false
      | is_sort _ = true
    fun has_sort (Type(_,ts)) = exists has_sort ts
      | has_sort (TVar(_,sort)) = is_sort sort
      | has_sort (TFree(_,sort)) = is_sort sort
    val (_,T) = Consts.the_const (Proof_Context.consts_of ctxt) name
    in has_sort T end
  | const_has_sorts _ t = raise TERM("const_has_sorts: expecting Const",[t])
;;
const_has_sorts \<^context> \<^term>\<open>map\<close>
\<close>

ML \<open>
(* consts must be <> [] *)
fun fixup_code_conv' ctxt idx consts ct = (* case Thm.term_of ct of
  Const(\<^const_name>\<open>Let\<close>,_) $ Const _ $ Abs _ => 
      Conv.arg_conv (fixup_code_conv' ctxt idx consts) ct
  | t =>  *) let
      val const = hd consts
      val tail = tl consts
      val const_name = Term.term_name const
      val context = make_context const_name const (Thm.term_of ct)
      val letx = infer_instantiate' ctxt [SOME (Thm.cterm_of ctxt context), SOME (Thm.cterm_of ctxt const)] 
                   (Thm.incr_indexes (idx+1) @{thm Let_def[symmetric]})
      val conv = if null tail then Conv.rewr_conv letx else Conv.rewr_conv letx then_conv fixup_code_conv' ctxt idx tail
    in conv ct end

fun fixup_code_conv ctxt ct = let
  val t = (Thm.term_of ct)
val _ = \<^print> ct
  val idx = Thm.maxidx_of_cterm ct
  val consts = fold_aterms (fn t => fn l => case t of 
    Const nT => Const nT::l | _ => l) t [] 
      |> sort Term_Ord.fast_term_ord
      |> distinct op=
      |> filter (const_has_sorts ctxt)
  val _ = if null consts then raise CTERM("no consts",[ct]) else ()
in fixup_code_conv' ctxt idx consts ct end

fun fixup_code_conv2 ctxt ct = case Thm.term_of ct of
  Const(\<^const_name>\<open>Let\<close>,_) $ Const _ $ Abs _ => 
      Conv.arg_conv (Conv.abs_conv (K (fixup_code_conv2 ctxt)) ctxt) ct
  | _ => fixup_code_conv ctxt ct


fun fixup_code ctxt thm = let
  val thm2 = Drule.abs_def thm
  val thm3 = Conv.fconv_rule (Conv.arg_conv (fixup_code_conv2 ctxt)) thm2 |> SOME
             handle CTERM _ => NONE
in thm3 end
\<close>

setup \<open>
Code_Preproc.add_functrans ("deduplicate_consts", Code_Preproc.simple_functrans (fn ctxt => fn thms => 
  case thms of [thm] => (case fixup_code ctxt thm of SOME thm' => SOME [thm'] |> \<^print>| _ => NONE) | _ => NONE))
\<close>

definition [code del]: "mark_for_let_simproc x == x"
lemma mark_for_let_simprocE: "mark_for_let_simproc x \<Longrightarrow> x"
  unfolding mark_for_let_simproc_def by simp

setup \<open>let fun simproc morph ctxt ct =
  SOME ((Conv.rewr_conv @{thm mark_for_let_simproc_def}
         then_conv 
         fixup_code_conv ctxt)
        ct) in
    Code_Preproc.map_pre (fn ctxt => ctxt
    addsimprocs [Simplifier.make_simproc ctxt "let" {lhss=[\<^term>\<open>mark_for_let_simproc x\<close>], proc=simproc}]) end
\<close>

end
