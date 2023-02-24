structure Print_Term_Reliably = struct

(* Identical to Sledgehammer_Isar_Annotate *)
fun post_traverse_term_type' f _ (t as Const (_, T)) s = f t T s
  | post_traverse_term_type' f _ (t as Free (_, T)) s = f t T s
  | post_traverse_term_type' f _ (t as Var (_, T)) s = f t T s
  | post_traverse_term_type' f env (t as Bound i) s = f t (nth env i) s
  | post_traverse_term_type' f env (Abs (x, T1, b)) s =
    let val ((b', s'), T2) = post_traverse_term_type' f (T1 :: env) b s in
      f (Abs (x, T1, b')) (T1 --> T2) s'
    end
  | post_traverse_term_type' f env (u $ v) s =
    let
      val ((u', s'), Type (_, [_, T])) = post_traverse_term_type' f env u s
      val ((v', s''), _) = post_traverse_term_type' f env v s'
    in f (u' $ v') T s'' end
    handle Bind => raise Fail "Sledgehammer_Isar_Annotate: post_traverse_term_type'"

(* Identical to Sledgehammer_Isar_Annotate *)
fun post_traverse_term_type f s t =
  post_traverse_term_type' (fn t => fn T => fn s => (f t T s, T)) [] t s |> fst
fun post_fold_term_type f s t =
  post_traverse_term_type (fn t => fn T => fn s => (t, f t T s)) s t |> snd

(* Identical to Sledgehammer_Isar_Annotate *)
fun fold_map_atypes f T s =
  (case T of
    Type (name, Ts) =>
    let val (Ts, s) = fold_map (fold_map_atypes f) Ts s in
      (Type (name, Ts), s)
    end
  | _ => f T s)

(* Identical to Sledgehammer_Isar_Annotate *)
val indexname_ord = Term_Ord.fast_indexname_ord
val cost_ord = prod_ord int_ord (prod_ord int_ord int_ord)

(* Identical to Sledgehammer_Isar_Annotate *)
structure Var_Set_Tab = Table(
  type key = indexname list
  val ord = list_ord indexname_ord)

(* Identical to Sledgehammer_Isar_Annotate *)
fun generalize_types ctxt t =
  let
    val erase_types = map_types (fn _ => dummyT)
    (* use schematic type variables *)
    val ctxt = ctxt |> Proof_Context.set_mode Proof_Context.mode_pattern
    val infer_types = singleton (Type_Infer_Context.infer_types ctxt)
  in
     t |> erase_types |> infer_types
  end

(* Identical to Sledgehammer_Isar_Annotate *)
fun match_types ctxt t1 t2 =
  let
    val thy = Proof_Context.theory_of ctxt
    val get_types = post_fold_term_type (K cons) []
  in
    fold (perhaps o try o Sign.typ_match thy) (get_types t1 ~~ get_types t2) Vartab.empty
  end


(* Identical to Sledgehammer_Isar_Annotate *)
fun key_of_atype (TVar (z, _)) = Ord_List.insert indexname_ord z
  | key_of_atype _ = I
fun key_of_type T = fold_atyps key_of_atype T []

(* Identical to Sledgehammer_Isar_Annotate *)
fun update_tab t T (tab, pos) =
  ((case key_of_type T of
     [] => tab
   | key =>
     let val cost = (size_of_typ T, (size_of_term t, pos)) in
       (case Var_Set_Tab.lookup tab key of
         NONE => Var_Set_Tab.update_new (key, cost) tab
       | SOME old_cost =>
         (case cost_ord (cost, old_cost) of
           LESS => Var_Set_Tab.update (key, cost) tab
         | _ => tab))
     end),
   pos + 1)

(* Identical to Sledgehammer_Isar_Annotate *)
val typing_spot_table = post_fold_term_type update_tab (Var_Set_Tab.empty, 0) #> fst

(* Identical to Sledgehammer_Isar_Annotate *)
fun reverse_greedy typing_spot_tab =
  let
    fun update_count z =
      fold (fn tvar => fn tab =>
        let val c = Vartab.lookup tab tvar |> the_default 0 in
          Vartab.update (tvar, c + z) tab
        end)
    fun superfluous tcount = forall (fn tvar => the (Vartab.lookup tcount tvar) > 1)
    fun drop_superfluous (tvars, (_, (_, spot))) (spots, tcount) =
      if superfluous tcount tvars then (spots, update_count ~1 tvars tcount)
      else (spot :: spots, tcount)

    val (typing_spots, tvar_count_tab) =
      Var_Set_Tab.fold (fn kv as (k, _) => apfst (cons kv) #> apsnd (update_count 1 k))
        typing_spot_tab ([], Vartab.empty)
      |>> sort_distinct (rev_order o cost_ord o apply2 snd)
  in
    fold drop_superfluous typing_spots ([], tvar_count_tab) |> fst
  end

(* Identical to Sledgehammer_Isar_Annotate *)
fun introduce_annotations subst spots t t' =
  let
    fun subst_atype (T as TVar (idxn, S)) subst =
        (Envir.subst_type subst T, Vartab.update (idxn, (S, dummyT)) subst)
      | subst_atype T subst = (T, subst)

    val subst_type = fold_map_atypes subst_atype

    fun collect_annot _ T (subst, cp, ps as p :: ps', annots) =
        if p <> cp then
          (subst, cp + 1, ps, annots)
        else
          let val (T, subst) = subst_type T subst in
            (subst, cp + 1, ps', (p, T) :: annots)
          end
      | collect_annot _ _ x = x

    val (_, _, _, annots) = post_fold_term_type collect_annot (subst, 0, spots, []) t'

    fun insert_annot t _ (cp, annots as (p, T) :: annots') =
        if p <> cp then (t, (cp + 1, annots)) else (Type.constraint T t, (cp + 1, annots'))
      | insert_annot t _ x = (t, x)
  in
    t |> post_traverse_term_type insert_annot (0, rev annots) |> fst
  end

(* Modified from Sledgehammer_Isar_Annotate: Invocation of handle_trivial_tfrees removed *)
fun annotate_types_in_term ctxt t =
  let
    val t' = generalize_types ctxt t
    val subst = match_types ctxt t' t
    val typing_spots = t' |> typing_spot_table |> reverse_greedy |> sort int_ord
  in
    introduce_annotations subst typing_spots t t'
  end

(* Given an unchecked term, fix it up so that unparsing with show_sorts=true will add a sort constraint to every type variable exactly once *)
fun strip_duplicate_sorts ctxt t = let
  val defaultS = Sign.defaultS (Proof_Context.theory_of ctxt)
  val seen = Unsynchronized.ref []
  fun f_sort T sort = if sort = defaultS orelse member (op=) (!seen) T then dummyS 
                      else (seen := T :: !seen; sort)
  fun f_atyp (T as TFree(name, sort)) = TFree(name, f_sort T sort)
    | f_atyp (T as TVar(name, sort)) = TVar(name, f_sort T sort)
    | f_atyp T = T
  val f_typ = map_atyps f_atyp
  fun f_aterm (Const("_type_constraint_", Type("fun",[T,_]))) = 
        let val T' = f_typ T in Const("_type_constraint_", T' --> T') end
    | f_aterm t = t
  val t = map_aterms f_aterm t
  in t end

fun print_term ctxt t = let
  val t = singleton (Syntax.uncheck_terms ctxt) t
  val t = annotate_types_in_term ctxt t
  val t = strip_duplicate_sorts ctxt t
  val ctxt = ctxt
    |> Config.put show_markup false
    |> Config.put Printer.show_type_emphasis false
    |> Config.put show_types false
    |> Config.put show_sorts true
    |> Config.put show_consts false
  val str = Print_Mode.setmp [] (Syntax.unparse_term ctxt #> Pretty.string_of) t
  val str = Sledgehammer_Util.simplify_spaces str
  val str = YXML.content_of str
in str end

end