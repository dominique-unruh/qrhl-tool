structure Registers = struct

datatype qc = Classical | Quantum (* TODO used? Otherwise move to qrhl-tool. *)

fun dest_qregisterT (\<^Type>\<open>qregister T U\<close>) = (T,U)
  | dest_qregisterT (\<^Type>\<open>dummy\<close>) = (dummyT, dummyT) (* So that it also works in not yet type-inferred terms *)
  | dest_qregisterT T = raise TYPE("dest_qregisterT", [T], [])

fun is_empty_qregisterT ctxt (\<^Type>\<open>qregister T _\<close>) = Sign.of_sort (Proof_Context.theory_of ctxt) (T,\<^sort>\<open>CARD_1\<close>)
  | is_empty_qregisterT _ T = raise TYPE("is_empty_qregisterT: not a qregister type", [T], [])

fun is_empty_qregister ctxt t = is_empty_qregisterT ctxt (fastype_of t)
  handle TYPE(_, Ts, _) => raise TYPE("is_empty_qregister: not a qregister type", Ts, [t])

fun is_index_qregister (\<^Const_>\<open>qregister_pair _ _ _\<close> $ t $ u) = is_index_qregister t andalso is_index_qregister u
  | is_index_qregister (\<^Const_>\<open>qregister_chain _ _ _\<close> $ t $ u) = is_index_qregister t andalso is_index_qregister u
  | is_index_qregister (\<^Const_>\<open>empty_qregister _ _\<close>) = true
  | is_index_qregister (\<^Const_>\<open>qregister_id _\<close>) = true
  | is_index_qregister (\<^Const_>\<open>qFst _ _\<close>) = true
  | is_index_qregister (\<^Const_>\<open>qSnd _ _\<close>) = true
  | is_index_qregister _ = false

fun is_INDEX_QREGISTER (\<^Const_>\<open>sup _\<close> $ t $ u) = is_INDEX_QREGISTER t andalso is_INDEX_QREGISTER u
  | is_INDEX_QREGISTER (\<^Const_>\<open>QREGISTER_chain _ _\<close> $ \<^Const_>\<open>qFst _ _\<close> $ t) = is_INDEX_QREGISTER t
  | is_INDEX_QREGISTER (\<^Const_>\<open>QREGISTER_chain _ _\<close> $ \<^Const_>\<open>qSnd _ _\<close> $ t) = is_INDEX_QREGISTER t
  | is_INDEX_QREGISTER (\<^Const_>\<open>bot \<open>\<^Type>\<open>QREGISTER _\<close>\<close>\<close>) = true
  | is_INDEX_QREGISTER (\<^Const_>\<open>top \<open>\<^Type>\<open>QREGISTER _\<close>\<close>\<close>) = true
  | is_INDEX_QREGISTER (\<^Const_>\<open>QREGISTER_fst _ _\<close>) = true
  | is_INDEX_QREGISTER (\<^Const_>\<open>QREGISTER_snd _ _\<close>) = true
  | is_INDEX_QREGISTER _ = false

fun same_prod f g (x,y) = (f x, Same.commit g y) handle Same.SAME => (x, g y)

(* raises SAME. Guaranteed to change the term. *)
fun quick_norm_register (\<^Const_>\<open>qregister_chain _ _ _\<close> $ \<^Const_>\<open>qregister_id _\<close> $ G) = 
      Same.commit quick_norm_register G
  | quick_norm_register (\<^Const_>\<open>qregister_chain _ _ _\<close> $ G $ \<^Const_>\<open>qregister_id _\<close>) =
      Same.commit quick_norm_register G
  | quick_norm_register (\<^Const_>\<open>qregister_chain _ _ _\<close> $ (\<^Const_>\<open>qregister_pair _ _ _\<close> $ F $ _) $ \<^Const_>\<open>qFst _ _\<close>) =
      Same.commit quick_norm_register F
  | quick_norm_register (\<^Const_>\<open>qregister_chain _ _ _\<close> $ (\<^Const_>\<open>qregister_pair _ _ _\<close> $ _ $ G) $ \<^Const_>\<open>qSnd _ _\<close>) =
      Same.commit quick_norm_register G
  | quick_norm_register (\<^Const_>\<open>qregister_chain _ _ _\<close> $ (\<^Const_>\<open>qregister_pair inF outF _\<close> $ F $ _) $ (\<^Const_>\<open>qregister_chain _ _ inG\<close> $ \<^Const_>\<open>qFst _ _\<close> $ G)) =
      Same.commit quick_norm_register (\<^Const>\<open>qregister_chain inF outF inG\<close> $ F $ G)
  | quick_norm_register (\<^Const_>\<open>qregister_chain _ _ _\<close> $ (\<^Const_>\<open>qregister_pair _ outF inF\<close> $ _ $ F) $ (\<^Const_>\<open>qregister_chain _ _ inG\<close> $ \<^Const_>\<open>qSnd _ _\<close> $ G)) =
      Same.commit quick_norm_register (\<^Const>\<open>qregister_chain inF outF inG\<close> $ F $ G)
  | quick_norm_register (\<^Const_>\<open>qregister_chain _ _ inH\<close> $ (\<^Const_>\<open>qregister_chain inF outF inG\<close> $ F $ G) $ H) =
      Same.commit quick_norm_register (\<^Const>\<open>qregister_chain inF outF inG\<close> $ F $ (\<^Const>\<open>qregister_chain inG inF inH\<close> $ G $ H))
  | quick_norm_register (t as (\<^Const_>\<open>qregister_chain _ _ _\<close> $ (\<^Const_>\<open>empty_qregister _ _\<close> $ _) $ _)) =
      Const(\<^const_name>\<open>empty_qregister\<close>, fastype_of t)
  | quick_norm_register (t as (\<^Const_>\<open>qregister_chain _ _ _\<close> $ _ $ (\<^Const_>\<open>empty_qregister _ _\<close> $ _))) =
      Const(\<^const_name>\<open>empty_qregister\<close>, fastype_of t)
  | quick_norm_register ((pair as \<^Const_>\<open>qregister_pair _ _ _\<close>) $ F $ G) = let
      val (F',G') = same_prod quick_norm_register quick_norm_register (F,G)
      in Same.commit quick_norm_register (pair $ F' $ G') end
  | quick_norm_register ((chain as \<^Const_>\<open>qregister_chain _ _ _\<close>) $ F $ G) = let
    val (F',G') = same_prod quick_norm_register quick_norm_register (F,G)
    in Same.commit quick_norm_register (chain $ F' $ G') end
  | quick_norm_register _ = raise Same.SAME

(* Transforms F into [F1,\<dots>,Fn] such that F is equivalent to (F1;\<dots>Fn). *)
(* TODO: support cregisters as well *)
(* TODO: rename \<rightarrow> ..._register *)
fun explode_variable' (Const(\<^const_name>\<open>qregister_pair\<close>,_) $ F $ G) = explode_variable' F @ explode_variable' G
  | explode_variable' (Const(\<^const_name>\<open>qregister_chain\<close>,_) $ F $ G) =
      explode_variable' G 
        |> map (fn g =>
                  \<^Const>\<open>qregister_chain \<open>fastype_of F |> dest_qregisterT |> fst\<close> \<open>fastype_of F |> dest_qregisterT |> snd\<close> \<open>fastype_of g |> dest_qregisterT |> fst\<close>\<close> 
                    $ F $ g)
        |> map (fn fg => explode_variable' (quick_norm_register fg) handle Same.SAME => [fg])
        |> flat
  | explode_variable' \<^Const_>\<open>empty_qregister _ _\<close> = []
  | explode_variable' F = [F]
fun explode_variable t = explode_variable' (Same.commit quick_norm_register t)

(* Transforms [F1,\<dots>,Fn] into (F1;\<dots>Fn). *)
(* Note: not an exact inverse of explode_variable: it's only guaranteed that 
   "implode_variable (explode_variable X)" is equivalent to X *)
(* TODO: support cregisters as well *)
(* TODO: rename \<rightarrow> ..._register *)
fun implode_variable _ [a] = a
  | implode_variable T [] = \<^Const>\<open>empty_qregister HOLogic.unitT T\<close>
  | implode_variable T (F::Gs) = let
      val G = implode_variable T Gs
      in
       \<^Const>\<open>qregister_pair \<open>fastype_of F |> dest_qregisterT |> fst\<close> \<open>fastype_of F |> dest_qregisterT |> snd\<close> \<open>fastype_of G |> dest_qregisterT |> fst\<close>\<close> 
        $ F $ G
      end

end
