structure Registers = struct

datatype qc = Classical | Quantum (* TODO used? Otherwise move to qrhl-tool. *)

fun dest_qregisterT (\<^Type>\<open>qregister T U\<close>) = (T,U)
  | dest_qregisterT (\<^Type>\<open>dummy\<close>) = (dummyT, dummyT) (* So that it also works in not yet type-inferred terms *)
  | dest_qregisterT T = raise TYPE("dest_qregisterT", [T], [])

fun is_empty_qregisterT ctxt (\<^Type>\<open>qregister T _\<close>) = Sign.of_sort (Proof_Context.theory_of ctxt) (T,\<^sort>\<open>CARD_1\<close>)
  | is_empty_qregisterT _ T = raise TYPE("is_empty_qregisterT: not a qregister type", [T], [])

fun is_empty_qregister ctxt t = is_empty_qregisterT ctxt (fastype_of t)
  handle TYPE(_, Ts, _) => raise TYPE("is_empty_qregister: not a qregister type", Ts, [t])

(* Transforms F into [F1,\<dots>,Fn] such that F is equivalent to (F1;\<dots>Fn). *)
(* TODO: support cregisters as well *)
(* TODO: rename \<rightarrow> ..._register *)
fun explode_variable (Const(\<^const_name>\<open>qregister_pair\<close>,_) $ F $ G) = explode_variable F @ explode_variable G
  | explode_variable (Const(\<^const_name>\<open>qregister_chain\<close>,_) $ \<^Const_>\<open>qregister_id _\<close> $ G) = explode_variable G
  | explode_variable (Const(\<^const_name>\<open>qregister_chain\<close>,_) $ F $ \<^Const_>\<open>qregister_id _\<close>) = explode_variable F
  | explode_variable (Const(\<^const_name>\<open>qregister_chain\<close>,_) $ F $ G) =
      explode_variable G |> map (fn g =>
         \<^Const>\<open>qregister_chain \<open>fastype_of F |> dest_qregisterT |> fst\<close> \<open>fastype_of F |> dest_qregisterT |> snd\<close> \<open>fastype_of g |> dest_qregisterT |> fst\<close>\<close> 
        $ F $ g)
  | explode_variable \<^Const_>\<open>empty_qregister _ _\<close> = []
  | explode_variable F = [F]    

(* Transforms [F1,\<dots>,Fn] into (F1;\<dots>Fn). *)
(* Note: not an exact inverse of explode_variable: it's only guaranteed that 
   "implode_variable (explode_variable X)" is equivalent to X *)
(* TODO: support cregisters as well *)
(* TODO: rename \<rightarrow> ..._register *)
fun implode_variable T [a] = a
  | implode_variable T [] = \<^Const>\<open>empty_qregister HOLogic.unitT T\<close>
  | implode_variable T (F::Gs) = let
      val G = implode_variable T Gs
      in
       \<^Const>\<open>qregister_pair \<open>fastype_of F |> dest_qregisterT |> fst\<close> \<open>fastype_of F |> dest_qregisterT |> snd\<close> \<open>fastype_of G |> dest_qregisterT |> fst\<close>\<close> 
        $ F $ G
      end

end
