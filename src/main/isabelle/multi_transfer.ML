structure Multi_Transfer = struct

fun thm_diff plus minus =
  let val minus' = Thmtab.make_set minus in filter_out (Thmtab.defined minus') plus end

fun local_transfer_rules lthy = let
    val mine = Transfer.get_transfer_raw lthy
    val thy = Proof_Context.theory_of lthy
    val their = Transfer.get_transfer_raw (Proof_Context.init_global thy)
  in
    thm_diff mine their
  end

structure Saved_Transfer_Rules = Generic_Data (
  type T = thm list Symtab.table
  val empty = Symtab.empty
  val merge = Symtab.merge (K true) (* TODO: proper merge? *)
  val extend = I)

fun save_transfer_rules locale lthy =
  let 
      val lthy_locale = Named_Target.init' {conclude=I, setup=I} locale (Proof_Context.theory_of lthy)
      val transfer_thms = local_transfer_rules lthy_locale
      val (transfer_thms_exported,thy) = Local_Theory.exit_result_global (fn m => map (Morphism.thm m)) (transfer_thms,lthy_locale)
      val lthy = Context.raw_transfer thy lthy
      val update = Saved_Transfer_Rules.map (Symtab.update (locale,transfer_thms_exported))
      val lthy = Local_Theory.declaration {pervasive=true, syntax=false} (K update) lthy
  in
    lthy
  end

fun transfer_import locale context =
  let val transfer_thms = case Symtab.lookup (Saved_Transfer_Rules.get context) locale of
                            SOME t => t | NONE => error ("Unknown transfer theorem set "^locale)
  in
    fold_rev (Transfer.transfer_raw_add) transfer_thms context
  end

fun transfer_import_attrib locale context =
  transfer_import (Locale.check (Context.theory_of context) locale) context

val _ = Attrib.setup @{binding transfer_import}
  (Scan.lift (Parse.position Parse.name)
    >> (fn locale => Thm.declaration_attribute (K (transfer_import_attrib locale))))
  "Imports transfer rules from locale (needs to be saved with using save_transfer_rules)" 
  |> Theory.setup

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>save_transfer_rules\<close> "Save transfer rules of locale (load with attribute transfer_import)"
    (Parse.position Parse.name >> 
      (fn locale => fn lthy => save_transfer_rules (Locale.check (Proof_Context.theory_of lthy) locale) lthy))

end