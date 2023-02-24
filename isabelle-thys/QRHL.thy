theory QRHL
  imports Real_Impl.Real_Impl QRHL_Core QRHL_Code Tactics (* Universe_Instances_CryptHOL *)
    Weakest_Precondition Strongest_Postcondition Joint_Measure Joint_Sample Squash_Sampling
    (* Universe_Instances_Bounded_Operators *) O2H Semi_Classical_Search
begin

(* no_notation Infinite_Set_Sum.abs_summable_on (infix "abs'_summable'_on" 50)
hide_const (open) Infinite_Set_Sum.abs_summable_on
notation Infinite_Sum.abs_summable_on (infixr "abs'_summable'_on" 46) *)

no_notation Lattice.meet (infixl "\<sqinter>\<index>" 70)
no_notation Lattice.join (infixl "\<squnion>\<index>" 65)
no_notation Order.top ("\<top>\<index>")
no_notation Order.bottom ("\<bottom>\<index>")

unbundle notation_norm
unbundle cblinfun_notation
unbundle no_jnf_notation

declare [[quick_and_dirty]]

(* declare [[show_types]] *)

end
