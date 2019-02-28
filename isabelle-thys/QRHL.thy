theory QRHL
  imports Algebraic_Numbers.Real_Algebraic_Numbers (* Real_Sqrt2 *) QRHL_Core QRHL_Code Tactics Universe_Instances_CryptHOL Weakest_Precondition
    Joint_Measure
begin

(* Hiding constants/syntax that were overwritten by Jordan_Normal_Form *)
hide_const (open) Lattice.sup
hide_const (open) Lattice.inf
hide_const (open) Order.top
hide_const (open) card_UNIV
hide_const (open) Coset.kernel
hide_const (open) span
no_notation "Order.bottom" ("\<bottom>\<index>")
no_notation "Order.top" ("\<top>\<index>")
no_notation "Lattice.meet" (infixl "\<sqinter>\<index>" 70)
no_notation "Lattice.join" (infixl "\<squnion>\<index>" 65)
hide_const (open) Order.bottom Order.top

declare [[quick_and_dirty]]

end
