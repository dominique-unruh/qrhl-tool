theory QRHL
  imports Real_Impl.Real_Impl QRHL_Core QRHL_Code Tactics Universe_Instances_CryptHOL
    Weakest_Precondition Strongest_Postcondition Joint_Measure Joint_Sample Squash_Sampling
    Universe_Instances_Bounded_Operators O2H Semi_Classical_Search
begin

no_notation Infinite_Set_Sum.abs_summable_on (infix "abs'_summable'_on" 50)
hide_const (open) Infinite_Set_Sum.abs_summable_on
notation Infinite_Sum.abs_summable_on (infixr "abs'_summable'_on" 46)

unbundle norm_syntax
unbundle cblinfun_syntax
unbundle no jnf_syntax

declare [[quick_and_dirty]]

end
