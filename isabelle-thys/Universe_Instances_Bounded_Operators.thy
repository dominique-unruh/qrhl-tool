theory Universe_Instances_Bounded_Operators
  imports Bounded_Operators.Complex_L2 Universe_Instances_Complex_Main
begin

derive universe ell2
derive universe linear_space
(* derive universe subspace *)
derive universe cblinfun
(* derive universe l2bounded *)

end