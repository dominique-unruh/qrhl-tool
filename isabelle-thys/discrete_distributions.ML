structure Discrete_Distributions = struct

fun mk_distrT T = Type(\<^type_name>\<open>distr\<close>, [T])
fun dest_distrT (Type(\<^type_name>\<open>distr\<close>, [T])) = T
  | dest_distrT T = raise TYPE ("dest_distrT",[T],[])

end