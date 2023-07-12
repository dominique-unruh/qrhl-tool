theory All_Unit_Tests
  imports 
    Test_Misc Test_Tactics Test_Expressions Test_QRHL_Core Test_Weakest_Precondition
    Test_QRHL_Operations Test_Strongest_Postcondition Test_Squash_Sampling
begin

ML \<open>

val has_missing = Unsynchronized.ref false

val tests =
  \<^theory> |> Resources.master_directory |> File.read_dir
  |> map_filter (fn f => 
      if String.isSuffix ".thy" f andalso f <> "All_Tests.thy" andalso f <> "UnitTest.thy" 
        andalso f <> "All_Unit_Tests.thy" andalso f <> "All_Example_Thys.thy"
      then SOME (substring (f, 0, String.size f - 4)) else NONE)

val theories = \<^theory> |> Context.parents_of |> map (Context.theory_name {long=false})

val _ = tests |> map (fn f =>
  if member op= theories f then () else (warning ("Add "^f^" to the imports"); has_missing := true))

val _ = if !has_missing then error "Please fix imports" else ()

\<close>

end
