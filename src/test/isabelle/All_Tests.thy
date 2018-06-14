theory All_Tests
  imports Test_Misc Test_Tactics Test_Encoding Test_QRHL_Core
begin

ML \<open> 

val files =
  @{theory} |> Resources.master_directory |> File.read_dir
  |> map_filter (fn f => 
      if String.isSuffix ".thy" f andalso f <> "All_Tests.thy" andalso f <> "UnitTest.thy"
      then SOME (substring (f, 0, String.size f - 4)) else NONE)

val theories = @{theory} |> Context.parents_of |> map Context.theory_name

val _ = files |> map (fn f =>
  if member op= theories f then () else error ("Add "^f^" to the imports"))

\<close>

end