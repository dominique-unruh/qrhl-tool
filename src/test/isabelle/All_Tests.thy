theory All_Tests
  imports 
    (* Tests *)
    Test_Misc Test_Tactics Test_Encoding Test_QRHL_Core

    (* Examples *)
   "QRHL-Examples.Example" "QRHL-Examples.Teleport_Terse" "QRHL-Examples.Teleport"
   "QRHL-Examples.Chsh" "QRHL-Examples.PrgEnc" "QRHL-Examples.Code_Example"
begin

ML \<open> 

val tests =
  \<^theory> |> Resources.master_directory |> File.read_dir
  |> map_filter (fn f => 
      if String.isSuffix ".thy" f andalso f <> "All_Tests.thy" andalso f <> "UnitTest.thy"
      then SOME (substring (f, 0, String.size f - 4)) else NONE)

val examples = \<^theory> |> Resources.master_directory |> (fn p => Path.append p (Path.explode "../../../examples")) |> File.read_dir
  |> map_filter (fn f => if String.isSuffix ".thy" f
      then SOME (substring (f, 0, String.size f - 4)) else NONE)

val theories = \<^theory> |> Context.parents_of |> map Context.theory_name

val _ = tests |> map (fn f =>
  if member op= theories f then () else error ("Add "^f^" to the imports"))

val _ = examples |> map (fn f =>
  if member op= theories f then () else error ("Add \"QRHL-Exports."^f^"\" to the imports"))
\<close>

end
