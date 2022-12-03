theory All_Example_Thys
  imports 
    (* Examples *)
    "QRHL-Examples.Example" "QRHL-Examples.Teleport"
    "QRHL-Examples.Chsh" "QRHL-Examples.PrgEnc" "QRHL-Examples.Code_Example"
    "QRHL-Examples.EPR" "QRHL-Examples.RandomOracle"
begin

ML \<open>

val has_missing = Unsynchronized.ref false

val examples = \<^theory> |> Resources.master_directory |> (fn p => Path.append p (Path.explode "../../../examples")) |> File.read_dir
  |> map_filter (fn f => if String.isSuffix ".thy" f andalso f <> "TestEx.thy"
      then SOME (substring (f, 0, String.size f - 4)) else NONE)

val theories = \<^theory> |> Context.parents_of |> map Context.theory_name

val _ = examples |> map (fn f =>
  if member op= theories f then () else (warning ("Add \"QRHL-Examples."^f^"\" to the imports"); has_missing := true))

val _ = if !has_missing then error "Please fix imports" else ()

\<close>

end
