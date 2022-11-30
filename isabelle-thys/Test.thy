theory Test
  imports 
    QRHL.QRHL
    QRHL.QRHL_Operations
begin

locale bla = fixes hello

ML "open QRHL_Operations"

ML \<open>
get_thms \<^context> "xxx"
\<close>

thm xxx[no_vars]

ML \<open>
get_thms \<^context> "xxx" : thm
\<close>

ML \<open>
thms_as_subgoals (\<^context>, "refl")
\<close>


end
