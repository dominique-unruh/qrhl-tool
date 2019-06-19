
theory Bot  
  imports Main
begin


typedef 'a t = \<open>{S::'a set. True}\<close>
  by simp

setup_lifting type_definition_t


end
