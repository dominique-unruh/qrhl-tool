
theory Complex_Inner_Product
  imports Complex_Main 
begin


typedef (overloaded) 'a linear_space = \<open>{S::'a set. True}\<close>
  by simp

setup_lifting type_definition_linear_space


end
