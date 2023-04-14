structure Register_Syntax = struct
local open Registers in

fun register_n Quantum true 1 = Const(\<^const_name>\<open>qregister_id\<close>, dummyT)
  | register_n Classical true 1 = Const(\<^const_name>\<open>cregister_id\<close>, dummyT)
  | register_n Quantum false 1 = Const(\<^const_name>\<open>qFst\<close>, dummyT)
  | register_n Classical false 1 = Const(\<^const_name>\<open>cFst\<close>, dummyT)
  | register_n Quantum true 2 = Const(\<^const_name>\<open>qSnd\<close>, dummyT)
  | register_n Classical true 2 = Const(\<^const_name>\<open>cSnd\<close>, dummyT)
  | register_n Quantum last n = let
      val _ = n > 1 orelse error "register_n: n must be >= 1"
      in Const(\<^const_name>\<open>qregister_chain\<close>, dummyT) $ Const(\<^const_name>\<open>qSnd\<close>, dummyT) $ register_n Quantum last (n-1) end
  | register_n Classical last n = let
      val _ = n > 1 orelse error "register_n: n must be >= 1"
      in Const(\<^const_name>\<open>cregister_chain\<close>, dummyT) $ Const(\<^const_name>\<open>cSnd\<close>, dummyT) $ register_n Classical last (n-1) end

end
end
