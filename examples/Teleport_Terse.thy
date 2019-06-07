theory Teleport_Terse
  imports QRHL.QRHL "../isabelle-thys/Code_Hacks"
begin

definition "xxx ==
idOp \<otimes> remove_qvar_unit_op \<cdot> (assoc_op* \<cdot> comm_op \<otimes> idOp \<cdot> assoc_op) \<cdot> assoc_op* \<cdot>
    eigenspace (1::complex) comm_op \<otimes> \<top>
    \<le> idOp \<otimes> remove_qvar_unit_op \<cdot> assoc_op* \<cdot>
       space_div_unlifted
        (assoc_op \<cdot>
         (idOp \<otimes> (assoc_op* \<cdot> (comm_op \<otimes> idOp \<cdot> assoc_op)) \<cdot>
          (assoc_op* \<cdot> (comm_op \<otimes> idOp \<cdot> assoc_op) \<cdot> idOp \<otimes> (idOp \<otimes> comm_op))) \<cdot>
         (idOp \<otimes> (idOp \<otimes> comm_op \<cdot> (assoc_op* \<cdot> comm_op \<otimes> idOp \<cdot> assoc_op)) \<cdot>
          (assoc_op* \<cdot> comm_op \<otimes> idOp \<cdot> assoc_op) \<cdot>
          assoc_op* \<cdot>
          CNOT \<otimes> idOp \<cdot>
          (assoc_op \<cdot>
           (assoc_op* \<cdot> (comm_op \<otimes> idOp \<cdot> assoc_op) \<cdot>
            idOp \<otimes> (assoc_op* \<cdot> (comm_op \<otimes> idOp \<cdot> assoc_op) \<cdot> idOp \<otimes> comm_op))) \<cdot>
          (idOp \<otimes> (idOp \<otimes> (idOp \<otimes> remove_qvar_unit_op \<cdot> assoc_op*) \<cdot> assoc_op*) \<cdot> assoc_op* \<cdot>
           (idOp \<otimes> (idOp \<otimes> comm_op \<cdot> (assoc_op* \<cdot> comm_op \<otimes> idOp \<cdot> assoc_op)) \<cdot>
            (assoc_op* \<cdot> comm_op \<otimes> idOp \<cdot> assoc_op) \<cdot>
            hadamard \<otimes> idOp \<cdot>
            (assoc_op* \<cdot> (comm_op \<otimes> idOp \<cdot> assoc_op) \<cdot>
             idOp \<otimes> (assoc_op* \<cdot> (comm_op \<otimes> idOp \<cdot> assoc_op) \<cdot> idOp \<otimes> comm_op)) \<cdot>
            (idOp \<otimes> (idOp \<otimes> (idOp \<otimes> remove_qvar_unit_op \<cdot> assoc_op*) \<cdot> assoc_op*) \<cdot>
             assoc_op* \<cdot>
             (\<Sqinter>x::bit.
                 idOp \<otimes> (idOp \<otimes> (idOp \<otimes> remove_qvar_unit_op \<cdot> assoc_op*) \<cdot> assoc_op*) \<cdot>
                 assoc_op* \<cdot>
                 (assoc_op* \<cdot> comm_op \<otimes> idOp \<cdot> assoc_op \<cdot>
                  idOp \<otimes> (assoc_op* \<cdot> comm_op \<otimes> idOp \<cdot> assoc_op) \<cdot>
                  idOp \<otimes> (idOp \<otimes> comm_op) \<cdot>
                  idOp \<otimes> assoc_op* \<cdot>
                  assoc_op* \<cdot>
                  (\<Sqinter>xa::bit.
                      idOp \<otimes> (idOp \<otimes> remove_qvar_unit_op \<cdot> assoc_op*) \<cdot> assoc_op* \<cdot>
                      (assoc_op* \<cdot>
                       ((if x = (0::bit) then \<top>
                         else idOp \<otimes> pauliX \<cdot>
                              (idOp \<otimes> remove_qvar_unit_op \<cdot> assoc_op* \<cdot>
                               (idOp \<otimes> remove_qvar_unit_op \<cdot> assoc_op* \<cdot>
                                (if xa = (0::bit) then \<top>
                                 else idOp \<otimes> pauliZ \<cdot>
                                      (idOp \<otimes> remove_qvar_unit_op \<cdot>
                                       (assoc_op* \<cdot> comm_op \<otimes> idOp \<cdot> assoc_op) \<cdot>
                                       assoc_op* \<cdot>
                                       eigenspace (1::complex) comm_op \<otimes> \<top>)) \<otimes>
                                \<top> \<sqinter>
                                (idOp \<otimes> remove_qvar_unit_op \<cdot>
                                 (assoc_op* \<cdot> comm_op \<otimes> idOp \<cdot> assoc_op) \<cdot>
                                 assoc_op* \<cdot>
                                 (if xa = (1::bit) then \<top>
                                  else eigenspace (1::complex) comm_op) \<otimes>
                                 \<top>)) \<otimes>
                               \<top>)) \<sqinter>
                        (if x = (1::bit) then \<top>
                         else idOp \<otimes> remove_qvar_unit_op \<cdot> assoc_op* \<cdot>
                              (if xa = (0::bit) then \<top>
                               else idOp \<otimes> pauliZ \<cdot>
                                    (idOp \<otimes> remove_qvar_unit_op \<cdot>
                                     (assoc_op* \<cdot> comm_op \<otimes> idOp \<cdot> assoc_op) \<cdot>
                                     assoc_op* \<cdot>
                                     eigenspace (1::complex) comm_op \<otimes> \<top>)) \<otimes>
                              \<top> \<sqinter>
                              (idOp \<otimes> remove_qvar_unit_op \<cdot>
                               (assoc_op* \<cdot> comm_op \<otimes> idOp \<cdot> assoc_op) \<cdot>
                               assoc_op* \<cdot>
                               (if xa = (1::bit) then \<top>
                                else eigenspace (1::complex) comm_op) \<otimes>
                               \<top>))) \<otimes>
                       \<top> \<sqinter>
                       (idOp \<otimes> comm_op \<cdot> (assoc_op* \<cdot> comm_op \<otimes> idOp \<cdot> assoc_op) \<cdot>
                        Complex_L2.span {ket xa} \<otimes> \<top>)) \<otimes>
                      \<top> +
                      idOp \<otimes> comm_op \<cdot> (assoc_op* \<cdot> comm_op \<otimes> idOp \<cdot> assoc_op) \<cdot>
                      ortho (Complex_L2.span {ket xa}) \<otimes> \<top>) \<otimes>
                  \<top> \<sqinter>
                  Complex_L2.span {ket x} \<otimes> \<top>) \<otimes>
                 \<top> +
                 ortho (Complex_L2.span {ket x}) \<otimes> \<top>) \<otimes>
             \<top>)) \<otimes>
           \<top>)))
        EPR \<otimes>
       \<top>
"

export_code xxx in SML module_name XXX file_prefix xxx

lemma teleport_terse:
  assumes[simp]: "declared_qvars \<lbrakk>A1,B1,C1,A2\<rbrakk>"
  shows "\<lbrakk>C1\<rbrakk> \<equiv>\<qq> \<lbrakk>A2\<rbrakk> \<le> \<CC>\<ll>\<aa>[norm EPR = 1] \<sqinter> (\<CC>\<ll>\<aa>[isometry CNOT] \<sqinter> ((CNOT\<guillemotright>\<lbrakk>C1, A1\<rbrakk>)* \<cdot> (\<CC>\<ll>\<aa>[isometry hadamard] \<sqinter> ((hadamard\<guillemotright>\<lbrakk>C1\<rbrakk>)* \<cdot> ((let M = computational_basis in \<CC>\<ll>\<aa>[mtotal M] \<sqinter> (\<Sqinter>z. let P = mproj M z\<guillemotright>\<lbrakk>A1\<rbrakk> \<cdot> \<top> in (let M = computational_basis in \<CC>\<ll>\<aa>[mtotal M] \<sqinter> (\<Sqinter>za. let P = mproj M za\<guillemotright>\<lbrakk>C1\<rbrakk> \<cdot> \<top> in (\<CC>\<ll>\<aa>[z \<noteq> 1] + \<CC>\<ll>\<aa>[isometry pauliX] \<sqinter> ((pauliX\<guillemotright>\<lbrakk>B1\<rbrakk>)* \<cdot> ((\<CC>\<ll>\<aa>[za \<noteq> 1] + \<CC>\<ll>\<aa>[isometry pauliZ] \<sqinter> ((pauliZ\<guillemotright>\<lbrakk>B1\<rbrakk>)* \<cdot> (\<lbrakk>B1\<rbrakk> \<equiv>\<qq> \<lbrakk>A2\<rbrakk> \<sqinter> (pauliZ\<guillemotright>\<lbrakk>B1\<rbrakk> \<cdot> \<top>)))) \<sqinter> (\<CC>\<ll>\<aa>[za = 1] + \<lbrakk>B1\<rbrakk> \<equiv>\<qq> \<lbrakk>A2\<rbrakk>) \<sqinter> (pauliX\<guillemotright>\<lbrakk>B1\<rbrakk> \<cdot> \<top>)))) \<sqinter> (\<CC>\<ll>\<aa>[z = 1] + (\<CC>\<ll>\<aa>[za \<noteq> 1] + \<CC>\<ll>\<aa>[isometry pauliZ] \<sqinter> ((pauliZ\<guillemotright>\<lbrakk>B1\<rbrakk>)* \<cdot> (\<lbrakk>B1\<rbrakk> \<equiv>\<qq> \<lbrakk>A2\<rbrakk> \<sqinter> (pauliZ\<guillemotright>\<lbrakk>B1\<rbrakk> \<cdot> \<top>)))) \<sqinter> (\<CC>\<ll>\<aa>[za = 1] + \<lbrakk>B1\<rbrakk> \<equiv>\<qq> \<lbrakk>A2\<rbrakk>)) \<sqinter> P + ortho P)) \<sqinter> P + ortho P)) \<sqinter> (hadamard\<guillemotright>\<lbrakk>C1\<rbrakk> \<cdot> \<top>))) \<sqinter> (CNOT\<guillemotright>\<lbrakk>C1, A1\<rbrakk> \<cdot> \<top>)))) \<div> EPR\<guillemotright>\<lbrakk>A1, B1\<rbrakk>"
  apply (simp add: prepare_for_code)
  using [[show_sorts]]
  apply (rule mark_for_let_simprocE)
  by eval

end
