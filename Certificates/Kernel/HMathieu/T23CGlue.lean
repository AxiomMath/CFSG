
module

public import Certificates.Kernel.HMathieu.T23C
public import Certificates.Kernel.HMathieu.T23Glue

public section

namespace CertificateChecks.KernelHMathieu.T23C

open CFSG.KC.HMathieu CFSG.KC.Enum CFSG.KS CFSG.Quasithin.H.Mathieu CertificateChecks.KernelHMathieu

theorem lenMc : Mc.length = 36 := by rw [mcOK, List.length_map, T23.lenP]

theorem act_el {k : Nat} (hk : k ≤ 35) :
    act23s2 (el inv23s2 k) = actM (Mc.getD k []) := by
  funext m
  have e := map_elems_get T23.packed (fun a => matOf 11 (act11 a)) (el inv23s2 k)
  unfold act23s2 mats23s2 matsOf11
  have hk' : k ≤ T23s2.invols.length := by rw [← inv23s2, T23.len]; exact hk
  rw [e, show inv23s2 = T23s2.invols from rfl, pk_el T23.packed T23.invData hk', mcOK]
  congr 2
  rw [getD_map_lt _ _ (by rw [T23.lenP]; omega) _ 0]
  unfold matP
  congr 1

theorem act_mem {x : T23s2.Elem} (hx : x ∈ inv23s2) :
    act23s2 x = actM (Mc.getD (inv23s2.idxOf x) []) := by
  rw [← act_el (by rw [← T23.len]; exact idxOf_le x), el_idxOf (Or.inl hx)]

end CertificateChecks.KernelHMathieu.T23C

end
