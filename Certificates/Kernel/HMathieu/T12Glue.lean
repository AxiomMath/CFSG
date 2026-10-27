module

public import Certificates.Kernel.HMathieu.T12
public import CFSG.Certificates.Kernel.HMathieu.TabSound
public import CFSG.Quasithin.H13.A5M12SylBase

public section

namespace CertificateChecks.KernelHMathieu.T12

open CFSG.KC.HMathieu CFSG.KC.Enum CFSG.KS CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H13.A5.M12

theorem t12_eq : T12s2 = PT.ofGens 24 (gens.map unpk) 64 := by
  unfold T12s2
  congr 1

theorem packed : Packed T12s2 E where
  elems := by
    rw [t12_eq]
    change bfsClosure 24 (gens.map unpk) 64 = _
    rw [bfsClosure_eq (List.all_eq_true.1 vpG), bfs]
  one := by rw [t12_eq]; rfl
  vp := List.all_eq_true.1 vpE

theorem invData : InvData T12s2 E inv P :=
  ⟨by rw [invols_idx packed, invOK], pOK⟩

theorem len : inv12s2.length = 35 := by
  rw [inv12s2, length_invols invData, lenOK.1]

theorem gtabs : GTabs inv12s2 (cmD rows) (mkD rows) :=
  gtabs_of packed invData (by rw [lenOK.1]; exact tabs)

theorem lenP : P.length = 36 := by rw [pOK]; simp [lenOK.1]

theorem act_el {k : Nat} (hk : k ≤ 35) :
    act12s2 (el inv12s2 k) = actM (Mc.getD k []) := by
  funext m
  have e := map_elems_get packed (fun a => matOf 10 (actC12 a)) (el inv12s2 k)
  unfold act12s2 mats12s2 matsOf12
  have hk' : k ≤ T12s2.invols.length := by rw [← inv12s2, len]; exact hk
  rw [e, show inv12s2 = T12s2.invols from rfl, pk_el packed invData hk', mcOK]
  congr 2
  rw [getD_map_lt _ _ (by rw [lenP]; omega) _ 0]
  unfold matP
  congr 1

end CertificateChecks.KernelHMathieu.T12

end
