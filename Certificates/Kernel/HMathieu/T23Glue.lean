
module

public import Certificates.Kernel.HMathieu.T23
public import CFSG.Certificates.Kernel.HMathieu.TabSound
public import CFSG.Quasithin.Background.HMathieuCodeInvInputs

public section

namespace CertificateChecks.KernelHMathieu.T23

open CFSG.KC.HMathieu CFSG.KC.Enum CFSG.KS CFSG.Quasithin.H.Mathieu

theorem t23_eq : T23s2 = PT.ofGens 24 (gens.map unpk) 64 := by
  unfold T23s2
  congr 1

theorem packed : Packed T23s2 E where
  elems := by
    rw [t23_eq]
    change bfsClosure 24 (gens.map unpk) 64 = _
    rw [bfsClosure_eq (List.all_eq_true.1 vpG), bfs]
  one := by rw [t23_eq]; rfl
  vp := List.all_eq_true.1 vpE

theorem invData : InvData T23s2 E inv P :=
  ⟨by rw [invols_idx packed, invOK], pOK⟩

theorem len : inv23s2.length = 35 := by
  rw [inv23s2, length_invols invData, lenOK]

theorem lenP : P.length = 36 := by rw [pOK]; simp [lenOK]

theorem actC_el {k : Nat} (hk : k ≤ 35) :
    (fun m => actM (matsC23[(el inv23s2 k).idx]!) m) = actM (Md.getD k []) := by
  funext m
  have e := map_elems_get packed (fun a => matOf 11 (actC11 a)) (el inv23s2 k)
  unfold matsC23 matsOfC11
  have hk' : k ≤ T23s2.invols.length := by rw [← inv23s2, len]; exact hk
  rw [e, show inv23s2 = T23s2.invols from rfl, pk_el packed invData hk', mdOK]
  congr 2
  rw [getD_map_lt _ _ (by rw [lenP]; omega) _ 0]
  unfold matP
  congr 1

theorem actC_mem {x : T23s2.Elem} (hx : x ∈ inv23s2) :
    (fun m => actM (matsC23[x.idx]!) m) = actM (Md.getD (inv23s2.idxOf x) []) := by
  rw [← actC_el (by rw [← len]; exact idxOf_le x), el_idxOf (Or.inl hx)]

end CertificateChecks.KernelHMathieu.T23

end
