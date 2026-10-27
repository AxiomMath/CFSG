module

public import Certificates.Kernel.HMathieu.T12Elems
public import CFSG.Certificates.Kernel.HMathieu.TabSound
public import Certificates.Data.SmithB45MatHat

public section

namespace CertificateChecks.KernelHMathieu.T12

open CFSG.KC.HMathieu CFSG.KC.Enum CFSG.KS CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H13.A5.M12
open CFSG.Quasithin.B45Mat

theorem packedF : Packed T12s2 E where
  elems := elems_eq
  one := by
    have e : T12s2 = PT.ofGens 24 (gens.map unpk) 64 := by
      unfold T12s2
      congr 1
    rw [e]
    rfl
  vp := List.all_eq_true.1 vpE

theorem lenPF : P.length = 36 := by rw [pOK]; simp [lenOK.1]

variable [Fact (T12s2.check = true)]

theorem invDataF : InvData T12s2 E inv P :=
  ⟨by rw [invols_idx packedF, invOK], pOK⟩

theorem lenF : inv12s2F.length = 35 := by
  rw [inv12s2F, length_invols invDataF, lenOK.1]

theorem gtabsF : GTabs inv12s2F (cmD rows) (mkD rows) :=
  gtabs_of packedF invDataF (by rw [lenOK.1]; exact tabs)

theorem act_elF {k : Nat} (hk : k ≤ 35) :
    act12s2 (el inv12s2F k) = actM (Mc.getD k []) := by
  funext m
  have e := map_elems_get packedF (fun a => matOf 10 (actC12 a)) (el inv12s2F k)
  unfold act12s2 mats12s2 matsOf12
  have hk' : k ≤ T12s2.invols.length := by rw [← inv12s2F, lenF]; exact hk
  rw [e, show inv12s2F = T12s2.invols from rfl, pk_el packedF invDataF hk', mcOK]
  congr 2
  rw [getD_map_lt _ _ (by rw [lenPF]; omega) _ 0]
  unfold matP
  congr 1

theorem act_memF {x : T12s2.Elem} (hx : x ∈ inv12s2F) :
    act12s2 x = actM (Mc.getD (inv12s2F.idxOf x) []) := by
  rw [← act_elF (by rw [← lenF]; exact idxOf_le x), el_idxOf (Or.inl hx)]

end CertificateChecks.KernelHMathieu.T12

end
