module

public import Certificates.Kernel.ThCent.L5Q

public section

namespace CFSG.KD.ThCent.L

open CFSG.KC.Th CFSG.KC.Th.BigS CFSG.KC.ThCent

@[expose] noncomputable def ch7q (i : Nat) : Bool :=
  chunkOK (eltRec ThS.c ThS.rm ThS.ONE V7 W.Z7 24) L7.E (i * 7) 7

theorem ch7_of_q (k : Nat) (h0 : ch7q (7 * k) = true) (h1 : ch7q (7 * k + 1) = true)
    (h2 : ch7q (7 * k + 2) = true) (h3 : ch7q (7 * k + 3) = true)
    (h4 : ch7q (7 * k + 4) = true) (h5 : ch7q (7 * k + 5) = true)
    (h6 : ch7q (7 * k + 6) = true) : ch7 k = true := by
  simp only [ch7q] at h0 h1 h2 h3 h4 h5 h6
  have e : (49 : Nat) = 7 + (7 + (7 + (7 + (7 + (7 + 7))))) := rfl
  rw [ch7, e]
  simp only [chunkOK_add, Bool.and_eq_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rwa [(by omega : 7 * k * 7 = k * 49)] at h0
  · rwa [(by omega : (7 * k + 1) * 7 = k * 49 + 7)] at h1
  · rwa [(by omega : (7 * k + 2) * 7 = k * 49 + 7 + 7)] at h2
  · rwa [(by omega : (7 * k + 3) * 7 = k * 49 + 7 + 7 + 7)] at h3
  · rwa [(by omega : (7 * k + 4) * 7 = k * 49 + 7 + 7 + 7 + 7)] at h4
  · rwa [(by omega : (7 * k + 5) * 7 = k * 49 + 7 + 7 + 7 + 7 + 7)] at h5
  · rwa [(by omega : (7 * k + 6) * 7 = k * 49 + 7 + 7 + 7 + 7 + 7 + 7)] at h6

end CFSG.KD.ThCent.L

end
