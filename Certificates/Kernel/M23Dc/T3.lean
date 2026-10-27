module

public import Certificates.Kernel.M23Dc.Final
public import Certificates.Kernel.M23Dc.T3Checks
public import CFSG.Quasithin.H13.NQCatT3Lat

public section

namespace CFSG.KD.M23Dc

open CFSG.KC.SLDc CFSG.QuasithinUnique.Ch1.SporLat CFSG.Quasithin.H13.NQCat.T3
open CFSG.Quasithin.H.MathieuLat


theorem m23K_notNormal {j : ℕ} (hj : j ∈ [10, 11, 12, 13, 14]) :
    ¬ m23CtxK.Y j ≤ Subgroup.normalizer (m23CtxK.S : Set G) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
  have hj16 : j < 16 := by omega
  have hjJ : j < m23CtxK.J := by rw [m23K_J]; exact hj16
  apply not_le_normalizer_of_label m23CtxK hjJ
  have h := List.all_eq_true.1 t3nnB j (List.mem_range'_1.2 ⟨by omega, by omega⟩)
  obtain ⟨l, hl, hs⟩ := List.any_eq_true.1 h
  obtain ⟨s, hs, hne⟩ := List.any_eq_true.1 hs
  refine ⟨l, ?_, s, ?_, ?_⟩
  · change l ∈ (m23LatK.Om[j]!).lbl.toList
    rw [Om_get hj16]
    simpa [Om, omOf] using hl
  · change s ∈ m23STabs
    rw [← T_eq.2.2]
    exact hs
  · change codeSetAct 23 s l ≠ l
    rw [codeSetAct_eq]
    simpa using hne

end CFSG.KD.M23Dc

end
