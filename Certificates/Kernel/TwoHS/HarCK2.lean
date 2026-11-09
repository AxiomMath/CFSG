module

public import Certificates.Kernel.TwoHS.HarCK
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

set_option maxRecDepth 400000

namespace CFSG.KD.TwoHS

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.EvenSporadicStandard.TwoHS

theorem harC_invY {p r : Nat} (hp : cnK p = true) (hr : cnK r = true)
    (h : invEqK 11200 14 (mask 14) (11200 * 14) p r = true) : invYK p (pinvY p) = true := by
  rw [pinvY_eq hp hr h]
  exact harC_invG (c := cnK) (e := invEqK 11200 14 (mask 14) (11200 * 14)) harC_invU hp hr h

theorem harC_invF {j k : Nat} (h : harCQA (harCQPairs.getD j ([], true)).1 k = true) :
    invYK (UK (harCQPairs.getD j ([], true)).1) (pinvY (UK (harCQPairs.getD j ([], true)).1)) =
      true := by
  unfold harCQA at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨he, hk, hkk⟩ := h
  rw [harC_UK, Nat.eq_of_beq_eq_true he]
  exact harC_invY hk hk hkk

theorem harC_invA : allN 6 (fun j => invYK (UK (harCQPairs.getD j ([], true)).1)
    (pinvY (UK (harCQPairs.getD j ([], true)).1))) = true :=
  CFSG.KS.Raw.Orb.allN_iff.2 fun j hj => harC_invF (harC_aF j hj)

theorem harC_inv3 : invYK G3K (pinvY G3K) = true := by
  have h := harC_tc
  simp only [Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, -⟩ := h
  rw [← harC_tG3]
  exact harC_invY h1 h2 h3

theorem harC_inv5 : invYK G5K (pinvY G5K) = true := by
  have h := harC_tc
  simp only [Bool.and_eq_true] at h
  obtain ⟨-, -, -, h4, h5, h6⟩ := h
  rw [← harC_tG5]
  exact harC_invY h4 h5 h6

theorem harC_inv : bAnd(allN 6 (fun j => invYK (UK (harCQPairs.getD j ([], true)).1)
    (pinvY (UK (harCQPairs.getD j ([], true)).1))),
    bAnd(invYK G3K (pinvY G3K), invYK G5K (pinvY G5K))) = true := by
  rw [harC_invA, harC_inv3, harC_inv5]

end CFSG.KD.TwoHS

end
