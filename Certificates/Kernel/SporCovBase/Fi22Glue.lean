
module

public import Certificates.Kernel.SporCovBase.Fi22GlueBase

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi22Witness
public import CFSG.LocalAnalysis.StandardType.GGSporKRestDistinct

public section

namespace CFSG.KD.SporCovBase.Fi22

open CFSG.KC.SporCov CFSG.KD.SporCov CFSG.StandardType.SporadicShape CFSG.Sporadic.Th
open CFSG.Sporadic.Fi22 (J a b)

theorem complete :
    ∀ s : J, orderOf s = 3 → ∃ j : Fin 4, IsConj (rT j) s :=
  sporKRest_complete_of_distinct (fun k : Fin 4 =>
      CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi22Three.xRep k)
    (fun s hs => by
      obtain ⟨k, hk, hc⟩ := CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi22Three.fi22_classify s hs
      exact ⟨⟨k, hk⟩, hc⟩)
    (fun j => rT j) (fun j => rT_order j.isLt)
    (fun j j' hc => F_inj j j' (by rw [← rT_fix j.isLt, ← rT_fix j'.isLt]; exact fixN_of_isConj hc))

theorem sporKRestCover_three_J :
    SporKRestCover 3 ↥J := by
  have hgen : ∀ j : Fin 4, ∀ y, IsConj (rT j) y → SporKRestGenerating 3 y := by
    intro j
    have ht := fun k (hk : k < 4) => (okF_parts.2 k hk)
    fin_cases j
    · exact gen_path (i := 0) (by norm_num)
    · exact gen_path (i := 1) (by norm_num)
    · have h2 := ht 2 (by norm_num)
      unfold chkT at h2
      simp only [Bool.and_eq_true] at h2
      exact gen_cent Ck.okC h2.1.1.1
    · have h3 := ht 3 (by norm_num)
      unfold chkT at h3
      simp only [Bool.and_eq_true] at h3
      exact gen_cent Ck.okD h3.1.1.1
  refine sporKRest_cover_of_classes Nat.prime_three (List.ofFn fun j : Fin 4 => rT j)
    (fun s hs => ?_) (fun r hr x hx => ?_)
  · obtain ⟨j, hj⟩ := complete s hs
    exact ⟨rT j, List.mem_ofFn.2 ⟨j, rfl⟩, hj⟩
  · obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hr
    exact hgen j x hx

end CFSG.KD.SporCovBase.Fi22

end
