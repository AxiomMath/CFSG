module

public import Certificates.Kernel.F4Planes.Glue
public import Certificates.Kernel.F4Planes.Wits
public import CFSG.Certificates.Kernel.F4Planes.WitSound

public section

namespace CFSG.KC.F4Planes

open CFSG.LieType.Simplicity.TitsBits CFSG.KC.F4Salt CFSG.KC.F4Syl3 CFSG.LieType.Ree
  CFSG.RankThree.PartTwo.Sec4.RonanK432 CFSG.LocalAnalysis.ComponentInitial CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


theorem wit3_F42 (K : Type) [Field K] [Finite K] (hK : Nat.card K = 2)
    (a : adjointGroup .F4 K) (ha1 : a ≠ 1) (ha3 : a ^ 3 = 1) :
    Wit3 (⊤ : Subgroup (adjointGroup .F4 K)) a := by
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (k := 1)
    (le_refl 1) (by simpa using hK)
  have hp := pres_F K
  have hm := modelOK_of_chk CFSG.KD.F4Syl3.model_ok
  set P := Subgroup.closure (gensP (sF K) (q4F K) (q5F K))
  have hP : Nat.card P = 3 ^ 6 := (card_P hp hm).trans (by norm_num)
  have hG : Nat.card (adjointGroup ReeTag.F4.tag K) = 3311126603366400 := by
    have h := CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_F4 (K := K)
    rw [hK] at h
    exact h.trans (by norm_num [CFSG.Open.ordF4])
  refine wit3_all_of_sylow ⊤ (fun _ _ _ => Subgroup.mem_top _) P 6 hP (by rw [hG]; decide) ?_
    a ha1 ha3
  intro σ hσ h1 h3
  obtain ⟨m, -, -, hk, hc⟩ := conj_rep hp hm CFSG.KD.F4Syl3.cover_ok hσ h1 h3
  obtain ⟨c, hc⟩ := isConj_iff.1 hc
  have hU3 : phi (sF K) (q4F K) (q5F K)
      (CFSG.KD.F4Syl3.reps.getD (CFSG.KD.F4Syl3.cover.getD m (0, 0)).2 0) ^ 3 = 1 := by
    rw [← hc, conj_pow, h3, mul_one, mul_inv_cancel]
  have hw := (witP_sound (hasBitsS_sF K) (hasBitsS_q4F K) (hasBitsS_q5F K) CFSG.KD.F4Planes.wit_ok
    hk hU3).conj c⁻¹ (fun _ _ => Subgroup.mem_top _)
  have e : c⁻¹ * (c * σ * c⁻¹) * c⁻¹⁻¹ = σ := by group
  rwa [← hc, e] at hw

end CFSG.KC.F4Planes

end
