module

public import Certificates.Kernel.IdxFour.Lbar
public import Certificates.Kernel.IdxFour.TcosetOK
public import CFSG.Certificates.Kernel.IdxFourTcosetSound
public import CFSG.GF2Type.Smith1979.IdxFourModelBasic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.KD.IF4T

open Module CFSG.KC.IF4C CFSG.KC.IF4R CFSG.KC.IF4L CFSG.KC.IF4T CFSG.KD.IF4L
open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA
open CFSG.GF2Type.Smith1979.GammaU.Viol CFSG.GF2Type.Smith1979.IdxFour

theorem maskOK_spec {LP : List ℕ} {OM : ℕ} {ms : List ℕ} (h : maskOK LP OM ms = true) :
    ∀ m < 2 ^ LP.length,
      (mulP (subP LP m) OM = mulP OM (subP LP m) ↔ m = 0 ∨ m ∈ ms) := by
  unfold maskOK at h
  rw [allBelow_iff, lenN_eq] at h
  intro m hm
  have hm' := h m hm
  have key : Nat.beq (mulP (subP LP m) OM) (mulP OM (subP LP m)) = (Nat.beq m 0 || memN m ms) := by
    revert hm'
    cases Nat.beq (mulP (subP LP m) OM) (mulP OM (subP LP m)) <;>
      cases (Nat.beq m 0 || memN m ms) <;> decide
  constructor
  · intro e
    have h1 : Nat.beq (mulP (subP LP m) OM) (mulP OM (subP LP m)) = true := by simp [e]
    rw [key] at h1
    simpa [memN_iff] using h1
  · intro h'
    have h1 : (Nat.beq m 0 || memN m ms) = true := by
      rcases h' with rfl | h'
      · rfl
      · simp [(memN_iff m ms).2 h']
    rw [← key] at h1
    exact Nat.eq_of_beq_eq_true h1

theorem isP_theta : IsP thetaU (packR omegaRows) :=
  (isP_iff_of_rowsP (by decide +kernel) thetaU).2 fun v => by
    rw [thetaU_apply, linOfRows_omegaRows]

theorem TR_masks : TR.map (fun r => nthD 0 r 0) = INN := by decide +kernel

theorem comm_theta_iff {m : ℕ} (hm : m < 32) :
    subG lbarL m * thetaU = thetaU * subG lbarL m ↔ m = 0 ∨ m ∈ INN := by
  have a := (isP_subG lbar_F m).mul isP_theta
  have b := isP_theta.mul (isP_subG lbar_F m)
  rw [← TR_masks, ← maskOK_spec cf17610mask m (by simpa [lbarGens] using hm)]
  constructor
  · intro e
    rw [e] at a
    exact mulP_eq_of_isP' a b
  · intro e
    rw [e] at a
    exact IsP.inj a b

theorem card_comm_theta :
    Nat.card {t // t ∈ genGrp lbarGens ∧ t * thetaU = thetaU * t} = 16 := by
  let f : {m : Fin 32 // m.1 = 0 ∨ m.1 ∈ INN} →
      {t // t ∈ genGrp lbarGens ∧ t * thetaU = thetaU * t} := fun m =>
    ⟨subG lbarL m.1.1, subG_mem_Lbar _, (comm_theta_iff m.1.2).2 m.2⟩
  have hf : Function.Bijective f := by
    refine ⟨fun a b e => Subtype.ext (Fin.ext (subG_inj_Lbar a.1.2 b.1.2
      (congrArg Subtype.val e))), ?_⟩
    rintro ⟨t, ht, hc⟩
    obtain ⟨m, hm, rfl⟩ := mem_Lbar_iff.1 ht
    exact ⟨⟨⟨m, hm⟩, (comm_theta_iff hm).1 hc⟩, rfl⟩
  rw [← Nat.card_eq_of_bijective f hf, Nat.card_eq_fintype_card]
  decide

theorem linP_vtBasis_mem (u : V12) : linP (packL vtBasis) u ∈ spanOf vtBasis := by
  rw [linP_apply]
  refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_
  have hj : fld (packL vtBasis) j = 0 ∨ fld (packL vtBasis) j ∈ vtBasis := by
    revert j
    decide +kernel
  rcases hj with h | h
  · rw [h, vecOf_zero]
    exact zero_mem _
  · exact Submodule.subset_span ⟨_, h, rfl⟩

theorem cf17610rec_all {k : ℕ} (hk : k < 15) : cf17610rec k = true := by
  interval_cases k
  · exact cf17610rec0
  · exact cf17610rec1
  · exact cf17610rec2
  · exact cf17610rec3
  · exact cf17610rec4
  · exact cf17610rec5
  · exact cf17610rec6
  · exact cf17610rec7
  · exact cf17610rec8
  · exact cf17610rec9
  · exact cf17610rec10
  · exact cf17610rec11
  · exact cf17610rec12
  · exact cf17610rec13
  · exact cf17610rec14

theorem modelInner_inner {t : V12 ≃ₗ[ZMod 2] V12} (ht : t ∈ genGrp lbarGens) (h1 : t ≠ 1)
    (h2 : thetaU * t = t * thetaU) : ModelInner (spanOf vtBasis) t := by
  obtain ⟨m, hm, rfl⟩ := mem_Lbar_iff.1 ht
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact h1 (subG_zero _)
  have hmem : m ∈ TR.map (fun r => nthD 0 r 0) := by
    rw [TR_masks]
    exact ((comm_theta_iff hm).1 h2.symm).resolve_left hm0
  obtain ⟨k, hk, hkm⟩ := List.getElem_of_mem hmem
  have hk' : k < TR.length := by simpa using hk
  have h15 : k < 15 := by
    have := cf17610len.1
    rw [lenN_eq] at this
    omega
  have hr : nthD 0 (nthD [] TR k) 0 = m := by
    rw [nthD_eq [] TR k, List.getD_eq_getElem _ _ hk', ← hkm, List.getElem_map]
  have htOK : tOK (lbarGens.map packR) (packL vtBasis) (nthD 0 (nthD [] TR k) 0)
      (nthD 0 (nthD [] TR k) 1) (nthD 0 (nthD [] TR k) 2) (nthD 0 (nthD [] TR k) 3)
      (nthD 0 (nthD [] TR k) 4) (nthD 0 (nthD [] TR k) 5) (nthD 0 (nthD [] TR k) 6)
      (nthD [] TW k) = true := cf17610rec_all h15
  rw [hr] at htOK
  exact modelInner_of_tOK (isP_subG lbar_F m) h2 linP_vtBasis_mem htOK

end CFSG.KD.IF4T

end
