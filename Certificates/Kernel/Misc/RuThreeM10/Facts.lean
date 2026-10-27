module

public import Certificates.Kernel.Misc.RuThreeM10.Checks
public import CFSG.Certificates.Kernel.FiveLocKSound
public import CFSG.Certificates.Kernel.Misc.ArrBind
import CFSG.Certificates.Kernel.Spor.RawOrbHead

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMisc.RuThreeM10

open CFSG.EvenSporadicStandard.RuStd.S2 CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum
  CFSG.KC.B3S3K CFSG.Monster.B.Co2.Native CFSG.RankThree.Native CFSG.Monster.B.Mathieu
open CFSG.Monster.B.Co2 (allLt_iff)

theorem hNA : EA.N = 7920 := Nat.eq_of_beq_eq_true n0.1

theorem hNT : ET.N = 720 := Nat.eq_of_beq_eq_true n0.2.1

theorem bindA : BindA 11 4 ruThreeM11 EA.ng EA.G := by
  refine ⟨by rw [Nat.eq_of_beq_eq_true n0.2.2.1]; decide +kernel, fun j hj => ?_⟩
  rw [Nat.eq_of_beq_eq_true n0.2.2.1] at hj
  exact arrBind_sound (bA j hj)

theorem bindT : BindA 11 4 ruThreeM ET.ng ET.G := by
  refine ⟨by rw [Nat.eq_of_beq_eq_true n0.2.2.2]; decide +kernel, fun j hj => ?_⟩
  rw [Nat.eq_of_beq_eq_true n0.2.2.2] at hj
  exact arrBind_sound (bT j hj)

theorem pGA : ∀ k < EA.ng, permB 11 4 (EA.G k) = true := fun k hk =>
  allN_spec pA k (by rwa [Nat.eq_of_beq_eq_true n0.2.2.1] at hk)

theorem pGT : ∀ k < ET.ng, permB 11 4 (ET.G k) = true := fun k hk =>
  allN_spec pT k (by rwa [Nat.eq_of_beq_eq_true n0.2.2.2] at hk)

theorem hkeys : ruThreeKeys11 = k11.toList := by decide +kernel

theorem keys_lt : ∀ p ∈ k11.toList, p < 11 := by decide

theorem enumA : enumOK 11 ruThreeM11 ruThreeKeys11 ruThreeM11Cert = true ∧
    ruThreeM11Cert.pts.size = EA.N ∧ ∀ i < EA.N, ruThreeM11Cert.pts[i]! = unpack 11 4 (EA.T i) := by
  rw [ruThreeM11Cert, hkeys]
  exact enum_of bindA pGA EA.ok keys_lt EA.keys (by rw [hNA]; omega)

theorem enumT : enumOK 11 ruThreeM ruThreeKeys11 ruThreeTCert = true ∧
    ruThreeTCert.pts.size = ET.N ∧ ∀ i < ET.N, ruThreeTCert.pts[i]! = unpack 11 4 (ET.T i) := by
  rw [ruThreeTCert, hkeys]
  exact enum_of bindT pGT ET.ok keys_lt ET.keys (by rw [hNT]; omega)

theorem pTA : ∀ i < EA.N, permB 11 4 (EA.T i) = true := allN_spec EA.perm

theorem pTT : ∀ i < ET.N, permB 11 4 (ET.T i) = true := allN_spec ET.perm

theorem get0 (p : Nat) : (unpack 11 4 p)[0]! = pg 4 (mask 4) p 0 := Orb.unpack_get (by norm_num)

theorem invA_unpack {p : Nat} (hp : permB 11 4 p = true) : invA 11 (unpack 11 4 p) = invK p := by
  unfold invA invK
  rw [comp_unpack' szOK' hp hp, eqA_id szOK' hp, eqA_id szOK' (permB_pcomp szOK' hp hp)]
  cases Nat.beq p (pidn 11 4) <;> rfl

theorem stab : ruThreeStabOK = true := by
  unfold ruThreeStabOK
  rw [allLt_iff]
  intro k hk
  have hk3 : k < ET.ng := by rwa [bindT.1] at hk
  have h := allN_spec kStab k (by rwa [Nat.eq_of_beq_eq_true n0.2.2.2] at hk3)
  rw [bindT.2 k hk3, any_eqA_unpack' szOK' enumA.2.1 enumA.2.2 pTA (pGT k hk3), get0]
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  rw [h1, Nat.eq_of_beq_eq_true h2]
  rfl

theorem cover : ruThreeStabCoverOK = true := by
  unfold ruThreeStabCoverOK
  rw [allLt_iff]
  intro i hi
  rw [enumA.2.1] at hi
  have h := allN_spec kCover i hi
  rw [enumA.2.2 i hi, get0, any_eqA_unpack' szOK' enumT.2.1 enumT.2.2 pTT (pTA i hi)]
  cases h0 : Nat.beq (pg 4 (mask 4) (EA.T i) 0) 0
  · have : (pg 4 (mask 4) (EA.T i) 0 == 0) = false := h0
    rw [this]
    rfl
  · rw [h0] at h
    dsimp only at h
    have : (pg 4 (mask 4) (EA.T i) 0 == 0) = true := h0
    rw [this, h]
    rfl

theorem center : ruThreeCenterOK = true := by
  unfold ruThreeCenterOK
  rw [allLt_iff]
  intro k hk
  rw [enumT.2.1] at hk
  have h := allN_spec kCenter k hk
  have h3 : ruThreeM.size = 3 := by decide +kernel
  have hc : (allLt 3 fun l => commA 11 ruThreeTCert.pts[k]! ruThreeM[l]!) =
      allN 3 (fun l => CFSG.KC.FiveLocK.commK 11 4 (ET.T k) (ET.G l)) := by
    refine CFSG.KC.FiveLocK.allLt_eq_allN fun l hl => ?_
    have hl' : l < ET.ng := by rwa [← bindT.1, h3]
    rw [enumT.2.2 k hk, bindT.2 l hl', CFSG.KC.FiveLocK.commA_unpack szOK' (pTT k hk) (pGT l hl')]
  rw [h3, hc, enumT.2.2 k hk, eqA_id szOK' (pTT k hk)]
  cases hA : allN 3 (fun l => CFSG.KC.FiveLocK.commK 11 4 (ET.T k) (ET.G l))
  · rfl
  · rw [hA] at h
    dsimp only at h
    rw [h]
    rfl

theorem odd : oddNormalOK 11 ruThreeTCert = true := by
  unfold oddNormalOK
  rw [allLt_iff]
  intro k hk
  rw [enumT.2.1] at hk
  have h := allN_spec kOdd k hk
  have hp := pTT k hk
  have hl : ruThreeTCert.pts.toList = (List.range ET.N).map fun i => unpack 11 4 (ET.T i) :=
    toList_of enumT.2.1 enumT.2.2
  rw [enumT.2.2 k hk, eqA_id szOK' hp, hl]
  cases h0 : Nat.beq (ET.T k) (pidn 11 4)
  · rw [h0] at h
    dsimp only at h
    rw [Bool.false_or, Bool.or_eq_true]
    cases h1 : CFSG.KC.LQT.P.anyN 16 fun e => invK (pw 11 4 (ET.T k) e)
    · rw [h1] at h
      right
      rw [anyNP_eq] at h
      obtain ⟨g, hg, hgi⟩ := List.any_eq_true.1 h
      have hg' : g < ET.N := List.mem_range.1 hg
      rw [List.any_map, List.any_eq_true]
      refine ⟨g, hg, ?_⟩
      change invA 11 (compA 11 (unpack 11 4 (ET.T k)) (conjA 11 (unpack 11 4 (ET.T g))
        (unpack 11 4 (ET.T k)))) = true
      rw [conj_unpack' szOK' (pTT g hg') hp, comp_unpack' szOK' hp
        (permB_pcomp szOK' (pTT g hg') (permB_pcomp szOK' hp (permB_pinvS szOK' (pTT g hg'))))]
      rw [invA_unpack (permB_pcomp szOK' hp (permB_pcomp szOK' (pTT g hg')
        (permB_pcomp szOK' hp (permB_pinvS szOK' (pTT g hg')))))]
      exact hgi
    · left
      rw [anyNP_eq] at h1
      obtain ⟨e, he, hei⟩ := List.any_eq_true.1 h1
      refine List.any_eq_true.2 ⟨e, he, ?_⟩
      rw [pow_unpack' szOK' hp, invA_unpack (permB_ppow szOK' hp e)]
      exact hei
  · rfl

theorem m10_ok :
    enumOK 11 ruThreeM11 ruThreeKeys11 ruThreeM11Cert = true ∧
      enumOK 11 ruThreeM ruThreeKeys11 ruThreeTCert = true ∧
      ruThreeStabOK = true ∧ ruThreeStabCoverOK = true ∧ ruThreeCenterOK = true ∧
      oddNormalOK 11 ruThreeTCert = true :=
  ⟨enumA.1, enumT.1, stab, cover, center, odd⟩

end CertificateChecks.KernelMisc.RuThreeM10

end
