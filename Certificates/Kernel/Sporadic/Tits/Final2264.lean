module

public import Certificates.Kernel.Sporadic.Tits.Order2264
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Tits2264

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin
open CFSG.Sporadic.Schreier.Tits CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Certificates.Native CertificateChecks.KernelMisc

theorem ambOK : allN 4 (fun i => bAnd(Nat.beq (TitsA.S i) (TitsText.F i),
    bAnd(canonK 1755 11 (mask 11) (1755 * 11) (TitsA.S i),
      canonK 1755 11 (mask 11) (1755 * 11) (TitsText.F i)))) = true := by
  quickRfl

theorem eq_of_beq {P Q : Nat} (hP : canonK 1755 11 (mask 11) (1755 * 11) P = true)
    (hQ : canonK 1755 11 (mask 11) (1755 * 11) Q = true) (h : P = Q) :
    eqA 1755 (unpack 1755 11 P) (unpack 1755 11 Q) = true := by
  rw [eqA_unpack hP hQ, h, Nat.beq_refl]

theorem facts : titsGenArrs.size = 4 ∧ titsAmbientArrs.size = 14 ∧ titsDerivedArrs.size = 13 ∧
    titsPerfectArrs.size = 12 ∧
    allPermsOK 1755 titsGenArrs = true ∧ allPermsOK 1755 titsAmbientArrs = true ∧
    allPermsOK 1755 titsDerivedArrs = true ∧ allPermsOK 1755 titsPerfectArrs = true ∧
    rawChainOK 1755 (titsAmbientArrs.extract 0 4) titsAmbientArrs (baseArr 1755 titsAmbientBase)
      (wordsArr 4 14 titsAmbientDerivations) 4 = true ∧
    rawChainOK 1755 (titsDerivedArrs.extract 0 2) titsDerivedArrs (baseArr 1755 titsDerivedBase)
      (wordsArr 2 13 titsDerivedDerivations) 4 = true ∧
    rawChainOK 1755 (titsPerfectArrs.extract 0 2) titsPerfectArrs (baseArr 1755 titsPerfectBase)
      (wordsArr 2 12 titsPerfectDerivations) 4 = true ∧
    rawOrbitSizes 1755 titsAmbientArrs (baseArr 1755 titsAmbientBase) = [1755, 80, 8, 2, 4, 4] ∧
    rawOrbitSizes 1755 titsDerivedArrs (baseArr 1755 titsDerivedBase) = [1755, 10, 8, 8, 8, 2] ∧
    rawOrbitSizes 1755 titsPerfectArrs (baseArr 1755 titsPerfectBase) =
      [1755, 10, 8, 2, 8, 4, 2] ∧
    (∀ i < 4, eqA 1755 titsAmbientArrs[i]! titsGenArrs[i]! = true) ∧
    (∀ j < 2, lettersOK 4 (titsU j) = true ∧ lettersOK 4 (titsV j) = true ∧
      isInvA 1755 (wordArr 1755 titsGenArrs (titsU j))
        (invCand 1755 (wordArr 1755 titsGenArrs (titsU j))) = true ∧
      isInvA 1755 (wordArr 1755 titsGenArrs (titsV j))
        (invCand 1755 (wordArr 1755 titsGenArrs (titsV j))) = true ∧
      eqA 1755 titsDerivedArrs[j]! (titsDArr j) = true) ∧
    (∀ j < 2, lettersOK 2 (titsPerfR j) = true ∧ lettersOK 2 (titsPerfS j) = true ∧
      isInvA 1755 (titsDArr j) (invCand 1755 (titsDArr j)) = true ∧
      isInvA 1755 (wordArr 1755 titsDArrs (titsPerfR j))
        (invCand 1755 (wordArr 1755 titsDArrs (titsPerfR j))) = true ∧
      isInvA 1755 (wordArr 1755 titsDArrs (titsPerfS j))
        (invCand 1755 (wordArr 1755 titsDArrs (titsPerfS j))) = true ∧
      eqA 1755 titsPerfectArrs[j]! (titsEArr j) = true) := by
  have hG := gens_bind
  refine ⟨hG.1, by simp [titsAmbientArrs, titsField1755], by simp [titsDerivedArrs, titsField1755],
    by simp [titsPerfectArrs, titsField1755], allPerms_of hG.1 hG.2 gens_perm,
    allPerms_of (by simp [titsAmbientArrs, titsField1755]) (fun j hj => amb_eq hj) permA,
    allPerms_of (by simp [titsDerivedArrs, titsField1755]) (fun j hj => der_eq hj) permD,
    allPerms_of (by simp [titsPerfectArrs, titsField1755]) (fun j hj => perf_eq hj) permP,
    chainA, chainD, chainP, orbitsA, orbitsD, orbitsP, fun i hi => ?_, fun j hj => ?_,
    fun j hj => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := (by simpa only [bAnd_iff] using allN_spec ambOK i hi :
      Nat.beq (TitsA.S i) (TitsText.F i) = true ∧ canonK 1755 11 (mask 11) (1755 * 11) (TitsA.S i) = true ∧
        canonK 1755 11 (mask 11) (1755 * 11) (TitsText.F i) = true)
    rw [amb_eq (by omega), gen_eq hi]
    exact eq_of_beq h2 h3 (Nat.eq_of_beq_eq_true h1)
  · obtain ⟨l1, l2, l3, l4⟩ := (by simpa only [bAnd_iff] using allN_spec lettersOK' j hj :
      lettersK 4 (titsU j) = true ∧ lettersK 4 (titsV j) = true ∧ lettersK 2 (titsPerfR j) = true ∧
        lettersK 2 (titsPerfS j) = true)
    obtain ⟨wU, wV, wD, -⟩ := w_spec hj
    refine ⟨lettersK_sound l1, lettersK_sound l2, by rw [wordU hj]; exact isInv_of wU,
      by rw [wordV hj]; exact isInv_of wV, ?_⟩
    rw [der_eq (by omega), titsDArr_eq hj]
    exact eq_of_beq (permC_spec (permD_spec j hj)).2.1 (permC_spec wD).2.1
      (Nat.eq_of_beq_eq_true (allN_spec dOK j hj)).symm
  · obtain ⟨l1, l2, l3, l4⟩ := (by simpa only [bAnd_iff] using allN_spec lettersOK' j hj :
      lettersK 4 (titsU j) = true ∧ lettersK 4 (titsV j) = true ∧ lettersK 2 (titsPerfR j) = true ∧
        lettersK 2 (titsPerfS j) = true)
    obtain ⟨-, -, wD, wR, wS, wE⟩ := w_spec hj
    have hE : TitsP.S j = Ep j := (Nat.eq_of_beq_eq_true (allN_spec eOK j hj)).symm
    refine ⟨lettersK_sound l3, lettersK_sound l4, by rw [titsDArr_eq hj]; exact isInv_of wD,
      by rw [wordR hj]; exact isInv_of wR, by rw [wordS hj]; exact isInv_of wS, ?_⟩
    rw [perf_eq (by omega), titsEArr_eq hj]
    exact eq_of_beq (by rw [hE]; exact (permC_spec wE).2.1) (permC_spec wE).2.1 hE

end CertificateChecks.KernelSpor.Tits2264

end
