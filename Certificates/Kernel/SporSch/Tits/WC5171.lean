module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeWCTitsInputs
public import Certificates.Kernel.SporSch.Tits.Abel2261
public import Certificates.Kernel.LocalComp.Child3Lemmas
public import CFSG.Certificates.Kernel.LocalQTCovTPrim
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Sporadic.Schreier.TitsInvCheck

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.TitsWC5171

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Child3
open CFSG.Sporadic.Schreier.Tits hiding titsXArr titsYArr titsZArr
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.RankThree.PartTwo.Sec4.Item434RemTits CFSG.LocalAnalysis.RankThreeTheoremC.TenNineOneThree
open CertificateChecks.KernelSpor CertificateChecks.KernelSporSch
open CertificateChecks.KernelSporSch.TitsAbel

@[expose] noncomputable def I : Nat := pidn 1755 11

@[expose] noncomputable def wcP (X Y Z g : Nat) : Bool :=
  canonK 1755 11 (mask 11) (1755 * 11) g &&
    (!(Nat.beq (pc g Y) (pc Y g) && Nat.beq (pc g Z) (pc Z g)) || Nat.beq g I || Nat.beq g X ||
      Nat.beq g (pc X X))

theorem wordK_eq {wd : List Int} (hl : lettersK 13 wd = true) :
    wordEqK 1755 11 (mask 11) (pidn 1755 11) TitsD.S TitsD.SI 13 wd (wK wd) = true := by
  have e : Nat.beq (wordK 1755 11 (mask 11) (pidn 1755 11) TitsD.S TitsD.SI wd) (wK wd) = true :=
    Nat.beq_refl _
  unfold wordEqK
  rw [hl, e] <;> rfl

theorem wa {wd : List Int} (hl : lettersK 13 wd = true) :
    wordArr 1755 titsDerivedArrs wd = unpack 1755 11 (wK wd) :=
  wa_eq (wordK_eq hl)

theorem hI : unpack 1755 11 I = idA 1755 := CFSG.KC.LQT.Cov.T.unpack_pidn (by norm_num) (by norm_num)

theorem lX : lettersK 13 xWord = true := by quickRfl
theorem lY : lettersK 13 yWord = true := by quickRfl
theorem lZ : lettersK 13 zWord = true := by quickRfl
theorem lU : lettersK 13 (titsUWord ++ titsUInvWord) = true := by quickRfl
theorem lS : sylWords.all (lettersK 13) = true := by quickRfl

theorem cI : CnN 1755 11 I := by quickRfl
theorem cX : CnN 1755 11 (wK xWord) := by quickRfl
theorem cY : CnN 1755 11 (wK yWord) := by quickRfl
theorem cZ : CnN 1755 11 (wK zWord) := by quickRfl
theorem cU : CnN 1755 11 (wK (titsUWord ++ titsUInvWord)) := by quickRfl

theorem kU : Nat.beq (wK (titsUWord ++ titsUInvWord)) I = true := by quickRfl

theorem kY : (!Nat.beq (wK yWord) I && !Nat.beq (wK yWord) (wK xWord) &&
    !Nat.beq (wK yWord) (pc (wK xWord) (wK xWord))) = true := by quickRfl

theorem kSyl : sylWords.all (fun w => wcP (wK xWord) (wK yWord) (wK zWord) (wK w)) = true := by
  quickRfl

theorem wcP_sound {w : List Int} (hl : lettersK 13 w = true)
    (h : wcP (wK xWord) (wK yWord) (wK zWord) (wK w) = true) :
    (!(commA (wordArr 1755 titsDerivedArrs w) titsYArr &&
        commA (wordArr 1755 titsDerivedArrs w) titsZArr) ||
      eqA 1755 (wordArr 1755 titsDerivedArrs w) (idA 1755) ||
      eqA 1755 (wordArr 1755 titsDerivedArrs w) titsXArr ||
      eqA 1755 (wordArr 1755 titsDerivedArrs w) (compA 1755 titsXArr titsXArr)) = true := by
  unfold wcP at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hc, h⟩ := h
  have cg : CnN 1755 11 (wK w) := hc
  unfold commA titsYArr titsZArr titsXArr
  rw [wa hl, wa lY, wa lZ, wa lX, ← hI, compA_unpackN cg cY, compA_unpackN cY cg,
    compA_unpackN cg cZ, compA_unpackN cZ cg, compA_unpackN cX cX,
    eqA_unpackN (canon_pcN cg cY) (canon_pcN cY cg), eqA_unpackN (canon_pcN cg cZ) (canon_pcN cZ cg),
    eqA_unpackN cg cI, eqA_unpackN cg cX, eqA_unpackN cg (canon_pcN cX cX)]
  exact h

theorem titsWC_true : titsWCCheck = true := by
  have h1 : lettersOK 13 xWord = true := by quickRfl
  have h2 : lettersOK 13 yWord = true := by quickRfl
  have h3 : lettersOK 13 zWord = true := by quickRfl
  have h4 : lettersOK 13 (titsUWord ++ titsUInvWord) = true := by quickRfl
  have h5 : eqA 1755 (wordArr 1755 titsDerivedArrs (titsUWord ++ titsUInvWord)) (idA 1755) =
      true := by
    rw [wa lU, ← hI, eqA_unpackN cU cI]
    exact kU
  have h6 : sylArrs.all (fun g => !(commA g titsYArr && commA g titsZArr) ||
      eqA 1755 g (idA 1755) || eqA 1755 g titsXArr || eqA 1755 g (compA 1755 titsXArr titsXArr)) =
      true := by
    unfold sylArrs
    rw [List.all_map]
    refine List.all_eq_true.2 fun w hw => ?_
    exact wcP_sound (List.all_eq_true.1 lS w hw) (List.all_eq_true.1 kSyl w hw)
  have h7 : (!(eqA 1755 titsYArr (idA 1755)) && !(eqA 1755 titsYArr titsXArr) &&
      !(eqA 1755 titsYArr (compA 1755 titsXArr titsXArr))) = true := by
    unfold titsYArr titsXArr
    rw [wa lY, wa lX, ← hI, compA_unpackN cX cX, eqA_unpackN cY cI, eqA_unpackN cY cX,
      eqA_unpackN cY (canon_pcN cX cX)]
    exact kY
  unfold titsWCCheck
  simp only [Bool.and_eq_true] at h7
  simp only [h1, h2, h3, h4, h5, h6, h7.1.1, h7.1.2, h7.2, Bool.and_self]

end CertificateChecks.KernelSporSch.TitsWC5171

end
