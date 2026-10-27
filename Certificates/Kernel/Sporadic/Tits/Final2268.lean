module

public import Certificates.Kernel.Sporadic.Tits.Texts2268
public import Certificates.Kernel.Sporadic.Tits.LocH
public import Certificates.Kernel.Sporadic.Tits.LocS
public import Certificates.Kernel.Sporadic.Tits.LocN
public import Certificates.Kernel.Sporadic.Tits.LocJ
public import Certificates.Kernel.Sporadic.Tits.LocK
public import Certificates.Kernel.Sporadic.Tits.LocR
public import Certificates.Kernel.Sporadic.Tits.GroupT2264
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Tits2268

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin
open CFSG.Sporadic.Schreier.Tits CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Certificates.Native CertificateChecks.KernelMisc CertificateChecks.KernelSpor.Tits2264

theorem derBind : titsDerivedArrs.size = 13 ∧
    ∀ j < 13, titsDerivedArrs[j]! = unpack 1755 11 (TitsD.S j) :=
  ⟨by simp [titsDerivedArrs, titsField1755], fun _ hj => der_eq hj⟩

theorem init_of {A : Array (Array Nat)} {ws : List (List Int)} {k : Nat} {PX : Nat → Nat}
    (hl : ws.length = k) (hA : ∀ i < k, A[i]! = unpack 1755 11 (PX i))
    (hw : allN k (fun i => bAnd(wordEqK 1755 11 (mask 11) (pidn 1755 11) TitsD.S TitsD.SI 13
      ws[i]! (PX i), canonK 1755 11 (mask 11) (1755 * 11) (PX i))) = true) :
    initialWordsOK A ws = true := by
  unfold initialWordsOK
  rw [allLt_iff, hl]
  intro i hi
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 (allN_spec hw i hi)
  have h := wordEqK_sound derBind permD h1
  rw [Bool.and_eq_true]
  refine ⟨h.2, ?_⟩
  rw [hA i hi]
  change eqA 1755 _ (wordA 1755 titsDerivedArrs (rawInvs 1755 titsDerivedArrs) ws[i]!) = true
  rw [h.1, eqA_unpack h2 h2, Nat.beq_refl]

theorem wH : allN 3 (fun i => bAnd(wordEqK 1755 11 (mask 11) (pidn 1755 11) TitsD.S TitsD.SI 13
    titsHWords[i]! (TitsH.S i), canonK 1755 11 (mask 11) (1755 * 11) (TitsH.S i))) = true := by
  unfold wordEqK
  quickRfl
theorem wS : allN 3 (fun i => bAnd(wordEqK 1755 11 (mask 11) (pidn 1755 11) TitsD.S TitsD.SI 13
    titsSWords[i]! (TitsS.S i), canonK 1755 11 (mask 11) (1755 * 11) (TitsS.S i))) = true := by
  unfold wordEqK
  quickRfl
theorem wN : allN 4 (fun i => bAnd(wordEqK 1755 11 (mask 11) (pidn 1755 11) TitsD.S TitsD.SI 13
    titsNWords[i]! (TitsN.S i), canonK 1755 11 (mask 11) (1755 * 11) (TitsN.S i))) = true := by
  unfold wordEqK
  quickRfl
theorem wJ : allN 4 (fun i => bAnd(wordEqK 1755 11 (mask 11) (pidn 1755 11) TitsD.S TitsD.SI 13
    titsJWords[i]! (TitsJ.S i), canonK 1755 11 (mask 11) (1755 * 11) (TitsJ.S i))) = true := by
  unfold wordEqK
  quickRfl
theorem wK : allN 2 (fun i => bAnd(wordEqK 1755 11 (mask 11) (pidn 1755 11) TitsD.S TitsD.SI 13
    titsKWords[i]! (TitsK.S i), canonK 1755 11 (mask 11) (1755 * 11) (TitsK.S i))) = true := by
  unfold wordEqK
  quickRfl
theorem wR : allN 3 (fun i => bAnd(wordEqK 1755 11 (mask 11) (pidn 1755 11) TitsD.S TitsD.SI 13
    titsRWords[i]! (TitsR.S i), canonK 1755 11 (mask 11) (1755 * 11) (TitsR.S i))) = true := by
  unfold wordEqK
  quickRfl

theorem letters : titsLocalWords.all (fun ws => ws.all (lettersOK 13)) = true ∧
    lettersOK 13 titsCenterWord = true ∧ lettersOK 13 titsXWord = true ∧
    lettersOK 13 titsYWord = true ∧
    (titsProvenance.all fun p => lettersOK 13 p.2.2) = true ∧
    (∀ j < 2, lettersOK 4 (titsU j) = true ∧ lettersOK 4 (titsV j) = true) ∧
    titsDerivedDerivations.length = 11 ∧
    (∀ i < 11, lettersOK (2 + i) titsDerivedDerivations[i]! = true) := by
  decide

theorem get_of {S : Array (Array Nat)} {PS : Nat → Nat} {kS nb BP : Nat} {base : Array Nat}
    (hb : Binds 1755 11 PS kS nb BP S base) : ∀ j < kS, S[j]! = unpack 1755 11 (PS j) :=
  hb.2.2.2.2.1

theorem size_of {S : Array (Array Nat)} {PS : Nat → Nat} {kS nb BP : Nat} {base : Array Nat}
    (hb : Binds 1755 11 PS kS nb BP S base) : S.size = kS :=
  hb.2.2.2.1

theorem data : titsFlagArrs.size = 4 ∧ titsAStarArrs.size = 4 ∧ titsDFlagStored.size = 2 ∧
    titsDStarStored.size = 2 ∧ titsHArrs.size = 9 ∧ titsSArrs.size = 9 ∧ titsNArrs.size = 10 ∧
    titsJArrs.size = 9 ∧ titsKArrs.size = 7 ∧ titsRArrs.size = 8 ∧
    allPermsOK 8775 titsFlagArrs = true ∧ allPermsOK 2925 titsAStarArrs = true ∧
    allPermsOK 8775 titsDFlagStored = true ∧ allPermsOK 2925 titsDStarStored = true ∧
    allPermsOK 1755 titsHArrs = true ∧ allPermsOK 1755 titsSArrs = true ∧
    allPermsOK 1755 titsNArrs = true ∧ allPermsOK 1755 titsJArrs = true ∧
    allPermsOK 1755 titsKArrs = true ∧ allPermsOK 1755 titsRArrs = true ∧
    allLt 8775 (fun j => decide (titsBetaArr[j]! < 1755)) = true ∧
    allLt 8775 (fun j => decide (titsKappaArr[j]! < 2925)) = true ∧
    titsLocalWords.all (fun ws => ws.all (lettersOK 13)) = true ∧
    lettersOK 13 titsCenterWord = true ∧ lettersOK 13 titsXWord = true ∧
    lettersOK 13 titsYWord = true ∧
    (titsProvenance.all fun p => lettersOK 13 p.2.2) = true ∧
    (∀ j < 2, lettersOK 4 (titsU j) = true ∧ lettersOK 4 (titsV j) = true) ∧
    titsDerivedDerivations.length = 11 ∧
    (∀ i < 11, lettersOK (2 + i) titsDerivedDerivations[i]! = true) := by
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := facts1
  exact ⟨by simp [titsFlagArrs], by simp [titsAStarArrs], by simp [titsDFlagStored],
    by simp [titsDStarStored], size_of bindsH, size_of bindsS, size_of bindsN, size_of bindsJ,
    size_of bindsK, size_of bindsR, f1, f2, f3, f4,
    allPerms_of (size_of bindsH) (get_of bindsH) permH,
    allPerms_of (size_of bindsS) (get_of bindsS) permS,
    allPerms_of (size_of bindsN) (get_of bindsN) permN,
    allPerms_of (size_of bindsJ) (get_of bindsJ) permJ,
    allPerms_of (size_of bindsK) (get_of bindsK) permK,
    allPerms_of (size_of bindsR) (get_of bindsR) permR, f5, f6, letters⟩

theorem chains : rawChainOK 1755 (titsHArrs.extract 0 3) titsHArrs (baseArr 1755 titsHBase)
      (wordsArr 3 9 titsHDerivations) 4 = true ∧
    rawChainOK 1755 (titsSArrs.extract 0 3) titsSArrs (baseArr 1755 titsSBase)
      (wordsArr 3 9 titsSDerivations) 4 = true ∧
    rawChainOK 1755 (titsNArrs.extract 0 4) titsNArrs (baseArr 1755 titsNBase)
      (wordsArr 4 10 titsNDerivations) 4 = true ∧
    rawChainOK 1755 (titsJArrs.extract 0 4) titsJArrs (baseArr 1755 titsJBase)
      (wordsArr 4 9 titsJDerivations) 4 = true ∧
    rawChainOK 1755 (titsKArrs.extract 0 2) titsKArrs (baseArr 1755 titsKBase)
      (wordsArr 2 7 titsKDerivations) 4 = true ∧
    rawChainOK 1755 (titsRArrs.extract 0 3) titsRArrs (baseArr 1755 titsRBase)
      (wordsArr 3 8 titsRDerivations) 4 = true ∧
    rawOrbitSizes 1755 titsHArrs (baseArr 1755 titsHBase) = [10, 8, 8, 8, 2] ∧
    rawOrbitSizes 1755 titsSArrs (baseArr 1755 titsSBase) = [8, 2, 16, 4, 2] ∧
    rawOrbitSizes 1755 titsNArrs (baseArr 1755 titsNBase) = [24, 2, 16, 4, 2] ∧
    rawOrbitSizes 1755 titsJArrs (baseArr 1755 titsJBase) = [2, 2, 64, 2] ∧
    rawOrbitSizes 1755 titsKArrs (baseArr 1755 titsKBase) = [8, 2, 8, 4, 2] ∧
    rawOrbitSizes 1755 titsRArrs (baseArr 1755 titsRBase) = [2, 2, 4, 8, 2] ∧
    titsHWords.length = 3 ∧ titsSWords.length = 3 ∧ titsNWords.length = 4 ∧
    titsJWords.length = 4 ∧ titsKWords.length = 2 ∧ titsRWords.length = 3 ∧
    initialWordsOK titsHArrs titsHWords = true ∧ initialWordsOK titsSArrs titsSWords = true ∧
    initialWordsOK titsNArrs titsNWords = true ∧ initialWordsOK titsJArrs titsJWords = true ∧
    initialWordsOK titsKArrs titsKWords = true ∧ initialWordsOK titsRArrs titsRWords = true := by
  refine ⟨rawChainK_sound (NS := 220) (CH := 8) bindsH TitsH.head TitsH.hl (by norm_num) TitsH.hs,
    rawChainK_sound (NS := 220) (CH := 8) bindsS TitsS.head TitsS.hl (by norm_num) TitsS.hs,
    rawChainK_sound (NS := 220) (CH := 8) bindsN TitsN.head TitsN.hl (by norm_num) TitsN.hs,
    rawChainK_sound (NS := 220) (CH := 8) bindsJ TitsJ.head TitsJ.hl (by norm_num) TitsJ.hs,
    rawChainK_sound (NS := 220) (CH := 8) bindsK TitsK.head TitsK.hl (by norm_num) TitsK.hs,
    rawChainK_sound (NS := 220) (CH := 8) bindsR TitsR.head TitsR.hl (by norm_num) TitsR.hs,
    ?_, ?_, ?_, ?_, ?_, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    init_of (by decide) (fun i hi => get_of bindsH i (by omega)) wH,
    init_of (by decide) (fun i hi => get_of bindsS i (by omega)) wS,
    init_of (by decide) (fun i hi => get_of bindsN i (by omega)) wN,
    init_of (by decide) (fun i hi => get_of bindsJ i (by omega)) wJ,
    init_of (by decide) (fun i hi => get_of bindsK i (by omega)) wK,
    init_of (by decide) (fun i hi => get_of bindsR i (by omega)) wR⟩
  · rw [rawOrbitSizesK_sound bindsH permH TitsH.hl]
    decide
  · rw [rawOrbitSizesK_sound bindsS permS TitsS.hl]
    decide
  · rw [rawOrbitSizesK_sound bindsN permN TitsN.hl]
    decide
  · rw [rawOrbitSizesK_sound bindsJ permJ TitsJ.hl]
    decide
  · rw [rawOrbitSizesK_sound bindsK permK TitsK.hl]
    decide
  · rw [rawOrbitSizesK_sound bindsR permR TitsR.hl]
    decide

end CertificateChecks.KernelSpor.Tits2268

end
