module

public import Certificates.Data.SuzOutComp
public import Certificates.Kernel.SuzOut.T3Fix
public import Certificates.Kernel.Sporadic.SuzInv.Inner3
public import Certificates.Kernel.Sporadic.OddCore.ChainCheckGlue
public import CFSG.Certificates.Kernel.Misc.SuzOutSound
public import CFSG.Certificates.Kernel.Misc.TitsPrimSound
public import CFSG.Certificates.Kernel.Spor.RawSound
public import CFSG.Certificates.Kernel.Spor.StrongOfSound
public import CFSG.Certificates.Kernel.LocalQTCovTPrim
import CFSG.Certificates.Kernel.Spor.Co2ChainSound
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSuzOut.T3G

open CFSG.ComponentClassification.SuzOutComp.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Certificates.Native CFSG.Sporadic.SuzOddCore
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.SuzOut CFSG.KC.TitsPrim
open CertificateChecks.KernelSpor CertificateChecks.KernelSuzOut CertificateChecks.KernelSuzOut.T3

private theorem texts' : natsPK 2 (T3Lc 0) 100 T3LabelsC.chars = true ∧
    natsPK 7 (T3Rc 0) 3 T3RootsC.chars = true ∧ intLinesOK (bodyK T3AbC.chars) = true ∧
    intLinesOK (bodyK T3XwC.chars) = true ∧ intLinesOK (bodyK T3DwC.chars) = true := by
  have h := texts
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

theorem labels_get : ∀ p < 100, t3Labels[p]! = Lc p := by
  intro p hp
  rw [t3Labels, T3LabelsC.eq]
  exact parseNats_get texts'.1 p hp

theorem roots_get : ∀ i < 3, t3Roots[i]! = Rc i := by
  intro i hi
  rw [t3Roots, T3RootsC.eq]
  exact parseNats_get texts'.2.1 i hi

private theorem toArray_get (l : List (List Int)) (i : Nat) : l.toArray[i]! = l.getD i [] := by
  rw [List.getElem!_toArray, List.getElem!_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  rfl

theorem ab_eq : t3Ab = abW.toArray := by
  rw [t3Ab, T3AbC.eq, textWords_eq texts'.2.2.1]
  rfl

theorem ab_get (i : Nat) : t3Ab[i]! = abW.getD i [] := by rw [ab_eq, toArray_get]

theorem xwords_eq : t3XWords = derivX3.toArray := by
  rw [t3XWords, T3XwC.eq, textWords_eq texts'.2.2.2.1]
  rfl

theorem dwords_eq : t3DWords = derivD3.toArray := by
  rw [t3DWords, T3DwC.eq, textWords_eq texts'.2.2.2.2]
  rfl

theorem fix_length : (fixList 3).length = 100 := by rw [fixList_eq3, fixL_length]

theorem kGens_size : (kGens 3).size = 5 := by
  rw [kGens, Array.size_map]
  exact SuzInv.gensI3.1

theorem kGens_get {j : Nat} (hj : j < 5) : (kGens 3)[j]! = unpack 100 7 (T3X.S j) := by
  have hj' : j < (invInnerGenArrs 3).size := by rw [SuzInv.gensI3.1]; exact hj
  rw [kGens, getElem!_pos _ j (by simpa using hj'), Array.getElem_map, ← getElem!_pos _ j hj',
    SuzInv.gensI3.2 j hj, fixList_eq3]
  have hr := Raw.Orb.allN_iff.1 kRes j hj
  simp only [Bool.and_eq_true] at hr
  rw [CFSG.KC.PermTool.restrictArr_unpack (w' := 7) hr.1 fixL_lt (by rw [fixL_length]; norm_num),
    fixL_length, Nat.eq_of_beq_eq_true hr.2]

theorem permX {j : Nat} (hj : j < 15) :
    permOK 100 7 (mask 7) (100 * 7) (T3X.S j) (T3X.SI j) = true :=
  Raw.Orb.allN_iff.1 (perms_of_head T3X.head) j hj

theorem permD {j : Nat} (hj : j < 7) :
    permOK 100 7 (mask 7) (100 * 7) (T3D.S j) (T3D.SI j) = true :=
  Raw.Orb.allN_iff.1 (perms_of_head T3D.head) j hj

theorem letters' : lettersOK 5 (abW.getD 0 []) = true ∧ lettersOK 5 (abW.getD 1 []) = true := by
  have h := letters
  simp only [Bool.and_eq_true] at h
  rw [← CFSG.KS.Co2SShape.lettersK_eq, ← CFSG.KS.Co2SShape.lettersK_eq]
  exact ⟨h.1.2, h.2⟩

private theorem word_eq {k : Nat} {P : Nat} (hl : lettersOK 5 (abW.getD k []) = true)
    (hP : ∀ y < 100, pg 7 (mask 7) P y = ptK 7 T3X.S T3X.SI (abW.getD k []) y) :
    wordA 100 (kGens 3) (rawInvs 100 (kGens 3)) t3Ab[k]! = unpack 100 7 P := by
  rw [ab_get]
  exact wordA_unpack kGens_size (fun j hj => kGens_get hj) (fun j hj => permX (by omega)) hl hP

theorem a_eq : t3A = unpack 100 7 A := by
  have h := abOK
  simp only [Bool.and_eq_true] at h
  exact word_eq letters'.1 fun y hy => Nat.eq_of_beq_eq_true (Raw.Orb.allN_iff.1 h.1 y hy)

theorem b_eq : t3B = unpack 100 7 B := by
  have h := abOK
  simp only [Bool.and_eq_true] at h
  exact word_eq letters'.2 fun y hy => Nat.eq_of_beq_eq_true (Raw.Orb.allN_iff.1 h.2 y hy)

theorem strongX : t3XStrong.size = 15 ∧ ∀ j < 15, t3XStrong[j]! = unpack 100 7 (T3X.S j) := by
  rw [t3XStrong, xwords_eq]
  exact strongOf_bind ⟨kGens_size, fun j hj => kGens_get hj⟩ T3X.head

theorem pair_get : t3O.size = 2 ∧ ∀ j < 2, t3O[j]! = unpack 100 7 (T3D.S j) := by
  refine ⟨rfl, fun j hj => ?_⟩
  interval_cases j
  · exact a_eq
  · exact b_eq

theorem strongD : t3DStrong.size = 7 ∧ ∀ j < 7, t3DStrong[j]! = unpack 100 7 (T3D.S j) := by
  rw [t3DStrong, dwords_eq]
  exact strongOf_bind pair_get T3D.head

private theorem baseX : allN 4 (fun t => Nat.beq ((t3XBase.map Fin.val).toArray)[t]!
    (pg 7 (mask 7) T3X.BP t)) = true := by decide +kernel

private theorem baseD : allN 4 (fun t => Nat.beq ((t3DBase.map Fin.val).toArray)[t]!
    (pg 7 (mask 7) T3D.BP t)) = true := by decide +kernel

theorem bindsX : Binds 100 7 T3X.S 15 4 T3X.BP t3XStrong (t3XBase.map Fin.val).toArray :=
  ⟨by norm_num, by norm_num, by norm_num, strongX.1, strongX.2, rfl,
    fun t ht => Nat.eq_of_beq_eq_true (Raw.Orb.allN_iff.1 baseX t ht)⟩

theorem bindsD : Binds 100 7 T3D.S 7 4 T3D.BP t3DStrong (t3DBase.map Fin.val).toArray :=
  ⟨by norm_num, by norm_num, by norm_num, strongD.1, strongD.2, rfl,
    fun t ht => Nat.eq_of_beq_eq_true (Raw.Orb.allN_iff.1 baseD t ht)⟩

theorem orbitsX : rawOrbitSizes 100 t3XStrong (t3XBase.map Fin.val).toArray = [100, 63, 24, 8] := by
  have h := rawOrbitSizesK_sound bindsX (perms_of_head T3X.head) T3X.hl
  have e : (List.range 4).map (fun i => rcnt (T3X.LR i)) = [100, 63, 24, 8] := by decide +kernel
  exact h.trans e

theorem orbitsD : rawOrbitSizes 100 t3DStrong (t3DBase.map Fin.val).toArray = [100, 63, 24, 4] := by
  have h := rawOrbitSizesK_sound bindsD (perms_of_head T3D.head) T3D.hl
  have e : (List.range 4).map (fun i => rcnt (T3D.LR i)) = [100, 63, 24, 4] := by decide +kernel
  exact h.trans e

private theorem repl (k : Nat) (A : Array (List Int)) {j : Nat} (hj : j < k) :
    (Array.replicate k ([] : List Int) ++ A)[j]! = [] := by
  rw [getElem!_pos _ j (by simp; omega), Array.getElem_append_left (by simp; omega)]
  simp

theorem rawX : t3XRaw = CFSG.Sporadic.Schreier.Co3.Native.wordsArr 5 15 derivX3 := by
  have hl : derivX3.length = 10 := by decide +kernel
  apply wordsArr_eq
  · simp [t3XRaw, xwords_eq, hl]
  · omega
  · intro j hj
    exact repl 5 _ hj
  · simp [t3XRaw, xwords_eq]

theorem rawD : t3DRaw = CFSG.Sporadic.Schreier.Co3.Native.wordsArr 2 7 derivD3 := by
  have hl : derivD3.length = 5 := by decide +kernel
  apply wordsArr_eq
  · simp [t3DRaw, dwords_eq, hl]
  · omega
  · intro j hj
    exact repl 2 _ hj
  · simp [t3DRaw, dwords_eq]

theorem chainX : rawChainOK 100 (t3XStrong.extract 0 (kGens 3).size) t3XStrong
    (t3XBase.map Fin.val).toArray t3XRaw 4 = true := by
  rw [kGens_size, rawX]
  exact rawChainK_sound bindsX T3X.head T3X.hl (by norm_num : 100 ≤ 2 * 50) T3X.hs

theorem chainD : rawChainOK 100 (t3DStrong.extract 0 t3O.size) t3DStrong
    (t3DBase.map Fin.val).toArray t3DRaw 4 = true := by
  rw [pair_get.1, rawD]
  exact rawChainK_sound bindsD T3D.head T3D.hl (by norm_num : 100 ≤ 2 * 50) T3D.hs

theorem prim' : CFSG.Quasithin.primCheck 100 t3DStrong 0 t3Labels t3Roots 3 t3Tw t3Hw = true := by
  rw [t3Tw, t3Hw, T3TwC.eq, T3HwC.eq, textWords_body, textWords_body]
  exact primCheck_of_walk strongD.1 strongD.2 (fun j hj => permD hj) labels_get roots_get
    (by norm_num) prim

theorem reach' : reachCheck 100 t3DStrong 0 t3Labels t3Roots 3 t3Tw t3Reach = true := by
  rw [t3Tw, t3Reach, T3TwC.eq, T3ReC.eq, textWords_body, textWords_body]
  exact reachCheck_of_walk strongD.1 strongD.2 (fun j hj => permD hj) (labels_get 0 (by norm_num))
    roots_get (by norm_num) reach

theorem szOK' : szOK 100 7 = true := by decide +kernel

theorem canon_pidn : canonK 100 7 (mask 7) (100 * 7) (pidn 100 7) = true := by decide +kernel

theorem idA_eq : idA 100 = unpack 100 7 (pidn 100 7) :=
  (CFSG.KC.LQT.Cov.T.unpack_pidn (by norm_num) (by norm_num)).symm

theorem cA : canonK 100 7 (mask 7) (100 * 7) A = true :=
  canon_of_perm szOK' (permD (j := 0) (by norm_num))

theorem cB : canonK 100 7 (mask 7) (100 * 7) B = true :=
  canon_of_perm szOK' (permD (j := 1) (by norm_num))

theorem cAB : canonK 100 7 (mask 7) (100 * 7) (pc A B) = true := CFSG.KC.BfsPin.canonK_pcomp cA cB

theorem cBA : canonK 100 7 (mask 7) (100 * 7) (pc B A) = true := CFSG.KC.BfsPin.canonK_pcomp cB cA

theorem ab_comp : compA 100 t3A t3B = unpack 100 7 (pc A B) := by
  rw [a_eq, b_eq, CFSG.KC.BfsPin.compA_unpack cA cB]
  rfl

theorem ba_comp : compA 100 t3B t3A = unpack 100 7 (pc B A) := by
  rw [a_eq, b_eq, CFSG.KC.BfsPin.compA_unpack cB cA]
  rfl

theorem check22618 :
    (fixList 3).length = 100 ∧ (kGens 3).size = 5 ∧ (kGens 3).size ≤ t3XStrong.size ∧
    (∀ i < (kGens 3).size, t3XStrong[i]! = (kGens 3)[i]!) ∧
    rawChainOK 100 (t3XStrong.extract 0 (kGens 3).size) t3XStrong (t3XBase.map Fin.val).toArray
      t3XRaw 4 = true ∧
    rawOrbitSizes 100 t3XStrong (t3XBase.map Fin.val).toArray = [100, 63, 24, 8] ∧
    lettersOK (kGens 3).size t3Ab[0]! = true ∧ lettersOK (kGens 3).size t3Ab[1]! = true ∧
    isInvA 100 t3A (invCand 100 t3A) = true ∧ isInvA 100 t3B (invCand 100 t3B) = true ∧
    t3O.size ≤ t3DStrong.size ∧ (∀ i < t3O.size, t3DStrong[i]! = t3O[i]!) ∧
    rawChainOK 100 (t3DStrong.extract 0 t3O.size) t3DStrong (t3DBase.map Fin.val).toArray
      t3DRaw 4 = true ∧
    rawOrbitSizes 100 t3DStrong (t3DBase.map Fin.val).toArray = [100, 63, 24, 4] ∧
    CFSG.Quasithin.primCheck 100 t3DStrong 0 t3Labels t3Roots 3 t3Tw t3Hw = true ∧
    reachCheck 100 t3DStrong 0 t3Labels t3Roots 3 t3Tw t3Reach = true ∧
    eqA 100 (CFSG.Quasithin.powA 100 t3A 3) (idA 100) = true ∧ eqA 100 t3A (idA 100) = false ∧
    eqA 100 (CFSG.Quasithin.powA 100 t3B 7) (idA 100) = true ∧ eqA 100 t3B (idA 100) = false ∧
    eqA 100 (CFSG.Quasithin.powA 100 (compA 100 t3A t3B) 5) (idA 100) = true ∧
    eqA 100 (compA 100 t3A t3B) (idA 100) = false ∧
    eqA 100 (compA 100 t3A t3B) (compA 100 t3B t3A) = false := by
  have oA := ord_of_K canon_pidn idA_eq cA ordA
  have oB := ord_of_K canon_pidn idA_eq cB ordB
  have oAB := ord_of_K canon_pidn idA_eq cAB ordAB
  rw [← a_eq] at oA
  rw [← b_eq] at oB
  rw [← ab_comp] at oAB
  refine ⟨fix_length, kGens_size, by rw [kGens_size, strongX.1]; norm_num,
    fun i hi => by rw [kGens_size] at hi; rw [strongX.2 i (by omega), kGens_get hi],
    chainX, orbitsX,
    by rw [kGens_size, ab_get]; exact letters'.1, by rw [kGens_size, ab_get]; exact letters'.2,
    by rw [a_eq]; exact isInvA_of_perm (permD (by norm_num)),
    by rw [b_eq]; exact isInvA_of_perm (permD (by norm_num)),
    by rw [pair_get.1, strongD.1]; norm_num,
    fun i hi => by rw [pair_get.1] at hi; rw [strongD.2 i (by omega), pair_get.2 i hi],
    chainD, orbitsD, prim', reach', oA.1, oA.2, oB.1, oB.2, oAB.1, oAB.2, ?_⟩
  rw [ab_comp, ba_comp, CFSG.KC.BfsPin.eqA_unpack cAB cBA]
  have h := comm
  simp only [Bool.not_eq_true'] at h
  exact h

end CertificateChecks.KernelSuzOut.T3G

end
