module

public import Certificates.Data.SuzOutComp
public import Certificates.Kernel.SuzOut.T2Check
public import Certificates.Kernel.Sporadic.SuzInv.Inner2
public import Certificates.Kernel.Sporadic.OddCore.ChainCheckGlue
public import CFSG.Sporadic.SuzOddCore.InvArrays
public import CFSG.Sporadic.SuzOddCore.ArraysCheck
public import Certificates.Data.CFSGNative.Schreier.Refine
public meta import CFSG.Sporadic.SuzOddCore.InvArrays
public meta import CFSG.Sporadic.SuzOddCore.ArraysCheck
public meta import Certificates.Data.CFSGNative.Schreier.Refine
public import CFSG.Sporadic.SuzOddCore.InvArraysCheck
public import Certificates.Data.CFSGNative.Schreier.Check
public meta import CFSG.Sporadic.SuzOddCore.InvArraysCheck
public meta import Certificates.Data.CFSGNative.Schreier.Check
public import CFSG.Certificates.Kernel.Misc.SuzOutSound
public import CFSG.Certificates.Kernel.Misc.TitsPrimSound
public import CFSG.Certificates.Kernel.Spor.RawOrbSound
public import CFSG.Certificates.Kernel.Spor.StrongOfSound
public import CFSG.Certificates.Kernel.Spor.PackWord
public import CFSG.Certificates.Kernel.LocalQTCovTPrim
public import CFSG.Certificates.Kernel.BfsPinUnpack
public import CFSG.LocalAnalysis.ComponentClassification.SuzOutCompBlock
public import CFSG.LocalAnalysis.ComponentClassification.SuzOutCompTools
public import CFSG.Sporadic.SuzOddCore.CTIBase
public import CFSG.Sporadic.SuzOddCore.InvCentralizers
import CFSG.Certificates.Kernel.Spor.Co2ChainSound
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.SuzOutCompSimple
public import CFSG.Sporadic.SuzOddCore.InvCentralizerBounds

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSuzOut.T2G

open CFSG.ComponentClassification.SuzOutComp.Native CFSG.ComponentClassification.SuzOutComp
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.SuzOddCore
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.SuzOut CFSG.KC.TitsPrim
open CertificateChecks.KernelSpor CertificateChecks.KernelSuzOut CertificateChecks.KernelSuzOut.T2

private theorem split2 {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true :=
  Bool.and_eq_true _ _ ▸ h

private theorem texts' : natsPK 9 (T2Lb 0) 1782 T2LabC.chars = true ∧
    natsPK 11 (T2Rp 0) 396 T2RepC.chars = true ∧ natsPK 4 (T2Lc 0) 396 T2LabelsC.chars = true ∧
    natsPK 9 (T2Rc 0) 10 T2RootsC.chars = true ∧ intLinesOK (bodyK T2AbC.chars) = true ∧
    intLinesOK (bodyK T2XwC.chars) = true ∧ intLinesOK (bodyK T2DwC.chars) = true := by
  have h := texts
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

theorem lab_get : ∀ x < 1782, t2Lab[x]! = L x := by
  intro x hx
  rw [t2Lab, T2LabC.eq]
  exact parseNats_get texts'.1 x hx

theorem rep_get : ∀ j < 396, t2Rep[j]! = R j := by
  intro j hj
  rw [t2Rep, T2RepC.eq]
  exact parseNats_get texts'.2.1 j hj

theorem labels_get : ∀ p < 396, t2Labels[p]! = Lc p := by
  intro p hp
  rw [t2Labels, T2LabelsC.eq]
  exact parseNats_get texts'.2.2.1 p hp

theorem roots_get : ∀ i < 10, t2Roots[i]! = Rc i := by
  intro i hi
  rw [t2Roots, T2RootsC.eq]
  exact parseNats_get texts'.2.2.2.1 i hi

private theorem toArray_get (l : List (List Int)) (i : Nat) : l.toArray[i]! = l.getD i [] := by
  rw [List.getElem!_toArray, List.getElem!_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  rfl

theorem ab_eq : t2Ab = abW.toArray := by
  rw [t2Ab, T2AbC.eq, textWords_eq texts'.2.2.2.2.1]
  rfl

theorem xwords_eq : t2XWords = derivX.toArray := by
  rw [t2XWords, T2XwC.eq, textWords_eq texts'.2.2.2.2.2.1]
  rfl

theorem dwords_eq : t2DWords = derivD.toArray := by
  rw [t2DWords, T2DwC.eq, textWords_eq texts'.2.2.2.2.2.2]
  rfl

theorem blocks : blocksOK 1782 396 t2Lab t2Rep = true := blocksOK_of_K lab_get rep_get reps

theorem gen_get {k : Nat} (hk : k < 2) :
    (invInnerGenArrs 2)[k]! = unpack 1782 11 (SuzInvT2.F (12 + k)) :=
  SuzInv.gensI2.2 k hk

theorem block_k {k : Nat} (hk : k < 2) :
    blockK 1782 11 396 9 (SuzInvT2.F (12 + k)) (T2X.S k) (T2X.SI k) L R = true := by
  interval_cases k
  · exact block0
  · exact block1

theorem blockOK_k {k : Nat} (hk : k < 2) :
    blockOK 1782 396 t2Lab t2Rep (invInnerGenArrs 2)[k]! = true := by
  rw [gen_get hk]
  exact blockOK_of_K lab_get rep_get (block_k hk)

theorem gens_size : t2Gens.size = 2 := by
  rw [t2Gens, Array.size_map]
  exact SuzInv.gensI2.1

theorem gens_get {k : Nat} (hk : k < 2) : t2Gens[k]! = unpack 396 9 (T2X.S k) := by
  rw [t2Gens, getElem!_pos _ k (by simpa [SuzInv.gensI2.1] using hk), Array.getElem_map,
    ← getElem!_pos _ k (by simpa [SuzInv.gensI2.1] using hk), gen_get hk]
  exact blockArr_of_K lab_get rep_get (block_k hk)

theorem permX {j : Nat} (hj : j < 7) :
    permOK 396 9 (mask 9) (396 * 9) (T2X.S j) (T2X.SI j) = true :=
  Raw.Orb.allN_iff.1 permsX j hj

theorem permD {j : Nat} (hj : j < 6) :
    permOK 396 9 (mask 9) (396 * 9) (T2D.S j) (T2D.SI j) = true :=
  Raw.Orb.allN_iff.1 permsD j hj

theorem gens_isInvA : ∀ k < t2Gens.size, isInvA 396 t2Gens[k]! (invCand 396 t2Gens[k]!) = true := by
  intro k hk
  rw [gens_size] at hk
  rw [gens_get hk]
  exact isInvA_of_perm (permX (by omega))

theorem letters' : lettersOK 2 (abW.getD 0 []) = true ∧ lettersOK 2 (abW.getD 1 []) = true := by
  have h := letters
  simp only [Bool.and_eq_true] at h
  rw [← CFSG.KS.Co2SShape.lettersK_eq, ← CFSG.KS.Co2SShape.lettersK_eq]
  exact ⟨h.1.2, h.2⟩

theorem ab_get (i : Nat) : t2Ab[i]! = abW.getD i [] := by rw [ab_eq, toArray_get]

private theorem word_eq {k : Nat} {P : Nat} (hl : lettersOK 2 (abW.getD k []) = true)
    (hP : ∀ y < 396, pg 9 (mask 9) P y = ptK 9 T2X.S T2X.SI (abW.getD k []) y) :
    wordA 396 t2Gens (rawInvs 396 t2Gens) t2Ab[k]! = unpack 396 9 P := by
  rw [ab_get]
  exact wordA_unpack gens_size (fun j hj => gens_get hj) (fun j hj => permX (by omega)) hl hP

theorem a_eq : t2A = unpack 396 9 A := by
  have h := abOK
  simp only [Bool.and_eq_true] at h
  exact word_eq letters'.1 fun y hy => Nat.eq_of_beq_eq_true (Raw.Orb.allN_iff.1 h.1 y hy)

theorem b_eq : t2B = unpack 396 9 B := by
  have h := abOK
  simp only [Bool.and_eq_true] at h
  exact word_eq letters'.2 fun y hy => Nat.eq_of_beq_eq_true (Raw.Orb.allN_iff.1 h.2 y hy)

theorem strongX : t2XStrong.size = 7 ∧ ∀ j < 7, t2XStrong[j]! = unpack 396 9 (T2X.S j) := by
  rw [t2XStrong, xwords_eq]
  exact strongOf_bind ⟨gens_size, fun j hj => gens_get hj⟩ T2X.head

theorem pair_get : t2O.size = 2 ∧ ∀ j < 2, t2O[j]! = unpack 396 9 (T2D.S j) := by
  refine ⟨rfl, fun j hj => ?_⟩
  interval_cases j
  · exact a_eq
  · exact b_eq

theorem strongD : t2DStrong.size = 6 ∧ ∀ j < 6, t2DStrong[j]! = unpack 396 9 (T2D.S j) := by
  rw [t2DStrong, dwords_eq]
  exact strongOf_bind pair_get T2D.head

private theorem baseX : allN 4 (fun t => Nat.beq ((t2XBase.map Fin.val).toArray)[t]!
    (pg 9 (mask 9) T2X.BP t)) = true := by decide +kernel

private theorem baseD : allN 3 (fun t => Nat.beq ((t2DBase.map Fin.val).toArray)[t]!
    (pg 9 (mask 9) T2D.BP t)) = true := by decide +kernel

theorem bindsX : Binds 396 9 T2X.S 7 4 T2X.BP t2XStrong (t2XBase.map Fin.val).toArray :=
  ⟨by norm_num, by norm_num, by norm_num, strongX.1, strongX.2, rfl,
    fun t ht => Nat.eq_of_beq_eq_true (Raw.Orb.allN_iff.1 baseX t ht)⟩

theorem bindsD : Binds 396 9 T2D.S 6 3 T2D.BP t2DStrong (t2DBase.map Fin.val).toArray :=
  ⟨by norm_num, by norm_num, by norm_num, strongD.1, strongD.2, rfl,
    fun t ht => Nat.eq_of_beq_eq_true (Raw.Orb.allN_iff.1 baseD t ht)⟩

theorem orbitsX : rawOrbitSizes 396 t2XStrong (t2XBase.map Fin.val).toArray = [396, 120, 2, 2] := by
  have h := rawOrbitSizesK_orb (NS := 7) (CH := 64) bindsX permsX T2X.ho (by norm_num)
  have e : (List.range 4).map (fun i => rcnt (T2X.LR i)) = [396, 120, 2, 2] := by decide +kernel
  exact h.trans e

theorem orbitsD : rawOrbitSizes 396 t2DStrong (t2DBase.map Fin.val).toArray = [396, 60, 4] := by
  have h := rawOrbitSizesK_orb (NS := 7) (CH := 64) bindsD permsD T2D.ho (by norm_num)
  have e : (List.range 3).map (fun i => rcnt (T2D.LR i)) = [396, 60, 4] := by decide +kernel
  exact h.trans e

@[expose] def lab (x : Fin 1782) : ℕ := t2Lab[(x : ℕ)]!

@[expose] def rep (j : Fin 396) : Fin 1782 := ⟨t2Rep[(j : ℕ)]! % 1782, Nat.mod_lt _ (by norm_num)⟩

theorem rep_spec (j : Fin 396) : (rep j : ℕ) = t2Rep[(j : ℕ)]! ∧ lab (rep j) = j := by
  have h := allLt_spec blocks j.2
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  have hv : (rep j : ℕ) = t2Rep[(j : ℕ)]! := Nat.mod_eq_of_lt h.1
  refine ⟨hv, ?_⟩
  rw [lab, hv]
  exact h.2

theorem rep_lab (j : Fin 396) : lab (rep j) = j := (rep_spec j).2

theorem invE2_le : invE 2 ≤ blockStab 1782 396 lab := by
  rw [invE_eq_closure (i := 2) (by norm_num), Subgroup.closure_le]
  rintro _ ⟨k, hk, rfl⟩
  have hk2 : k < 2 := SuzInv.gensI2.1 ▸ hk
  exact mem_blockStab_of_blockOK (rep_invInnerGen (i := 2) (by norm_num) hk) (blockOK_k hk2)

noncomputable def rho : invE 2 →* Equiv.Perm (Fin 396) :=
  (blockHom rep_lab).comp (Subgroup.inclusion invE2_le)

theorem rho_gen {k : Nat} (hk : k < 2) :
    rho ⟨invInnerGen 2 k, invInnerGen_mem (by norm_num) (SuzInv.gensI2.1 ▸ hk)⟩ =
      permOfArr 396 t2Gens[k]! := by
  have hk' : k < (invInnerGenArrs 2).size := SuzInv.gensI2.1 ▸ hk
  have h1 : t2Gens[k]! = blockArr t2Lab t2Rep 396 (invInnerGenArrs 2)[k]! := by
    rw [t2Gens, getElem!_pos _ k (by simpa using hk'), Array.getElem_map,
      ← getElem!_pos _ k hk']
  have hrep : Rep 396 t2Gens[k]! (rho ⟨invInnerGen 2 k, invInnerGen_mem (by norm_num) hk'⟩) := by
    rw [h1]
    exact rep_blockArr rep_lab (fun x => rfl) (fun j => (rep_spec j).1) _
      (rep_invInnerGen (i := 2) (by norm_num) hk')
  exact hrep.unique (rep_permOfArr (gens_isInvA k (by rw [gens_size]; exact hk))).1

abbrev J : Subgroup (Equiv.Perm (Fin 396)) :=
  Subgroup.closure {g | ∃ k < t2Gens.size, permOfArr 396 t2Gens[k]! = g}

theorem card_J : Nat.card J ≤ 190080 := by
  have hle : J ≤ rho.range := by
    rw [Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    rw [gens_size] at hk
    exact ⟨_, rho_gen hk⟩
  have hE : Nat.card (invE 2) = 190080 := card_invE (i := 2) (by norm_num)
  have hR : Nat.card rho.range ≤ Nat.card (invE 2) :=
    Nat.card_le_card_of_surjective rho.rangeRestrict rho.rangeRestrict_surjective
  exact (Subgroup.card_le_of_le hle).trans (hR.trans hE.le)

theorem strongX_gens {j : Nat} (hj : j < 2) : t2XStrong[j]! = t2Gens[j]! := by
  rw [strongX.2 j (by omega), gens_get hj]

theorem card_le_X : Nat.card (Subgroup.closure (Set.range fun j : Fin 2 =>
    permOfArr 396 t2XStrong[j.val]!)) ≤ (rawOrbitSizes 396 t2XStrong
      (t2XBase.map Fin.val).toArray).prod := by
  have hle : Subgroup.closure (Set.range fun j : Fin 2 => permOfArr 396 t2XStrong[j.val]!) ≤ J := by
    rw [Subgroup.closure_le]
    rintro _ ⟨j, rfl⟩
    exact Subgroup.subset_closure ⟨j.val, by rw [gens_size]; exact j.2, by
      dsimp only
      rw [strongX_gens j.2]⟩
  rw [orbitsX]
  exact (Subgroup.card_le_of_le hle).trans (card_J.trans (by norm_num))

@[expose] def Rel (x y : Fin 396) : Prop := MemR 9 60 T2Rw x y

theorem preserve {σ : Equiv.Perm (Fin 396)}
    (hσ : σ ∈ Set.range fun j : Fin 2 => permOfArr 396 t2DStrong[j.val]!) :
    ∀ x y, Rel x y → Rel (σ x) (σ y) := by
  obtain ⟨j, rfl⟩ := hσ
  have hp := (Raw.Orb.prep_PS bindsD permsD (j := j.val) (by omega)).1
  rcases j with ⟨_ | _ | j, hj⟩
  · exact relK_sound relA hp
  · exact relK_sound relB hp
  · omega

theorem a_mem : permOfArr 396 t2A ∈ J :=
  permOfArr_wordA_mem gens_isInvA (by rw [gens_size, ab_get]; exact letters'.1)
    (by rw [← t2A, a_eq]; exact isInvA_of_perm (permD (by norm_num)))

theorem b_mem : permOfArr 396 t2B ∈ J :=
  permOfArr_wordA_mem gens_isInvA (by rw [gens_size, ab_get]; exact letters'.2)
    (by rw [← t2B, b_eq]; exact isInvA_of_perm (permD (by norm_num)))

theorem card_le_D : Nat.card (Subgroup.closure (Set.range fun j : Fin 2 =>
    permOfArr 396 t2DStrong[j.val]!)) ≤ (rawOrbitSizes 396 t2DStrong
      (t2DBase.map Fin.val).toArray).prod := by
  have hle : Subgroup.closure (Set.range fun j : Fin 2 => permOfArr 396 t2DStrong[j.val]!) ≤ J := by
    rw [Subgroup.closure_le]
    rintro _ ⟨j, rfl⟩
    have e : t2DStrong[j.val]! = t2O[j.val]! := by
      rw [strongD.2 j.val (by omega), pair_get.2 j.val j.2]
    change permOfArr 396 t2DStrong[j.val]! ∈ J
    rw [e]
    rcases j with ⟨_ | _ | j, hj⟩
    · exact a_mem
    · exact b_mem
    · omega
  have hg : permOfArr 396 t2XStrong[0]! ∈ J := by
    rw [strongX_gens (by norm_num)]
    exact Subgroup.subset_closure ⟨0, by rw [gens_size]; norm_num, rfl⟩
  have hm := moveK_sound move (Raw.Orb.prep_PS bindsX permsX (j := 0) (by norm_num)).1
  obtain ⟨x, y, hxy, hgxy⟩ := hm
  have h2 := card_le_half_of_rel (R := Rel) (fun σ hσ => preserve hσ) hle hg hxy hgxy
  rw [orbitsD]
  have := card_J
  norm_num
  omega

private theorem rep2 (A : Array (List Int)) {j : Nat} (hj : j < 2) :
    (Array.replicate 2 ([] : List Int) ++ A)[j]! = [] := by
  rw [getElem!_pos _ j (by simp; omega), Array.getElem_append_left (by simp; omega)]
  simp

theorem rawX : t2XRaw = CFSG.Sporadic.Schreier.Co3.Native.wordsArr 2 7 derivX := by
  have hl : derivX.length = 5 := by decide +kernel
  apply wordsArr_eq
  · simp [t2XRaw, xwords_eq, hl]
  · omega
  · intro j hj
    exact rep2 _ hj
  · simp [t2XRaw, xwords_eq]

theorem rawD : t2DRaw = CFSG.Sporadic.Schreier.Co3.Native.wordsArr 2 6 derivD := by
  have hl : derivD.length = 4 := by decide +kernel
  apply wordsArr_eq
  · simp [t2DRaw, dwords_eq, hl]
  · omega
  · intro j hj
    exact rep2 _ hj
  · simp [t2DRaw, dwords_eq]

theorem chainX : rawChainOK 396 (t2XStrong.extract 0 t2Gens.size) t2XStrong
    (t2XBase.map Fin.val).toArray t2XRaw 4 = true := by
  rw [gens_size, rawX]
  exact rawChainK_of_card_orb 4 bindsX T2X.head T2X.ho (by norm_num : 396 ≤ 7 * 64) card_le_X

theorem chainD : rawChainOK 396 (t2DStrong.extract 0 t2O.size) t2DStrong
    (t2DBase.map Fin.val).toArray t2DRaw 4 = true := by
  rw [pair_get.1, rawD]
  exact rawChainK_of_card_orb 4 bindsD T2D.head T2D.ho (by norm_num : 396 ≤ 7 * 64) card_le_D

theorem prim' : CFSG.Quasithin.primCheck 396 t2DStrong 0 t2Labels t2Roots 10 t2Tw t2Hw = true := by
  rw [t2Tw, t2Hw, T2TwC.eq, T2HwC.eq, textWords_body, textWords_body]
  exact primCheck_of_walk strongD.1 strongD.2 (fun j hj => permD hj) labels_get roots_get
    (by norm_num) prim

theorem reach' : reachCheck 396 t2DStrong 0 t2Labels t2Roots 10 t2Tw t2Reach = true := by
  rw [t2Tw, t2Reach, T2TwC.eq, T2ReC.eq, textWords_body, textWords_body]
  exact reachCheck_of_walk strongD.1 strongD.2 (fun j hj => permD hj) (labels_get 0 (by norm_num))
    roots_get (by norm_num) reach

theorem szOK' : szOK 396 9 = true := by decide +kernel

theorem canon_pidn : canonK 396 9 (mask 9) (396 * 9) (pidn 396 9) = true := by decide +kernel

theorem idA_eq : idA 396 = unpack 396 9 (pidn 396 9) :=
  (CFSG.KC.LQT.Cov.T.unpack_pidn (by norm_num) (by norm_num)).symm

theorem cA : canonK 396 9 (mask 9) (396 * 9) A = true :=
  canon_of_perm szOK' (permD (j := 0) (by norm_num))

theorem cB : canonK 396 9 (mask 9) (396 * 9) B = true :=
  canon_of_perm szOK' (permD (j := 1) (by norm_num))

theorem cAB : canonK 396 9 (mask 9) (396 * 9) (pc A B) = true := CFSG.KC.BfsPin.canonK_pcomp cA cB

theorem cBA : canonK 396 9 (mask 9) (396 * 9) (pc B A) = true := CFSG.KC.BfsPin.canonK_pcomp cB cA

theorem ab_comp : compA 396 t2A t2B = unpack 396 9 (pc A B) := by
  rw [a_eq, b_eq, CFSG.KC.BfsPin.compA_unpack cA cB]
  rfl

theorem ba_comp : compA 396 t2B t2A = unpack 396 9 (pc B A) := by
  rw [a_eq, b_eq, CFSG.KC.BfsPin.compA_unpack cB cA]
  rfl

theorem check22617 :
    blocksOK 1782 396 t2Lab t2Rep = true ∧
    blockOK 1782 396 t2Lab t2Rep (invInnerGenArrs 2)[0]! = true ∧
    blockOK 1782 396 t2Lab t2Rep (invInnerGenArrs 2)[1]! = true ∧
    t2Gens.size = 2 ∧ t2Gens.size ≤ t2XStrong.size ∧
    (∀ i < t2Gens.size, t2XStrong[i]! = t2Gens[i]!) ∧
    rawChainOK 396 (t2XStrong.extract 0 t2Gens.size) t2XStrong (t2XBase.map Fin.val).toArray
      t2XRaw 4 = true ∧
    rawOrbitSizes 396 t2XStrong (t2XBase.map Fin.val).toArray = [396, 120, 2, 2] ∧
    lettersOK t2Gens.size t2Ab[0]! = true ∧ lettersOK t2Gens.size t2Ab[1]! = true ∧
    isInvA 396 t2A (invCand 396 t2A) = true ∧ isInvA 396 t2B (invCand 396 t2B) = true ∧
    t2O.size ≤ t2DStrong.size ∧ (∀ i < t2O.size, t2DStrong[i]! = t2O[i]!) ∧
    rawChainOK 396 (t2DStrong.extract 0 t2O.size) t2DStrong (t2DBase.map Fin.val).toArray
      t2DRaw 4 = true ∧
    rawOrbitSizes 396 t2DStrong (t2DBase.map Fin.val).toArray = [396, 60, 4] ∧
    CFSG.Quasithin.primCheck 396 t2DStrong 0 t2Labels t2Roots 10 t2Tw t2Hw = true ∧
    reachCheck 396 t2DStrong 0 t2Labels t2Roots 10 t2Tw t2Reach = true ∧
    eqA 396 (CFSG.Quasithin.powA 396 t2A 3) (idA 396) = true ∧ eqA 396 t2A (idA 396) = false ∧
    eqA 396 (CFSG.Quasithin.powA 396 t2B 11) (idA 396) = true ∧ eqA 396 t2B (idA 396) = false ∧
    eqA 396 (CFSG.Quasithin.powA 396 (compA 396 t2A t2B) 11) (idA 396) = true ∧
    eqA 396 (compA 396 t2A t2B) (idA 396) = false ∧
    eqA 396 (compA 396 t2A t2B) (compA 396 t2B t2A) = false := by
  have oA := ord_of_K canon_pidn idA_eq cA ordA
  have oB := ord_of_K canon_pidn idA_eq cB ordB
  have oAB := ord_of_K canon_pidn idA_eq cAB ordAB
  rw [← a_eq] at oA
  rw [← b_eq] at oB
  rw [← ab_comp] at oAB
  refine ⟨blocks, blockOK_k (by norm_num), blockOK_k (by norm_num), gens_size,
    by rw [gens_size, strongX.1]; norm_num,
    fun i hi => strongX_gens (by rw [gens_size] at hi; exact hi), chainX, orbitsX,
    by rw [gens_size, ab_get]; exact letters'.1, by rw [gens_size, ab_get]; exact letters'.2,
    by rw [a_eq]; exact isInvA_of_perm (permD (by norm_num)),
    by rw [b_eq]; exact isInvA_of_perm (permD (by norm_num)),
    by rw [pair_get.1, strongD.1]; norm_num,
    fun i hi => by rw [pair_get.1] at hi; rw [strongD.2 i (by omega), pair_get.2 i hi],
    chainD, orbitsD, prim', reach', oA.1, oA.2, oB.1, oB.2, oAB.1, oAB.2, ?_⟩
  rw [ab_comp, ba_comp, CFSG.KC.BfsPin.eqA_unpack cAB cBA]
  have h := comm
  simp only [Bool.not_eq_true'] at h
  exact h

end CertificateChecks.KernelSuzOut.T2G

end
