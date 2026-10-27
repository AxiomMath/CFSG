module

public import Certificates.Kernel.LocalComp.HeFix4.Checks
public import Certificates.Kernel.Sporadic.He.Bind2112
public import CFSG.Certificates.Kernel.HfPointBfsSound
public import CFSG.Certificates.Kernel.BfsPinSetSound
public import CFSG.Certificates.Kernel.Spor.RawOrbHead
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.HeFix4

open CFSG.KC.Enum CFSG.KC.BfsPin CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KS.PEnum
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.PSL3Four.Native
open CFSG.Sporadic.HeldB CFSG.Sporadic.SmallOddCore CFSG.ComponentClassification.GrSLit.HeldFix
open CertificateChecks.KernelSpor

theorem wL_append (X : Nat) : ∀ w1 w2 : List Int, wL X (w1 ++ w2) = wL (wL X w2) w1
  | [], _ => rfl
  | z :: w1, w2 => by
    have ih := wL_append X w1 w2
    unfold wL at ih ⊢
    rw [List.cons_append, CFSG.KS.Raw.Orb.wordK_cons, CFSG.KS.Raw.Orb.wordK_cons, ih]

theorem wL_split (X k : Nat) (wd : List Int) : wL X wd = wL (wL X (wd.drop k)) (wd.take k) := by
  rw [← wL_append, List.take_append_drop]

theorem parts_of_kWK {X r : Nat} {wd : List Int} (h : kWK X wd r = true) :
    lettersK 3 wd = true ∧ wL X wd = r := by
  unfold kWK at h
  simp only [bAnd_iff] at h
  exact ⟨h.1, Nat.eq_of_beq_eq_true h.2.2⟩

theorem wordEq_of {wd : List Int} {r : Nat} (hl : lettersK 3 wd = true) (he : wL idP wd = r) :
    wordEqK 8330 14 (mask 14) idP L1 L1I 3 wd r = true := by
  have he' : wordK 8330 14 (mask 14) idP L1 L1I wd = r := he
  unfold wordEqK
  rw [bAnd_iff, bAnd_iff, he']
  exact ⟨kSz, hl, Nat.beq_refl r⟩

theorem kWC : ∀ j, (j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 8) →
    wordEqK 8330 14 (mask 14) idP L1 L1I 3 (cw j) (C1P j) = true := by
  rintro j (rfl | rfl | rfl | rfl)
  · obtain ⟨hl, he⟩ := parts_of_kWK kC1
    exact wordEq_of hl he
  · obtain ⟨hl, he⟩ := parts_of_kWK kC2
    exact wordEq_of hl he
  · obtain ⟨-, ea⟩ := parts_of_kWK kC3a
    obtain ⟨-, eb⟩ := parts_of_kWK kC3b
    obtain ⟨-, ec⟩ := parts_of_kWK kC3c
    refine wordEq_of kL3 ?_
    rw [wL_split idP 34 (cw 3), wL_split idP 40 ((cw 3).drop 34), ea, eb, ec]
    rfl
  · obtain ⟨-, ea⟩ := parts_of_kWK kC8a
    obtain ⟨-, eb⟩ := parts_of_kWK kC8b
    obtain ⟨-, ec⟩ := parts_of_kWK kC8c
    obtain ⟨-, ed⟩ := parts_of_kWK kC8d
    obtain ⟨-, ee⟩ := parts_of_kWK kC8e
    refine wordEq_of kL8 ?_
    rw [wL_split idP 10 (cw 8), wL_split idP 40 ((cw 8).drop 10),
      wL_split idP 40 (((cw 8).drop 10).drop 40), wL_split idP 40 ((((cw 8).drop 10).drop 40).drop 40),
      ea, eb, ec, ed, ee]
    rfl

theorem kT : ∀ g < 5, kTK g = true := by
  intro g hg
  interval_cases g
  exacts [kT0, kT1, kT2, kT3, kT4]

theorem kJ : ∀ j ∈ heStabIdx, kJK j = true := by
  intro j hj
  simp only [heStabIdx, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [kJ0, kJ2, kJ3, kJ4, kJ5, kJ6, kJ7, kJ8]

theorem kE : ∀ g < 5, kEK g = true := by
  intro g hg
  interval_cases g
  exacts [kE0, kE1, kE2, kE3, kE4]

theorem kO : ∀ j < 13, kOK j = true := by
  intro j hj
  interval_cases j
  exacts [kO0, kO1, kO2, kO3, kO4, kO5, kO6, kO7, kO8, kO9, kO10, kO11, kO12]

theorem comp_unpack {p q : Nat} (hp : cK p = true) (hq : cK q = true) :
    comp 8330 (unpack 8330 14 p) (unpack 8330 14 q) = unpack 8330 14 (cP p q) :=
  compA_unpack hp hq

theorem cK_cP {p q : Nat} (hp : cK p = true) (hq : cK q = true) : cK (cP p q) = true :=
  canonK_pcomp hp hq

theorem inv_unpack {p : Nat} (h : pK p = true) :
    invCand 8330 (unpack 8330 14 p) = unpack 8330 14 (iP p) :=
  invCand_unpack h

theorem isInv_unpack {p : Nat} (h : pK p = true) :
    isInvA 8330 (unpack 8330 14 p) (invCand 8330 (unpack 8330 14 p)) = true := by
  rw [inv_unpack h]
  exact (invEqK_sound h).2

theorem eqA_self (x : Array Nat) : eqA 8330 x x = true :=
  CFSG.Monster.B.Co2.allLt_iff.2 fun _ _ => beq_self_eq_true _

theorem unpack_ne {p q : Nat} (hp : cK p = true) (hq : cK q = true) (h : (!Nat.beq p q) = true) :
    unpack 8330 14 p ≠ unpack 8330 14 q := by
  intro e
  have h2 := eqA_unpack hp hq
  rw [e, eqA_self] at h2
  rw [← h2] at h
  exact absurd h (by decide)

theorem mem_unpack {x : Nat} {L : List Nat} (h : L.any (Nat.beq x) = true) :
    unpack 8330 14 x ∈ L.map (unpack 8330 14) := by
  obtain ⟨y, hy, e⟩ := List.any_eq_true.1 h
  rw [Nat.eq_of_beq_eq_true e]
  exact List.mem_map_of_mem hy

theorem range_unpack {p x : Nat} (hp : cK p = true) (hx : x < 8330) :
    (unpack 8330 14 p)[x]! < 8330 := by
  rw [unpack_get' hx]
  exact Nat.blt_eq.mp (allN_spec (range_of_canonK hp) x hx)

theorem orb_get_lt {j : Nat} (hj : j < 8) :
    hfOrbGens[j]! = hfConjK (heStrong (heStabIdx.getD j 0)) := by
  have hl : (heStabIdx.map fun j => hfConjK (heStrong j)).length = 8 := by simp [heStabIdx]
  unfold hfOrbGens
  rw [getElem!_pos _ j (by simp [hl]; omega), Array.getElem_append_left (by simpa [hl] using hj),
    List.getElem_toArray, List.getElem_map, List.getD_eq_getElem _ _ (by simpa [heStabIdx] using hj)]

theorem orb_get_ge {j : Nat} (hj1 : 8 ≤ j) (hj2 : j < 13) :
    hfOrbGens[j]! = hfTTabs[j - 8]! := by
  have hl : (heStabIdx.map fun j => hfConjK (heStrong j)).length = 8 := by simp [heStabIdx]
  have ht : hfTTabs.size = 5 := by simp [hfTTabs]
  unfold hfOrbGens
  rw [getElem!_pos _ j (by simp [hl, ht]; omega), Array.getElem_append_right (by simpa [hl] using hj1),
    getElem!_pos hfTTabs (j - 8) (by omega)]
  simp [hl]

theorem idx_lt : ∀ j < 8, heStabIdx.getD j 0 < 9 := by decide
theorem tau_lt : ∀ g < 4, ∀ j ∈ hfTauWords.getD g [], j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 8 := by
  decide
theorem b1_lt : ∀ i < 2, ∀ j ∈ hfB1Words.getD i [], j < 5 := by decide

theorem facts :
    lettersOK 2 hfKWord = true ∧ hfKTab.size = 8330 ∧
      isInvA 8330 hfKTab (invCand 8330 hfKTab) = true ∧ hfKTab[0]! = 7750 ∧
      (∀ i < 2, ∀ j ∈ hfB1Words.getD i [], j < 5) ∧ (∀ j ∈ hfE2Word, j < 5) ∧
      comp 8330 hfB1Tabs[0]! hfB1Tabs[0]! = idTab 8330 ∧
      comp 8330 hfB1Tabs[1]! hfB1Tabs[1]! = idTab 8330 ∧
      comp 8330 hfB1Tabs[0]! hfB1Tabs[1]! = comp 8330 hfB1Tabs[1]! hfB1Tabs[0]! ∧
      hfB1Tabs[0]! ≠ idTab 8330 ∧ hfB1Tabs[1]! ≠ idTab 8330 ∧ hfB1Tabs[1]! ≠ hfB1Tabs[0]! ∧
      (∀ j < 9, isInvA 8330 (heStrong j) (invCand 8330 (heStrong j)) = true) ∧
      (∀ j < 9, (heStrong j)[0]! = 0 → j ∈ heStabIdx) ∧
      (∀ j ∈ heStabIdx, j < 9 ∧ ∀ i < 2,
        comp 8330 (comp 8330 (hfConjK (heStrong j)) hfB1Tabs[i]!)
          (hfConjK (invCand 8330 (heStrong j))) ∈ hfB1Elems) ∧
      comp 8330 hfE2Tab hfE2Tab = idTab 8330 ∧ hfE2Tab ≠ idTab 8330 ∧ hfE2Tab ≠ heT1Arr ∧
      (∀ g < 5, isInvA 8330 hfTTabs[g]! (invCand 8330 hfTTabs[g]!) = true ∧
        comp 8330 (comp 8330 hfTTabs[g]! hfE2Tab) (invCand 8330 hfTTabs[g]!) ∈
          [hfE2Tab, comp 8330 hfE2Tab heT1Arr]) ∧
      hfPointTreeOK 8330 hfOrbGens 7750 hfOrbTree.1 hfOrbTree.2.1 hfOrbTree.2.2
        (hfPositions 8330 hfOrbTree.1) = true := by
  obtain ⟨kId, kPid, kP2, kpT1, kpK, kcT1, kcK, kcKi, kpL, k0, ks1, kcS⟩ := by
    have h := kA
    unfold kAK at h
    simp only [bAnd_iff] at h
    exact h
  obtain ⟨kB2, kBE, kcB0, kcB1, kcE2, kb00, kb11, kb01, knB0, knB1, knB10, ke22, knE, knET⟩ := by
    have h := kB
    unfold kBK at h
    simp only [bAnd_iff] at h
    exact h
  have hid : idTab 8330 = unpack 8330 14 idP := (idK_sound kId).symm
  have hGen : ∀ k < 2, heGen k = unpack 8330 14 (HeC.S k) := by
    intro k hk
    have e := He2112.gen_eq k hk
    rwa [heGenArrs, getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn] at e
  have hAB : heABArrs.size = 2 ∧ ∀ j < 2, heABArrs[j]! = unpack 8330 14 (HeC.S j) := by
    refine ⟨rfl, fun j hj => ?_⟩
    interval_cases j
    · simpa [heABArrs] using hGen 0 (by decide)
    · simpa [heABArrs] using hGen 1 (by decide)
  have hT1 : heT1Arr = unpack 8330 14 T1P := (wordEqK_sound hAB kP2 kWT1).1
  have hK : hfKTab = unpack 8330 14 KP := (wordEqK_sound hAB kP2 kWKP).1
  have l0 : L1 0 = HeC.S 0 := rfl
  have l1 : L1 1 = HeC.S 1 := rfl
  have l2 : L1 2 = T1P := rfl
  have hL : heInnerLetters1.size = 3 ∧ ∀ k < 3, heInnerLetters1[k]! = unpack 8330 14 (L1 k) := by
    refine ⟨rfl, fun k hk => ?_⟩
    interval_cases k
    · rw [l0]
      simpa [heInnerLetters1] using hGen 0 (by decide)
    · rw [l1]
      simpa [heInnerLetters1] using hGen 1 (by decide)
    · rw [l2]
      simpa [heInnerLetters1] using hT1
  have hC1 : ∀ j, (j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 8) → hfC1Tabs[j]! = unpack 8330 14 (C1P j) := by
    intro j hj
    have hj9 : j < 9 := by omega
    rw [hfC1Tabs, getElem!_pos _ j (by simpa using hj9), Array.getElem_ofFn]
    exact (wordEqK_sound hL kpL (kWC j hj)).1
  have kcC : ∀ j, (j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 8) → cK (C1P j) = true := by
    rintro j (rfl | rfl | rfl | rfl)
    exacts [kCc.1, kCc.2.1, kCc.2.2.1, kCc.2.2.2]
  have hTT : ∀ g < 5, hfTTabs[g]! = unpack 8330 14 (TP g) := by
    intro g hg
    rw [hfTTabs, getElem!_pos _ g (by simpa using hg), Array.getElem_ofFn]
    dsimp only
    by_cases h0 : g = 0
    · subst h0
      exact hT1
    rw [ite_eq_right h0]
    obtain ⟨h1, -⟩ := (bAnd_iff _ _).1 (kT g hg)
    have e : Nat.beq g 0 = false := by
      cases h : Nat.beq g 0
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true h) h0
    rw [e] at h1
    rw [← Nat.eq_of_beq_eq_true h1]
    exact (wordTabK_eq hid kPid _ fun j hj =>
      ⟨hC1 j (tau_lt _ (by omega) j hj), kcC j (tau_lt _ (by omega) j hj)⟩).1
  have kTT : ∀ g < 5, cK (TP g) = true ∧ pK (TP g) = true ∧ cK (iP (TP g)) = true := by
    intro g hg
    obtain ⟨-, h2⟩ := (bAnd_iff _ _).1 (kT g hg)
    obtain ⟨h3, h4⟩ := (bAnd_iff _ _).1 h2
    exact ⟨h3, (bAnd_iff _ _).1 h4⟩
  have hcT : ∀ g < 5, cK (TP g) = true := fun g hg => (kTT g hg).1
  have hB1 : ∀ i < 2, hfB1Tabs[i]! = unpack 8330 14 (B1P i) := by
    intro i hi
    rw [hfB1Tabs, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn,
      ← Nat.eq_of_beq_eq_true (allN_spec kB2 i hi)]
    exact (wordTabK_eq hid kPid _ fun j hj =>
      ⟨hTT j (b1_lt i hi j hj), hcT j (b1_lt i hi j hj)⟩).1
  have hE2 : hfE2Tab = unpack 8330 14 E2P := by
    rw [← Nat.eq_of_beq_eq_true kBE]
    exact (wordTabK_eq hid kPid _ fun j hj =>
      ⟨hTT j (by revert j hj; decide), hcT j (by revert j hj; decide)⟩).1
  have hStr : ∀ j < 9, heStrong j = unpack 8330 14 (HeC.S j) := by
    intro j hj
    have e := He2112.strong_eq j hj
    rwa [heStrongArrs, getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn] at e
  have hCj : ∀ s, cK s = true → hfConjK (unpack 8330 14 s) = unpack 8330 14 (cjK s) := by
    intro s hs
    unfold hfConjK
    rw [hK, inv_unpack kpK, comp_unpack kcK hs, comp_unpack (cK_cP kcK hs) kcKi]
    rfl
  have hcB : ∀ i < 2, cK (B1P i) = true := by
    intro i hi
    interval_cases i
    · exact kcB0
    · exact kcB1
  have hOG : hfOrbGens.size = 13 ∧ ∀ j < 13, hfOrbGens[j]! = unpack 8330 14 (OG j) := by
    refine ⟨by simp [hfOrbGens, heStabIdx, hfTTabs], fun j hj => ?_⟩
    rcases Nat.lt_or_ge j 8 with h8 | h8
    · obtain ⟨hcS, -⟩ := (bAnd_iff _ _).1 (allN_spec kcS _ (idx_lt j h8))
      have e : Nat.blt j 8 = true := Nat.blt_eq.mpr h8
      obtain ⟨h1, -⟩ := (bAnd_iff _ _).1 (kO j hj)
      rw [e] at h1
      rw [orb_get_lt h8, hStr _ (idx_lt j h8), hCj _ hcS, Nat.eq_of_beq_eq_true h1]
    · rw [orb_get_ge h8 hj, hTT _ (by omega)]
      have e : Nat.blt j 8 = false := by
        cases h : Nat.blt j 8
        · rfl
        · exact absurd (Nat.blt_eq.mp h) (by omega)
      unfold OG
      rw [e]
      rfl
  refine ⟨(wordEqK_sound hAB kP2 kWKP).2, ?_, ?_, ?_, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hK]
    simp [unpack]
  · rw [hK]
    exact isInv_unpack kpK
  · rw [hK, unpack_get' (by decide)]
    exact Nat.eq_of_beq_eq_true k0
  · rw [hB1 0 (by decide), comp_unpack kcB0 kcB0, hid, Nat.eq_of_beq_eq_true kb00]
  · rw [hB1 1 (by decide), comp_unpack kcB1 kcB1, hid, Nat.eq_of_beq_eq_true kb11]
  · rw [hB1 0 (by decide), hB1 1 (by decide), comp_unpack kcB0 kcB1, comp_unpack kcB1 kcB0,
      Nat.eq_of_beq_eq_true kb01]
  · rw [hB1 0 (by decide), hid]
    exact unpack_ne kcB0 kPid knB0
  · rw [hB1 1 (by decide), hid]
    exact unpack_ne kcB1 kPid knB1
  · rw [hB1 1 (by decide), hB1 0 (by decide)]
    exact unpack_ne kcB1 kcB0 knB10
  · intro j hj
    rw [hStr j hj, (invEqK_sound (allN_spec He2112.perm j hj)).1]
    exact (invEqK_sound (allN_spec He2112.perm j hj)).2
  · intro j hj h0
    interval_cases j
    all_goals first
      | decide
      | (rw [hStr 1 (by decide), unpack_get' (by decide)] at h0
         rw [h0] at ks1
         exact absurd ks1 (by decide))
  · intro j hj
    have hj9 : j < 9 := HeText.idx_lt j hj
    refine ⟨hj9, fun i hi => ?_⟩
    obtain ⟨hcS, hcSI⟩ := (bAnd_iff _ _).1 (allN_spec kcS j hj9)
    have hmem := allN_spec (kJ j hj) i hi
    have hc1 : cK (cjK (HeC.S j)) = true := cK_cP (cK_cP kcK hcS) kcKi
    have hc2 : cK (cjK (HeC.SI j)) = true := cK_cP (cK_cP kcK hcSI) kcKi
    rw [hStr j hj9, (invEqK_sound (allN_spec He2112.perm j hj9)).1, hCj _ hcS, hCj _ hcSI,
      hB1 i hi, comp_unpack hc1 (hcB i hi), comp_unpack (cK_cP hc1 (hcB i hi)) hc2,
      hfB1Elems, hid, hB1 0 (by decide), hB1 1 (by decide), comp_unpack kcB0 kcB1]
    exact mem_unpack hmem
  · rw [hE2, comp_unpack kcE2 kcE2, hid, Nat.eq_of_beq_eq_true ke22]
  · rw [hE2, hid]
    exact unpack_ne kcE2 kPid knE
  · rw [hE2, hT1]
    exact unpack_ne kcE2 kcT1 knET
  · intro g hg
    obtain ⟨hc, hp, hci⟩ := kTT g hg
    rw [hTT g hg]
    refine ⟨isInv_unpack hp, ?_⟩
    rw [inv_unpack hp, hE2, hT1, comp_unpack hc kcE2, comp_unpack (cK_cP hc kcE2) hci,
      comp_unpack kcE2 kcT1]
    exact mem_unpack (kE g hg)
  · unfold hfOrbTree
    refine CFSG.KC.PointBfs.hfPointTreeOK_of_orbit (by decide) (fun j hj x hx => ?_)
      (CFSG.KC.PointBfs.orbR_of_forestK kF hOG.1 hOG.2)
    rw [hOG.1] at hj
    rw [hOG.2 j hj]
    exact range_unpack ((bAnd_iff _ _).1 (kO j hj)).2 hx

end CertificateChecks.KernelLC.HeFix4

end
