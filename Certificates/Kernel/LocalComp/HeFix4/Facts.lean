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

theorem cK_cP {p q : Nat} (hp : cK p = true) (hq : cK q = true) : cK (cP p q) = true :=
  canonK_pcomp hp hq

theorem kIdc :idK 8330 14 (mask 14) = true ∧ cK idP = true ∧ cK T1P = true ∧
    ∀ j < 9, cK (HeC.S j) = true ∧ cK (HeC.SI j) = true := by
  obtain ⟨kId, kPid, -, -, -, kcT1, -, -, -, -, -, kcS, kcSI⟩ := kA
  exact ⟨kId, kPid, kcT1, fun j hj => ⟨allN_spec kcS j hj, allN_spec kcSI j hj⟩⟩

theorem pg_cP {p q i : Nat} (hi : i < 8330) :
    pg 14 (mask 14) (cP p q) i = pg 14 (mask 14) p (pg 14 (mask 14) q i) :=
  CFSG.KS.PF.pg_pcomp (by decide) hi

theorem cP_ext {p q : Nat} (hp : cK p = true) (hq : cK q = true)
    (h : ∀ i < 8330, pg 14 (mask 14) p i = pg 14 (mask 14) q i) : p = q :=
  CFSG.KS.PF.eq_of_fields (by decide) (CFSG.KS.PF.canon_facts hp).2.2.1
    (CFSG.KS.PF.canon_facts hq).2.2.1 h

theorem cP_assoc {p q r : Nat} (hp : cK p = true) (hq : cK q = true) (hr : cK r = true) :
    cP (cP p q) r = cP p (cP q r) := by
  refine cP_ext (cK_cP (cK_cP hp hq) hr) (cK_cP hp (cK_cP hq hr)) fun i hi => ?_
  rw [pg_cP hi, pg_cP hi, pg_cP hi, pg_cP ((CFSG.KS.PF.canon_facts hr).2.2.2 i hi)]

theorem cP_id {q : Nat} (hq : cK q = true) : cP idP q = q := by
  refine cP_ext (cK_cP kIdc.2.1 hq) hq fun i hi => ?_
  rw [pg_cP hi]
  exact Nat.eq_of_beq_eq_true (allN_spec kIdc.1 _ ((CFSG.KS.PF.canon_facts hq).2.2.2 i hi))

@[expose] noncomputable def lP (z : Int) : Nat :=
  nIf(Nat.beq (Nat.land (CFSG.KS.Mathieu.icode z) (nat_lit 1)) (nat_lit 0),
    L1 (Nat.sub (Nat.shiftRight (CFSG.KS.Mathieu.icode z) (nat_lit 1)) (nat_lit 1)),
    L1I (Nat.sub (Nat.shiftRight (CFSG.KS.Mathieu.icode z) (nat_lit 1)) (nat_lit 1)))

theorem wL_cons (X : Nat) (z : Int) (wd : List Int) : wL X (z :: wd) = cP (lP z) (wL X wd) := by
  unfold wL
  rw [CFSG.KS.Raw.Orb.wordK_cons]
  rfl

theorem kLc : ∀ k < 3, cK (L1 k) = true ∧ cK (L1I k) = true := by
  have l0 : L1 0 = HeC.S 0 := rfl
  have l1 : L1 1 = HeC.S 1 := rfl
  have l2 : L1 2 = T1P := rfl
  have i0 : L1I 0 = HeC.SI 0 := rfl
  have i1 : L1I 1 = HeC.SI 1 := rfl
  have i2 : L1I 2 = T1I := rfl
  intro k hk
  interval_cases k
  · rw [l0, i0]
    exact kIdc.2.2.2 0 (by decide)
  · rw [l1, i1]
    exact kIdc.2.2.2 1 (by decide)
  · rw [l2, i2]
    exact ⟨kIdc.2.2.1, kcT1I⟩

theorem lettersK_cons' {z : Int} {wd : List Int} (h : lettersK 3 (z :: wd) = true) :
    0 < CFSG.KS.Mathieu.icode z ∧ Nat.shiftRight (CFSG.KS.Mathieu.icode z) 1 ≤ 3 ∧
      lettersK 3 wd = true := by
  have e : lettersK 3 (z :: wd) = bAnd(Nat.blt (nat_lit 0) (CFSG.KS.Mathieu.icode z),
      bAnd(Nat.ble (Nat.shiftRight (CFSG.KS.Mathieu.icode z) (nat_lit 1)) 3, lettersK 3 wd)) :=
    CFSG.KC.BfsPin.strictB_app (CFSG.KS.Mathieu.icode z) (fun c => bAnd(Nat.blt (nat_lit 0) c,
      bAnd(Nat.ble (Nat.shiftRight c (nat_lit 1)) 3, lettersK 3 wd)))
  rw [e] at h
  simp only [bAnd_iff, Nat.blt_eq, Nat.ble_eq] at h
  exact h

theorem lP_canon {z : Int} (hz3 : Nat.shiftRight (CFSG.KS.Mathieu.icode z) 1 ≤ 3) :
    cK (lP z) = true := by
  have hk : Nat.sub (Nat.shiftRight (CFSG.KS.Mathieu.icode z) (nat_lit 1)) (nat_lit 1) < 3 := by
    have e : Nat.sub (Nat.shiftRight (CFSG.KS.Mathieu.icode z) (nat_lit 1)) (nat_lit 1) =
        Nat.shiftRight (CFSG.KS.Mathieu.icode z) 1 - 1 := rfl
    rw [e]
    omega
  unfold lP
  generalize Nat.beq (Nat.land (CFSG.KS.Mathieu.icode z) (nat_lit 1)) (nat_lit 0) = b
  cases b
  · exact (kLc _ hk).2
  · exact (kLc _ hk).1

theorem wL_mul {Y : Nat} (hY : cK Y = true) :
    ∀ v : List Int, lettersK 3 v = true → wL Y v = cP (wL idP v) Y ∧ cK (wL idP v) = true
  | [], _ => ⟨(cP_id hY).symm, kIdc.2.1⟩
  | z :: v, h => by
    obtain ⟨-, hz3, hv⟩ := lettersK_cons' h
    obtain ⟨ih1, ih2⟩ := wL_mul hY v hv
    have hl := lP_canon hz3
    rw [wL_cons, wL_cons, ih1, cP_assoc hl ih2 hY]
    exact ⟨rfl, cK_cP hl ih2⟩

@[expose] def repW (v : List Int) : Nat → List Int
  | 0 => []
  | k + 1 => v ++ repW v k

theorem wL_rep {v : List Int} {P : Nat} (hl : lettersK 3 v = true) (hP : wL idP v = P)
    (hc : cK P = true) : ∀ k, wL idP (repW v k) = ppow 8330 14 (mask 14) idP P k ∧
      cK (ppow 8330 14 (mask 14) idP P k) = true
  | 0 => ⟨rfl, kIdc.2.1⟩
  | k + 1 => by
    obtain ⟨ih1, ih2⟩ := wL_rep hl hP hc k
    have e : ppow 8330 14 (mask 14) idP P (k + 1) = cP P (ppow 8330 14 (mask 14) idP P k) := by
      change strictN (ppow 8330 14 (mask 14) idP P k) (fun q => pcomp 8330 14 (mask 14) P q) = _
      exact strictN_app' _ _
    have e2 : repW v (k + 1) = v ++ repW v k := rfl
    rw [e, e2, wL_append, ih1, (wL_mul ih2 v hl).1, hP]
    exact ⟨rfl, cK_cP hc ih2⟩

theorem cw1_eq : cw 1 = (cw 1).take 5 ++ repW (((cw 1).drop 5).take 12) 2 := by decide

theorem cw2_eq : cw 2 = (cw 2).take 0 ++ repW (((cw 2).drop 0).take 8) 2 := by decide

theorem cw3_eq : cw 3 = (cw 3).take 4 ++ repW (((cw 3).drop 4).take 10) 11 := by decide

theorem cw8_eq : cw 8 = (cw 8).take 8 ++ repW (((cw 8).drop 8).take 18) 9 := by decide

theorem kWC : ∀ j, (j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 8) →
    wordEqK 8330 14 (mask 14) idP L1 L1I 3 (cw j) (C1P j) = true := by
  rintro j (rfl | rfl | rfl | rfl)
  · obtain ⟨hl, eP⟩ := parts_of_kWK kP1
    obtain ⟨-, eC⟩ := parts_of_kWK kC1
    refine wordEq_of kL1 ?_
    rw [cw1_eq, wL_append, (wL_rep hl eP kcP12.1 2).1, eC]
    rfl
  · obtain ⟨hl, eP⟩ := parts_of_kWK kP2
    obtain ⟨-, eC⟩ := parts_of_kWK kC2
    refine wordEq_of kL2 ?_
    rw [cw2_eq, wL_append, (wL_rep hl eP kcP12.2 2).1, eC]
    rfl
  · obtain ⟨hl, eP⟩ := parts_of_kWK kP3
    obtain ⟨-, eC⟩ := parts_of_kWK kC3
    refine wordEq_of kL3 ?_
    rw [cw3_eq, wL_append, (wL_rep hl eP kcP.1 11).1, eC]
    rfl
  · obtain ⟨hl, eP⟩ := parts_of_kWK kP8
    obtain ⟨-, eC⟩ := parts_of_kWK kC8
    refine wordEq_of kL8 ?_
    rw [cw8_eq, wL_append, (wL_rep hl eP kcP.2 9).1, eC]
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

theorem inv_unpack {p q : Nat} (h : pK p q = true) :
    invCand 8330 (unpack 8330 14 p) = unpack 8330 14 q :=
  (invEqK_sound h).1

theorem isInv_unpack {p q : Nat} (h : pK p q = true) :
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

theorem fxId : idTab 8330 = unpack 8330 14 idP := (idK_sound kA.1).symm

theorem fxGen : ∀ k < 2, heGen k = unpack 8330 14 (HeC.S k) := by
  intro k hk
  have e := He2112.gen_eq k hk
  rwa [heGenArrs, getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn] at e

theorem fxAB : heABArrs.size = 2 ∧ ∀ j < 2, heABArrs[j]! = unpack 8330 14 (HeC.S j) := by
  refine ⟨rfl, fun j hj => ?_⟩
  interval_cases j
  · simpa [heABArrs] using fxGen 0 (by decide)
  · simpa [heABArrs] using fxGen 1 (by decide)

theorem fxT1 : heT1Arr = unpack 8330 14 T1P := by
  obtain ⟨-, -, kP2, -⟩ := kA
  exact (wordEqK_sound fxAB kP2 kWT1).1

theorem fxKw : lettersOK 2 hfKWord = true ∧ hfKTab = unpack 8330 14 KP := by
  obtain ⟨-, -, kP2, -⟩ := kA
  exact ⟨(wordEqK_sound fxAB kP2 kWKP).2, (wordEqK_sound fxAB kP2 kWKP).1⟩

theorem fxL : heInnerLetters1.size = 3 ∧ ∀ k < 3, heInnerLetters1[k]! = unpack 8330 14 (L1 k) := by
  have l0 : L1 0 = HeC.S 0 := rfl
  have l1 : L1 1 = HeC.S 1 := rfl
  have l2 : L1 2 = T1P := rfl
  refine ⟨rfl, fun k hk => ?_⟩
  interval_cases k
  · rw [l0]
    simpa [heInnerLetters1] using fxGen 0 (by decide)
  · rw [l1]
    simpa [heInnerLetters1] using fxGen 1 (by decide)
  · rw [l2]
    simpa [heInnerLetters1] using fxT1

theorem fxC1 : ∀ j, (j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 8) → hfC1Tabs[j]! = unpack 8330 14 (C1P j) := by
  obtain ⟨-, -, -, -, -, -, -, -, kpL, -⟩ := kA
  intro j hj
  have hj9 : j < 9 := by omega
  rw [hfC1Tabs, getElem!_pos _ j (by simpa using hj9), Array.getElem_ofFn]
  exact (wordEqK_sound fxL kpL (kWC j hj)).1

theorem fxcC : ∀ j, (j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 8) → cK (C1P j) = true := by
  rintro j (rfl | rfl | rfl | rfl)
  exacts [kCc.1, kCc.2.1, kCc.2.2.1, kCc.2.2.2]

theorem fxTT : ∀ g < 5, hfTTabs[g]! = unpack 8330 14 (TP g) := by
  obtain ⟨-, kPid, -⟩ := kA
  intro g hg
  rw [hfTTabs, getElem!_pos _ g (by simpa using hg), Array.getElem_ofFn]
  dsimp only
  by_cases h0 : g = 0
  · subst h0
    rw [if_pos rfl]
    exact fxT1
  rw [ite_eq_right h0]
  obtain ⟨h1, -⟩ := (bAnd_iff _ _).1 (kT g hg)
  have e : Nat.beq g 0 = false := by
    cases h : Nat.beq g 0
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true h) h0
  rw [e] at h1
  rw [← Nat.eq_of_beq_eq_true h1]
  exact (wordTabK_eq fxId kPid _ fun j hj =>
    ⟨fxC1 j (tau_lt _ (by omega) j hj), fxcC j (tau_lt _ (by omega) j hj)⟩).1

theorem fxkTT : ∀ g < 5, cK (TP g) = true ∧ pK (TP g) (TIP g) = true ∧ cK (TIP g) = true := by
  intro g hg
  obtain ⟨-, h2⟩ := (bAnd_iff _ _).1 (kT g hg)
  obtain ⟨h3, h4⟩ := (bAnd_iff _ _).1 h2
  exact ⟨h3, (bAnd_iff _ _).1 h4⟩

theorem fxB1 : ∀ i < 2, hfB1Tabs[i]! = unpack 8330 14 (B1P i) := by
  obtain ⟨-, kPid, -⟩ := kA
  obtain ⟨kB2, -⟩ := kB
  intro i hi
  rw [hfB1Tabs, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn,
    ← Nat.eq_of_beq_eq_true (allN_spec kB2 i hi)]
  exact (wordTabK_eq fxId kPid _ fun j hj =>
    ⟨fxTT j (b1_lt i hi j hj), (fxkTT j (b1_lt i hi j hj)).1⟩).1

theorem fxE2 : hfE2Tab = unpack 8330 14 E2P := by
  obtain ⟨-, kPid, -⟩ := kA
  obtain ⟨-, kBE, -⟩ := kB
  rw [← Nat.eq_of_beq_eq_true kBE]
  exact (wordTabK_eq fxId kPid _ fun j hj =>
    ⟨fxTT j (by revert j hj; decide), (fxkTT j (by revert j hj; decide)).1⟩).1

theorem fxStr : ∀ j < 9, heStrong j = unpack 8330 14 (HeC.S j) := by
  intro j hj
  have e := He2112.strong_eq j hj
  rwa [heStrongArrs, getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn] at e

theorem fxCj : ∀ s, cK s = true → hfConjK (unpack 8330 14 s) = unpack 8330 14 (cjK s) := by
  obtain ⟨-, -, -, -, kpK, -, kcK, kcKi, -⟩ := kA
  intro s hs
  unfold hfConjK
  rw [fxKw.2, inv_unpack kpK, comp_unpack kcK hs, comp_unpack (cK_cP kcK hs) kcKi]
  rfl

theorem fxcB : ∀ i < 2, cK (B1P i) = true := by
  obtain ⟨-, -, kcB0, kcB1, -⟩ := kB
  intro i hi
  interval_cases i
  · exact kcB0
  · exact kcB1

theorem fxOG : hfOrbGens.size = 13 ∧ ∀ j < 13, hfOrbGens[j]! = unpack 8330 14 (OG j) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, kcS, -⟩ := kA
  refine ⟨by simp [hfOrbGens, heStabIdx, hfTTabs], fun j hj => ?_⟩
  rcases Nat.lt_or_ge j 8 with h8 | h8
  · have hcS := allN_spec kcS _ (idx_lt j h8)
    have e : Nat.blt j 8 = true := Nat.blt_eq.mpr h8
    obtain ⟨h1, -⟩ := (bAnd_iff _ _).1 (kO j hj)
    rw [e] at h1
    rw [orb_get_lt h8, fxStr _ (idx_lt j h8), fxCj _ hcS, Nat.eq_of_beq_eq_true h1]
  · rw [orb_get_ge h8 hj, fxTT _ (by omega)]
    have e : Nat.blt j 8 = false := by
      cases h : Nat.blt j 8
      · rfl
      · exact absurd (Nat.blt_eq.mp h) (by omega)
    unfold OG
    rw [e]
    rfl

theorem fxKsz : hfKTab.size = 8330 := by
  rw [fxKw.2]
  simp [unpack]

theorem fxKinv : isInvA 8330 hfKTab (invCand 8330 hfKTab) = true := by
  obtain ⟨-, -, -, -, kpK, -⟩ := kA
  rw [fxKw.2]
  exact isInv_unpack kpK

theorem fxK0 : hfKTab[0]! = 7750 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, k0, -⟩ := kA
  rw [fxKw.2, unpack_get' (by decide)]
  exact Nat.eq_of_beq_eq_true k0

theorem fxE2w : ∀ j ∈ hfE2Word, j < 5 := by decide

theorem fxB1f : comp 8330 hfB1Tabs[0]! hfB1Tabs[0]! = idTab 8330 ∧
    comp 8330 hfB1Tabs[1]! hfB1Tabs[1]! = idTab 8330 ∧
    comp 8330 hfB1Tabs[0]! hfB1Tabs[1]! = comp 8330 hfB1Tabs[1]! hfB1Tabs[0]! ∧
    hfB1Tabs[0]! ≠ idTab 8330 ∧ hfB1Tabs[1]! ≠ idTab 8330 ∧ hfB1Tabs[1]! ≠ hfB1Tabs[0]! := by
  obtain ⟨-, kPid, -⟩ := kA
  obtain ⟨-, -, kcB0, kcB1, -, kb00, kb11, kb01, knB0, knB1, knB10, -⟩ := kB
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [fxB1 0 (by decide), comp_unpack kcB0 kcB0, fxId, Nat.eq_of_beq_eq_true kb00]
  · rw [fxB1 1 (by decide), comp_unpack kcB1 kcB1, fxId, Nat.eq_of_beq_eq_true kb11]
  · rw [fxB1 0 (by decide), fxB1 1 (by decide), comp_unpack kcB0 kcB1, comp_unpack kcB1 kcB0,
      Nat.eq_of_beq_eq_true kb01]
  · rw [fxB1 0 (by decide), fxId]
    exact unpack_ne kcB0 kPid knB0
  · rw [fxB1 1 (by decide), fxId]
    exact unpack_ne kcB1 kPid knB1
  · rw [fxB1 1 (by decide), fxB1 0 (by decide)]
    exact unpack_ne kcB1 kcB0 knB10

theorem fxSinv : ∀ j < 9, isInvA 8330 (heStrong j) (invCand 8330 (heStrong j)) = true := by
  intro j hj
  rw [fxStr j hj, (invEqK_sound (allN_spec He2112.perm j hj)).1]
  exact (invEqK_sound (allN_spec He2112.perm j hj)).2

theorem fxS0 : ∀ j < 9, (heStrong j)[0]! = 0 → j ∈ heStabIdx := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, ks1, -⟩ := kA
  intro j hj h0
  rw [fxStr j hj, unpack_get' (by decide)] at h0
  interval_cases j
  all_goals first
    | decide
    | (rw [h0] at ks1
       exact absurd ks1 (by decide))

theorem fxJ : ∀ j ∈ heStabIdx, j < 9 ∧ ∀ i < 2,
    comp 8330 (comp 8330 (hfConjK (heStrong j)) hfB1Tabs[i]!)
      (hfConjK (invCand 8330 (heStrong j))) ∈ hfB1Elems := by
  obtain ⟨-, -, -, -, -, -, kcK, kcKi, -, -, -, kcS, kcSI⟩ := kA
  obtain ⟨-, -, kcB0, kcB1, -⟩ := kB
  intro j hj
  have hj9 : j < 9 := HeText.idx_lt j hj
  refine ⟨hj9, fun i hi => ?_⟩
  have hcS := allN_spec kcS j hj9
  have hcSI := allN_spec kcSI j hj9
  have hmem := allN_spec (kJ j hj) i hi
  have hc1 : cK (cjK (HeC.S j)) = true := cK_cP (cK_cP kcK hcS) kcKi
  have hc2 : cK (cjK (HeC.SI j)) = true := cK_cP (cK_cP kcK hcSI) kcKi
  rw [fxStr j hj9, (invEqK_sound (allN_spec He2112.perm j hj9)).1, fxCj _ hcS, fxCj _ hcSI,
    fxB1 i hi, comp_unpack hc1 (fxcB i hi), comp_unpack (cK_cP hc1 (fxcB i hi)) hc2,
    hfB1Elems, fxId, fxB1 0 (by decide), fxB1 1 (by decide), comp_unpack kcB0 kcB1]
  exact mem_unpack hmem

theorem fxEf : comp 8330 hfE2Tab hfE2Tab = idTab 8330 ∧ hfE2Tab ≠ idTab 8330 ∧ hfE2Tab ≠ heT1Arr := by
  obtain ⟨-, kPid, -, -, -, kcT1, -⟩ := kA
  obtain ⟨-, -, -, -, kcE2, -, -, -, -, -, -, ke22, knE, knET⟩ := kB
  refine ⟨?_, ?_, ?_⟩
  · rw [fxE2, comp_unpack kcE2 kcE2, fxId, Nat.eq_of_beq_eq_true ke22]
  · rw [fxE2, fxId]
    exact unpack_ne kcE2 kPid knE
  · rw [fxE2, fxT1]
    exact unpack_ne kcE2 kcT1 knET

theorem fxTf : ∀ g < 5, isInvA 8330 hfTTabs[g]! (invCand 8330 hfTTabs[g]!) = true ∧
    comp 8330 (comp 8330 hfTTabs[g]! hfE2Tab) (invCand 8330 hfTTabs[g]!) ∈
      [hfE2Tab, comp 8330 hfE2Tab heT1Arr] := by
  obtain ⟨-, -, -, -, -, kcT1, -⟩ := kA
  obtain ⟨-, -, -, -, kcE2, -⟩ := kB
  intro g hg
  obtain ⟨hc, hp, hci⟩ := fxkTT g hg
  rw [fxTT g hg]
  refine ⟨isInv_unpack hp, ?_⟩
  rw [inv_unpack hp, fxE2, fxT1, comp_unpack hc kcE2, comp_unpack (cK_cP hc kcE2) hci,
    comp_unpack kcE2 kcT1]
  exact mem_unpack (kE g hg)

theorem fxOrb : hfPointTreeOK 8330 hfOrbGens 7750 hfOrbTree.1 hfOrbTree.2.1 hfOrbTree.2.2
    (hfPositions 8330 hfOrbTree.1) = true := by
  unfold hfOrbTree
  refine CFSG.KC.PointBfs.hfPointTreeOK_of_orbit (by decide) (fun j hj x hx => ?_)
    (CFSG.KC.PointBfs.orbR_of_forestK kF fxOG.1 fxOG.2)
  rw [fxOG.1] at hj
  rw [fxOG.2 j hj]
  exact range_unpack ((bAnd_iff _ _).1 (kO j hj)).2 hx

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
  obtain ⟨b00, b11, b01, nb0, nb1, nb10⟩ := fxB1f
  obtain ⟨e22, ne, net⟩ := fxEf
  exact ⟨fxKw.1, fxKsz, fxKinv, fxK0, b1_lt, fxE2w, b00, b11, b01, nb0, nb1, nb10, fxSinv, fxS0,
    fxJ, e22, ne, net, fxTf, fxOrb⟩

end CertificateChecks.KernelLC.HeFix4

end
