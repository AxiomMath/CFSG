module

public import Certificates.Kernel.Misc.YamakiAut.FinalT

public section

namespace CFSG.KD.YamakiAutM

open CFSG.KC.YamakiAutM CFSG.KC.YamakiAut CFSG.KD.YamakiAut CFSG.KD.YamakiRepF CFSG.KD.YamakiRep
  CFSG.KC.YamakiS0 CFSG.KC.YamakiA0 CFSG.KD.YamakiA0 CFSG.KD.BfsK CFSG.KC.BfsEnum
  CFSG.KC.YamakiRep CFSG.ClassicalInvolution.Solomon73.Yamaki
open CFSG.KD.YamakiNA (vnum)
open CFSG.KD.Sp62 (MULF ONE)

@[expose] def SFact (p z : ℕ) (L : List ℕ) : Prop :=
  ∀ y < 64, L.getD y 0 < 64 ∧ MULF (recX RN 14 p) (vnum y) = vnum (L.getD y 0) ∧
    MULF z (vnum y) = vnum (sPi.getD (L.getD (sPi.getD y 0) 0) 0)

theorem appT1 {c p : ℕ} (hp : p < 23040) (hc : c = recX RH 14 p) :
    appF (enumH ()) (tabT1 ()) (arrN c) = arrN (RT p % 2 ^ 36) := by
  have hl : (enumH ()).lookup (arrN (recX RH 14 p)) = some p := lookup_of_inv enumH_repF.1 hp
  unfold appF
  rw [hc, hl, Option.getD_some, ya550712_tab1.2 p hp]

theorem appT2 {c p : ℕ} (hp : p < 23040) (hc : c = recX RH 14 p) :
    appF (enumH ()) (tabT2 ()) (arrN c) = arrN (RT p / 2 ^ 36) := by
  have hl : (enumH ()).lookup (arrN (recX RH 14 p)) = some p := lookup_of_inv enumH_repF.1 hp
  unfold appF
  rw [hc, hl, Option.getD_some, ya550712_tab2.2 p hp]

theorem appS {c p z : ℕ} {L : List ℕ} (hp : p < 10752) (hc : c = recX RN 14 p)
    (h : SFact p z L) : appF (enumN ()) (tabS ()) (arrN c) = arrN z := by
  have hl : (enumN ()).lookup (arrN (recX RN 14 p)) = some p := lookup_of_inv enumN_repF.1 hp
  unfold appF
  rw [hc, hl, Option.getD_some, ya550712_tabS.2 p hp]
  refine ext64 (size_compA _ _) (arrN_size _) fun y hy => ?_
  obtain ⟨p1, -⟩ := ya550712_pi y hy
  obtain ⟨l1, l2, -⟩ := h _ p1
  obtain ⟨-, -, l3⟩ := h y hy
  rw [compA_get _ _ hy, ya550712_piA y hy, compA_get _ _ p1,
    (CFSG.KC.YamakiNW.arrN_get_iff p1 l1).2 l2, ya550712_piA _ l1]
  exact ((CFSG.KC.YamakiNW.arrN_get_iff hy (ya550712_pi _ l1).1).2 l3).symm

theorem lookX {c p : ℕ} (hp : p < 1536) (hc : c = recX RX 14 p) :
    ((enumX ()).lookup (arrN c)).isSome = true := by
  have hl : (enumX ()).lookup (arrN (recX RX 14 p)) = some p := lookup_of_inv enumX_repF.1 hp
  rw [hc, hl]
  rfl

theorem gX_get0 : (gX ())[0]! = arrN (RX 12) := by
  rw [gX, wordsA_get _ _ (by simp [gWords]), words_gen yfX_gens gWords 12 (by decide) yfX_gen 0
    (by simp [gWords])]

theorem gX_get1 : (gX ())[1]! = arrN (RX 13) := by
  rw [gX, wordsA_get _ _ (by simp [gWords]), words_gen yfX_gens gWords 12 (by decide) yfX_gen 1
    (by simp [gWords])]

theorem wordA_gX : ∀ w : List ℕ, (∀ i ∈ w, i < 2) →
    wordA (gX ()) w = arrN (wordN (fun i => RX (12 + i)) w)
  | [], _ => by rw [wordA, wordN, arrN_one]
  | i :: w, h => by
    have hi := h i List.mem_cons_self
    have hg : (gX ())[i]! = arrN (RX (12 + i)) := by
      rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
      · exact gX_get0
      · exact gX_get1
    rw [wordA, wordN, hg, wordA_gX w fun j hj => h j (List.mem_cons_of_mem _ hj), arrN_mul]

theorem map_toArray_get {α β : Type} [Inhabited β] (f : α → β) (L : List α) (d : α) {k : ℕ}
    (hk : k < L.length) : (L.map f).toArray[k]! = f (L.getD k d) := by
  rw [getElem!_pos _ k (by simpa using hk)]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]

@[expose] noncomputable def repC (k : ℕ) : ℕ × ℕ :=
  (wordN (fun i => RX (12 + i)) (repWords.getD k ([], [])).1,
    wordN (fun i => RX (12 + i)) (repWords.getD k ([], [])).2)

theorem repWords_lt : ∀ k < 16, (∀ i ∈ (repWords.getD k ([], [])).1, i < 2) ∧
    ∀ i ∈ (repWords.getD k ([], [])).2, i < 2 := by
  decide

theorem repsA_get {k : ℕ} (hk : k < 16) :
    (repsA ())[k]! = (arrN (repC k).1, arrN (repC k).2) := by
  unfold repsA
  rw [map_toArray_get (fun p => (wordA (gX ()) p.1, wordA (gX ()) p.2)) repWords ([], [])
    (by simpa [repWords] using hk)]
  rw [wordA_gX _ (repWords_lt k hk).1, wordA_gX _ (repWords_lt k hk).2]
  rfl

@[expose] def sL2635 : List ℕ :=
  [0, 37, 57, 28, 42, 15, 19, 54, 10, 47, 51, 22, 32, 5, 25, 60, 17, 52, 40, 13, 59, 30, 2, 39, 27,
    62, 34, 7, 49, 20, 8, 45, 53, 16, 12, 41, 31, 58, 38, 3, 63, 26, 6, 35, 21, 48, 44, 9, 36, 1, 29,
    56, 14, 43, 55, 18, 46, 11, 23, 50, 4, 33, 61, 24]

@[expose] def sL5906 : List ℕ :=
  [0, 57, 3, 58, 32, 25, 35, 26, 2, 59, 1, 56, 34, 27, 33, 24, 41, 16, 42, 19, 9, 48, 10, 51, 43, 18,
    40, 17, 11, 50, 8, 49, 5, 60, 6, 63, 37, 28, 38, 31, 7, 62, 4, 61, 39, 30, 36, 29, 44, 21, 47, 22,
    12, 53, 15, 54, 46, 23, 45, 20, 14, 55, 13, 52]

@[expose] def sL3616 : List ℕ :=
  [0, 3, 57, 58, 26, 25, 35, 32, 44, 47, 21, 22, 54, 53, 15, 12, 7, 4, 62, 61, 29, 30, 36, 39, 43, 40,
    18, 17, 49, 50, 8, 11, 5, 6, 60, 63, 31, 28, 38, 37, 41, 42, 16, 19, 51, 48, 10, 9, 2, 1, 59, 56,
    24, 27, 33, 34, 46, 45, 23, 20, 52, 55, 13, 14]

@[expose] def sL2264 : List ℕ :=
  [0, 57, 37, 28, 12, 53, 41, 16, 2, 59, 39, 30, 14, 55, 43, 18, 35, 26, 6, 63, 47, 22, 10, 51, 33,
    24, 4, 61, 45, 20, 8, 49, 15, 54, 42, 19, 3, 58, 38, 31, 13, 52, 40, 17, 1, 56, 36, 29, 44, 21, 9,
    48, 32, 25, 5, 60, 46, 23, 11, 50, 34, 27, 7, 62]

@[expose] def sL8348 : List ℕ :=
  [0, 57, 37, 28, 42, 19, 15, 54, 2, 59, 39, 30, 40, 17, 13, 52, 5, 60, 32, 25, 47, 22, 10, 51, 7,
    62, 34, 27, 45, 20, 8, 49, 41, 16, 12, 53, 3, 58, 38, 31, 43, 18, 14, 55, 1, 56, 36, 29, 44, 21, 9,
    48, 6, 63, 35, 26, 46, 23, 11, 50, 4, 61, 33, 24]

@[expose] def sL7246 : List ℕ :=
  [0, 57, 3, 58, 6, 63, 5, 60, 2, 59, 1, 56, 4, 61, 7, 62, 15, 54, 12, 53, 9, 48, 10, 51, 13, 52, 14,
    55, 11, 50, 8, 49, 35, 26, 32, 25, 37, 28, 38, 31, 33, 24, 34, 27, 39, 30, 36, 29, 44, 21, 47, 22,
    42, 19, 41, 16, 46, 23, 45, 20, 40, 17, 43, 18]

theorem ya550712_s1 : SFact 2635 42137404184 sL2635 := by unfold SFact; decide +kernel

theorem ya550712_s2 : SFact 5906 59082287623 sL5906 := by unfold SFact; decide +kernel

theorem ya550712_s3 : SFact 3616 43211111896 sL3616 := by unfold SFact; decide +kernel

theorem ya550712_s4 : SFact 2264 20427730483 sL2264 := by unfold SFact; decide +kernel

theorem ya550712_s5 : SFact 8348 41902482227 sL8348 := by unfold SFact; decide +kernel

theorem ya550712_s6 : SFact 7246 3247924999 sL7246 := by unfold SFact; decide +kernel

theorem ya550712_pos :
    RX 12 = recX RN 14 2635 ∧ RX 13 = recX RN 14 5906 ∧ RX 12 = recX RH 14 20438 ∧
      RX 13 = recX RH 14 16904 ∧ RT 20438 % 2 ^ 36 = recX RX 14 1100 ∧
      RT 16904 % 2 ^ 36 = recX RX 14 1208 ∧ RT 20438 / 2 ^ 36 = recX RX 14 1100 ∧
      RT 16904 / 2 ^ 36 = recX RX 14 1082 ∧ 42137404184 = recX RX 14 22 ∧
      59082287623 = recX RX 14 32 ∧ RH 5 = recX RH 14 22990 ∧ RT 22990 % 2 ^ 36 = RH 5 ∧
      RT 22990 / 2 ^ 36 = RH 5 := by
  decide +kernel

theorem ya550712_std :
    RX 12 = (repC 0).1 ∧ RX 13 = (repC 0).2 ∧
    RT 20438 / 2 ^ 36 = (repC 1).1 ∧ RT 16904 / 2 ^ 36 = (repC 1).2 ∧
    RT 20438 % 2 ^ 36 = (repC 2).1 ∧ RT 16904 % 2 ^ 36 = (repC 2).2 ∧
    RT 20438 / 2 ^ 36 = recX RH 14 11395 ∧ RT 11395 % 2 ^ 36 = (repC 3).1 ∧
      RT 16904 / 2 ^ 36 = recX RH 14 1957 ∧ RT 1957 % 2 ^ 36 = (repC 3).2 ∧
    42137404184 = (repC 4).1 ∧ 59082287623 = (repC 4).2 ∧
    RT 20438 / 2 ^ 36 = recX RN 14 3616 ∧ 43211111896 = (repC 5).1 ∧
      RT 16904 / 2 ^ 36 = recX RN 14 2264 ∧ 20427730483 = (repC 5).2 ∧
    RT 20438 % 2 ^ 36 = recX RN 14 3616 ∧ 43211111896 = (repC 6).1 ∧
      RT 16904 % 2 ^ 36 = recX RN 14 8348 ∧ 41902482227 = (repC 6).2 ∧
    RT 11395 % 2 ^ 36 = recX RN 14 2635 ∧ 42137404184 = (repC 7).1 ∧
      RT 1957 % 2 ^ 36 = recX RN 14 7246 ∧ 3247924999 = (repC 7).2 := by
  unfold repC
  decide +kernel

section
variable (EN EH : Enum) (S T1 T2 : Array (Array ℕ)) (t : Array ℕ)

theorem stdRep0 : stdRep EN EH S T1 T2 0 t = t := rfl
theorem stdRep1 : stdRep EN EH S T1 T2 1 t = appF EH T2 t := rfl
theorem stdRep2 : stdRep EN EH S T1 T2 2 t = appF EH T1 t := rfl
theorem stdRep3 : stdRep EN EH S T1 T2 3 t = appF EH T1 (appF EH T2 t) := rfl
theorem stdRep4 : stdRep EN EH S T1 T2 4 t = appF EN S t := rfl
theorem stdRep5 : stdRep EN EH S T1 T2 5 t = appF EN S (appF EH T2 t) := rfl
theorem stdRep6 : stdRep EN EH S T1 T2 6 t = appF EN S (appF EH T1 t) := rfl
theorem stdRep7 : stdRep EN EH S T1 T2 7 t = appF EN S (appF EH T1 (appF EH T2 t)) := rfl

end

theorem stabCheck_holds : stabCheck () = true := by
  obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13⟩ := ya550712_pos
  have ha : (genA ())[5]! = arrN (RH 5) := genA_eq12 yfH_gens (by norm_num)
  unfold stabCheck
  dsimp only
  simp only [Bool.and_eq_true, decide_eq_true_eq, allLt_iff]
  refine ⟨⟨fun j hj => ?_, ?_⟩, ?_⟩
  · rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
    · rw [gX_get0, appS (by norm_num) q1 ya550712_s1, appT1 (by norm_num) q3,
        appT2 (by norm_num) q3]
      exact ⟨⟨lookX (by norm_num) q9, lookX (by norm_num) q5⟩, lookX (by norm_num) q7⟩
    · rw [gX_get1, appS (by norm_num) q2 ya550712_s2, appT1 (by norm_num) q4,
        appT2 (by norm_num) q4]
      exact ⟨⟨lookX (by norm_num) q10, lookX (by norm_num) q6⟩, lookX (by norm_num) q8⟩
  · rw [ha, appT1 (by norm_num) q11, q12]
  · rw [ha, appT2 (by norm_num) q11, q13]

theorem stdCheck_holds : stdCheck () = true := by
  obtain ⟨q1, q2, q3, q4, -⟩ := ya550712_pos
  obtain ⟨d0a, d0b, d1a, d1b, d2a, d2b, d3a, d3b, d3c, d3d, d4a, d4b, d5a, d5b, d5c, d5d, d6a, d6b,
    d6c, d6d, d7a, d7b, d7c, d7d⟩ := ya550712_std
  have hsz : (repsA ()).size = 16 := by simp [repsA, repWords]
  unfold stdCheck
  dsimp only
  simp only [Bool.and_eq_true, decide_eq_true_eq, allLt_iff]
  refine ⟨hsz, fun k hk => ?_⟩
  rw [repsA_get (by omega), gX_get0, gX_get1]
  dsimp only
  interval_cases k
  · rw [stdRep0, stdRep0, ← d0a, ← d0b]
    exact ⟨rfl, rfl⟩
  · rw [stdRep1, stdRep1, appT2 (by norm_num) q3, appT2 (by norm_num) q4, d1a, d1b]
    exact ⟨rfl, rfl⟩
  · rw [stdRep2, stdRep2, appT1 (by norm_num) q3, appT1 (by norm_num) q4, d2a, d2b]
    exact ⟨rfl, rfl⟩
  · rw [stdRep3, stdRep3, appT2 (by norm_num) q3, appT2 (by norm_num) q4,
      appT1 (by norm_num) d3a, appT1 (by norm_num) d3c, d3b, d3d]
    exact ⟨rfl, rfl⟩
  · rw [stdRep4, stdRep4, appS (by norm_num) q1 ya550712_s1, appS (by norm_num) q2 ya550712_s2,
      ← d4a, ← d4b]
    exact ⟨rfl, rfl⟩
  · rw [stdRep5, stdRep5, appT2 (by norm_num) q3, appT2 (by norm_num) q4,
      appS (by norm_num) d5a ya550712_s3, appS (by norm_num) d5c ya550712_s4, ← d5b, ← d5d]
    exact ⟨rfl, rfl⟩
  · rw [stdRep6, stdRep6, appT1 (by norm_num) q3, appT1 (by norm_num) q4,
      appS (by norm_num) d6a ya550712_s3, appS (by norm_num) d6c ya550712_s5, ← d6b, ← d6d]
    exact ⟨rfl, rfl⟩
  · rw [stdRep7, stdRep7, appT2 (by norm_num) q3, appT2 (by norm_num) q4,
      appT1 (by norm_num) d3a, appT1 (by norm_num) d3c, appS (by norm_num) d7a ya550712_s1,
      appS (by norm_num) d7c ya550712_s6, ← d7b, ← d7d]
    exact ⟨rfl, rfl⟩

end CFSG.KD.YamakiAutM

end
