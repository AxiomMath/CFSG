module

public import Certificates.Kernel.LocalComp.HeFixWords

public section

namespace CertificateChecks.KernelLC.HeFix

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.PermTool
open CFSG.KC.Misc.HexFlat CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.Sporadic.HeldB CFSG.ComponentClassification.GrSLit.HeldFix
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SuzOddCore CFSG.PSL3Four.Native

theorem ofFn_get {α : Type} [Inhabited α] {m : Nat} (f : Fin m → α) {j : Nat} (hj : j < m) :
    (Array.ofFn f)[j]! = f ⟨j, hj⟩ := by
  rw [getElem!_pos (Array.ofFn f) j (by simpa using hj)]
  simp

theorem arr_get {α : Type} [Inhabited α] (l : List α) {i : Nat} (h : i < l.length) :
    l.toArray[i]! = l[i] := by
  rw [getElem!_pos l.toArray i (by simpa using h)]
  simp

theorem map_get {α β : Type} [Inhabited α] [Inhabited β] (f : α → β) (a : Array α) {i : Nat}
    (h : i < a.size) : (a.map f)[i]! = f a[i]! := by
  rw [getElem!_pos (a.map f) i (by simpa using h), Array.getElem_map, getElem!_pos a i h]

theorem L2_0 : L2 0 = HG.F 0 := by simp only [L2, List.getD_cons_zero]
theorem L2_1 : L2 1 = HG.F 1 := by simp only [L2, List.getD_cons_succ, List.getD_cons_zero]
theorem L3_0 : L3 0 = HG.F 0 := by simp only [L3, List.getD_cons_zero]
theorem L3_1 : L3 1 = HG.F 1 := by simp only [L3, List.getD_cons_succ, List.getD_cons_zero]
theorem L3_2 : L3 2 = PT1 := by simp only [L3, List.getD_cons_succ, List.getD_cons_zero]
theorem LU_0 : LU 0 = HG.F 0 := by simp only [LU, List.getD_cons_zero]
theorem LU_1 : LU 1 = HG.F 1 := by simp only [LU, List.getD_cons_succ, List.getD_cons_zero]
theorem LU_2 : LU 2 = PU := by simp only [LU, List.getD_cons_succ, List.getD_cons_zero]

theorem LY_lt {k : Nat} (hk : k < 9) : LY k = PC1 k := by
  match k, hk with
  | 0, _ => simp only [LY, List.getD_cons_zero]
  | 1, _ => simp only [LY, List.getD_cons_succ, List.getD_cons_zero]
  | 2, _ => simp only [LY, List.getD_cons_succ, List.getD_cons_zero]
  | 3, _ => simp only [LY, List.getD_cons_succ, List.getD_cons_zero]
  | 4, _ => simp only [LY, List.getD_cons_succ, List.getD_cons_zero]
  | 5, _ => simp only [LY, List.getD_cons_succ, List.getD_cons_zero]
  | 6, _ => simp only [LY, List.getD_cons_succ, List.getD_cons_zero]
  | 7, _ => simp only [LY, List.getD_cons_succ, List.getD_cons_zero]
  | 8, _ => simp only [LY, List.getD_cons_succ, List.getD_cons_zero]

theorem LY_9 : LY 9 = PX := by simp only [LY, List.getD_cons_succ, List.getD_cons_zero]

theorem T0K_0 : T0K 0 = PT1 := by simp only [T0K, List.getD_cons_zero]

theorem T0K_succ {i : Nat} (hi : i < 4) :
    T0K (i + 1) = wordTabK 8330 14 PC1 (hfTauWords.getD i []) := by
  match i, hi with
  | 0, _ => simp only [T0K, List.getD_cons_succ, List.getD_cons_zero]
  | 1, _ => simp only [T0K, List.getD_cons_succ, List.getD_cons_zero]
  | 2, _ => simp only [T0K, List.getD_cons_succ, List.getD_cons_zero]
  | 3, _ => simp only [T0K, List.getD_cons_succ, List.getD_cons_zero]

theorem T0K_5 : T0K 5 = wordTabK 8330 14 LY hfYWord := by
  simp only [T0K, List.getD_cons_succ, List.getD_cons_zero]

theorem hid : cn (pidn 8330 14) = true := by
  have h := kId
  simp only [Bool.and_eq_true] at h
  exact h.1

theorem hidA : idA 8330 = unpack 8330 14 (pidn 8330 14) := by
  have h := kId
  simp only [Bool.and_eq_true] at h
  exact (idK_sound h.2).symm

theorem cnR : cn (HR.F 0) = true := by
  have h := kCanonG
  simp only [Bool.and_eq_true] at h
  exact h.2

theorem cnW : cn PT1 = true ∧ cn PU = true ∧ cn PX = true := by
  have h := kCanonW
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem cnC1 {j : Nat} (hj : j < 9) : cn (PC1 j) = true := allN_spec kCanonC j hj

theorem cnLY {k : Nat} (hk : k < 10) : cn (LY k) = true := by
  rcases Nat.lt_or_ge k 9 with h | h
  · rw [LY_lt h]
    exact cnC1 h
  · have : k = 9 := by omega
    subst this
    rw [LY_9]
    exact cnW.2.2

theorem heGen_eq {k : Nat} (hk : k < 2) : heGen k = unpack 8330 14 (HG.F k) := by
  rw [heGen, HG.eq]
  exact hexTable_sound HG.all k hk

theorem heAutR_eq : heAutRArr = unpack 8330 14 (HR.F 0) := by
  rw [heAutRArr, HR.eq]
  exact hexTable_sound HR.all 0 (by decide)

theorem heT1_eq : heT1Arr = unpack 8330 14 PT1 := by
  have hS : heABArrs.size = 2 ∧ ∀ j < 2, heABArrs[j]! = unpack 8330 14 (L2 j) := by
    refine ⟨by simp [heABArrs], fun j hj => ?_⟩
    rw [heABArrs, arr_get _ (by simpa using hj)]
    match j, hj with
    | 0, _ => simpa [L2_0] using heGen_eq (k := 0) (by decide)
    | 1, _ => simpa [L2_1] using heGen_eq (k := 1) (by decide)
  exact (wordEqK_sound hS kPL2 kT1).1

theorem word_of {S SI R : Nat → Nat} {wd : List Int} {nb r : Nat}
    (hN : (Nat.beq (R nb) (pidn 8330 14) && Nat.ble wd.length (32 * nb)) = true)
    (h : ∀ i < nb, Nat.beq (wordK 8330 14 (mask 14) (R (i + 1)) S SI ((wd.drop (32 * i)).take 32))
      (R i) = true)
    (hL : (szOK 8330 14 && lettersK 3 wd) = true) (hF : Nat.beq (R 0) r = true) :
    wordEqK 8330 14 (mask 14) (pidn 8330 14) S SI 3 wd r = true := by
  simp only [Bool.and_eq_true] at hN hL
  have hw : wordK 8330 14 (mask 14) (pidn 8330 14) S SI wd = r :=
    (wordK_chain (Nat.le_of_ble_eq_true hN.2) (Nat.eq_of_beq_eq_true hN.1)
      fun i hi => Nat.eq_of_beq_eq_true (h i hi)).trans (Nat.eq_of_beq_eq_true hF)
  unfold wordEqK
  rw [hL.1, hL.2, hw, Nat.beq_refl]

theorem word_j {j : Nat} (hj : j < 10) (hall : ∀ i < NB j, ckW j i = true) :
    wordEqK 8330 14 (mask 14) (pidn 8330 14) (SJ j) (SIJ j) 3 (WJ j) (FJ j) = true := by
  have he := enAll j hj
  rw [enK, Bool.and_eq_true, Bool.and_eq_true] at he
  exact word_of he.1.1 hall he.1.2 he.2

theorem c1K_all {j : Nat} (hj : j < 9) :
    wordEqK 8330 14 (mask 14) (pidn 8330 14) L3 L3I 3 (heInnerWords1.getD j []) (PC1 j) = true := by
  have hall : ∀ i < NB (j + 1), ckW (j + 1) i = true := by
    match j, hj with
    | 0, _ => exact ck1All
    | 1, _ => exact ck2All
    | 2, _ => exact ck3All
    | 3, _ => exact ck4All
    | 4, _ => exact ck5All
    | 5, _ => exact ck6All
    | 6, _ => exact ck7All
    | 7, _ => exact ck8All
    | 8, _ => exact ck9All
  exact word_j (by omega) hall

theorem heC1_eq {j : Nat} (hj : j < 9) : heInnerC1 j = unpack 8330 14 (PC1 j) := by
  have hS : heInnerLetters1.size = 3 ∧ ∀ j < 3, heInnerLetters1[j]! = unpack 8330 14 (L3 j) := by
    refine ⟨by simp [heInnerLetters1], fun j hj => ?_⟩
    rw [heInnerLetters1, arr_get _ (by simpa using hj)]
    match j, hj with
    | 0, _ => simpa [L3_0] using heGen_eq (k := 0) (by decide)
    | 1, _ => simpa [L3_1] using heGen_eq (k := 1) (by decide)
    | 2, _ => simpa [L3_2] using heT1_eq
  exact (wordEqK_sound hS kPL3 (c1K_all hj)).1

theorem heU_eq : heUArr = unpack 8330 14 PU := by
  rw [heUArr, heAutR_eq, hePowA_unpack hid hidA cnR 5, Nat.eq_of_beq_eq_true kU]

theorem hfX_eq : hfXTab = unpack 8330 14 PX := by
  have hS : hfAUArrs.size = 3 ∧ ∀ j < 3, hfAUArrs[j]! = unpack 8330 14 (LU j) := by
    refine ⟨by simp [hfAUArrs], fun j hj => ?_⟩
    rw [hfAUArrs, arr_get _ (by simpa using hj)]
    match j, hj with
    | 0, _ => simpa [LU_0] using heGen_eq (k := 0) (by decide)
    | 1, _ => simpa [LU_1] using heGen_eq (k := 1) (by decide)
    | 2, _ => simpa [LU_2] using heU_eq
  exact (wordEqK_sound hS kPLU (word_j (j := 0) (by decide) ck0All)).1

theorem tau_lt : ∀ i < 4, ∀ j ∈ hfTauWords.getD i [], j < 9 := by decide

theorem c1Tab_eq {k : Nat} (hk : k < 9) : hfC1Tabs[k]! = unpack 8330 14 (PC1 k) := by
  rw [hfC1Tabs, ofFn_get _ hk]
  exact heC1_eq hk

theorem tau_eq {i : Nat} (hi : i < 4) :
    wordTabS 8330 hfC1Tabs (hfTauWords.getD i []) =
      unpack 8330 14 (wordTabK 8330 14 PC1 (hfTauWords.getD i [])) :=
  wordTabS_unpack hid hidA _ (fun k hk => cnC1 (tau_lt i hi k hk))
    (fun k hk => c1Tab_eq (tau_lt i hi k hk))

theorem yw_lt : ∀ j ∈ hfYWord, j < 10 := by decide

theorem yLetter_eq {k : Nat} (hk : k < 10) : hfYLetterTabs[k]! = unpack 8330 14 (LY k) := by
  rw [hfYLetterTabs, ofFn_get _ hk]
  rcases Nat.lt_or_ge k 9 with h | h
  · simp only [h, ite_true]
    rw [LY_lt h]
    exact heC1_eq h
  · have h9 : k = 9 := by omega
    subst h9
    simp only [Nat.lt_irrefl, ite_false]
    rw [LY_9]
    exact hfX_eq

theorem hfY_eq : hfYTab = unpack 8330 14 (wordTabK 8330 14 LY hfYWord) :=
  wordTabS_unpack hid hidA _ (fun k hk => cnLY (yw_lt k hk)) (fun k hk => yLetter_eq (yw_lt k hk))

theorem T0_get {j : Nat} (hj : j < 6) :
    hfT0Tabs[j]! = unpack 8330 14 (T0K j) ∧ cn (T0K j) = true := by
  rw [hfT0Tabs, ofFn_get _ hj]
  rcases Nat.lt_or_ge j 5 with h5 | h5
  · simp only [h5, ite_true]
    rw [hfTTabs, ofFn_get _ h5]
    rcases j with _ | i
    · simp only [ite_true]
      rw [T0K_0]
      exact ⟨heT1_eq, cnW.1⟩
    · have hi : i < 4 := by omega
      simp only [Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel]
      rw [T0K_succ hi]
      exact ⟨tau_eq hi, canonK_wordTabK hid _ fun k hk => cnC1 (tau_lt i hi k hk)⟩
  · have h6 : j = 5 := by omega
    subst h6
    simp only [Nat.lt_irrefl, ite_false]
    rw [T0K_5]
    exact ⟨hfY_eq, canonK_wordTabK hid _ fun k hk => cnLY (yw_lt k hk)⟩

theorem kRes_all {j : Nat} (hj : j < 6) : restrictK 14 6 hfDelta32 (T0K j) = Q j := by
  apply Nat.eq_of_beq_eq_true
  match j, hj with
  | 0, _ => exact kRes0
  | 1, _ => exact kRes1
  | 2, _ => exact kRes2
  | 3, _ => exact kRes3
  | 4, _ => exact kRes4
  | 5, _ => exact kRes5

theorem delta_lt : ∀ x ∈ hfDelta32, x < 8330 := by decide

theorem delta_len : hfDelta32.length = 32 := by decide

theorem hfT0Tabs32_get :
    hfT0Tabs32.size = 6 ∧ ∀ j < 6, hfT0Tabs32[j]! = unpack 32 6 (Q j) := by
  have h6 : hfT0Tabs.size = 6 := by simp [hfT0Tabs]
  refine ⟨by simp [hfT0Tabs32, h6], fun j hj => ?_⟩
  have hres := restrictArr_unpack (w' := 6) (T0_get hj).2 delta_lt (by rw [delta_len]; decide)
  rw [delta_len] at hres
  rw [hfT0Tabs32, map_get _ _ (by omega), (T0_get hj).1, hfRes, hres, kRes_all hj]

end CertificateChecks.KernelLC.HeFix

end
