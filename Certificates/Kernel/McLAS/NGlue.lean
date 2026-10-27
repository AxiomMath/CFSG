module

public import Certificates.Kernel.McLAS.Glue
public import Certificates.Data.Kernel.McLAS.Nrm
public import CFSG.Sporadic.Recognition.LyonsAS44McLInputs
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Spor.RawOrbHead
import Mathlib.Tactic.IntervalCases
import CFSG.Certificates.Kernel.Spor.RawOrbGrp

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMcLAS

open CFSG.Sporadic.Recognition.McLAS CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.KC.Enum CFSG.KS CFSG.KS.Raw
open CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KC.BfsPin CFSG.Monster.B.Co2.Native
open CFSG.KS.McLAS CFSG.KS.Raw.Orb

theorem not_memT_of {cnt : Nat} {T PL SRT SRI : Nat → Nat} {X s : Nat}
    (hS : ∀ i < cnt, r32 SRT i < cnt ∧ r32 SRI (r32 SRT i) = i ∧
      (i + 1 < cnt → T (r32 SRT i) < T (r32 SRT (i + 1))))
    (hc : ∀ q < cnt, Cn (T q)) (hX : Cn X) (hb : brK cnt T SRT X s = true) :
    memT 275 (hRec 275 9 cnt T PL).1 (tabT (unpack 275 9 X)) = false := by
  have hmono : ∀ i j, i < j → j < cnt → T (r32 SRT i) < T (r32 SRT j) := by
    intro i j hij hj
    induction j with
    | zero => omega
    | succ j ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h | h
      · exact lt_trans (ih h (by omega)) ((hS j (by omega)).2.2 hj)
      · subst h
        exact (hS i (by omega)).2.2 hj
  have hle : ∀ i j, i ≤ j → j < cnt → T (r32 SRT i) ≤ T (r32 SRT j) := fun i j h hj => by
    rcases Nat.lt_or_eq_of_le h with h | h
    · exact Nat.le_of_lt (hmono i j h hj)
    · rw [h]
  have hsurj : ∀ a < cnt, ∃ i < cnt, r32 SRT i = a := by
    classical
    have himg : (Finset.range cnt).image (r32 SRT) = Finset.range cnt := by
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hx
        exact Finset.mem_range.2 (hS i (Finset.mem_range.1 hi)).1
      · rw [Finset.card_image_of_injOn]
        intro i hi j hj e
        have h1 := (hS i (Finset.mem_range.1 hi)).2.1
        have h2 := (hS j (Finset.mem_range.1 hj)).2.1
        rw [← h1, ← h2]
        exact congrArg (r32 SRI) e
    intro a ha
    have hm : a ∈ (Finset.range cnt).image (r32 SRT) := by
      rw [himg]
      exact Finset.mem_range.2 ha
    obtain ⟨i, hi, e⟩ := Finset.mem_image.1 hm
    exact ⟨i, Finset.mem_range.1 hi, e⟩
  unfold brK at hb
  obtain ⟨h1, h23⟩ := (bAnd_iff _ _).1 hb
  obtain ⟨h2, h3⟩ := (bAnd_iff _ _).1 h23
  have h1 : s ≤ cnt := Nat.le_of_ble_eq_true h1
  rw [Bool.eq_false_iff]
  intro hm
  unfold memT at hm
  rw [Array.any_eq_true] at hm
  obtain ⟨q, hq, hqe⟩ := hm
  simp only [hRec, Array.size_ofFn] at hq
  simp only [hRec, Array.getElem_ofFn] at hqe
  rw [tblEq_unpack hX (hc q hq)] at hqe
  have hXq : X = T q := Nat.eq_of_beq_eq_true hqe
  obtain ⟨i, hi, hiq⟩ := hsurj q hq
  rw [← hiq] at hXq
  by_cases his : i < s
  · have hs0 : s ≠ 0 := by omega
    have e : Nat.beq s 0 = false := Bool.eq_false_iff.2 fun h => hs0 (Nat.eq_of_beq_eq_true h)
    rw [e] at h2
    have h2' : T (r32 SRT (Nat.sub s 1)) < X := Nat.blt_eq.mp h2
    have := hle i (s - 1) (by omega) (by omega)
    change T (r32 SRT (s - 1)) < X at h2'
    omega
  · have hsc : s ≠ cnt := by omega
    have e : Nat.beq s cnt = false := Bool.eq_false_iff.2 fun h => hsc (Nat.eq_of_beq_eq_true h)
    rw [e] at h3
    have h3' : X < T (r32 SRT s) := Nat.blt_eq.mp h3
    have := hle s i (by omega) hi
    omega

theorem nrmY_get {j : Nat} (hj : j < 10) : nrmY[j]! = tabT (unpack 275 9 (NT.F j)) := by
  unfold nrmY
  rw [getElem!_pos _ j (by simpa using hj)]
  simp only [Array.getElem_map, List.getElem_toArray, List.getElem_range]
  exact tabNT (by omega)

theorem nrmY_size : nrmY.size = 10 := by
  unfold nrmY
  simp

theorem nrmC_get {j : Nat} (hj : j < 10) : nrmC[j]! = tabT (unpack 275 9 (NT.F (12 + j))) := by
  unfold nrmC
  rw [getElem!_pos _ j (by simpa using hj)]
  simp only [Array.getElem_map, List.getElem_toArray, List.getElem_range]
  exact tabNT (by omega)

theorem nrmC_size : nrmC.size = 10 := by
  unfold nrmC
  simp

theorem aGens3_get {j : Nat} (hj : j < 4) : aGens3[j]! = tabT (unpack 275 9 (TL.F (j + 7))) := by
  unfold aGens3
  rw [getElem!_pos _ j (by simpa using hj)]
  simp only [List.getElem_toArray, List.getElem_map, List.getElem_range]
  exact tabTL (by omega)

theorem aGens3_size : aGens3.size = 4 := by
  unfold aGens3
  simp

theorem yPred_eq {Z j : Nat} (hZ : Cn Z) (hj : j < 10) :
    (tblEq 275 (tabT (unpack 275 9 Z)) nrmY[j]! ||
      tblEq 275 (tabT (unpack 275 9 Z)) (invT 275 nrmY[j]!)) = yPredK NT.F NTI Z j := by
  rw [nrmY_get hj, invT_unpack (by norm_num) (NTinv (by omega)), tblEq_unpack hZ (NTc (by omega)),
    tblEq_unpack hZ (NTIc (by omega))]
  unfold yPredK
  cases Nat.beq Z (NT.F j) <;> rfl

theorem nrmPt_eq {Z v : Nat} (hZ : Cn Z) (h : firstK NT.F NTI Z v = true) :
    nrmPt (tabT (unpack 275 9 Z)) = v := by
  unfold firstK at h
  simp only [bAnd_eq, Bool.and_eq_true, blt_dec, decide_eq_true_eq] at h
  obtain ⟨hv, hp, hall⟩ := h
  unfold nrmPt
  have hf : (List.range 10).find? (fun j => tblEq 275 (tabT (unpack 275 9 Z)) nrmY[j]! ||
      tblEq 275 (tabT (unpack 275 9 Z)) (invT 275 nrmY[j]!)) = some v := by
    rw [List.find?_range_eq_some]
    refine ⟨by rw [yPred_eq hZ hv]; exact hp, List.mem_range.2 hv, fun j hj => ?_⟩
    have hk := allN_spec hall j hj
    rw [yPred_eq hZ (by omega)]
    cases e : yPredK NT.F NTI Z j
    · rfl
    · rw [e] at hk
      exact absurd hk (by decide)
  rw [hf]
  rfl

theorem nrmPt_lt {Z : Nat} (hZ : Cn Z) (h : anyYK NT.F NTI Z = true) :
    nrmPt (tabT (unpack 275 9 Z)) < 10 := by
  unfold anyYK at h
  have hex : ∃ j < 10, yPredK NT.F NTI Z j = true := by
    by_contra hne
    have hne' : ∀ j < 10, yPredK NT.F NTI Z j = false := fun j hj =>
      Bool.eq_false_iff.2 fun hp => hne ⟨j, hj, hp⟩
    have ha : allN 10 (fun j => bIf(yPredK NT.F NTI Z j, false, true)) = true :=
      allN_of fun j hj => by rw [hne' j hj]
    rw [ha] at h
    exact absurd h (by decide)
  obtain ⟨j, hj, hpj⟩ := hex
  unfold nrmPt
  have hs : ((List.range 10).find? (fun j => tblEq 275 (tabT (unpack 275 9 Z)) nrmY[j]! ||
      tblEq 275 (tabT (unpack 275 9 Z)) (invT 275 nrmY[j]!))).isSome := by
    rw [List.find?_isSome]
    exact ⟨j, List.mem_range.2 hj, by rw [yPred_eq hZ hj]; exact hpj⟩
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hs
  rw [hv]
  have := List.mem_range.1 (List.mem_of_find?_eq_some hv)
  exact this

end CertificateChecks.KernelMcLAS

end
