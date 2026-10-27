module

public import CFSG.Certificates.Kernel.E8PlaneGlue
public import Certificates.Kernel.E8Plane.Bridge
public import Certificates.Kernel.E8Plane.Checks
public import Certificates.Kernel.E8Plane.SortCheck
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E8KilledPlaneWords

public section

namespace CFSG.KD.E8Plane

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E8NonToral
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E8NonToral.E8Plane CFSG.KC.E8Plane


theorem nthL_eq_getD {α : Type} (L : List α) (d : α) (i : ℕ) : nthL L d i = L.getD i d := by
  induction L generalizing i with
  | nil => simp [nthL]
  | cons x L ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i

theorem rW_lt : ∀ w ∈ RW, ∀ l ∈ w, l < 8 := by
  rw [RW_eq_e8PlaneWord]
  intro w hw
  obtain ⟨c, -, rfl⟩ := List.mem_map.1 hw
  exact e8PlaneWord_lt c

theorem qW_lt : ∀ w ∈ QW, ∀ l ∈ w, l < 8 := by
  rw [QW_eq_e8PlaneWord]
  intro w hw
  obtain ⟨c, -, rfl⟩ := List.mem_map.1 hw
  exact e8PlaneWord_lt c

theorem rW_getD_lt (i : ℕ) : ∀ l ∈ RW.getD i [], l < 8 := by
  intro l hl
  by_cases hi : i < RW.length
  · rw [List.getD_eq_getElem _ _ hi] at hl
    exact rW_lt _ (List.getElem_mem hi) l hl
  · rw [List.getD_eq_default _ _ (by omega)] at hl
    simp at hl

theorem rW_getD_lt' (i : ℕ) : ∀ l ∈ RW.getD i [], l < 240 := fun l hl => by
  have := rW_getD_lt i l hl
  omega

theorem hT : pk 64 TB = pk 64 e8Certificate.table := by rw [TB_eq_e8Certificate_table]

theorem hRP : pk 32 RC = pk 32 e8Certificate.roots := by rw [RC_eq_e8Certificate_roots]

theorem reflTable_rt : ReflTable (rtA (pk 32 RC) (pk 32 SC) (pk 8 SI)) :=
  reflTable_rtA hRP sort_check

theorem qW_getD {c : ℕ} (hc : c < 243) : QW.getD c [] = e8PlaneWord c := by
  rw [QW_eq_e8PlaneWord]
  simp [hc]

theorem rep3B_check : rep3B (pk 32 RC) (pk 32 SC) (pk 8 SI) (permP (pk 64 TB) (nthL RW [] 2)) FM13
    FL13 FC13 WS13 D213 D313 = true := by
  unfold rep3B excB
  rw [rep13_fix, rep13_pairs, rep13_d2, rep13_d3]
  rfl

theorem wS1_pos : 0 < WS1.length := by decide +kernel

theorem wS4_pos : 0 < WS4.length := by decide +kernel

theorem planeOK_rep (i : ℕ) (b : Fin 2 → Fin Tag.E8.rank → ZMod 3)
    (hfix : ∀ s x, triPairing (b s) (wordR (RW.getD i []) • x) = triPairing (b s) x) :
    E8PlaneOK (wordR (RW.getD i [])) b := by
  have hP := permOf8_permA reflTable_rt (rW_getD_lt' i)
  by_cases hi : i < 4
  · interval_cases i
    · rw [← nthL_eq_getD] at hP hfix ⊢
      exact planeOK_of_facts reflTable_rt hP
        (easyB_facts hT hRP sort_check (by rw [nthL_eq_getD]; exact rW_getD_lt 0) wS1_pos
          rep1_check reflTable_rt) b hfix
    · rw [← nthL_eq_getD] at hP hfix ⊢
      exact planeOK_of_facts reflTable_rt hP
        (easyB_facts hT hRP sort_check (by rw [nthL_eq_getD]; exact rW_getD_lt 1) wS4_pos
          rep4_check reflTable_rt) b hfix
    · rw [← nthL_eq_getD] at hP hfix ⊢
      exact planeOK_of_facts reflTable_rt hP
        (rep3B_facts hT hRP sort_check (by rw [nthL_eq_getD]; exact rW_getD_lt 2)
          rep3B_check reflTable_rt) b hfix
    · rw [← nthL_eq_getD] at hP hfix ⊢
      exact planeOK_of_facts reflTable_rt hP
        (rep4B_facts hT hRP sort_check (by rw [nthL_eq_getD]; exact rW_getD_lt 3)
          rep40_check reflTable_rt) b hfix
  · have hlen : RW.length ≤ i := by
      rw [RW_eq_e8PlaneWord]
      simp only [List.length_map, List.length_cons, List.length_nil]
      omega
    rw [List.getD_eq_default _ _ hlen]
    exact Or.inl (one_mem _)

theorem e8ThreeKilledPlaneBlocks_kernel : E8ThreeKilledPlaneBlocks :=
  e8ThreeKilledPlaneBlocks_of_reps reflTable_rt rW_getD_lt
    (fun c hc => by
      have h := qB_facts hT qW_lt rW_lt lett_check q_check reflTable_rt c
        (by rw [QW_eq_e8PlaneWord]; simpa using hc)
      rwa [qW_getD hc] at h)
    planeOK_rep

end CFSG.KD.E8Plane
