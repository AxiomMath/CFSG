module

public import Certificates.Kernel.Sporadic.OddCore.S129062K
public import Certificates.Kernel.Sporadic.OddCore.S2307
public import CFSG.Certificates.Kernel.L34KSnd.Tab
import CFSG.Certificates.Kernel.HeSylKSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.S129062

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.L34K CFSG.KS.PEnum CFSG.KC.L34KSnd
open CFSG.Sporadic.SuzOddCore CFSG.PSL3Four.Native CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic
open CertificateChecks.KernelSpor.S2307
open CFSG.KLie.CT (andB orB notB)

attribute [local irreducible] isInvTab idTab ET SSE.T

theorem strictB_app (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem cn {k : Nat} (hk : k < 16384) : canonK 1782 11 (mask 11) (1782 * 11) (SSE.T k) = true :=
  (T_PP k hk).1

theorem hsz : szOK 1782 11 = true := canon_sz (cn (k := 0) (by norm_num))

theorem invTab_eq {k : Nat} (hk : k < 16384) : isInvTab (unpack 1782 11 (SSE.T k)) = invK (SSE.T k) := by
  unfold isInvTab invK
  have e1 : (comp 1782 (unpack 1782 11 (SSE.T k)) (unpack 1782 11 (SSE.T k)) == idTab 1782) =
      invPt 1782 11 (SSE.T k) := by
    rw [Bool.eq_iff_iff, beq_iff_eq, invPt_iff (cn hk)]
  rw [e1, idTab_unpack' hsz, beq_unpack (cn hk) (canon_pidn hsz)]
  cases invPt 1782 11 (SSE.T k) <;> cases Nat.beq (SSE.T k) (pidn 1782 11) <;> rfl

theorem idx_parts {j : Nat} (hj : j < 911) : ix j < 16384 ∧ (j + 1 < 911 → ix j < ix (j + 1)) ∧
    invK (SSE.T (ix j)) = true := by
  have h := CFSG.KS.Raw.Orb.allN_iff.1 kIdx j hj
  rw [strictB_app] at h
  obtain ⟨h1, h2⟩ := andB_iff.1 h
  obtain ⟨h3, h4⟩ := andB_iff.1 h2
  refine ⟨Nat.blt_eq.mp h1, fun hj1 => ?_, h4⟩
  rcases orB_iff.1 h3 with h5 | h5
  · exact absurd (Nat.eq_of_beq_eq_true h5) (by change ¬ j + 1 = 911; omega)
  · exact Nat.blt_eq.mp h5

theorem filter_eq : (List.range 16384).filter (fun k => invK (SSE.T k)) =
    (List.range 911).map ix := by
  refine filter_range_eq_map (p := fun k => invK (SSE.T k)) (fun j hj => idx_parts hj) ?_
  have h0 := kCnt
  unfold cntOK at h0
  have h := Nat.eq_of_beq_eq_true h0
  rw [CFSG.KC.HeAutK.cntR_eq] at h
  exact h

theorem tabs_eq : sylowEnum.tabs = EA := by
  rw [sylowEnum_eq.1]
  exact ER_tabs

theorem EA_toList : EA.toList = (List.range 16384).map ET := by
  unfold EA
  exact CFSG.KC.BfsPin.pts_toList ET

theorem invTabs_def : suzInvTabs () = sylowEnum.tabs.filter isInvTab := by
  unfold suzInvTabs
  rfl

theorem filter_map' {α β : Type} (p : β → Bool) (f : α → β) : ∀ l : List α,
    (l.map f).filter p = (l.filter fun x => p (f x)).map f
  | [] => rfl
  | x :: l => by
    rw [List.map_cons, List.filter_cons, List.filter_cons, filter_map' p f l]
    cases p (f x) <;> rfl

theorem filter_ET_gen : ∀ l : List Nat, (∀ k ∈ l, k < 16384) →
    (l.filter fun k => isInvTab (ET k)) = l.filter (fun k => invK (SSE.T k))
  | [], _ => rfl
  | k :: l, h => by
    have e : isInvTab (ET k) = invK (SSE.T k) := by
      unfold ET
      exact invTab_eq (h k List.mem_cons_self)
    rw [List.filter_cons, List.filter_cons, e,
      filter_ET_gen l (fun x hx => h x (List.mem_cons_of_mem k hx))]

theorem invTabs_eq : (suzInvTabs ()).toList = (List.range 911).map fun j => ET (ix j) := by
  rw [invTabs_def, tabs_eq, Array.toList_filter, EA_toList, filter_map',
    filter_ET_gen _ fun _ hk => List.mem_range.1 hk, filter_eq, List.map_map]
  rfl

theorem invTabs_size : (suzInvTabs ()).size = 911 := by
  rw [← Array.length_toList, invTabs_eq, List.length_map, List.length_range]

theorem invTabs_get {j : Nat} (hj : j < 911) : (suzInvTabs ())[j]! = ET (ix j) := by
  rw [getElem!_pos _ j (by rw [invTabs_size]; exact hj), ← Array.getElem_toList]
  simp only [invTabs_eq, List.getElem_map, List.getElem_range]

theorem col_eq {j : Nat} (hj : j < 911) : suzCol j = col j := by
  have h := CFSG.KC.Misc.HexFlat.hexTable_sound S129C.all 0 (by norm_num)
  rw [Nat.mul_zero, ← S129C.eq] at h
  unfold suzCol col
  rw [h, CFSG.KC.BfsPin.unpack_get' hj]

theorem rank_true : suzRankCheck () = true := by
  unfold suzRankCheck
  simp only [invTabs_size, beq_self_eq_true, Bool.true_and]
  rw [CFSG.KS.BfsReplay.allBelow_iff]
  intro i hi
  have h := CFSG.KS.Raw.Orb.allN_iff.1 kRank i hi
  rw [strictB_app] at h
  obtain ⟨hc, h⟩ := andB_iff.1 h
  rw [Bool.and_eq_true, col_eq hi, decide_eq_true_eq, CFSG.KS.BfsReplay.allBelow_iff]
  refine ⟨Nat.blt_eq.mp hc, fun j hj => ?_⟩
  have h2 := CFSG.KS.Raw.Orb.allN_iff.1 h j hj
  rw [col_eq hj, invTabs_get hi, invTabs_get hj]
  have ci := cn (idx_parts hi).1
  have cj := cn (idx_parts hj).1
  have ec : (comp 1782 (ET (ix i)) (ET (ix j)) == comp 1782 (ET (ix j)) (ET (ix i))) =
      commPt 1782 11 (SSE.T (ix i)) (SSE.T (ix j)) := by
    unfold ET
    rw [Bool.eq_iff_iff, beq_iff_eq, commPt_iff ci cj]
  rw [ec]
  rcases orB_iff.1 h2 with h3 | h3
  · have e : decide (j ≤ i) = true := decide_eq_true (Nat.ble_eq.mp h3)
    rw [e, Bool.true_or, Bool.true_or]
  rcases orB_iff.1 h3 with h4 | h4
  · rw [notB_iff] at h4
    have e : (col j == col i) = false := by
      rw [beq_eq_false_iff_ne]
      exact fun e => by rw [e, Nat.beq_refl] at h4; exact Bool.noConfusion h4
    rw [e, Bool.not_false, Bool.or_true, Bool.true_or]
  · rw [notB_iff] at h4
    rw [h4, Bool.not_false, Bool.or_true]

end CertificateChecks.KernelSpor.S129062

end
