
module

public import Certificates.Kernel.Sporadic.ONC.ChainBase
public import CFSG.Certificates.Kernel.ONOut.InvVSound
import Certificates.Kernel.Sporadic.ONC.T1
import Certificates.Kernel.Sporadic.ONC.T5
import Certificates.Kernel.Sporadic.ONC.T6
import Certificates.Kernel.Sporadic.ONC.HdS
import Certificates.Kernel.Sporadic.ONC.Ln
import Certificates.Kernel.Sporadic.ON.Gen
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

#kon_join CertificateChecks.KernelSpor.ONC.tr3All CertificateChecks.KernelSpor.ONC.tr3 1
#kon_join CertificateChecks.KernelSpor.ONC.tr4All CertificateChecks.KernelSpor.ONC.tr4 6
#kon_join CertificateChecks.KernelSpor.ONC.tr5All CertificateChecks.KernelSpor.ONC.tr5 59
#kon_join CertificateChecks.KernelSpor.ONC.tr6All CertificateChecks.KernelSpor.ONC.tr6 53
#kon_join CertificateChecks.KernelSpor.ONC.tr7All CertificateChecks.KernelSpor.ONC.tr7 7
#kon_join CertificateChecks.KernelSpor.ONC.hd3All CertificateChecks.KernelSpor.ONC.hd3 123
#kon_join CertificateChecks.KernelSpor.ONC.hd4All CertificateChecks.KernelSpor.ONC.hd4 123
#kon_join CertificateChecks.KernelSpor.ONC.hd5All CertificateChecks.KernelSpor.ONC.hd5 123
#kon_join CertificateChecks.KernelSpor.ONC.hd6All CertificateChecks.KernelSpor.ONC.hd6 123
#kon_join CertificateChecks.KernelSpor.ONC.hd7All CertificateChecks.KernelSpor.ONC.hd7 123
#kon_join CertificateChecks.KernelSpor.ONC.lnAll CertificateChecks.KernelSpor.ONC.lnSl 246
#kon_join CertificateChecks.KernelSpor.ONC.rpAll CertificateChecks.KernelSpor.ONC.rpSl 123
#kon_join CertificateChecks.KernelSpor.ONC.lbAll CertificateChecks.KernelSpor.ONC.lbSl 123
#kon_join CertificateChecks.KernelSpor.ONC.lb0All CertificateChecks.KernelSpor.ONC.lb0 1
#kon_join CertificateChecks.KernelSpor.ONC.lb1All CertificateChecks.KernelSpor.ONC.lb1 6
#kon_join CertificateChecks.KernelSpor.ONC.lb2All CertificateChecks.KernelSpor.ONC.lb2 59
#kon_join CertificateChecks.KernelSpor.ONC.lb3All CertificateChecks.KernelSpor.ONC.lb3 53
#kon_join CertificateChecks.KernelSpor.ONC.lb4All CertificateChecks.KernelSpor.ONC.lb4 7

namespace CertificateChecks.KernelSpor.ONC

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON CFSG.KS.PEnum CFSG.KS.TBfs CFSG.KS.PC CFSG.KS.ONC
open CFSG.Sporadic.ON CFSG.Sporadic.ON.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.Perm.Native CFSG.Sporadic.ON.Kernel
open CFSG.Sporadic.SmallF2.Native (labelsOf inTreeB)

noncomputable abbrev negN : Table := negTable (orbitData ()) posOrb

theorem neg_pt {k : ℕ} (hk : k < 245520) : tab ONW2.NEG k < 245520 ∧
    key ONW.K (tab ONW2.NEG k) = vneg (key ONW.K k) ∧ tab ONW2.NEG (tab ONW2.NEG k) = k := by
  have e := CertificateChecks.KernelSpor.ON.pt_of CertificateChecks.KernelSpor.ON2.negAll
    (fun _ => rfl) k hk
  unfold negAt at e
  rw [strictB_eq', bAnd_iff', bAnd_iff'] at e
  exact ⟨Nat.blt_eq.mp e.1, Nat.eq_of_beq_eq_true e.2.1, Nat.eq_of_beq_eq_true e.2.2⟩

theorem negN_ap {k : ℕ} (hk : k < 245520) : ap negN k = tab ONW2.NEG k := by
  have hidx := index_sound CertificateChecks.KernelSpor.ON2.keys2 CertificateChecks.KernelSpor.ON2.canon2
    (CertificateChecks.KernelSpor.ON.pt_of CertificateChecks.KernelSpor.ON2.sortAll fun _ => rfl)
  obtain ⟨hj, hk', -⟩ := neg_pt hk
  have hneg : (orbitData ()).keys[k]!.neg = (orbitData ()).keys[tab ONW2.NEG k]! := by
    rw [CertificateChecks.KernelSpor.ON2.key_get hk, CertificateChecks.KernelSpor.ON2.key_get hj,
      wOfK_vneg (CertificateChecks.KernelSpor.ON2.canon2 k hk), hk']
  have hs : (orbitData ()).keys.size = 245520 := by
    rw [CertificateChecks.KernelSpor.ON2.keys2, Array.size_ofFn]
  unfold ap negN negTable posOrb
  rw [getElem!_pos _ k (by simp [hs]; omega), Array.getElem_map, ← getElem!_pos _ k (by omega),
    hneg, hidx _ hj, UInt32.toNat_ofNat']
  exact Nat.mod_eq_of_lt (by omega)

theorem ln_pt {k : ℕ} (hk : k < 245520) : r32 LF k < 122760 ∧
    r32 LF (tab ONW2.NEG k) = r32 LF k ∧
    (r32 RP (r32 LF k) = k ∨ r32 RP (r32 LF k) = tab ONW2.NEG k) := by
  have h := slice_all (N := 245520) (S := 246) (by norm_num) (fun s hs => lnAll s hs) k hk
  rw [strictB_eq', strictB_eq', bAnd_iff', bAnd_iff'] at h
  refine ⟨Nat.blt_eq.mp h.1, Nat.eq_of_beq_eq_true h.2.1, ?_⟩
  have h3 := h.2.2
  cases e : Nat.beq (r32 RP (r32 LF k)) k
  · rw [e] at h3
    exact Or.inr (Nat.eq_of_beq_eq_true h3)
  · exact Or.inl (Nat.eq_of_beq_eq_true e)

theorem rp_pt {j : ℕ} (hj : j < 122760) : r32 RP j < 245520 ∧ r32 LF (r32 RP j) = j ∧
    r32 RP j < tab ONW2.NEG (r32 RP j) ∧ (j + 1 < 122760 → r32 RP j < r32 RP (j + 1)) := by
  have h := slice_all (N := 122760) (S := 123) (by norm_num) (fun s hs => rpAll s hs) j hj
  rw [strictB_eq', bAnd_iff', bAnd_iff', bAnd_iff'] at h
  refine ⟨Nat.blt_eq.mp h.1, Nat.eq_of_beq_eq_true h.2.1, Nat.blt_eq.mp h.2.2.1, fun hj1 => ?_⟩
  have h4 := h.2.2.2
  have hb : Nat.blt (Nat.succ j) 122760 = true := Nat.blt_eq.mpr hj1
  rw [hb] at h4
  exact Nat.blt_eq.mp h4

theorem rp_mono {i j : ℕ} (hij : i < j) (hj : j < 122760) : r32 RP i < r32 RP j := by
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h | rfl
    · exact lt_trans (ih h (by omega)) ((rp_pt (by omega)).2.2.2 hj)
    · exact (rp_pt (by omega)).2.2.2 hj

theorem foldl_push_if {q : ℕ → Prop} [DecidablePred q] {f : ℕ → UInt32} :
    ∀ (l : List ℕ) (acc : Array UInt32),
      l.foldl (fun r k => if q k then r.push (f k) else r) acc =
        acc ++ ((l.filter fun k => decide (q k)).map f).toArray
  | [], acc => by simp
  | k :: l, acc => by
    rw [List.foldl_cons, foldl_push_if l]
    by_cases h : q k
    · simp [h, List.filter_cons]
    · simp [h, List.filter_cons]

theorem lineReps_eq (N : Table) : lineReps N =
    (((List.range' 0 nPts).filter fun k => decide (k < ap N k)).map UInt32.ofNat).toArray := by
  unfold lineReps
  simp only [Id.run_bind, Id.run_pure, Std.Legacy.Range.forIn_eq_forIn_range',
    CFSG.KS.ONOut.InvV.ite_pure_yield, List.forIn_pure_yield_eq_foldl, pure_bind, bind_pure,
    Std.Legacy.Range.size, Nat.add_sub_cancel, Nat.div_one]
  rw [Nat.sub_zero, foldl_push_if (q := fun k => k < ap N k) (f := UInt32.ofNat)]
  simp

theorem filter_eq : ((List.range' 0 nPts).filter fun k => decide (k < ap negN k)) =
    (List.range 122760).map (r32 RP) := by
  refine List.Perm.eq_of_pairwise (le := (· < ·))
    (fun a b _ _ h1 h2 => absurd (lt_trans h1 h2) (lt_irrefl a)) ?_ ?_ ?_
  · exact (List.pairwise_lt_range' (s := 0) (n := nPts)).filter _
  · rw [List.pairwise_map]
    exact List.pairwise_lt_range.imp_of_mem fun _ hj h => rp_mono h (List.mem_range.1 hj)
  · apply (List.perm_ext_iff_of_nodup ((List.nodup_range' ..).filter _) _).2
    · intro x
      rw [List.mem_filter, List.mem_range'_1, List.mem_map]
      simp only [List.mem_range, decide_eq_true_eq]
      constructor
      · rintro ⟨⟨-, hx⟩, hlt⟩
        have hx' : x < 245520 := by rw [Nat.zero_add] at hx; exact hx
        rw [negN_ap hx'] at hlt
        obtain ⟨hl, -, hr⟩ := ln_pt hx'
        refine ⟨r32 LF x, hl, ?_⟩
        rcases hr with hr | hr
        · exact hr
        · exfalso
          have := (rp_pt hl).2.2.1
          rw [hr, (neg_pt hx').2.2] at this
          omega
      · rintro ⟨j, hj, rfl⟩
        obtain ⟨h1, -, h3, -⟩ := rp_pt hj
        refine ⟨⟨Nat.zero_le _, by rw [Nat.zero_add]; exact h1⟩, ?_⟩
        rw [negN_ap h1]
        exact h3
    · apply List.Nodup.map_on _ List.nodup_range
      intro i hi j hj e
      rw [List.mem_range] at hi hj
      rcases lt_trichotomy i j with h | h | h
      · exact absurd e (ne_of_lt (rp_mono h hj))
      · exact h
      · exact absurd e (ne_of_gt (rp_mono h hi))

theorem reps_size : (lineReps negN).size = 122760 := by
  rw [lineReps_eq, filter_eq]
  simp

theorem reps_ap {j : ℕ} (hj : j < 122760) : ap (lineReps negN) j = r32 RP j := by
  have h1 := (rp_pt hj).1
  unfold ap
  rw [lineReps_eq, filter_eq, getElem!_pos _ j (by simp; omega)]
  simp only [List.getElem_toArray, List.getElem_map, List.getElem_range, UInt32.toNat_ofNat']
  exact Nat.mod_eq_of_lt (by omega)

theorem set2_loop {N : Nat} {D₁ D₂ : ℕ → ℕ} {v : ℕ → UInt32} :
    ∀ {m : ℕ}, (∀ j < m, D₁ j < N ∧ D₂ j < N ∧ D₁ j ≠ D₂ j) →
      (∀ j < m, ∀ i < j, D₁ i ≠ D₁ j ∧ D₁ i ≠ D₂ j ∧ D₂ i ≠ D₁ j ∧ D₂ i ≠ D₂ j) →
      ((List.range' 0 m).foldl (fun t j => (t.set! (D₁ j) (v j)).set! (D₂ j) (v j))
        (Array.replicate N 0)).size = N ∧
      ∀ j < m, ((List.range' 0 m).foldl (fun t j => (t.set! (D₁ j) (v j)).set! (D₂ j) (v j))
        (Array.replicate N 0))[D₁ j]! = v j ∧
        ((List.range' 0 m).foldl (fun t j => (t.set! (D₁ j) (v j)).set! (D₂ j) (v j))
        (Array.replicate N 0))[D₂ j]! = v j
  | 0, _, _ => ⟨by simp, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  | m + 1, hD, hd => by
    obtain ⟨hs, hv⟩ := set2_loop (m := m) (fun j hj => hD j (by omega))
      (fun j hj i hi => hd j (by omega) i hi)
    rw [List.range'_1_concat, List.foldl_append, List.foldl_cons, List.foldl_nil]
    simp only [Nat.zero_add]
    generalize (List.range' 0 m).foldl (fun t j => (t.set! (D₁ j) (v j)).set! (D₂ j) (v j))
      (Array.replicate N 0) = q at hs hv
    obtain ⟨h1, h2, h12⟩ := hD m (by omega)
    have hs1 : (q.set! (D₁ m) (v m)).size = N := by
      rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, hs]
    have hs2 : ((q.set! (D₁ m) (v m)).set! (D₂ m) (v m)).size = N := by
      rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, hs1]
    refine ⟨hs2, fun j hj => ?_⟩
    rw [getElem!_set!' _ _ _ _ (by rw [hs1]; exact (hD j hj).1),
      getElem!_set!' _ _ _ _ (by rw [hs]; exact (hD j hj).1),
      getElem!_set!' _ _ _ _ (by rw [hs1]; exact (hD j hj).2.1),
      getElem!_set!' _ _ _ _ (by rw [hs]; exact (hD j hj).2.1)]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj' | rfl
    · obtain ⟨a, b, c, d⟩ := hd m (by omega) j hj'
      rw [if_neg (Ne.symm b), if_neg (Ne.symm a), if_neg (Ne.symm d), if_neg (Ne.symm c)]
      exact hv j hj'
    · rw [if_neg (Ne.symm h12), if_pos rfl, if_pos rfl]
      exact ⟨rfl, rfl⟩

theorem lineOfT_eq (N R : Table) : lineOfT N R = (List.range' 0 R.size).foldl
    (fun t j => (t.set! (ap R j) (UInt32.ofNat j)).set! (ap N (ap R j)) (UInt32.ofNat j))
    (Array.replicate nPts 0) := by
  unfold lineOfT
  simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.forIn_pure_yield_eq_foldl]

theorem lineT_facts : (lineOfT negN (lineReps negN)).size = 245520 ∧
    ∀ k < 245520, ap (lineOfT negN (lineReps negN)) k = r32 LF k := by
  rw [lineOfT_eq, reps_size]
  have hD : ∀ j < 122760, ap (lineReps negN) j < 245520 ∧ ap negN (ap (lineReps negN) j) < 245520 ∧
      ap (lineReps negN) j ≠ ap negN (ap (lineReps negN) j) := fun j hj => by
    rw [reps_ap hj, negN_ap (rp_pt hj).1]
    exact ⟨(rp_pt hj).1, (neg_pt (rp_pt hj).1).1, ne_of_lt (rp_pt hj).2.2.1⟩
  have hd : ∀ j < 122760, ∀ i < j, ap (lineReps negN) i ≠ ap (lineReps negN) j ∧
      ap (lineReps negN) i ≠ ap negN (ap (lineReps negN) j) ∧
      ap negN (ap (lineReps negN) i) ≠ ap (lineReps negN) j ∧
      ap negN (ap (lineReps negN) i) ≠ ap negN (ap (lineReps negN) j) := fun j hj i hi => by
    have hi' : i < 122760 := by omega
    rw [reps_ap hj, reps_ap hi', negN_ap (rp_pt hj).1, negN_ap (rp_pt hi').1]
    have hm := rp_mono hi hj
    obtain ⟨a1, -, a3, -⟩ := rp_pt hi'
    obtain ⟨b1, -, b3, -⟩ := rp_pt hj
    obtain ⟨-, -, na⟩ := neg_pt a1
    obtain ⟨-, -, nb⟩ := neg_pt b1
    refine ⟨ne_of_lt hm, fun e => ?_, fun e => ?_, fun e => ?_⟩
    · have := congrArg (tab ONW2.NEG) e
      rw [nb] at this
      rw [← this] at b3
      omega
    · have := congrArg (tab ONW2.NEG) e
      rw [na] at this
      rw [this] at a3
      omega
    · have := congrArg (tab ONW2.NEG) e
      rw [na, nb] at this
      omega
  have hl := set2_loop (v := fun j => UInt32.ofNat j) hD hd
  refine ⟨hl.1, fun k hk => ?_⟩
  obtain ⟨f1, -, f3⟩ := ln_pt hk
  have hw := hl.2 _ f1
  rw [reps_ap f1, negN_ap (rp_pt f1).1] at hw
  have hv : (UInt32.ofNat (r32 LF k)).toNat = r32 LF k := by
    simp only [UInt32.toNat_ofNat']
    exact Nat.mod_eq_of_lt (by omega)
  unfold ap
  rcases f3 with e | e
  · have h1 := hw.1
    rw [e] at h1
    exact (congrArg UInt32.toNat h1).trans hv
  · have e2 : tab ONW2.NEG (r32 RP (r32 LF k)) = k := by rw [e, (neg_pt hk).2.2]
    have h2 := hw.2
    rw [e2] at h2
    exact (congrArg UInt32.toNat h2).trans hv

end CertificateChecks.KernelSpor.ONC

end
