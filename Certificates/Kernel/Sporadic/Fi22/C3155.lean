module

public import Certificates.Kernel.Sporadic.Fi22.C3155K
public import Certificates.Kernel.Sporadic.Fi22.Cert3149
public import CFSG.Certificates.Kernel.Misc.MergeTreeSound
public import CFSG.Certificates.Kernel.Misc.OrbLabSound
public import CFSG.Monster.B.Fischer.PinnedChain

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.F3155

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CertificateChecks.KernelSpor.F3149
open CFSG.Monster.B.Fischer CFSG.Monster.B.Co2 CFSG.Certificates

theorem unpack_get12 {P p : ℕ} (hp : p < 3510) : (unpack 3510 12 P)[p]! = at12 P p := by
  unfold unpack
  rw [getElem!_pos _ p (by rw [Array.size_ofFn]; exact hp), Array.getElem_ofFn]
  rfl

theorem strong_at {j : ℕ} (hj : j < 19) (y : Fin 3510) :
    at12 (Fi22ChT.F j) y = (fi22StrongPerm j y : ℕ) := by
  rw [← unpack_get12 y.isLt, ← Fi22X.strong_eq hj]
  exact rep_fi22Strong hj y

theorem gen_at (i : Fin 2) (y : Fin 3510) :
    pg 12 (mask 12) (Fi22CGT.F i) y = (fi22GenPerm i y : ℕ) := by
  have h := unpack_get12 (P := Fi22CGT.F i) y.isLt
  rw [at12, ← Fi22G.gen_eq i.isLt] at h
  rw [← h]
  exact rep_fi22Gen i.isLt y

theorem idx_eq :
    fi22StabIdx = (List.range 19).filter fun j => decide (fi22StrongPerm j 0 = 0) := by
  rw [← idxOK]
  apply List.filter_congr
  intro j hj
  have e : at12 (Fi22ChT.F j) 0 = (fi22StrongPerm j 0 : ℕ) := strong_at (List.mem_range.1 hj) 0
  rw [e]
  apply Bool.eq_iff_iff.2
  rw [Nat.beq_eq, decide_eq_true_iff]
  exact ⟨fun h => Fin.ext h, fun h => by rw [h]; rfl⟩

theorem jOf_lt {j : ℕ} (hj : j < 18) : jOf j < 19 := by
  rw [← jOfOK j hj]
  have : ∀ j < 18, fi22StabIdx.getD j 0 < 19 := by decide
  exact this j hj

theorem h0_eq : fi22H0 = Subgroup.closure {h | ∃ j < 18, fi22StrongPerm (jOf j) = h} := by
  rw [fi22H0]
  congr 1
  ext σ
  simp only [Set.mem_setOf_eq]
  have hlen : fi22StabIdx.length = 18 := rfl
  constructor
  · rintro ⟨j, hj, rfl⟩
    obtain ⟨i, hi, e⟩ := List.getElem_of_mem hj
    refine ⟨i, by omega, ?_⟩
    rw [← jOfOK i (by omega), List.getD_eq_getElem _ _ hi, e]
  · rintro ⟨j, hj, rfl⟩
    refine ⟨jOf j, ?_, rfl⟩
    rw [← jOfOK j hj, List.getD_eq_getElem _ _ (by omega)]
    exact List.getElem_mem _

theorem fS_eq :
    ∀ j < 18, ∀ y : Fin 3510, fS j y = fi22StrongPerm (jOf j) y := fun j hj y =>
  strong_at (jOf_lt hj) y

theorem blk_eq (s : ℕ) : blk s = if s < 1 then 0 else if s < 2817 then 1 else 2 := by
  unfold blk
  by_cases h1 : s < 1
  · rw [if_pos h1, Nat.blt_eq.mpr h1]
  · rw [if_neg h1, Bool.eq_false_iff.2 fun h => h1 (Nat.blt_eq.mp h)]
    by_cases h2 : s < 2817
    · rw [if_pos h2, Nat.blt_eq.mpr h2]
    · rw [if_neg h2, Bool.eq_false_iff.2 fun h => h2 (Nat.blt_eq.mp h)]

theorem blk_iff {t s : ℕ} (ht : t < 3) (hs : s < 3510) :
    blk s = t ↔ fi22StabOrbitStart t ≤ s ∧ s < fi22StabOrbitStart t + fi22StabOrbitSizes.getD t 0 := by
  rw [blk_eq]
  interval_cases t
  · have e1 : fi22StabOrbitStart 0 = 0 := rfl
    have e2 : fi22StabOrbitSizes.getD 0 0 = 1 := rfl
    rw [e1, e2]
    by_cases h1 : s < 1 <;> by_cases h2 : s < 2817 <;> simp [h1, h2] <;> omega
  · have e1 : fi22StabOrbitStart 1 = 1 := rfl
    have e2 : fi22StabOrbitSizes.getD 1 0 = 2816 := rfl
    rw [e1, e2]
    by_cases h1 : s < 1 <;> by_cases h2 : s < 2817 <;> simp [h1, h2] <;> omega
  · have e1 : fi22StabOrbitStart 2 = 2817 := rfl
    have e2 : fi22StabOrbitSizes.getD 2 0 = 693 := rfl
    rw [e1, e2]
    by_cases h1 : s < 1 <;> by_cases h2 : s < 2817 <;> simp [h1, h2] <;> omega

theorem bij_of {H : ℕ → ℕ} (h : orbK H = true) : ∀ y < 3510, at12 (OT 3) y < 3510 ∧
    G (at12 (OT 3) y) = y ∧ G y < 3510 ∧ at12 (OT 3) (G y) = y := by
  rw [orbK.eq_1] at h
  exact CFSG.KC.OrbLab.ol_bij h

theorem bij : ∀ y < 3510, at12 (OT 3) y < 3510 ∧ G (at12 (OT 3) y) = y ∧ G y < 3510 ∧
    at12 (OT 3) (G y) = y :=
  bij_of orbOK

noncomputable def gS (j : ℕ) : Equiv.Perm (Fin 3510) := fi22StrongPerm (jOf j)

theorem h0_eq' : fi22H0 = Subgroup.closure {h | ∃ j < 18, gS j = h} := by
  simp only [gS.eq_1]
  exact h0_eq

theorem fS_eq' :
    ∀ j < 18, ∀ y : Fin 3510, fS j y = ((gS j y : Fin 3510) : ℕ) := fun j hj y => by
  rw [gS.eq_1]
  exact fS_eq j hj y

theorem orbit_of {H : ℕ → ℕ} (h : orbK H = true) {t : ℕ}
    (ht : t < 3) (hH : H t < 3510) (y : Fin 3510) :
    blk (at12 (OT 3) y) = t ↔ y ∈ MulAction.orbit fi22H0 (⟨H t, hH⟩ : Fin 3510) := by
  rw [orbK.eq_1] at h
  exact CFSG.KC.OrbLab.mem_orbit_iff (g := gS) h0_eq' fS_eq' h ht hH y

theorem mem_stab_iff {t : ℕ} (ht : t < 3) (y : Fin 3510) :
    (y : ℕ) ∈ fi22StabOrbit t ↔ blk (at12 (OT 3) y) = t := by
  have hs := start_le t ht
  unfold fi22StabOrbit
  rw [List.mem_map]
  constructor
  · rintro ⟨k, hk, e⟩
    have hk' := List.mem_range.1 hk
    rw [G_eq (by omega)] at e
    rw [← e, (bij _ (by omega)).2.2.2, blk_iff ht (by omega)]
    omega
  · intro e
    obtain ⟨h1, h2, -, -⟩ := bij y y.isLt
    rw [blk_iff ht h1] at e
    refine ⟨at12 (OT 3) y - fi22StabOrbitStart t, List.mem_range.2 (by omega), ?_⟩
    rw [G_eq (by omega), Nat.add_sub_cancel' e.1, h2]

theorem headD_eq {t : ℕ} (ht : t < 3) : (fi22StabOrbit t).headD 0 = hd t := by
  have key : Nat.beq (G 0) 0 = true ∧ Nat.beq (G 1) 1 = true ∧ Nat.beq (G 2817) 11 = true := by
    have hh := headsOK
    revert hh
    cases Nat.beq (G 0) 0 <;> cases Nat.beq (G 1) 1 <;> cases Nat.beq (G 2817) 11 <;> intro hh <;>
      first | exact ⟨rfl, rfl, rfl⟩ | exact absurd hh Bool.false_ne_true
  obtain ⟨h0, h1, h2⟩ := key
  have hm : ∀ L s, 0 < L → s < 3510 →
      ((List.range L).map fun k =>
        CFSG.Monster.B.Max2.Native.hexAt fi22StabOrbitsBytes (3 * (s + k)) 3).headD 0 = G s := by
    intro L s hL hs
    obtain ⟨L, rfl⟩ := Nat.exists_eq_add_of_lt hL
    rw [Nat.zero_add, List.range_succ_eq_map, List.map_cons, List.headD_cons, Nat.add_zero,
      G_eq hs]
  unfold fi22StabOrbit
  interval_cases t
  · rw [hm _ _ (by decide) (by decide)]
    exact Nat.eq_of_beq_eq_true h0
  · rw [show fi22StabOrbitStart 1 = 1 by decide, hm _ _ (by decide) (by decide)]
    exact Nat.eq_of_beq_eq_true h1
  · rw [show fi22StabOrbitStart 2 = 2817 by decide, hm _ _ (by decide) (by decide)]
    exact Nat.eq_of_beq_eq_true h2

theorem hd_lt {t : ℕ} (ht : t < 3) : hd t < 3510 := by
  interval_cases t <;> decide

theorem orbit_eq {t : ℕ} (ht : t < 3) :
    {y : Fin 3510 | (y : ℕ) ∈ fi22StabOrbit t} =
      MulAction.orbit fi22H0 (fi22Pt ((fi22StabOrbit t).headD 0)) := by
  have ep : fi22Pt ((fi22StabOrbit t).headD 0) = ⟨hd t, hd_lt ht⟩ := by
    rw [headD_eq ht]
    exact Fin.ext (Nat.mod_eq_of_lt (hd_lt ht))
  rw [ep]
  ext y
  rw [Set.mem_setOf_eq, mem_stab_iff ht]
  exact orbit_of orbOK ht (hd_lt ht) y

theorem cover (y : Fin 3510) : ∃ t < 3, (y : ℕ) ∈ fi22StabOrbit t := by
  refine ⟨blk (at12 (OT 3) y), ?_, (mem_stab_iff ?_ y).2 rfl⟩ <;>
  · rw [blk_eq]
    split_ifs <;> omega

theorem heads : ((List.range 3).map fun t => (fi22StabOrbit t).headD 0) = [0, 1, 11] := by
  rw [show List.range 3 = [0, 1, 2] from rfl, List.map_cons, List.map_cons, List.map_cons,
    List.map_nil, headD_eq (by decide), headD_eq (by decide), headD_eq (by decide)]
  rfl

theorem instr_eq {m : ℕ} (hm : m < 2) : ∀ k (hk : k < (fi22MergeList m).length),
    mI m k = (((fi22MergeList m)[k]).1 : ℕ) ∧ mU m k = (((fi22MergeList m)[k]).2.1 : ℕ) ∧
      mV m k = (((fi22MergeList m)[k]).2.2 : ℕ) := by
  intro k hk
  have e : fi22MergeLength = 3508 := rfl
  have hk' : k < 3508 := by simpa [fi22MergeList, e] using hk
  simp only [fi22MergeList, List.getElem_map, List.getElem_range, fi22MergeRaw, fi22Pt, e]
  refine ⟨?_, ?_, ?_⟩
  · rw [mI, D_eq (by omega)]
  · rw [mU, D3_eq (by omega)]
  · rw [mV, D3_eq (by omega)]

theorem merge_len (m : ℕ) : (fi22MergeList m).length = 3508 := by
  simp [fi22MergeList, fi22MergeLength]

noncomputable def gA (k : Fin 2) : Equiv.Perm (Fin 3510) := fi22GenPerm k

theorem gen_at' (i : Fin 2) (y : Fin 3510) :
    pg 12 (mask 12) (Fi22CGT.F i) y = ((gA i y : Fin 3510) : ℕ) := by
  rw [gA.eq_1]
  exact gen_at i y

theorem merge_of {m x : ℕ} (hm : m < 2) (hx : x < 3510)
    (h : mergeK m x = true) :
    ValidInvariantMerge (fun k : Fin 2 => fi22GenPerm k) 0 (fi22Pt x) (fi22MergeList m) := by
  rw [mergeK.eq_1] at h
  have e : ((fi22Pt x : Fin 3510) : ℕ) = x := Nat.mod_eq_of_lt hx
  have e0 : ((0 : Fin 3510) : ℕ) = 0 := rfl
  have hV : ValidInvariantMerge gA 0 (fi22Pt x) (fi22MergeList m) := by
    refine CFSG.KC.MTree.valid_of_mtOK (S := gA) (GP := Fi22CGT.F) (I := mI m) (U := mU m)
      (V := mV m) (nI := 3508) (par := at12 (MT (3 * m))) (tim := at12 (MT (3 * m + 1)))
      (dep := at12 (MT (3 * m + 2))) (root := 0) gen_at' (merge_len m) (instr_eq hm) ?_
    rw [e, e0]
    exact h
  have eA : gA = fun k : Fin 2 => fi22GenPerm k := by
    funext k
    rw [gA.eq_1]
  rw [eA] at hV
  exact hV

theorem merge_one :
    ValidInvariantMerge (fun k : Fin 2 => fi22GenPerm k) 0 (fi22Pt 1) (fi22MergeList 0) :=
  merge_of (m := 0) (x := 1) (by decide) (by decide) merge0

theorem merge_eleven :
    ValidInvariantMerge (fun k : Fin 2 => fi22GenPerm k) 0 (fi22Pt 11) (fi22MergeList 1) :=
  merge_of (m := 1) (x := 11) (by decide) (by decide) merge1

end CertificateChecks.KernelSpor.F3155

end
