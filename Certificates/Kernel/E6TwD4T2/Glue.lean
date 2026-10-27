module

public import CFSG.Certificates.Kernel.E6TwD4T2Sound
public import Certificates.Kernel.E6TwD4T2.Data
public import Certificates.Data.E6ThreeTwD4T2Gen

set_option maxRecDepth 100000

public section

namespace CertificateChecks.KernelE6TwD4T2

open CFSG.KD.E6TwD4T2 CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.HardMathSupport.Timmesfeld.CrossChar

theorem r3_root_check : ((List.range 72).all fun p => (List.finRange Tag.E6.rank).all fun j =>
    decide (e6Certificate.root p j % 3 = (((r3.getD p []).getD j 0 : ℕ) : ℤ))) = true := by
  decide +kernel

theorem sig_check : (twD4T2Sig () == sig) = true := by decide +kernel

theorem elems_check : (twD4T2Elems.map (fun e => decodeT Tag.E6.rank e.1) == elems) = true := by
  decide +kernel

theorem elems_lt_check : (elems.all fun t => (List.range 6).all fun j => decide (t.getD j 0 < 72)) =
    true := by decide +kernel

theorem negs_check : ((List.range elems.length).all fun i => (negs.getD i []).all fun p =>
    decide (p < 72) && sig.contains p && decide (0 < height (e6Certificate.root p)) &&
      decide (height (e6Certificate.tupleVec (elems.getD i []) (e6Certificate.root p)) ≤ 0)) =
    true := by decide +kernel

theorem len_check : elems.length ≤ negs.length := by decide +kernel

theorem sig_eq : twD4T2Sig () = sig := beq_iff_eq.1 sig_check

theorem elems_eq : twD4T2Elems.map (fun e => decodeT Tag.E6.rank e.1) = elems :=
  beq_iff_eq.1 elems_check

theorem r3_root {p : ℕ} (hp : p < 72) (j : Fin Tag.E6.rank) :
    ((e6Certificate.root p j : ℤ) : ZMod 3) = (((r3.getD p []).getD j 0 : ℕ) : ZMod 3) := by
  have h := r3_root_check
  simp only [List.all_eq_true, List.mem_range, List.mem_finRange, true_implies,
    decide_eq_true_eq] at h
  rw [← ZMod.intCast_mod, Nat.cast_ofNat, h p hp j, Int.cast_natCast]

theorem nat_zmod3 {n : ℕ} (h : n < 3) : (n : ZMod 3) = 0 ↔ n = 0 := by
  interval_cases n <;> decide

theorem dot3_cast (k : ℕ) (l : List ℕ) : ((dot3 k l : ℕ) : ZMod 3) =
    ∑ i ∈ Finset.range 6, ((k / 3 ^ i % 3 : ℕ) : ZMod 3) * ((l.getD i 0 : ℕ) : ZMod 3) := by
  unfold dot3
  rw [ZMod.natCast_mod, Nat.cast_sum]
  simp only [Nat.cast_mul]

theorem pair_eq (k : ℕ) (v : Fin Tag.E6.rank → ℤ) (l : List ℕ)
    (h : ∀ j : Fin Tag.E6.rank, ((v j : ℤ) : ZMod 3) = ((l.getD j 0 : ℕ) : ZMod 3)) :
    triPairing (vec3OfIndex (τ := .E6) k) v = ((dot3 k l : ℕ) : ZMod 3) := by
  rw [dot3_cast]
  unfold triPairing
  simp only [h, vec3OfIndex]
  exact Fin.sum_univ_eq_sum_range (fun j => ((k / 3 ^ j % 3 : ℕ) : ZMod 3) * ((l.getD j 0 : ℕ) : ZMod 3)) 6

theorem pair_root (k : ℕ) {p : ℕ} (hp : p < 72) :
    triPairing (vec3OfIndex (τ := .E6) k) (e6Certificate.root p) =
      ((dot3 k (r3.getD p []) : ℕ) : ZMod 3) :=
  pair_eq k _ _ (r3_root hp)

theorem getD_range_map {α : Type} (g : ℕ → α) (d : α) {i : ℕ} (hi : i < 6) :
    ((List.range 6).map g).getD i d = g i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
  rfl

theorem fixes_iff (k : ℕ) {t : List ℕ} (ht : ∀ j < 6, t.getD j 0 < 72) :
    twD4T2Fixes (vec3OfIndex (τ := .E6) k) t = true ↔ ∀ w ∈ wv r3 t, dot3 k w = 0 := by
  simp only [twD4T2Fixes, List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq]
  unfold wv
  simp only [List.forall_mem_map, List.mem_range]
  have key : ∀ P d : ZMod 3, P + d * 2 = 0 ↔ P = d := by decide
  have hj : ∀ j < 6, (dot3 k ((List.range 6).map fun i =>
      ((r3.getD (t.getD j 0) []).getD i 0 + (if i == j then 2 else 0)) % 3) = 0 ↔
      ((dot3 k (r3.getD (t.getD j 0) []) : ℕ) : ZMod 3) = ((k / 3 ^ j % 3 : ℕ) : ZMod 3)) := by
    intro j hj
    rw [← nat_zmod3 (dot3_lt _ _), dot3_cast, dot3_cast]
    rw [Finset.sum_congr rfl fun i hi => by
      rw [getD_range_map _ _ (Finset.mem_range.1 hi)]]
    simp only [ZMod.natCast_mod, Nat.cast_add, beq_iff_eq, Nat.cast_ite, Nat.cast_ofNat,
      Nat.cast_zero, mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq',
      Finset.sum_ite_eq, Finset.mem_range, hj, if_true]
    exact key _ _
  constructor
  · intro h j hj'
    exact (hj j hj').2 (by rw [← pair_root k (ht j hj')]; exact h ⟨j, hj'⟩)
  · intro h j
    rw [pair_root k (ht j j.2)]
    exact (hj j j.2).1 (h j j.2)

end CertificateChecks.KernelE6TwD4T2
