module

public import Certificates.Kernel.LocalComp.FendelBridge
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Co3IdentTree
public import Certificates.Data.Kernel.Co3Bfs

public section

namespace CFSG.KC.Co3Bfs

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Fendel
open CFSG.Monster.B.Co2.Native CFSG.EvenSmallLie.SympSix.Co3Ident

theorem blocks {f : Nat → Bool} {B nb : Nat} (hB : 0 < B)
    (h : ∀ j < nb, allFrom (B * j) B f = true) : ∀ k < B * nb, f k = true := by
  intro k hk
  have hj := h (k / B) (Nat.div_lt_of_lt_mul hk)
  unfold allFrom at hj
  have h2 := allN_spec hj (k % B) (Nat.mod_lt _ hB)
  rw [Fendel.strictB_eq] at h2
  have e : Nat.add (B * (k / B)) (k % B) = k := Nat.div_add_mod k B
  rwa [e] at h2

theorem beq_zero_false {k : Nat} (hk : 0 < k) : Nat.beq k 0 = false := by
  cases k with
  | zero => omega
  | succ k => rfl

theorem ofFn_get {α : Type} [Inhabited α] {c : Nat} (f : Nat → α) {j : Nat} (hj : j < c) :
    (Array.ofFn (n := c) fun k => f k.val)[j]! = f j := by
  rw [getElem!_pos _ j (by simpa using hj)]
  simp

theorem inj_of_sort {key E S SI : Nat → Nat} {c : Nat} (h : ∀ m < c, sortK key E S SI c m = true) :
    ∀ a b, a < c → b < c → key (E a) = key (E b) → a = b := by
  have hS : ∀ m < c, S m < c ∧ SI m < c ∧ S (SI m) = m ∧
      (m + 1 < c → key (E (S m)) < key (E (S (m + 1)))) := by
    intro m hm
    have hm' := h m hm
    unfold sortK at hm'
    obtain ⟨h1, hm'⟩ := (bAnd_iff _ _).1 hm'
    obtain ⟨h2, hm'⟩ := (bAnd_iff _ _).1 hm'
    obtain ⟨h3, h4⟩ := (bAnd_iff _ _).1 hm'
    refine ⟨Nat.le_of_ble_eq_true h1, Nat.le_of_ble_eq_true h2, Nat.eq_of_beq_eq_true h3,
      fun hm1 => ?_⟩
    have hb : Nat.blt (Nat.succ m) c = true := Nat.ble_eq_true_of_le hm1
    rw [hb] at h4
    exact Nat.le_of_ble_eq_true h4
  have mono : ∀ m1 m2, m1 < m2 → m2 < c → key (E (S m1)) < key (E (S m2)) := by
    intro m1 m2 h12 h2c
    induction m2 with
    | zero => omega
    | succ m ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 h12 with h | h
      · exact lt_trans (ih h (by omega)) ((hS m (by omega)).2.2.2 h2c)
      · subst h
        exact (hS m1 (by omega)).2.2.2 h2c
  intro a b ha hb e
  obtain ⟨-, ha1, ha2, -⟩ := hS a ha
  obtain ⟨-, hb1, hb2, -⟩ := hS b hb
  rcases Nat.lt_trichotomy (SI a) (SI b) with hlt | heq | hgt
  · have := mono _ _ hlt hb1
    rw [ha2, hb2] at this
    omega
  · rw [← ha2, ← hb2, heq]
  · have := mono _ _ hgt ha1
    rw [ha2, hb2] at this
    omega

theorem strictInc_of_pairwise : ∀ l : List Nat, l.Pairwise (· < ·) → strictInc l = true
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: l, h => by
    have h1 : a < b := List.rel_of_pairwise_cons h (List.mem_cons_self ..)
    have h2 := strictInc_of_pairwise (b :: l) (List.Pairwise.of_cons h)
    simp only [strictInc, h2, Bool.and_true, decide_eq_true_eq]
    exact h1

theorem keysOK_of_inj {pts : List Nat} {T : Array (Array Nat)} {N : Nat}
    (hinj : ∀ a b, a < N → b < N → keyOf pts T[a]! = keyOf pts T[b]! → a = b) :
    keysOK pts T N = true := by
  unfold keysOK
  apply strictInc_of_pairwise
  have hnd : ((List.range N).map fun j => keyOf pts T[j]!).Nodup := by
    refine List.Nodup.map_on (fun a ha b hb e => ?_) List.nodup_range
    exact hinj a b (List.mem_range.1 ha) (List.mem_range.1 hb) e
  have hp := List.mergeSort_perm ((List.range N).map fun j => keyOf pts T[j]!)
    (fun a b => decide (a ≤ b))
  have hs := List.pairwise_mergeSort (le := fun a b => decide (a ≤ b))
    (fun a b c hab hbc => by simp_all only [decide_eq_true_eq]; omega)
    (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega)
    ((List.range N).map fun j => keyOf pts T[j]!)
  have hnd' := hp.nodup_iff.2 hnd
  refine (hs.and hnd').imp ?_
  intro a b ⟨h1, h2⟩
  simp only [decide_eq_true_eq] at h1
  omega

theorem keyOf_unpack2 (X : Nat) : keyOf [0, 1] (unpack 276 9 X) = keyR X := by
  simp [keyOf, unpack, keyR, pt]

theorem keyOf_unpack4 (X : Nat) : keyOf [0, 1, 2, 3] (unpack 276 9 X) = key4 X := by
  simp [keyOf, unpack, key4, pt]

end CFSG.KC.Co3Bfs

end
