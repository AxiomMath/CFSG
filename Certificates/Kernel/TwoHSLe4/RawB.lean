module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S8Raw

public section

namespace CertificateChecks.KernelTwoHSLe4

open CFSG.EvenSporadicStandard.TwoHS

@[expose] def r4eq (a b : R4) : Bool :=
  a.a00 == b.a00 && a.a01 == b.a01 && a.a02 == b.a02 && a.a03 == b.a03 &&
  a.a10 == b.a10 && a.a11 == b.a11 && a.a12 == b.a12 && a.a13 == b.a13 &&
  a.a20 == b.a20 && a.a21 == b.a21 && a.a22 == b.a22 && a.a23 == b.a23 &&
  a.a30 == b.a30 && a.a31 == b.a31 && a.a32 == b.a32 && a.a33 == b.a33

theorem r4eq_iff {a b : R4} : r4eq a b = true ↔ a = b := by
  cases a
  cases b
  simp [r4eq, and_assoc]

@[expose] def rveq (v w : RV) : Bool :=
  v.v0 == w.v0 && v.v1 == w.v1 && v.v2 == w.v2 && v.v3 == w.v3

theorem rveq_iff {v w : RV} : rveq v w = true ↔ v = w := by
  cases v
  cases w
  simp [rveq, and_assoc]

@[expose] def memR (x : R4) (l : List R4) : Bool :=
  List.rec false (fun b _ ih => r4eq x b || ih) l

theorem memR_iff {x : R4} {l : List R4} : memR x l = true ↔ x ∈ l := by
  induction l with
  | nil => simp [memR]
  | cons b l ih =>
    change (r4eq x b || memR x l) = true ↔ _
    rw [Bool.or_eq_true, r4eq_iff, ih, List.mem_cons]

@[expose] def memV (x : RV) (l : List RV) : Bool :=
  List.rec false (fun b _ ih => rveq x b || ih) l

theorem memV_iff {x : RV} {l : List RV} : memV x l = true ↔ x ∈ l := by
  induction l with
  | nil => simp [memV]
  | cons b l ih =>
    change (rveq x b || memV x l) = true ↔ _
    rw [Bool.or_eq_true, rveq_iff, ih, List.mem_cons]

@[expose] def allR (p : R4 → Bool) (l : List R4) : Bool :=
  List.rec true (fun b _ ih => p b && ih) l

theorem allR_iff {p : R4 → Bool} {l : List R4} : allR p l = true ↔ ∀ b ∈ l, p b = true := by
  induction l with
  | nil => simp [allR]
  | cons b l ih =>
    change (p b && allR p l) = true ↔ _
    rw [Bool.and_eq_true, ih, List.forall_mem_cons]

@[expose] def allV (p : RV → Bool) (l : List RV) : Bool :=
  List.rec true (fun b _ ih => p b && ih) l

theorem allV_iff {p : RV → Bool} {l : List RV} : allV p l = true ↔ ∀ b ∈ l, p b = true := by
  induction l with
  | nil => simp [allV]
  | cons b l ih =>
    change (p b && allV p l) = true ↔ _
    rw [Bool.and_eq_true, ih, List.forall_mem_cons]

end CertificateChecks.KernelTwoHSLe4
