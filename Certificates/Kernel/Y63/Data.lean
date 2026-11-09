module

public import Certificates.Kernel.Y63.D

public section

namespace CertificateChecks.KernelY63

open CFSG.KC.Enum CFSG.KS CFSG.OddStandard.HigherRank.YamadaG23.Y63Chk

@[expose] noncomputable def f9 (R i : Nat) : Nat := pg 9 (mask 9) R i

@[expose] noncomputable def f10 (R i : Nat) : Nat := pg 10 (mask 10) R i

@[expose] noncomputable def cnt (i : Nat) : Nat := pg 16 (mask 16) (LNT 0) i

@[expose] noncomputable def cjK (i j : Nat) : Nat × Nat :=
  match (List.range (cnt 1)).find? fun t =>
      Nat.beq (f9 (CJT 0) (4 * t)) i && Nat.beq (f9 (CJT 0) (4 * t + 1)) j with
  | some t => (f9 (CJT 0) (4 * t + 2), f9 (CJT 0) (4 * t + 3))
  | none => (4, 0)

@[expose] noncomputable def dK : Data where
  T x c := f9 (TT x) c
  W y := (List.range (f9 (WT y) 0)).map fun i => f9 (WT y) (i + 1)
  mt x y := f9 (MT x) y
  iv x := f9 (IVT 0) x
  m0 := (List.range 64).map fun i => f9 (M0T 0) i
  reps := (List.range (cnt 0)).map fun i => f9 (M0T 1) i
  sk k := (List.range 64).map fun i => f9 (SKT k) i
  cj := cjK
  tau k x := f9 (TAUT k) x
  z := 165
  u0 k := (List.range 128).map fun i => f10 (U0T k) i
  cw k := (List.range (cnt (2 + k))).map fun i =>
    ⟨f10 (CWT k) (4 * i), f10 (CWT k) (4 * i + 1), f10 (CWT k) (4 * i + 2), f10 (CWT k) (4 * i + 3)⟩

theorem cenSpec_of_gens {D : Data} {k : ℕ} (gs : List ℕ)
    (h1 : D.z < 1024 ∧ D.z ≠ 0 ∧ ∀ y < 1024, D.mq k D.z y = D.mq k y D.z)
    (h2 : ∀ x < 1024, x = 0 ∨ x = D.z ∨ ∃ y ∈ gs, y < 1024 ∧ D.mq k x y ≠ D.mq k y x) :
    D.CenSpec k := by
  refine ⟨h1.1, h1.2.1, h1.2.2, fun x hx hc => ?_⟩
  rcases h2 x hx with h | h | ⟨y, -, hy, hne⟩
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd (hc y hy) hne

@[expose] noncomputable def f7u (R i : Nat) : Nat := pg 7 (mask 7) R i

@[expose] def mqF (D : Data) (k x y : ℕ) : ℕ :=
  Nat.add (D.mt (Nat.mod x 512)
      (cond (Nat.beq (Nat.div x 512) 1) (D.tau k (Nat.mod y 512)) (Nat.mod y 512)))
    (Nat.mul 512 (cond (Nat.beq (Nat.div x 512) (Nat.div y 512)) 0 1))

@[expose] def allY63 (n : ℕ) (f : ℕ → Bool) : Bool := Nat.rec true (fun i ih => f i && ih) n

theorem allY63_iff {n : ℕ} {f : ℕ → Bool} : allY63 n f = true ↔ ∀ i < n, f i = true := by
  induction n with
  | zero => exact ⟨fun _ i hi => absurd hi (Nat.not_lt_zero _), fun _ => rfl⟩
  | succ n ih =>
    change (f n && allY63 n f) = true ↔ _
    rw [Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact h2 i hi
      · exact h1
    · intro h
      exact ⟨h n (Nat.lt_succ_self n), fun i hi => h i (Nat.lt_succ_of_lt hi)⟩

@[expose] def czB (D : Data) (k a b : ℕ) : Bool :=
  Nat.beq (mqF D k a b) (mqF D k b a) || Nat.beq (mqF D k a b) (mqF D k D.z (mqF D k b a))

theorem nbeq_eq_decide (a b : ℕ) : Nat.beq a b = decide (a = b) :=
  Bool.eq_iff_iff.2 (by simp)

theorem mq_eq_mqF (D : Data) (k x y : ℕ) : D.mq k x y = mqF D k x y := by
  change _ = D.mt (x % 512) (cond (Nat.beq (x / 512) 1) (D.tau k (y % 512)) (y % 512)) +
    512 * cond (Nat.beq (x / 512) (y / 512)) 0 1
  simp only [Data.mq, nbeq_eq_decide, Bool.cond_decide]

theorem decide_cz (D : Data) (k a b : ℕ) : decide (D.cz k a b) = czB D k a b := by
  simp only [Data.cz, czB, mq_eq_mqF, nbeq_eq_decide, Bool.decide_or]

theorem czAll_of {D : Data} {k : ℕ} (u : ℕ → ℕ) (hu : D.u0 k = (List.range 128).map u)
    (h : allY63 128 (fun i => allY63 128 fun j => czB D k (u i) (u j)) = true) :
    ∀ a ∈ D.u0 k, ∀ b ∈ D.u0 k, D.cz k a b := by
  rw [hu]
  intro a ha b hb
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 ha
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hb
  have e := allY63_iff.1 (allY63_iff.1 h i (List.mem_range.1 hi)) j (List.mem_range.1 hj)
  rwa [← decide_cz, decide_eq_true_iff] at e

theorem candSpec_of {D : Data} {k : ℕ} (h1 : ∀ w ∈ D.cw k, D.WitOK k w)
    (h2 : ∀ x < 512, x ≠ 0 → mqF D k x x = 0 →
      128 ≤ ((List.range 1024).filter fun y => Nat.beq (mqF D k x y) (mqF D k y x)).length →
      ∃ w ∈ D.cw k, w.x = x) : D.CandSpec k := by
  refine ⟨h1, fun x hx h0 hq hl => h2 x hx h0 (by rwa [← mq_eq_mqF]) ?_⟩
  have e : D.Cen k x = (List.range 1024).filter fun y => Nat.beq (mqF D k x y) (mqF D k y x) :=
    List.filter_congr fun y _ => by
      rw [mq_eq_mqF, mq_eq_mqF, nbeq_eq_decide]
      exact Bool.eq_iff_iff.2 (by simp)
  rwa [← e]

theorem uClos_of_pos {D : Data} {k : ℕ} (u : ℕ → ℕ) (p : ℕ → ℕ → ℕ)
    (hu : D.u0 k = (List.range 128).map u)
    (h : allY63 128 (fun i => allY63 128 fun j =>
      Nat.blt (p i j) 128 && Nat.beq (mqF D k (u i) (u j)) (u (p i j))) = true) :
    ∀ a ∈ D.u0 k, ∀ b ∈ D.u0 k, D.mq k a b ∈ D.u0 k := by
  rw [hu]
  intro a ha b hb
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 ha
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hb
  have hij := allY63_iff.1 (allY63_iff.1 h i (List.mem_range.1 hi)) j (List.mem_range.1 hj)
  simp only [Bool.and_eq_true, Nat.blt_eq, nbeq_eq_decide, decide_eq_true_eq] at hij
  obtain ⟨hp, he⟩ := hij
  exact List.mem_map.2 ⟨p i j, List.mem_range.2 hp, (he.symm.trans (mq_eq_mqF D k _ _).symm)⟩

theorem uMax_of {D : Data} {k : ℕ} (n : ℕ) (s wa wb : ℕ → ℕ)
    (hS : (List.range 1024).filter (fun y => decide (D.sqz k y)) = (List.range n).map s)
    (h : ∀ i < n, s i ∉ D.u0 k →
      (((List.range n).map s).filter fun y => czB D k (s i) y).length < 128 ∨
      ((((List.range n).map s).filter fun y => czB D k (s i) y).length = 128 ∧
        wa i < 1024 ∧ D.sqz k (wa i) ∧ czB D k (s i) (wa i) = true ∧
        wb i < 1024 ∧ D.sqz k (wb i) ∧ czB D k (s i) (wb i) = true ∧
        czB D k (wa i) (wb i) = false)) :
    ∀ x < 1024, D.sqz k x → x ∉ D.u0 k → Crit 128 (D.Dz k x) fun a b => ¬ D.cz k a b := by
  intro x hx hs hu
  have hmem : ∀ y, y < 1024 → D.sqz k y → y ∈ (List.range n).map s := fun y hy hq => by
    rw [← hS]
    exact List.mem_filter.2 ⟨List.mem_range.2 hy, decide_eq_true hq⟩
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 (hmem x hx hs)
  have hD : D.Dz k (s i) =
      ((List.range n).map s).filter fun y => czB D k (s i) y := by
    rw [Data.Dz, ← hS, List.filter_filter]
    exact List.filter_congr fun y _ => by rw [Bool.decide_and, Bool.and_comm, decide_cz]
  rw [hD]
  rcases h i (List.mem_range.1 hi) hu with hl | ⟨hl, ha, hsa, hca, hb, hsb, hcb, hab⟩
  · exact Or.inl hl
  · refine Or.inr ⟨hl, wa i, List.mem_filter.2 ⟨hmem _ ha hsa, hca⟩,
      wb i, List.mem_filter.2 ⟨hmem _ hb hsb, hcb⟩, fun hc => ?_⟩
    rw [← decide_cz, decide_eq_false_iff_not] at hab
    exact hab hc

end CertificateChecks.KernelY63

end
