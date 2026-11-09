module

public import Certificates.Kernel.Y63.Data

public section

namespace CertificateChecks.KernelY63

open CFSG.OddStandard.HigherRank.YamadaG23.Y63Chk

theorem ball_blocks {N B : ℕ} {P : ℕ → Prop} (h : ∀ j < B, ∀ x < N, P (N * j + x)) :
    ∀ x < N * B, P x := by
  intro x hx
  have hN : 0 < N := Nat.pos_of_ne_zero fun e => by subst e; simp at hx
  have hj : x / N < B := (Nat.div_lt_iff_lt_mul hN).2 (by rwa [Nat.mul_comm] at hx)
  have := h (x / N) hj (x % N) (Nat.mod_lt _ hN)
  rwa [Nat.div_add_mod] at this

theorem mem_map_range {g : ℕ → ℕ} {n : ℕ} {P : ℕ → Prop} (h : ∀ i < n, P (g i)) :
    ∀ a ∈ (List.range n).map g, P a := by
  intro a ha
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 ha
  exact h i (List.mem_range.1 hi)

@[expose] def UHead (D : Data) (k : ℕ) : Prop :=
  (D.u0 k).Nodup ∧ (D.u0 k).length = 128 ∧ (∀ a ∈ D.u0 k, a < 1024) ∧ 0 ∈ D.u0 k ∧
    D.z ∈ D.u0 k

instance (D : Data) (k : ℕ) : Decidable (UHead D k) := by
  unfold UHead
  infer_instance

@[expose] def UCi (D : Data) (k a : ℕ) : Prop := ∀ b ∈ D.u0 k, D.mq k a b ∈ D.u0 k

instance (D : Data) (k a : ℕ) : Decidable (UCi D k a) := by
  unfold UCi
  infer_instance

@[expose] def UMid (D : Data) (k : ℕ) : Prop :=
  (∀ a ∈ D.u0 k, ∃ b ∈ D.u0 k, D.mq k a b = 0) ∧ (∀ a ∈ D.u0 k, D.sqz k a) ∧
    ∀ a ∈ D.u0 k, ∀ b ∈ D.u0 k, D.cz k a b

instance (D : Data) (k : ℕ) : Decidable (UMid D k) := by
  unfold UMid
  infer_instance

@[expose] def ULx (D : Data) (k x : ℕ) : Prop :=
  D.sqz k x → x ∉ D.u0 k → Crit 128 (D.Dz k x) fun a b => ¬ D.cz k a b

instance (D : Data) (k x : ℕ) : Decidable (ULx D k x) := by
  unfold ULx
  infer_instance

@[expose] def CandA (D : Data) (k : ℕ) : Prop := ∀ w ∈ D.cw k, D.WitOK k w

instance (D : Data) (k : ℕ) : Decidable (CandA D k) := by
  unfold CandA
  infer_instance

@[expose] def CBx (D : Data) (k x : ℕ) : Prop :=
  x ≠ 0 → D.mq k x x = 0 → 128 ≤ (D.Cen k x).length → ∃ w ∈ D.cw k, w.x = x

instance (D : Data) (k x : ℕ) : Decidable (CBx D k x) := by
  unfold CBx
  infer_instance

theorem USpec_of {D : Data} {k : ℕ} (hH : UHead D k) (hC : ∀ a ∈ D.u0 k, UCi D k a)
    (hM : UMid D k) (hL : ∀ x < 1024, ULx D k x) : D.USpec k := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hH
  obtain ⟨m1, m2, m3⟩ := hM
  unfold Data.USpec
  exact ⟨h1, h2, h3, h4, h5, hC, m1, m2, m3, hL⟩

theorem CandSpec_of {D : Data} {k : ℕ} (hA : CandA D k) (hB : ∀ x < 512, CBx D k x) :
    D.CandSpec k := by
  unfold Data.CandSpec
  exact ⟨hA, hB⟩

theorem QSpec_of {D : Data} {k : ℕ} (hT : D.TauSpec k) (hC : D.CenSpec k) (hU : D.USpec k)
    (hW : D.CandSpec k) : D.QSpec k := by
  unfold Data.QSpec
  exact ⟨hT, hC, hU, hW⟩

@[expose] def CenZ (D : Data) (k : ℕ) : Prop :=
  D.z < 1024 ∧ D.z ≠ 0 ∧ ∀ y < 1024, D.mq k D.z y = D.mq k y D.z

instance (D : Data) (k : ℕ) : Decidable (CenZ D k) := by
  unfold CenZ
  infer_instance

@[expose] def CenW (D : Data) (k : ℕ) (gs : List ℕ) (x : ℕ) : Prop :=
  x = 0 ∨ x = D.z ∨ ∃ g ∈ gs, g < 1024 ∧ D.mq k x g ≠ D.mq k g x

instance (D : Data) (k : ℕ) (gs : List ℕ) (x : ℕ) : Decidable (CenW D k gs x) := by
  unfold CenW
  infer_instance

@[expose] noncomputable def cgs : List ℕ :=
  (List.range 10).map (fun c => dK.T 0 c) ++ 512 :: List.range 1024

theorem CenSpec_of {D : Data} {k : ℕ} {gs : List ℕ} (hZ : CenZ D k)
    (hW : ∀ x < 1024, CenW D k gs x) : D.CenSpec k := by
  obtain ⟨h1, h2, h3⟩ := hZ
  unfold Data.CenSpec
  refine ⟨h1, h2, h3, fun x hx hc => ?_⟩
  rcases hW x hx with h | h | ⟨g, -, hg, hne⟩
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd (hc g hg) hne

@[expose] noncomputable def allB (n : ℕ) (f : ℕ → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun i ih => f i && ih) n

theorem allB_iff {n : ℕ} {f : ℕ → Bool} : allB n f = true ↔ ∀ i < n, f i = true := by
  induction n with
  | zero => exact ⟨fun _ i hi => absurd hi (Nat.not_lt_zero i), fun _ => rfl⟩
  | succ n ih =>
    show (f n && allB n f) = true ↔ _
    rw [Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_or_ge i n with h | h
      · exact h2 i h
      · have e : i = n := Nat.le_antisymm (Nat.le_of_lt_succ hi) h
        subst e
        exact h1
    · intro h
      exact ⟨h n (Nat.lt_succ_self n), fun i hi => h i (Nat.lt_succ_of_lt hi)⟩

@[expose] def ParOK (D : Data) (par lt : ℕ → ℕ) : Prop :=
  D.W 0 = [] ∧ ∀ y < 512, y ≠ 0 → par y < 512 ∧ D.W y = D.W (par y) ++ [lt y]

instance (D : Data) (par lt : ℕ → ℕ) : Decidable (ParOK D par lt) := by
  unfold ParOK
  infer_instance

@[expose] noncomputable def mulRowB (D : Data) (par lt : ℕ → ℕ) (x : ℕ) : Bool :=
  allB 512 fun y => Nat.beq (D.mt x y) (bif Nat.beq y 0 then x else D.T (D.mt x (par y)) (lt y)) &&
    Nat.blt (D.mt x y) 512

theorem MulSpec_of_par {D : Data} {par lt : ℕ → ℕ} (hP : ParOK D par lt)
    (hR : ∀ x < 512, mulRowB D par lt x = true) : D.MulSpec := by
  obtain ⟨hW0, hW⟩ := hP
  unfold Data.MulSpec
  intro x hx
  have hr := fun y (hy : y < 512) => Bool.and_eq_true_iff.1 (allB_iff.1 (hR x hx) y hy)
  have key : ∀ n, ∀ y < 512, (D.W y).length ≤ n → D.mt x y = (D.W y).foldl D.T x := by
    intro n
    induction n with
    | zero =>
      intro y hy hl
      have e := Nat.eq_of_beq_eq_true (hr y hy).1
      by_cases h0 : y = 0
      · subst h0
        rw [hW0, e]
        rfl
      · exfalso
        obtain ⟨-, hy'⟩ := hW y hy h0
        rw [hy', List.length_append, List.length_singleton] at hl
        omega
    | succ n ih =>
      intro y hy hl
      have e := Nat.eq_of_beq_eq_true (hr y hy).1
      by_cases h0 : y = 0
      · subst h0
        rw [hW0, e]
        rfl
      · obtain ⟨hp, hy'⟩ := hW y hy h0
        have hb : Nat.beq y 0 = false := by
          cases h : Nat.beq y 0
          · rfl
          · exact absurd (Nat.eq_of_beq_eq_true h) h0
        have hl' : (D.W (par y)).length ≤ n := by
          rw [hy', List.length_append, List.length_singleton] at hl
          omega
        rw [e, hb, hy', List.foldl_append, ← ih (par y) hp hl']
        rfl
  intro y hy
  exact ⟨key _ y hy (Nat.le_refl _), Nat.le_of_ble_eq_true (hr y hy).2⟩

end CertificateChecks.KernelY63

end
