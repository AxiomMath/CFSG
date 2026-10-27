
module

public import Certificates.Kernel.ExcIns.GrowAll
public import CFSG.Certificates.Kernel.ExcIns.A8Sound
public import Certificates.Kernel.ExcIns.WitChecks
public import Certificates.Kernel.ExcIns.A8Checks

public section

noncomputable section

namespace CFSG.ExcInsK

open CFSG.ExcExtK CFSG.StandardType.GGQ2Frame.ExcRaw

@[expose] def InsT (m : Fin 6) (c : ℕ) : Prop :=
  Nonempty (SatWitness m (ofMask m c)) ∨ ((m.val = 2 ∨ m.val = 3) ∧ (ofMask m c = Finset.univ ∨
    ∃ k, ofMask m c = Finset.univ.filter fun i => pairing m k i = 0 ∧ pairing m i k = 0))

theorem pairSigned0 (u : Root 0) (hu : u.val < 4) : ∃ ε : Root 0 → ℤ, (∀ i, ε i = 1 ∨ ε i = -1) ∧
    ∀ i j : Root 0, pairing 0 (rtR tabsOK0 u i) (rtR tabsOK0 u j) = ε i * ε j * pairing 0 i j :=
  pairSigned_of tabsOK_D0 ch712571sg u hu

theorem pairSigned2 (u : Root 2) (hu : u.val < 6) : ∃ ε : Root 2 → ℤ, (∀ i, ε i = 1 ∨ ε i = -1) ∧
    ∀ i j : Root 2, pairing 2 (rtR tabsOK2 u i) (rtR tabsOK2 u j) = ε i * ε j * pairing 2 i j :=
  pairSigned_of tabsOK_D2 ch712574sg u hu

theorem pairSigned3 (u : Root 3) (hu : u.val < 6) : ∃ ε : Root 3 → ℤ, (∀ i, ε i = 1 ∨ ε i = -1) ∧
    ∀ i j : Root 3, pairing 3 (rtR tabsOK3 u i) (rtR tabsOK3 u j) = ε i * ε j * pairing 3 i j :=
  pairSigned_of tabsOK_D3 ch712575sg u hu

theorem pairSigned4 (u : Root 4) (hu : u.val < 7) : ∃ ε : Root 4 → ℤ, (∀ i, ε i = 1 ∨ ε i = -1) ∧
    ∀ i j : Root 4, pairing 4 (rtR tabsOK4 u i) (rtR tabsOK4 u j) = ε i * ε j * pairing 4 i j :=
  pairSigned_of tabsOK_D4 ch712572sg u hu

theorem pairSigned5 (u : Root 5) (hu : u.val < 8) : ∃ ε : Root 5 → ℤ, (∀ i, ε i = 1 ∨ ε i = -1) ∧
    ∀ i j : Root 5, pairing 5 (rtR tabsOK5 u i) (rtR tabsOK5 u j) = ε i * ε j * pairing 5 i j :=
  pairSigned_of tabsOK_D5 ch712573sg u hu

private theorem Q0 (c : ℕ) (x : KRep) (h : repK D.T0 D.hx0 4 false c x = true) : InsT 0 c :=
  repK_sound tabsOK_D0 (fun h => absurd h Bool.false_ne_true) h

private theorem all0 : ∀ x < 8, InsT 0 (ln128 D0.R x) := by
  have h1 := forall_lt_succ (P := fun x => InsT 0 (ln128 D0.R x)) (forall_lt_zero _) (Q0 _ _ ch712571w_0)
  have h2 := forall_lt_succ h1 (Q0 _ _ ch712571w_1)
  have h3 := forall_lt_succ h2 (Q0 _ _ ch712571w_2)
  have h4 := forall_lt_succ h3 (Q0 _ _ ch712571w_3)
  have h5 := forall_lt_succ h4 (Q0 _ _ ch712571w_4)
  have h6 := forall_lt_succ h5 (Q0 _ _ ch712571w_5)
  have h7 := forall_lt_succ h6 (Q0 _ _ ch712571w_6)
  exact forall_lt_succ h7 (Q0 _ _ ch712571w_7)

theorem repT0 (x : Fin 8) : Nonempty (SatWitness 0 (ofMask 0 (R0 x))) ∨ (((0 : Fin 6).val = 2 ∨ (0 : Fin 6).val = 3) ∧
    (ofMask 0 (R0 x) = Finset.univ ∨
      ∃ k, ofMask 0 (R0 x) = Finset.univ.filter fun i => pairing 0 k i = 0 ∧ pairing 0 i k = 0)) :=
  all0 x.val x.isLt

private theorem Q2 (c : ℕ) (x : KRep) (h : repK D.T2 D.hx2 6 true c x = true) : InsT 2 c :=
  repK_sound tabsOK_D2 (fun _ => Or.inl rfl) h

private theorem all2 : ∀ x < 8, InsT 2 (ln128 D2.R x) := by
  have h1 := forall_lt_succ (P := fun x => InsT 2 (ln128 D2.R x)) (forall_lt_zero _) (Q2 _ _ ch712574w_0)
  have h2 := forall_lt_succ h1 (Q2 _ _ ch712574w_1)
  have h3 := forall_lt_succ h2 (Q2 _ _ ch712574w_2)
  have h4 := forall_lt_succ h3 (Q2 _ _ ch712574w_3)
  have h5 := forall_lt_succ h4 (Q2 _ _ ch712574w_4)
  have h6 := forall_lt_succ h5 (Q2 _ _ ch712574w_5)
  have h7 := forall_lt_succ h6 (Q2 _ _ ch712574w_6)
  exact forall_lt_succ h7 (Q2 _ _ ch712574w_7)

theorem repT2 (x : Fin 8) : Nonempty (SatWitness 2 (ofMask 2 (R2 x))) ∨ (((2 : Fin 6).val = 2 ∨ (2 : Fin 6).val = 3) ∧
    (ofMask 2 (R2 x) = Finset.univ ∨
      ∃ k, ofMask 2 (R2 x) = Finset.univ.filter fun i => pairing 2 k i = 0 ∧ pairing 2 i k = 0)) :=
  all2 x.val x.isLt

private theorem Q3 (c : ℕ) (x : KRep) (h : repK D.T3 D.hx2 6 true c x = true) : InsT 3 c :=
  repK_sound tabsOK_D3 (fun _ => Or.inr rfl) h

private theorem all3 : ∀ x < 6, InsT 3 (ln128 D3.R x) := by
  have h1 := forall_lt_succ (P := fun x => InsT 3 (ln128 D3.R x)) (forall_lt_zero _) (Q3 _ _ ch712575w_0)
  have h2 := forall_lt_succ h1 (Q3 _ _ ch712575w_1)
  have h3 := forall_lt_succ h2 (Q3 _ _ ch712575w_2)
  have h4 := forall_lt_succ h3 (Q3 _ _ ch712575w_3)
  have h5 := forall_lt_succ h4 (Q3 _ _ ch712575w_4)
  exact forall_lt_succ h5 (Q3 _ _ ch712575w_5)

theorem repT3 (x : Fin 6) : Nonempty (SatWitness 3 (ofMask 3 (R3 x))) ∨ (((3 : Fin 6).val = 2 ∨ (3 : Fin 6).val = 3) ∧
    (ofMask 3 (R3 x) = Finset.univ ∨
      ∃ k, ofMask 3 (R3 x) = Finset.univ.filter fun i => pairing 3 k i = 0 ∧ pairing 3 i k = 0)) :=
  all3 x.val x.isLt

private theorem Q4 (c : ℕ) (x : KRep) (h : repK D.T4 D.hx4 7 false c x = true) : InsT 4 c :=
  repK_sound tabsOK_D4 (fun h => absurd h Bool.false_ne_true) h

private theorem all4 : ∀ x < 12, InsT 4 (ln128 D4.R x) := by
  have h1 := forall_lt_succ (P := fun x => InsT 4 (ln128 D4.R x)) (forall_lt_zero _) (Q4 _ _ ch712572w_0)
  have h2 := forall_lt_succ h1 (Q4 _ _ ch712572w_1)
  have h3 := forall_lt_succ h2 (Q4 _ _ ch712572w_2)
  have h4 := forall_lt_succ h3 (Q4 _ _ ch712572w_3)
  have h5 := forall_lt_succ h4 (Q4 _ _ ch712572w_4)
  have h6 := forall_lt_succ h5 (Q4 _ _ ch712572w_5)
  have h7 := forall_lt_succ h6 (Q4 _ _ ch712572w_6)
  have h8 := forall_lt_succ h7 (Q4 _ _ ch712572w_7)
  have h9 := forall_lt_succ h8 (Q4 _ _ ch712572w_8)
  have h10 := forall_lt_succ h9 (Q4 _ _ ch712572w_9)
  have h11 := forall_lt_succ h10 (Q4 _ _ ch712572w_10)
  exact forall_lt_succ h11 (Q4 _ _ ch712572w_11)

theorem repT4 (x : Fin 12) : Nonempty (SatWitness 4 (ofMask 4 (R4 x))) ∨ (((4 : Fin 6).val = 2 ∨ (4 : Fin 6).val = 3) ∧
    (ofMask 4 (R4 x) = Finset.univ ∨
      ∃ k, ofMask 4 (R4 x) = Finset.univ.filter fun i => pairing 4 k i = 0 ∧ pairing 4 i k = 0)) :=
  all4 x.val x.isLt

@[expose] def A8 (n : ℕ) : Prop := ∃ i < 960, ln128 A5.AP i = n

def F8 (i : ℕ) : Prop := Nonempty (A8Witness 5 (ofMask 5 (ln128 A5.AP i))) ∧
  ∀ u : Root 5, u.val < 8 → ∃ idx < 960,
    ln128 A5.AP idx = Chk.imgN (tabsK 5 D.T5) (nroots 5) u.val (ln128 A5.AP i)

def G8 (q : ℕ) : Prop := ∀ i, 60 * q ≤ i → i < 60 * q + 60 → F8 i

private theorem chunk (q lo hi : ℕ) (hlo : lo = 60 * q) (hhi : hi = 60 * q + 60) (L : List KA8R)
    (h : chunkK D.T5 D.fx5 8 8 A5.AP 960 hi L lo = true) : G8 q := by
  subst hlo hhi
  exact chunk_facts (m := 5) tabsOK_D5 h

private theorem allG : ∀ q < 16, G8 q := by
  have h1 := forall_lt_succ (P := G8) (forall_lt_zero _) (chunk 0 _ _ rfl rfl _ ch712573a8_0)
  have h2 := forall_lt_succ h1 (chunk 1 _ _ rfl rfl _ ch712573a8_1)
  have h3 := forall_lt_succ h2 (chunk 2 _ _ rfl rfl _ ch712573a8_2)
  have h4 := forall_lt_succ h3 (chunk 3 _ _ rfl rfl _ ch712573a8_3)
  have h5 := forall_lt_succ h4 (chunk 4 _ _ rfl rfl _ ch712573a8_4)
  have h6 := forall_lt_succ h5 (chunk 5 _ _ rfl rfl _ ch712573a8_5)
  have h7 := forall_lt_succ h6 (chunk 6 _ _ rfl rfl _ ch712573a8_6)
  have h8 := forall_lt_succ h7 (chunk 7 _ _ rfl rfl _ ch712573a8_7)
  have h9 := forall_lt_succ h8 (chunk 8 _ _ rfl rfl _ ch712573a8_8)
  have h10 := forall_lt_succ h9 (chunk 9 _ _ rfl rfl _ ch712573a8_9)
  have h11 := forall_lt_succ h10 (chunk 10 _ _ rfl rfl _ ch712573a8_10)
  have h12 := forall_lt_succ h11 (chunk 11 _ _ rfl rfl _ ch712573a8_11)
  have h13 := forall_lt_succ h12 (chunk 12 _ _ rfl rfl _ ch712573a8_12)
  have h14 := forall_lt_succ h13 (chunk 13 _ _ rfl rfl _ ch712573a8_13)
  have h15 := forall_lt_succ h14 (chunk 14 _ _ rfl rfl _ ch712573a8_14)
  exact forall_lt_succ h15 (chunk 15 _ _ rfl rfl _ ch712573a8_15)

private theorem allF : ∀ i < 960, F8 i := fun i hi =>
  allG (i / 60) (by omega) i (by omega) (by omega)

theorem a8_closed (u : Root 5) (hu : u.val < 8) (n : ℕ) (hn : A8 n) :
    A8 (Chk.imgN (tabsK 5 D.T5) (nroots 5) u.val n) := by
  obtain ⟨i, hi, rfl⟩ := hn
  obtain ⟨idx, hidx, he⟩ := (allF i hi).2 u hu
  exact ⟨idx, hidx, he⟩

theorem a8_flag (n : ℕ) (hn : A8 n) : InsideFlag 5 (ofMask 5 n) := by
  obtain ⟨i, hi, rfl⟩ := hn
  exact Or.inr ⟨rfl, (allF i hi).1⟩

private theorem Q5 (c : ℕ) (x : KRep) (h : repK D.T5 D.hx5 8 false c x = true) : InsT 5 c ∨ A8 c :=
  Or.inl (repK_sound tabsOK_D5 (fun h => absurd h Bool.false_ne_true) h)

private theorem r12 : InsT 5 (ln128 D5.R 12) ∨ A8 (ln128 D5.R 12) :=
  Or.inr ⟨0, by decide, (Nat.eq_of_beq_eq_true ch712573a8r).symm⟩

private theorem all5 : ∀ x < 14, InsT 5 (ln128 D5.R x) ∨ A8 (ln128 D5.R x) := by
  have h1 := forall_lt_succ (P := fun x => InsT 5 (ln128 D5.R x) ∨ A8 (ln128 D5.R x))
    (forall_lt_zero _) (Q5 _ _ ch712573w_0)
  have h2 := forall_lt_succ h1 (Q5 _ _ ch712573w_1)
  have h3 := forall_lt_succ h2 (Q5 _ _ ch712573w_2)
  have h4 := forall_lt_succ h3 (Q5 _ _ ch712573w_3)
  have h5 := forall_lt_succ h4 (Q5 _ _ ch712573w_4)
  have h6 := forall_lt_succ h5 (Q5 _ _ ch712573w_5)
  have h7 := forall_lt_succ h6 (Q5 _ _ ch712573w_6)
  have h8 := forall_lt_succ h7 (Q5 _ _ ch712573w_7)
  have h9 := forall_lt_succ h8 (Q5 _ _ ch712573w_8)
  have h10 := forall_lt_succ h9 (Q5 _ _ ch712573w_9)
  have h11 := forall_lt_succ h10 (Q5 _ _ ch712573w_10)
  have h12 := forall_lt_succ h11 (Q5 _ _ ch712573w_11)
  have h13 := forall_lt_succ h12 r12
  exact forall_lt_succ h13 (Q5 _ _ ch712573w_13)

theorem repT5 (x : Fin 14) : (Nonempty (SatWitness 5 (ofMask 5 (R5 x))) ∨ (((5 : Fin 6).val = 2 ∨ (5 : Fin 6).val = 3) ∧
    (ofMask 5 (R5 x) = Finset.univ ∨
      ∃ k, ofMask 5 (R5 x) = Finset.univ.filter fun i => pairing 5 k i = 0 ∧ pairing 5 i k = 0))) ∨
    A8 (R5 x) :=
  all5 x.val x.isLt

end CFSG.ExcInsK

end

end
