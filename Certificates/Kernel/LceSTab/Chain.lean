module

public import Certificates.Data.Kernel.LceSSeg
public import Certificates.Kernel.LceSTab.Assemble
public import Certificates.Kernel.HeRu.Assemble

public section

namespace CFSG.KC.LceSeg

open CFSG.KC

theorem strictL_eq (y : Nat) (k : Nat → List Nat) : strictL y k = k y := by
  cases y <;> rfl

theorem seg_zero (f : Nat → Nat) (k : Nat) : seg f 0 k = [] := rfl

theorem seg_succ (f : Nat → Nat) (n k : Nat) : seg f (n + 1) k = f k :: seg f n (k + 1) := by
  change f k :: strictL (Nat.succ k) (seg f n) = _
  rw [strictL_eq]

theorem seg_add (f : Nat → Nat) (a b : Nat) :
    ∀ k, seg f (a + b) k = List.append (seg f a k) (seg f b (k + a)) := by
  induction a with
  | zero => intro k; simp [seg_zero]
  | succ a ih =>
    intro k
    rw [Nat.add_right_comm, seg_succ, seg_succ, ih (k + 1)]
    simp [Nat.add_assoc, Nat.add_comm 1 a]

theorem forall_of_rows {P : Nat → Prop} (B r : Nat) (h : ∀ k < r, ∀ t < B, P (B * k + t)) :
    ∀ i < B * r, P i := by
  intro i hi
  have hB : 0 < B := Nat.pos_of_ne_zero (by rintro rfl; rw [Nat.zero_mul] at hi; omega)
  have hk : i / B < r := (Nat.div_lt_iff_lt_mul hB).2 (by rw [Nat.mul_comm]; exact hi)
  have := h (i / B) hk (i % B) (Nat.mod_lt _ hB)
  rwa [Nat.div_add_mod] at this

theorem forall_append {P : Nat → Prop} (a n : Nat) (h1 : ∀ i < a, P i)
    (h2 : ∀ t < n, P (a + t)) : ∀ i < a + n, P i := by
  intro i hi
  by_cases h : i < a
  · exact h1 i h
  · have := h2 (i - a) (by omega)
    rwa [Nat.add_sub_cancel' (by omega)] at this

theorem andB_eq_true {a b : Bool} (h : andB a b = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all [andB]

theorem slOK_chain (F : List Nat → Nat → Nat) (hF0 : ∀ x, F [] x = x)
    (hF : ∀ (l1 l2 : List Nat) (x : Nat), F (List.append l1 l2) x = F l2 (F l1 x))
    (f lo acc : Nat → Nat) :
    ∀ n, (∀ i < n, slOK F f lo acc i = true) →
      lo 0 ≤ lo n ∧ F (seg f (lo n - lo 0) (lo 0)) (acc 0) = acc n := by
  intro n
  induction n with
  | zero => intro _; exact ⟨Nat.le_refl _, by rw [Nat.sub_self, seg_zero, hF0]⟩
  | succ n ih =>
    intro h
    obtain ⟨h0, h1⟩ := ih (fun i hi => h i (Nat.lt_succ_of_lt hi))
    obtain ⟨hle, hrun⟩ := andB_eq_true (h n (Nat.lt_succ_self n))
    have hle : lo n ≤ lo (n + 1) := Nat.le_of_ble_eq_true hle
    have hrun : F (seg f (lo (n + 1) - lo n) (lo n)) (acc n) = acc (n + 1) :=
      Nat.eq_of_beq_eq_true hrun
    refine ⟨Nat.le_trans h0 hle, ?_⟩
    have e : lo (n + 1) - lo 0 = (lo n - lo 0) + (lo (n + 1) - lo n) := by omega
    have e2 : lo 0 + (lo n - lo 0) = lo n := by omega
    rw [e, seg_add, hF, h1, e2, hrun]

theorem slOK_chain_beq (F : List Nat → Nat → Nat) (hF0 : ∀ x, F [] x = x)
    (hF : ∀ (l1 l2 : List Nat) (x : Nat), F (List.append l1 l2) x = F l2 (F l1 x))
    (f lo acc : Nat → Nat) (n : Nat) (h : ∀ i < n, slOK F f lo acc i = true) :
    Nat.beq (F (seg f (Nat.sub (lo n) (lo 0)) (lo 0)) (acc 0)) (acc n) = true :=
  by
  rw [Nat.beq_eq]
  exact (slOK_chain F hF0 hF f lo acc n h).2

theorem facts_chain (blk WT : Nat → Nat) (INV nC L : Nat) (f lo acc : Nat → Nat) (n : Nat)
    (h : ∀ i < n, slOK (LceS.runFacts blk WT INV nC L) f lo acc i = true) :
    Nat.beq (LceS.runFacts blk WT INV nC L (seg f (Nat.sub (lo n) (lo 0)) (lo 0)) (acc 0)) (acc n) =
      true :=
  slOK_chain_beq _ (fun _ => rfl) (CFSG.Certificates.LCE.runFacts_append blk WT INV nC L) f lo acc n h

theorem cover_chain (blk LVs : Nat → Nat) (nf L : Nat) (f lo acc : Nat → Nat) (n : Nat)
    (h : ∀ i < n, slOK (LceS.runCover blk LVs nf L) f lo acc i = true) :
    Nat.beq (LceS.runCover blk LVs nf L (seg f (Nat.sub (lo n) (lo 0)) (lo 0)) (acc 0)) (acc n) =
      true :=
  slOK_chain_beq _ (fun _ => rfl) (CFSG.Certificates.LCE.runCover_append blk LVs nf L) f lo acc n h

theorem labF_chain (WT LB : Nat → Nat) (Hs : Nat) (f lo acc : Nat → Nat) (n : Nat)
    (h : ∀ i < n, slOK (LabF.runLab WT LB Hs) f lo acc i = true) :
    Nat.beq (LabF.runLab WT LB Hs (seg f (Nat.sub (lo n) (lo 0)) (lo 0)) (acc 0)) (acc n) = true :=
  slOK_chain_beq _ (fun _ => rfl) (CFSG.Certificates.LS.labF_append WT LB Hs) f lo acc n h

end CFSG.KC.LceSeg

end
