module

public import Certificates.Data.Kernel.SmithEKI
public import Certificates.Data.Kernel.SmithEKC
public import CFSG.Certificates.Kernel.Common.SliceGlue

public section

namespace CFSG.SmithE.K

theorem drop_succ_tail {α : Type} (n : Nat) (l : List α) : l.drop (n + 1) = l.tail.drop n := by
  cases l <;> simp

@[expose] noncomputable def basOKp (T : List (List (List (List Nat)))) : List Nat → List (List Nat) → Bool :=
  fun P => List.rec (motive := fun _ => List (List Nat) → Bool) (fun _ => true)
    (fun p _ ih Bs => basRow T p (Bs.headD []) && ih Bs.tail) P

theorem basOK_eq (T : List (List (List (List Nat)))) : ∀ (P : List Nat) (Bs : List (List Nat)),
    basOK T P Bs = (basOKp T P Bs && (Bs.drop P.length).isEmpty)
  | [], Bs => by simp [basOK, basOKp]
  | p :: P, Bs => by
    show (basRow T p (Bs.headD []) && basOK T P Bs.tail) =
      ((basRow T p (Bs.headD []) && basOKp T P Bs.tail) && (Bs.drop (P.length + 1)).isEmpty)
    rw [basOK_eq T P Bs.tail, Bool.and_assoc, drop_succ_tail]

theorem basOKp_append (T : List (List (List (List Nat)))) : ∀ (A B : List Nat) (Bs : List (List Nat)),
    basOKp T (A ++ B) Bs = (basOKp T A Bs && basOKp T B (Bs.drop A.length))
  | [], B, Bs => by simp [basOKp]
  | p :: A, B, Bs => by
    show (basRow T p (Bs.headD []) && basOKp T (A ++ B) Bs.tail) =
      ((basRow T p (Bs.headD []) && basOKp T A Bs.tail) && basOKp T B (Bs.drop (A.length + 1)))
    rw [basOKp_append T A B Bs.tail, Bool.and_assoc, drop_succ_tail]

theorem basOK_of_slices (T : List (List (List (List Nat)))) (b m : Nat) (P : List Nat) (Bs : List (List Nat))
    (hP : P.length = m * b)
    (h : ∀ j < m, basOKp T (CFSG.KC.SliceGlue.slice P (j * b) b) (Bs.drop (j * b)) = true)
    (he : (Bs.drop P.length).isEmpty = true) : basOK T P Bs = true := by
  have key : ∀ j, j ≤ m → basOKp T (P.take (j * b)) Bs = true := by
    intro j
    induction j with
    | zero => intro _; simp [basOKp]
    | succ j ih =>
      intro hj
      have hle : j * b ≤ P.length := by rw [hP]; exact Nat.mul_le_mul_right b (by omega)
      rw [Nat.succ_mul, List.take_add, basOKp_append, ih (by omega), Bool.true_and,
        List.length_take, Nat.min_eq_left hle]
      exact h j (by omega)
  have := key m (Nat.le_refl m)
  rw [List.take_of_length_le (by rw [hP]; exact Nat.le_refl _)] at this
  rw [basOK_eq, this, he]; rfl

theorem rowsC_append (ONE REP ID Bpk : Nat) (Qs : List Nat) (R : Nat → Nat) :
    ∀ (A B : List (List Nat)) (Pr : List Nat) (j : Nat),
      rowsC ONE REP ID Bpk Qs R (A ++ B) Pr j =
        (rowsC ONE REP ID Bpk Qs R A Pr j && rowsC ONE REP ID Bpk Qs R B (Pr.drop A.length) (j + A.length))
  | [], B, Pr, j => by simp [rowsC]
  | a :: A, B, Pr, j => by
    show (rowC ONE REP ID Bpk Qs a (Pr.headD 0) (R j) && rowsC ONE REP ID Bpk Qs R (A ++ B) Pr.tail (j + 1)) =
      ((rowC ONE REP ID Bpk Qs a (Pr.headD 0) (R j) && rowsC ONE REP ID Bpk Qs R A Pr.tail (j + 1)) &&
        rowsC ONE REP ID Bpk Qs R B (Pr.drop (A.length + 1)) (j + (A.length + 1)))
    rw [rowsC_append ONE REP ID Bpk Qs R A B Pr.tail (j + 1), Bool.and_assoc, drop_succ_tail,
      Nat.add_assoc, Nat.add_comm 1 A.length]

theorem rowsC_of_slices (ONE REP ID Bpk : Nat) (Qs : List Nat) (R : Nat → Nat) (b m : Nat)
    (C : List (List Nat)) (Pr : List Nat) (hC : C.length = m * b)
    (h : ∀ j < m, rowsC ONE REP ID Bpk Qs R (CFSG.KC.SliceGlue.slice C (j * b) b) (Pr.drop (j * b)) (0 + j * b) = true) :
    rowsC ONE REP ID Bpk Qs R C Pr 0 = true := by
  have key : ∀ j, j ≤ m → rowsC ONE REP ID Bpk Qs R (C.take (j * b)) Pr 0 = true := by
    intro j
    induction j with
    | zero => intro _; simp [rowsC]
    | succ j ih =>
      intro hj
      have hle : j * b ≤ C.length := by rw [hC]; exact Nat.mul_le_mul_right b (by omega)
      rw [Nat.succ_mul, List.take_add, rowsC_append, ih (by omega), Bool.true_and,
        List.length_take, Nat.min_eq_left hle]
      exact h j (by omega)
  have := key m (Nat.le_refl m)
  rwa [List.take_of_length_le (by rw [hC]; exact Nat.le_refl _)] at this

@[expose] noncomputable def rectI (W1 : Nat) (R S Pc Mc : List Nat) : Bool :=
  List.rec (motive := fun _ => List Nat → Bool) (fun _ => true)
    (fun p _ ih S => rowI W1 p (S.headD 0) Pc Mc && ih S.tail) R S

theorem rowI_append (W1 p m : Nat) : ∀ (A B MA MB : List Nat), MA.length = A.length →
    rowI W1 p m (A ++ B) (MA ++ MB) = (rowI W1 p m A MA && rowI W1 p m B MB)
  | [], B, [], MB, _ => by simp [rowI]
  | [], _, _ :: _, _, h => by simp at h
  | _ :: _, _, [], _, h => by simp at h
  | q :: A, B, x :: MA, MB, h => by
    show (pairI W1 p m q x && rowI W1 p m (A ++ B) (MA ++ MB)) =
      ((pairI W1 p m q x && rowI W1 p m A MA) && rowI W1 p m B MB)
    rw [rowI_append W1 p m A B MA MB (by simpa using h), Bool.and_assoc]

theorem rowsI_split (W1 : Nat) : ∀ (R S T MT U MU : List Nat), R.length ≤ T.length + 1 →
    MT.length = T.length →
    rowsI W1 R S (T ++ U) (MT ++ MU) = (rowsI W1 R S T MT && rectI W1 R S U MU)
  | [], _, _, _, _, _, _, _ => rfl
  | p :: R, S, [], MT, U, MU, hR, hM => by
    have hR0 : R = [] := List.eq_nil_of_length_eq_zero (by
      simp only [List.length_cons, List.length_nil] at hR; omega)
    have hM0 : MT = [] := List.eq_nil_of_length_eq_zero (by simpa using hM)
    subst hR0; subst hM0
    show (rowI W1 p (S.headD 0) U MU && true) =
      ((rowI W1 p (S.headD 0) [] [] && true) && (rowI W1 p (S.headD 0) U MU && true))
    simp [rowI]
  | p :: R, S, t :: T, [], U, MU, _, hM => by simp at hM
  | p :: R, S, t :: T, x :: MT, U, MU, hR, hM => by
    show (rowI W1 p (S.headD 0) ((t :: T) ++ U) ((x :: MT) ++ MU) &&
        rowsI W1 R S.tail (T ++ U) (MT ++ MU)) =
      ((rowI W1 p (S.headD 0) (t :: T) (x :: MT) && rowsI W1 R S.tail T MT) &&
        (rowI W1 p (S.headD 0) U MU && rectI W1 R S.tail U MU))
    rw [rowI_append W1 p _ (t :: T) U (x :: MT) MU hM,
      rowsI_split W1 R S.tail T MT U MU (by simp at hR; omega) (by simpa using hM)]
    cases rowI W1 p (S.headD 0) (t :: T) (x :: MT) <;> cases rowI W1 p (S.headD 0) U MU <;>
      cases rowsI W1 R S.tail T MT <;> cases rectI W1 R S.tail U MU <;> rfl

theorem rectI_append (W1 : Nat) (A B MA MB : List Nat) (h : MA.length = A.length) :
    ∀ (R S : List Nat), rectI W1 R S (A ++ B) (MA ++ MB) = (rectI W1 R S A MA && rectI W1 R S B MB)
  | [], _ => rfl
  | p :: R, S => by
    show (rowI W1 p (S.headD 0) (A ++ B) (MA ++ MB) && rectI W1 R S.tail (A ++ B) (MA ++ MB)) =
      ((rowI W1 p (S.headD 0) A MA && rectI W1 R S.tail A MA) &&
        (rowI W1 p (S.headD 0) B MB && rectI W1 R S.tail B MB))
    rw [rowI_append W1 p _ A B MA MB h, rectI_append W1 A B MA MB h R S.tail]
    cases rowI W1 p (S.headD 0) A MA <;> cases rowI W1 p (S.headD 0) B MB <;>
      cases rectI W1 R S.tail A MA <;> cases rectI W1 R S.tail B MB <;> rfl

theorem rectI_nil (W1 : Nat) : ∀ (R S : List Nat), rectI W1 R S [] [] = true
  | [], _ => rfl
  | p :: R, S => by
    show (rowI W1 p (S.headD 0) [] [] && rectI W1 R S.tail [] []) = true
    rw [rectI_nil W1 R S.tail]
    rfl

theorem rectI_of_slices (W1 : Nat) (R S U MU : List Nat) (b K : Nat) (hU : U.length ≤ K * b)
    (hM : MU.length = U.length)
    (h : ∀ k < K, rectI W1 R S (CFSG.KC.SliceGlue.slice U (k * b) b) (CFSG.KC.SliceGlue.slice MU (k * b) b) = true) :
    rectI W1 R S U MU = true := by
  have key : ∀ k, k ≤ K → rectI W1 R S (U.take (k * b)) (MU.take (k * b)) = true := by
    intro k
    induction k with
    | zero => intro _; simp only [Nat.zero_mul, List.take_zero]; exact rectI_nil W1 R S
    | succ k ih =>
      intro hk
      rw [Nat.succ_mul, List.take_add, List.take_add, rectI_append W1 _ _ _ _ (by simp [hM]),
        ih (by omega), Bool.true_and]
      exact h k (by omega)
  have := key K (Nat.le_refl K)
  rwa [List.take_of_length_le hU, List.take_of_length_le (by rw [hM]; exact hU)] at this

theorem drop_split {α : Type} (L : List α) (a n : Nat) (hn : 1 ≤ n) :
    L.drop (a + 1) = CFSG.KC.SliceGlue.slice L (a + 1) (n - 1) ++ L.drop (a + n) := by
  have e : a + n = a + 1 + (n - 1) := by omega
  rw [e, ← List.drop_drop (i := n - 1) (j := a + 1) (l := L)]
  exact (List.take_append_drop (n - 1) (L.drop (a + 1))).symm

theorem chunkI_of_parts (W1 : Nat) (P Ms : List Nat) (a n : Nat) (hn : 1 ≤ n)
    (hM : Ms.length = P.length)
    (ht : rowsI W1 (CFSG.KC.SliceGlue.slice P a n) (CFSG.KC.SliceGlue.slice Ms a n) (CFSG.KC.SliceGlue.slice P (a + 1) (n - 1)) (CFSG.KC.SliceGlue.slice Ms (a + 1) (n - 1)) =
      true)
    (hr : rectI W1 (CFSG.KC.SliceGlue.slice P a n) (CFSG.KC.SliceGlue.slice Ms a n) (P.drop (a + n)) (Ms.drop (a + n)) = true) :
    chunkI W1 P Ms a n = true := by
  unfold chunkI
  rw [drop_split P a n hn, drop_split Ms a n hn, rowsI_split]
  · exact (Bool.and_eq_true _ _).mpr ⟨ht, hr⟩
  · simp only [CFSG.KC.SliceGlue.slice, List.length_take, List.length_drop]; omega
  · simp only [CFSG.KC.SliceGlue.slice, List.length_take, List.length_drop, hM]

end CFSG.SmithE.K

end
