module

public import Certificates.Data.Kernel.OpsLayMcert

public section

namespace CFSG.KC.OpsLayK

open CFSG.KC.LQT CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native

@[expose] noncomputable def runF (c : Lay) (prog : List Op) (R : List Nat) : List Nat :=
  prog.foldl (fun R o => R.set (Op.tgt o) (stepV c R o)) R

theorem runF_append (c : Lay) (p q : List Op) (R : List Nat) :
    runF c (p ++ q) R = runF c q (runF c p R) := by
  unfold runF
  rw [List.foldl_append]

theorem runF_length (c : Lay) : ∀ (prog : List Op) (R : List Nat),
    (runF c prog R).length = R.length
  | [], _ => rfl
  | o :: prog, R => by
    change (runF c prog (R.set (Op.tgt o) (stepV c R o))).length = R.length
    rw [runF_length c prog, List.length_set]

theorem getR_set_eq (c : Lay) {R : List Nat} {t : Nat} (ht : t < R.length) (x : Nat) :
    getR c (R.set t x) t = x := by
  simp [getR, List.getD_eq_getElem?_getD, ht]

theorem getR_set_neW (c : Lay) (R : List Nat) {t i : Nat} (h : t ≠ i) (x : Nat) :
    getR c (R.set t x) i = getR c R i := by
  simp only [getR, List.getD_eq_getElem?_getD, List.getElem?_set_ne h]

theorem getR_append (c : Lay) {R : List Nat} (T : List Nat) {i : Nat} (hi : i < R.length) :
    getR c (R ++ T) i = getR c R i := by
  simp only [getR, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem stepV_append (c : Lay) {n : Nat} {R : List Nat} (T : List Nat) (hR : R.length = n) :
    ∀ o : Op, o.lt n = true → stepV c (R ++ T) o = stepV c R o
  | .mul i j k, h => by
    simp only [Op.lt, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [stepV, getR_append c T (hR ▸ h.1.1), getR_append c T (hR ▸ h.1.2)]
  | .pow e i k, h => by
    simp only [Op.lt, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [stepV, getR_append c T (hR ▸ h.1)]

theorem tgt_lt {n : Nat} : ∀ o : Op, o.lt n = true → Op.tgt o < n
  | .mul i j k, h => by
    simp only [Op.lt, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.2
  | .pow e i k, h => by
    simp only [Op.lt, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.2

theorem runF_append_regs (c : Lay) {n : Nat} (T : List Nat) : ∀ (prog : List Op),
    prog.all (Op.lt n) = true → ∀ R : List Nat, R.length = n →
      runF c prog (R ++ T) = runF c prog R ++ T
  | [], _, _, _ => rfl
  | o :: prog, h, R, hR => by
    rw [List.all_cons, Bool.and_eq_true] at h
    change runF c prog ((R ++ T).set (Op.tgt o) (stepV c (R ++ T) o)) =
      runF c prog (R.set (Op.tgt o) (stepV c R o)) ++ T
    rw [stepV_append c T hR o h.1, List.set_append_left _ _ (by rw [hR]; exact tgt_lt o h.1)]
    exact runF_append_regs c T prog h.2 _ (by rw [List.length_set, hR])

theorem evalWL_congrW (c : Lay) {R R' : List Nat} : ∀ w : Word,
    (∀ x ∈ w, getR c R x.1 = getR c R' x.1) → evalWL c R w = evalWL c R' w
  | [], _ => rfl
  | (r, e) :: w, h => by
    rw [evalWL, evalWL, h (r, e) List.mem_cons_self,
      evalWL_congrW c w fun x hx => h x (List.mem_cons_of_mem _ hx)]

@[expose] def pReg (r e : Nat) : Nat := cond (Nat.beq e 1) r (2 * r + e + 6)

@[expose] def powOps : List (Nat × Nat) → List Op
  | [] => []
  | (r, e) :: L => Op.pow e r (pReg r e) :: powOps L

@[expose] def slpW : List Op :=
  [.mul 32 8 33, .mul 29 33 34, .mul 32 9 35, .mul 34 35 36, .mul 36 34 37, .mul 31 8 38,
    .mul 38 37 39, .mul 11 30 40, .mul 32 10 41, .mul 39 39 42, .mul 40 9 43, .mul 10 35 44,
    .mul 44 10 45, .mul 45 41 46, .mul 33 37 47, .mul 47 42 48, .mul 43 46 49, .mul 49 35 50,
    .mul 50 40 51, .mul 51 48 52, .mul 52 42 53, .mul 53 41 54, .mul 54 39 55, .mul 30 9 56,
    .mul 55 56 57, .mul 38 36 58, .mul 58 36 59, .mul 54 59 60, .mul 60 43 61, .mul 38 30 62,
    .mul 62 8 63, .mul 43 61 27, .mul 27 57 27, .mul 27 55 27, .mul 27 30 27, .mul 27 48 27,
    .mul 27 41 27, .mul 27 39 27, .mul 27 63 27, .mul 27 9 27, .mul 27 8 27, .mul 27 56 27,
    .mul 9 43 28, .mul 28 57 28, .mul 28 57 28, .mul 28 57 28, .mul 28 61 28, .mul 28 55 28,
    .mul 28 59 28, .mul 28 46 28, .mul 28 63 28, .mul 28 56 28, .mul 28 8 28, .mul 28 31 28]

theorem getR_runF_pow (c : Lay) (R : List Nat) {e i t : Nat} (ht : t < R.length) :
    getR c (runF c [.pow e i t] R) t = powK c (getR c R i) e :=
  getR_set_eq c ht _

theorem getR_runF_ne (c : Lay) (R : List Nat) (o : Op) {i : Nat} (h : Op.tgt o ≠ i) :
    getR c (runF c [o] R) i = getR c R i :=
  getR_set_neW c R h _

theorem factL_congrW (c : Lay) {R R' : List Nat} (h : ∀ i, getR c R i = getR c R' i) (n : Nat) :
    ∀ f : MFact, factL c R n f = factL c R' n f
  | .ord r e => by simp only [factL, h]
  | .conj k u w => by
    simp only [factL, h, evalWL_congrW c u fun x _ => h x.1, evalWL_congrW c w fun x _ => h x.1]
  | .ne u w t => by
    simp only [factL, evalWL_congrW c u fun x _ => h x.1, evalWL_congrW c w fun x _ => h x.1]
  | .eq u w => by
    simp only [factL, evalWL_congrW c u fun x _ => h x.1, evalWL_congrW c w fun x _ => h x.1]

theorem factL_eq_of (c : Lay) {R : List Nat} {n X : Nat} {u w : Word}
    (hX : evalWL c R w = X) (h : (wordOK n u && wordOK n w && Nat.beq (evalWL c R u) X) = true) :
    factL c R n (.eq u w) = true := by
  rw [factL, hX]
  exact h

theorem getR_take (c : Lay) (R : List Nat) {n i : Nat} (hi : i < n) :
    getR c (R.take n) i = getR c R i := by
  simp only [getR, List.getD_eq_getElem?_getD, List.getElem?_take, hi, ite_true]

theorem getR_of_le (c : Lay) {R : List Nat} {i : Nat} (hi : R.length ≤ i) : getR c R i = c.ONE := by
  simp only [getR, List.getD_eq_getElem?_getD, List.getElem?_eq_none hi, Option.getD_none]

end CFSG.KC.OpsLayK

end
