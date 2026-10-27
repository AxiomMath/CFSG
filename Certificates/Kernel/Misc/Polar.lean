
module

public import Certificates.Kernel.Misc.PolarMath
public import Certificates.Kernel.Misc.T46
public import Certificates.Data.Kernel.Misc.Polar
import all Certificates.Data.CFSGNative.F4.Basic
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.EachUnfold
import CFSG.Certificates.Kernel.Common.ForallChunks
import Mathlib.Tactic.IntervalCases
public import CFSG.Fischer.HermitianEquiv
public import CFSG.Fischer.PolarCertBase

public section

set_option maxRecDepth 200000

namespace CFSG.KD.Misc.Polar

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc CFSG.KC.Misc.O73 CFSG.KC.Misc.T46 CFSG.KC.Misc.Polar
  CFSG.KD.Misc.T46 CFSG.Fischer CFSG.Fischer.Native CFSG.F4.Native CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native

attribute [local irreducible] CFSG.F4.Native.uPts ptIdx uVec tvTabs

theorem nontrivC : nontrivK UP = true := by quickRfl
@[expose] noncomputable def sepF (k : Nat) : Bool := sepK UP (33 * k) 33

#kc_each_unfold sepF 0 21 as CFSG.KD.Misc.Polar.sep

theorem andB_true {a b : Bool} : andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> simp [andB]

theorem orB_true {a b : Bool} : orB a b = true ↔ a = true ∨ b = true := by
  cases a <;> simp [orB]

theorem notB_true {a : Bool} : notB a = true ↔ a = false := by
  cases a <;> simp [notB]

theorem impB_true {a b : Bool} : impB a b = true ↔ (a = true → b = true) := by
  cases a <;> simp [impB]

theorem letB_eq (y : Nat) (k : Nat → Bool) : letB y k = k y := by
  cases y <;> rfl

theorem allN_true {m : Nat} {f : Nat → Bool} (h : allN m f = true) : ∀ i < m, f i = true := by
  induction m with
  | zero => intro i hi; omega
  | succ m ih =>
    have h' : andB (f m) (allN m f) = true := h
    rw [andB_true] at h'
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact ih h'.2 i hi
    · exact h'.1

theorem anyN_true {m : Nat} {f : Nat → Bool} (h : anyN m f = true) : ∃ i < m, f i = true := by
  induction m with
  | zero => exact absurd h (by simp [anyN])
  | succ m ih =>
    have h' : orB (f m) (anyN m f) = true := h
    rw [orB_true] at h'
    rcases h' with h' | h'
    · exact ⟨m, Nat.lt_succ_self m, h'⟩
    · obtain ⟨i, hi, hf⟩ := ih h'
      exact ⟨i, Nat.lt_succ_of_lt hi, hf⟩

theorem nthN_eq (l : List Nat) (i : Nat) : wordM7.nthN l i = l.getD i 0 := by
  induction l generalizing i with
  | nil => rfl
  | cons x t ih =>
    cases i with
    | zero => rfl
    | succ n =>
      change wordM7.nthN t n = _
      rw [ih]
      simp

theorem at_UP {i : Nat} (hi : i < 693) : at' 12 UP i = uPts[i]! := by
  have h := pts
  simp only [ptsK, andB_true] at h
  have := Nat.eq_of_beq_eq_true (allN_true h.2.2.1 i hi)
  rw [nthN_eq] at this
  rw [this, CFSG.KD.Misc.Unitary.hU, CFSG.KD.Misc.Unitary.getE]

theorem hermR_eq (c d : Nat) : hermR c d = hermC c d := rfl

theorem hermR_UP (x p : Fin 693) :
    hermR (at' 12 UP x) (at' 12 UP p) = 0 ↔ hermStd (uVec x) (uVec p) = 0 := by
  rw [at_UP x.2, at_UP p.2, hermR_eq, ← codeOf_uVec ptsFacts x.2, ← codeOf_uVec ptsFacts p.2,
    hermC_codeOf, code_eq_zero_iff]

theorem nontriv_pts (p : Fin 693) : ∃ x : Fin 693, hermStd (uVec x) (uVec p) ≠ 0 := by
  have h := allN_true nontrivC p p.2
  rw [letB_eq] at h
  obtain ⟨x, hx, hf⟩ := anyN_true h
  rw [notB_true] at hf
  exact ⟨⟨x, hx⟩, fun h0 => Nat.ne_of_beq_eq_false hf ((hermR_UP ⟨x, hx⟩ p).2 h0)⟩

#kc_forall_chunks sepAllK (fun k => sepK UP (33 * k) 33 = true) 21 CFSG.KD.Misc.Polar.sep 1

theorem sepAll : ∀ k < 21, sepK UP (33 * k) 33 = true := sepAllK

theorem sep_pts (p q : Fin 693) (hpq : p < q) : ∃ x : Fin 693,
    (hermStd (uVec x) (uVec p) = 0 ∧ hermStd (uVec x) (uVec q) ≠ 0) ∨
    (hermStd (uVec x) (uVec q) = 0 ∧ hermStd (uVec x) (uVec p) ≠ 0) := by
  have h := allN_true (sepAll (p.val / 33) (by omega)) (p.val % 33) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (33 * (p.val / 33)) (p.val % 33) = p.val := Nat.div_add_mod _ _
  rw [letB_eq, e, impB_true] at h
  have h := h (by simp [p.2])
  rw [letB_eq] at h
  have h := allN_true h q q.2
  rw [impB_true] at h
  have h := h (by simpa using hpq)
  rw [letB_eq] at h
  obtain ⟨x, hx, hf⟩ := anyN_true h
  simp only [letB_eq, orB_true, andB_true, notB_true] at hf
  have ep := hermR_UP ⟨x, hx⟩ p
  have eq := hermR_UP ⟨x, hx⟩ q
  refine ⟨⟨x, hx⟩, ?_⟩
  rcases hf with hf | hf
  · exact Or.inl ⟨ep.1 (Nat.eq_of_beq_eq_true hf.1),
      fun h0 => Nat.ne_of_beq_eq_false hf.2 (eq.2 h0)⟩
  · exact Or.inr ⟨eq.1 (Nat.eq_of_beq_eq_true hf.1),
      fun h0 => Nat.ne_of_beq_eq_false hf.2 (ep.2 h0)⟩

theorem tvP_ne_one' (p : Fin 693) : tvP p ≠ 1 := by
  intro h1
  obtain ⟨x, hx⟩ := nontriv_pts p
  exact hx ((tvP_fix p x).1 (by rw [h1]; rfl))

theorem herm_iff (p q : Fin 693) :
    (hermC uPts[p.val]! uPts[q.val]! == 0) = true ↔ hermStd (uVec p) (uVec q) = 0 := by
  rw [beq_iff_eq, ← codeOf_uVec ptsFacts p.2, ← codeOf_uVec ptsFacts q.2, hermC_codeOf,
    code_eq_zero_iff]

theorem tab_eq_iff {P Q : Table} {g h : Equiv.Perm (Fin 693)} (hP : P.size = 693)
    (hQ : Q.size = 693) (hg : Rep 693 P g) (hh : Rep 693 Q h) : P = Q ↔ g = h :=
  ⟨fun e => perm_eq_of_rep hg (e ▸ hh), fun e => rep_unique_table hP hQ hg (e ▸ hh)⟩

theorem polar_true : polarCertificate () = true := by
  unfold polarCertificate
  simp only [Bool.and_eq_true, beq_iff_eq]
  have hsize : tvTabs.size = 693 := by unfold tvTabs; simp
  refine ⟨⟨⟨⟨hsize, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · unfold commPerpOK
    rw [allIn_eq_true]
    intro p _ hp
    rw [allIn_eq_true]
    intro q _ hq
    rw [Bool.beq_eq_decide_eq, decide_eq_true_eq, Bool.eq_iff_iff, beq_iff_eq,
      herm_iff ⟨p, hp⟩ ⟨q, hq⟩, tab_eq_iff (compT_size _ _) (compT_size _ _)
        ((rep_tvP ⟨p, hp⟩).compT (rep_tvP ⟨q, hq⟩)) ((rep_tvP ⟨q, hq⟩).compT (rep_tvP ⟨p, hp⟩))]
    exact tvP_comm_iff sep_pts _ _
  · unfold tvInjOK
    rw [allIn_eq_true]
    intro p _ hp
    rw [allIn_eq_true]
    intro q _ hq
    simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq]
    by_cases hpq : p = q
    · exact Or.inl hpq
    · refine Or.inr fun e => hpq ?_
      have := (tab_eq_iff (tvTabs_size ⟨p, hp⟩) (tvTabs_size ⟨q, hq⟩) (rep_tvP ⟨p, hp⟩)
        (rep_tvP ⟨q, hq⟩)).1 e
      exact congrArg Fin.val (tvP_inj sep_pts this)
  · unfold tvNontrivOK
    rw [allIn_eq_true]
    intro p _ hp
    simp only [bne_iff_ne, ne_eq]
    intro e
    exact tvP_ne_one' ⟨p, hp⟩ ((tab_eq_iff (tvTabs_size ⟨p, hp⟩) (by unfold idT; simp)
      (rep_tvP ⟨p, hp⟩) (Rep.idT (by norm_num))).1 e)
  · unfold tvConjOK
    rw [allIn_eq_true]
    intro p _ hp
    rw [allIn_eq_true]
    intro q _ hq
    rw [beq_iff_eq]
    have hq' : ap tvTabs[p]! q = (tvP ⟨p, hp⟩ ⟨q, hq⟩).val := by
      rw [rep_tvP ⟨p, hp⟩ q hq, idx_of_lt _ hq]
      rfl
    rw [hq']
    refine (tab_eq_iff (compT_size _ _) (tvTabs_size _)
      (((rep_tvP ⟨p, hp⟩).compT (rep_tvP ⟨q, hq⟩)).compT (rep_tvP ⟨p, hp⟩))
      (rep_tvP (tvP ⟨p, hp⟩ ⟨q, hq⟩))).2 (tvP_conj' _ _)

end CFSG.KD.Misc.Polar

end
