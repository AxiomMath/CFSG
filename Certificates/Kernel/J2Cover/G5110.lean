module

public import Certificates.Kernel.J2Cover.U5110
public import Certificates.Kernel.J2Cover.M22Bind

public section

namespace CertificateChecks.KernelJ2Cover

open CFSG.KC.Enum CFSG.KS CFSG.GH74.KGroups.J2 CFSG.ComponentClassification.J2Cover.Models

theorem mulIdx_eq {a d : Nat} (ha : a < 128) (hd : d < 128) : mulIdx a d = mtK a d := by
  rw [← mt_pt]
  unfold mulTab
  rw [getElem!_ofFn' ha, getElem!_ofFn' hd]

theorem mulM_eq {p q : ℕ × ℕ} (hp : p.2 < 128) (hq : q.2 < 128) : mulM p q = mulU p q := by
  have hf : fRows[p.2]! = fRK p.2 := congrFun fR_eq p.2
  unfold mulM mulU bitAt
  rw [hf, mulIdx_eq hp hq]

theorem u_lt : ∀ p ∈ uList, p.1 < 2 ∧ p.2 < 128 := by
  intro p hp
  have h := List.all_eq_true.1 k5110_lt p hp
  simp only [Bool.and_eq_true, Nat.blt_eq] at h
  exact h

theorem u_mem {p : ℕ × ℕ} : uList.elem p = true ↔ p ∈ uList := by
  rw [List.elem_eq_mem, decide_eq_true_iff]

theorem u_mulM {p q : ℕ × ℕ} (hp : p ∈ uList) (hq : q ∈ uList) : mulM p q = mulU p q :=
  mulM_eq (u_lt p hp).2 (u_lt q hq).2

theorem memU_mem {x : ℕ × ℕ} (h : memU x = true) : x ∈ uList := by
  obtain ⟨y, hy, e⟩ := List.any_eq_true.1 h
  simp only [Bool.and_eq_true, Nat.beq_eq] at e
  have : y = x := Prod.ext e.1 e.2
  exact this ▸ hy

theorem bitU_mem {x : ℕ × ℕ} (h : bitU x = true) : x ∈ uList := by
  unfold bitU at h
  simp only [Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have hc : 128 * x.1 + x.2 < 256 := by omega
  have hm := allN_spec k5110_mask _ hc
  rw [h3, Bool.not_true, Bool.false_or] at hm
  have e : ((128 * x.1 + x.2) / 128, (128 * x.1 + x.2) % 128) = x := Prod.ext (by simp; omega)
    (by simp; omega)
  exact e ▸ memU_mem hm

theorem u_mul : ∀ p ∈ uList, ∀ q ∈ uList, mulM p q ∈ uList := by
  intro p hp q hq
  rw [u_mulM hp hq]
  exact bitU_mem (List.all_eq_true.1 (List.all_eq_true.1 k5110_mul p hp) q hq)

theorem u_nodup_aux : ∀ l : List (ℕ × ℕ), nodupU l = true → l.Nodup
  | [], _ => List.nodup_nil
  | x :: xs, h => by
    simp only [nodupU, Bool.and_eq_true, Bool.not_eq_true'] at h
    refine List.nodup_cons.2 ⟨fun hx => ?_, u_nodup_aux xs h.2⟩
    have : xs.elem x = true := by rw [List.elem_eq_mem, decide_eq_true_iff]; exact hx
    rw [this] at h
    exact Bool.noConfusion h.1

theorem u_one : ((0, 0) : ℕ × ℕ) ∈ uList := by
  rw [← u_mem]
  rfl

theorem n_mem : nElt ∈ uList := by
  rw [← u_mem]
  rfl

theorem facts5110 : (∀ p ∈ uList, p.1 < 2 ∧ p.2 < 128)
    ∧ (uList.Nodup)
    ∧ (uList.length = 64)
    ∧ (((0, 0) : ℕ × ℕ) ∈ uList)
    ∧ (∀ p ∈ uList, ∀ q ∈ uList, mulM p q ∈ uList)
    ∧ (∀ p ∈ uList, ∃ q ∈ uList, mulM p q = (0, 0))
    ∧ (nElt ∈ uList)
    ∧ (mulM nElt nElt = (0, 0))
    ∧ (nElt ≠ (0, 0))
    ∧ (∀ p ∈ uList, mulM nElt p = mulM p nElt)
    ∧ (∀ p ∈ uList, mulM p p = (0, 0) ∨ mulM p p = nElt)
    ∧ (∀ p ∈ uList, ∀ q ∈ uList,
    mulM p q = mulM (0, 0) (mulM q p) ∨ mulM p q = mulM nElt (mulM q p)) := by
  refine ⟨u_lt, u_nodup_aux _ k5110_nodup, rfl, u_one, u_mul, ?_, n_mem, ?_, by decide, ?_, ?_,
    ?_⟩
  · intro p hp
    obtain ⟨q, hq, e⟩ := List.any_eq_true.1 (List.all_eq_true.1 k5110_inv p hp)
    exact ⟨q, hq, by rw [u_mulM hp hq]; exact beq_iff_eq.1 e⟩
  · rw [u_mulM n_mem n_mem]
    exact beq_iff_eq.1 k5110_nsq
  · intro p hp
    rw [u_mulM n_mem hp, u_mulM hp n_mem]
    exact beq_iff_eq.1 (List.all_eq_true.1 k5110_central p hp)
  · intro p hp
    rw [u_mulM hp hp]
    have h := List.all_eq_true.1 k5110_sq p hp
    simpa only [Bool.or_eq_true, beq_iff_eq] using h
  · intro p hp q hq
    have hqp := u_mul q hq p hp
    rw [u_mulM hp hq, u_mulM hq hp, u_mulM u_one ((u_mulM hq hp) ▸ hqp),
      u_mulM n_mem ((u_mulM hq hp) ▸ hqp)]
    have h := List.all_eq_true.1 (List.all_eq_true.1 k5110_comm p hp) q hq
    simpa only [Bool.or_eq_true, beq_iff_eq] using h

end CertificateChecks.KernelJ2Cover
