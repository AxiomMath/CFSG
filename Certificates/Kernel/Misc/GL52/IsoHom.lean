
module

public import Certificates.Kernel.Misc.GL52.IsoLemmas
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelMisc.GL52L

open CFSG.Literature.GL52 Matrix CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.KC.Misc.GLM

section Letters

variable {Q : Type*} [Group Q]

@[expose] def letQ (qs : List Q) (l : ℤ) : Q :=
  if 0 < l then qs.getD (l.toNat - 1) 1 else (qs.getD ((-l).toNat - 1) 1)⁻¹

@[expose] def evQ (qs : List Q) (w : List ℤ) : Q := (w.map (letQ qs)).prod

theorem lkFun_mul_of_letters {K : Type} [DecidableEq K] (gs : List G) (qs : List Q)
    (key : Q → K) (L : List (K × List ℤ)) (Ls : List ℤ)
    (hL : ∀ q, ∀ l ∈ lkWord key L q, l ∈ Ls)
    (h₁ : ∀ q, ∀ l ∈ Ls, lkFun gs key L (q * letQ qs l) = lkFun gs key L q * letterG gs l)
    (h₂ : ∀ r, evQ qs (lkWord key L r) = r) (q r : Q) :
    lkFun gs key L (q * r) = lkFun gs key L q * lkFun gs key L r := by
  have hw : ∀ w : List ℤ, (∀ l ∈ w, l ∈ Ls) → ∀ q,
      lkFun gs key L (q * evQ qs w) = lkFun gs key L q * wordG (letterG gs) w := by
    intro w
    induction w with
    | nil =>
      intro _ q
      simp [evQ, wordG]
    | cons l w ih =>
      intro hw q
      have e₁ : evQ qs (l :: w) = letQ qs l * evQ qs w := by simp [evQ]
      have e₂ : wordG (letterG gs) (l :: w) = letterG gs l * wordG (letterG gs) w := by
        simp [wordG]
      rw [e₁, e₂, ← mul_assoc, ih (fun l' hl' => hw l' (List.mem_cons_of_mem _ hl')),
        h₁ q l (hw l List.mem_cons_self), mul_assoc]
  have h := hw (lkWord key L r) (hL r) q
  rw [h₂ r] at h
  rw [h]
  rfl

theorem tblEq_of_lkFun_mul {K : Type} [DecidableEq K] (gs : List G) (key : Q → K)
    (L : List (K × List ℤ)) (q r : Q)
    (h : lkFun gs key L (q * r) = lkFun gs key L q * lkFun gs key L r) :
    tblEq 31 (lkTableT (genTables gs) (genInvTables gs) key L (q * r))
      (compT 31 (lkTableT (genTables gs) (genInvTables gs) key L q)
        (lkTableT (genTables gs) (genInvTables gs) key L r)) = true := by
  change tblEq 31 (lkTable gs key L (q * r)) (compT 31 (lkTable gs key L q) (lkTable gs key L r)) =
    true
  rw [tblEq_rep (rep_lkTable gs key L (q * r))
    (Rep.compT (rep_lkTable gs key L q) (rep_lkTable gs key L r)), h, beq_self_eq_true]

end Letters

@[expose] def gA : GL (Fin 3) (ZMod 2) :=
  ⟨!![0, 1, 0; 0, 0, 1; 1, 0, 0], !![0, 0, 1; 1, 0, 0; 0, 1, 0], by decide, by decide⟩

@[expose] def gB : GL (Fin 3) (ZMod 2) :=
  ⟨!![1, 1, 0; 0, 1, 0; 0, 0, 1], !![1, 1, 0; 0, 1, 0; 0, 0, 1], by decide, by decide⟩

@[expose] def keyEv (w : List ℤ) : List ℕ :=
  w.foldr (fun l acc => mulKey (keyGL3 (letQ [gA, gB] l)) acc) (keyGL3 1)

theorem keyGL3_evQ (w : List ℤ) : keyGL3 (evQ [gA, gB] w) = keyEv w := by
  induction w with
  | nil => simp [evQ, keyEv]
  | cons l w ih =>
    have e : evQ [gA, gB] (l :: w) = letQ [gA, gB] l * evQ [gA, gB] w := by simp [evQ]
    rw [e, keyGL3_mul, ih]
    rfl

abbrev lets3 : List ℤ := [1, 2, -1, -2]

theorem g3Words : (tblGL3.all fun e => (e.2.all fun l => lets3.contains l) &&
    keyEv (lkW tblGL3 e.1) == e.1) = true := by
  quickRfl

theorem lets_mem (q : GL (Fin 3) (ZMod 2)) : ∀ l ∈ lkWord keyGL3 tblGL3 q, l ∈ lets3 := by
  intro l hl
  rcases List.mem_cons.1 (lkWord_mem keyGL3 tblGL3 q) with h | h
  · rw [h] at hl
    simp at hl
  · obtain ⟨e, he, hw⟩ := List.mem_map.1 h
    have hc : ((e.2.all fun l => lets3.contains l) && keyEv (lkW tblGL3 e.1) == e.1) = true :=
      List.all_eq_true.1 g3Words e he
    simp only [Bool.and_eq_true, List.all_eq_true] at hc
    rw [← hw] at hl
    simpa using hc.1 l hl

theorem evQ_lkWord (r : GL (Fin 3) (ZMod 2)) : evQ [gA, gB] (lkWord keyGL3 tblGL3 r) = r := by
  obtain ⟨e, he, hr⟩ := keyGL3_mem r
  have hc : ((e.2.all fun l => lets3.contains l) && keyEv (lkW tblGL3 e.1) == e.1) = true :=
    List.all_eq_true.1 g3Words e he
  simp only [Bool.and_eq_true, beq_iff_eq] at hc
  apply keyGL3_inj
  rw [keyGL3_evQ]
  change keyEv (lkW tblGL3 (keyGL3 r)) = keyGL3 r
  rw [← hr]
  exact hc.2

theorem gl3_hom (gs : List G) (hchk : (tblGL3.all fun e => lets3.all fun l =>
      lkK gs tblGL3 (mulKey e.1 (keyGL3 (letQ [gA, gB] l))) ==
        mmulK (lkK gs tblGL3 e.1) (letterK (gK gs) (giK gs) l)) = true)
    (q r : GL (Fin 3) (ZMod 2)) :
    lkFun gs keyGL3 tblGL3 (q * r) = lkFun gs keyGL3 tblGL3 q * lkFun gs keyGL3 tblGL3 r := by
  refine lkFun_mul_of_letters gs [gA, gB] keyGL3 tblGL3 lets3 lets_mem (fun q l hl => ?_)
    evQ_lkWord q r
  obtain ⟨e, he, hq⟩ := keyGL3_mem q
  have h₁ : (lets3.all fun l => lkK gs tblGL3 (mulKey e.1 (keyGL3 (letQ [gA, gB] l))) ==
      mmulK (lkK gs tblGL3 e.1) (letterK (gK gs) (giK gs) l)) = true :=
    List.all_eq_true.1 hchk e he
  have h₂ : (lkK gs tblGL3 (mulKey e.1 (keyGL3 (letQ [gA, gB] l))) ==
      mmulK (lkK gs tblGL3 e.1) (letterK (gK gs) (giK gs) l)) = true :=
    List.all_eq_true.1 h₁ l hl
  rw [beq_iff_eq, hq, ← keyGL3_mul] at h₂
  rw [eq_iff_cG, cG_mul, lkFun, lkFun, cG_wordG, cG_wordG, cG_letterG]
  exact h₂

end CertificateChecks.KernelMisc.GL52L

end
