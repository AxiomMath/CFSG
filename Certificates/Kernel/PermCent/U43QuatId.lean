module

public import Certificates.Kernel.PermCent.U43QuatP
import CFSG.Certificates.Kernel.Spor.PcompFacts

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelPermCent.U43Quat

open CFSG.ComponentClassification.HarrisLit.P1.U43.Quat CFSG.KC.QuatK
  CertificateChecks.KernelPermCent.U43P1 CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def uvuOK (u v : Nat) : Bool :=
  (List.range 820).all fun i =>
    Nat.beq (pg 10 (mask 10) u (pg 10 (mask 10) v (pg 10 (mask 10) u i))) (pg 10 (mask 10) v i)

theorem beq_uvu (u v : Nat) (hv : v >>> (820 * 10) = 0) :
    Nat.beq (mulK 820 10 u (mulK 820 10 v u)) v = uvuOK u v := by
  have hn : (820 : Nat) < 2 ^ 32 := by decide
  have hw : (0 : Nat) < 10 := by decide
  apply Bool.eq_iff_iff.2
  unfold uvuOK
  rw [List.all_eq_true]
  constructor
  · intro h i hi
    have hi' : i < 820 := List.mem_range.1 hi
    have e := Nat.eq_of_beq_eq_true h
    have h2 : pg 10 (mask 10) (mulK 820 10 u (mulK 820 10 v u)) i = pg 10 (mask 10) v i := by
      rw [e]
    unfold mulK at h2
    rw [CFSG.KS.PF.pg_pcomp hn hi', CFSG.KS.PF.pg_pcomp hn hi'] at h2
    rw [h2]
    exact Nat.beq_refl _
  · intro h
    have e : mulK 820 10 u (mulK 820 10 v u) = v := by
      unfold mulK
      refine CFSG.KS.PF.eq_of_fields hw (CFSG.KS.PF.pcomp_shr _ _ hn hw) hv fun i hi => ?_
      rw [CFSG.KS.PF.pg_pcomp hn hi, CFSG.KS.PF.pg_pcomp hn hi]
      exact Nat.eq_of_beq_eq_true (h i (List.mem_range.2 hi))
    rw [e]
    exact Nat.beq_refl _

theorem all_congr_mem {α : Type} (L : List α) (f g : α → Bool) (h : ∀ x ∈ L, f x = g x) :
    L.all f = L.all g := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    rw [List.all_cons, List.all_cons, h a (by simp), ih fun x hx => h x (by simp [hx])]

@[expose] noncomputable def identSqK' (e r : Nat) (S : List Nat) (W : List (Nat × Nat))
    (Ls : List (List Nat)) : Bool :=
  S.all fun u => W.any (badWitK 820 10 u) || S.all fun v =>
    !uvuOK u v ||
      (Ls.any (sameSetK (q8K 820 10 e r u v)) || W.any (violatesK 820 10 (q8K 820 10 e r u v) u v))

theorem identSq_eq (e r : Nat) (S : List Nat) (W : List (Nat × Nat)) (Ls : List (List Nat))
    (hS : ∀ v ∈ S, v >>> (820 * 10) = 0) :
    identSqCheckK 820 10 e r S W Ls = identSqK' e r S W Ls := by
  unfold identSqCheckK identSqK'
  refine all_congr_mem _ _ _ fun u _ => ?_
  congr 1
  refine all_congr_mem _ _ _ fun v hv => ?_
  rw [beq_uvu u v (hS v hv)]

theorem hS0 : ((rootIdx.map CgIn.T).all fun v => Nat.beq (v >>> (820 * 10)) 0) = true := by
  decide +kernel

theorem ident_scan :
    identSqCheckK 820 10 eP rF (rootIdx.map CgIn.T) [(w0F, w0F)] [l0F, l1F] = true := by
  rw [identSq_eq _ _ _ _ _ fun v hv => Nat.eq_of_beq_eq_true (List.all_eq_true.1 hS0 v hv)]
  decide +kernel

end CertificateChecks.KernelPermCent.U43Quat

end
