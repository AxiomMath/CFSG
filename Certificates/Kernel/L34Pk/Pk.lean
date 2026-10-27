
module

public import Certificates.Kernel.L34Pk.Data
public import CFSG.Certificates.Kernel.L34PkSound
public import Certificates.Kernel.Sporadic.M22Syl.Facts
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelL34

open Equiv CFSG.KS.PCnt CFSG.KC.L34 CFSG.KC.WCnt CFSG.KC.Enum CFSG.Quasithin.L34Amalgam
  CFSG.Sporadic.Mathieu CFSG.ComponentClassification.WittDesign CertificateChecks.KernelSpor.M22Syl

set_option maxRecDepth 100000

theorem I_eq : I = pI := Nat.eq_of_beq_eq_true (by quickRfl)

theorem pk_one' : pkw 5 (1 : Perm (Fin 22)) = pI := pk_one.trans I_eq

theorem pkw_mul' (σ τ : Perm (Fin 22)) : pkw 5 (σ * τ) = pm (pkw 5 σ) (pkw 5 τ) := by
  have h := pkw_mul (n := 22) (w := 5) (by norm_num) (by norm_num) σ τ
  rw [mask_five] at h
  exact h.symm

theorem pfold_cons (L : Char → Nat) (c : Char) (cs : List Char) (g : Nat) :
    pfold L (c :: cs) g = pfold L cs (pm g (L c)) :=
  strictN_eq' _ _

theorem pkw_foldl (Lg : Char → M22) (L : Char → Nat)
    (hL : ∀ c, pkw 5 ((Lg c : M22) : Perm (Fin 22)) = L c) :
    ∀ (cs : List Char) (g : M22),
      pkw 5 ((cs.foldl (fun g c => g * Lg c) g : M22) : Perm (Fin 22)) =
        pfold L cs (pkw 5 (g : Perm (Fin 22)))
  | [], _ => rfl
  | c :: cs, g => by
    rw [List.foldl_cons, pkw_foldl Lg L hL cs, pfold_cons, Subgroup.coe_mul, pkw_mul', hL]

@[expose] noncomputable def labL (c : Char) : Nat :=
  if c = 'a' then A else if c = 'b' then B else if c = 'A' then Ai else Bi

theorem pkw_m22OfWord (s : String) :
    pkw 5 ((m22OfWord s : M22) : Perm (Fin 22)) = pfold labL s.toList pI := by
  unfold m22OfWord
  rw [pkw_foldl _ labL (fun c => ?_), OneMemClass.coe_one, pk_one']
  unfold labL
  split_ifs
  · exact pk_a
  · exact pk_b
  · rw [Subgroup.coe_inv]
    exact pk_ai
  · rw [Subgroup.coe_inv]
    exact pk_bi

theorem pk_c1 : pkw 5 (bC1 : Perm (Fin 22)) = gL.getD 0 0 := by
  unfold bC1
  rw [pkw_m22OfWord]
  exact Nat.eq_of_beq_eq_true (by quickRfl)

theorem pk_c2 : pkw 5 (bC2 : Perm (Fin 22)) = gL.getD 1 0 := by
  unfold bC2
  rw [pkw_m22OfWord]
  exact Nat.eq_of_beq_eq_true (by quickRfl)

theorem pk_c3 : pkw 5 (bC3 : Perm (Fin 22)) = gL.getD 2 0 := by
  unfold bC3
  rw [pkw_m22OfWord]
  exact Nat.eq_of_beq_eq_true (by quickRfl)

theorem pk_t1 : pkw 5 (bT1 : Perm (Fin 22)) = gL.getD 3 0 := by
  unfold bT1
  rw [pkw_m22OfWord]
  exact Nat.eq_of_beq_eq_true (by quickRfl)

theorem pk_t2 : pkw 5 (bT2 : Perm (Fin 22)) = gL.getD 4 0 := by
  unfold bT2
  rw [pkw_m22OfWord]
  exact Nat.eq_of_beq_eq_true (by quickRfl)

theorem pk_a2 : pkw 5 (a2r : Perm (Fin 22)) = tA2 := by
  unfold a2r
  rw [pkw_m22OfWord]
  exact Nat.eq_of_beq_eq_true (by quickRfl)

theorem pk_b2 : pkw 5 (b2r : Perm (Fin 22)) = tB2 := by
  unfold b2r
  rw [pkw_m22OfWord]
  exact Nat.eq_of_beq_eq_true (by quickRfl)

theorem pk_e0 : pkw 5 (refE0 : Perm (Fin 22)) = cL.getD 1 0 := by
  unfold refE0
  rw [pkw_m22OfWord]
  exact Nat.eq_of_beq_eq_true (by quickRfl)

theorem pk_e1 : pkw 5 (refE1 : Perm (Fin 22)) = cL.getD 2 0 := by
  unfold refE1
  rw [pkw_m22OfWord]
  exact Nat.eq_of_beq_eq_true (by quickRfl)

theorem pk_e2 : pkw 5 (refE2 : Perm (Fin 22)) = cL.getD 4 0 := by
  unfold refE2
  rw [pkw_m22OfWord]
  exact Nat.eq_of_beq_eq_true (by quickRfl)

theorem pk_e3 : pkw 5 (refE3 : Perm (Fin 22)) = cL.getD 8 0 := by
  unfold refE3
  rw [pkw_m22OfWord]
  exact Nat.eq_of_beq_eq_true (by quickRfl)

theorem pkw_inv_two {g : Perm (Fin 22)} {G : Nat} (hg : pkw 5 g = G)
    (h : Nat.beq (pm G G) pI = true) : pkw 5 g⁻¹ = G := by
  have e : g * g = 1 := pkw_inj (n := 22) (w := 5) (by norm_num) (by
    rw [pkw_mul', hg, Nat.eq_of_beq_eq_true h, pk_one'])
  rw [inv_eq_of_mul_eq_one_right e, hg]

theorem pkw_inv_three {g : Perm (Fin 22)} {G : Nat} (hg : pkw 5 g = G)
    (h : Nat.beq (pm G (pm G G)) pI = true) : pkw 5 g⁻¹ = pm G G := by
  have e : g * (g * g) = 1 := pkw_inj (n := 22) (w := 5) (by norm_num) (by
    rw [pkw_mul', pkw_mul', hg, Nat.eq_of_beq_eq_true h, pk_one'])
  rw [inv_eq_of_mul_eq_one_right e, pkw_mul', hg]

theorem pk_c1i : pkw 5 ((bC1⁻¹ : M22) : Perm (Fin 22)) = giL.getD 0 0 := by
  rw [Subgroup.coe_inv]
  exact pkw_inv_two pk_c1 (by quickRfl)

theorem pk_c2i : pkw 5 ((bC2⁻¹ : M22) : Perm (Fin 22)) = giL.getD 1 0 := by
  rw [Subgroup.coe_inv]
  exact pkw_inv_two pk_c2 (by quickRfl)

theorem pk_c3i : pkw 5 ((bC3⁻¹ : M22) : Perm (Fin 22)) = giL.getD 2 0 := by
  rw [Subgroup.coe_inv]
  exact (pkw_inv_three pk_c3 (by quickRfl)).trans (Nat.eq_of_beq_eq_true (by quickRfl))

theorem pk_t1i : pkw 5 ((bT1⁻¹ : M22) : Perm (Fin 22)) = giL.getD 3 0 := by
  rw [Subgroup.coe_inv]
  exact pkw_inv_two pk_t1 (by quickRfl)

theorem pk_t2i : pkw 5 ((bT2⁻¹ : M22) : Perm (Fin 22)) = giL.getD 4 0 := by
  rw [Subgroup.coe_inv]
  exact pkw_inv_two pk_t2 (by quickRfl)

theorem pk_selM (b : Bool) (g : M22) :
    pkw 5 ((selM b g : M22) : Perm (Fin 22)) = if b then pkw 5 (g : Perm (Fin 22)) else pI := by
  unfold selM
  cases b
  · rw [if_neg (by decide), if_neg (by decide), OneMemClass.coe_one, pk_one']
  · rw [if_pos rfl, if_pos rfl]

theorem pk_gen : ∀ j : Fin 5, pkw 5 ((gen j : M22) : Perm (Fin 22)) = gL.getD j.val 0 := by
  intro j
  fin_cases j
  exacts [pk_c1, pk_c2, pk_c3, pk_t1, pk_t2]

theorem pk_geni : ∀ j : Fin 5, pkw 5 ((gen j : M22) : Perm (Fin 22))⁻¹ = giL.getD j.val 0 := by
  intro j
  fin_cases j
  · exact pkw_inv_two pk_c1 (by quickRfl)
  · exact pkw_inv_two pk_c2 (by quickRfl)
  · exact (pkw_inv_three pk_c3 (by quickRfl)).trans (Nat.eq_of_beq_eq_true (by quickRfl))
  · exact pkw_inv_two pk_t1 (by quickRfl)
  · exact pkw_inv_two pk_t2 (by quickRfl)

theorem pk_b2i : pkw 5 ((b2r : Perm (Fin 22)))⁻¹ = tB2i :=
  (pkw_inv_three pk_b2 (by quickRfl)).trans (Nat.eq_of_beq_eq_true (by quickRfl))

theorem pkw_c2OfWord (s : String) :
    pkw 5 ((c2OfWord s : M22) : Perm (Fin 22)) = pfold labC2 s.toList pI := by
  unfold c2OfWord
  rw [pkw_foldl _ labC2 (fun c => ?_), OneMemClass.coe_one, pk_one']
  unfold labC2
  split_ifs
  · exact pk_a2
  · exact pk_b2
  · rw [Subgroup.coe_inv]
    exact pk_b2i

theorem coe_evalW (f : Fin 5 → M22) : ∀ w : List (Fin 5 × Bool),
    ((evalW f w : M22) : Perm (Fin 22)) = evalW (fun j => (f j : Perm (Fin 22))) w
  | [] => rfl
  | x :: w => by
    have ih := coe_evalW f w
    unfold evalW at ih ⊢
    rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons, Subgroup.coe_mul, ih]
    cases x.2
    · simp only [cond_false, Subgroup.coe_inv]
    · simp only [cond_true]

theorem evalW_cons (f : Fin 5 → Perm (Fin 22)) (x : Fin 5 × Bool) (w : List (Fin 5 × Bool)) :
    evalW f (x :: w) = cond x.2 (f x.1) (f x.1)⁻¹ * evalW f w := by
  unfold evalW
  rw [List.map_cons, List.prod_cons]

theorem pkw_cond (f : Fin 5 → Perm (Fin 22)) (b : Bool) (j : Fin 5) :
    pkw 5 (cond b (f j) (f j)⁻¹) = cond b (pkw 5 (f j)) (pkw 5 (f j)⁻¹) := by
  cases b
  · rw [cond_false, cond_false]
  · rw [cond_true, cond_true]

theorem pkw_evalW (f : Fin 5 → Perm (Fin 22)) (w : List (Fin 5 × Bool)) :
    pkw 5 (evalW f w) = pevT (fun j => pkw 5 (f j)) (fun j => pkw 5 (f j)⁻¹) w := by
  induction w with
  | nil =>
    have e : evalW f [] = 1 := List.prod_nil
    rw [e, pevT_nil, pk_one']
  | cons x w ih => rw [evalW_cons, pkw_mul', pkw_cond, ih, pevT_cons]

theorem evalW_gen_eq_one {w : List (Fin 5 × Bool)}
    (h : Nat.beq (pevT (fun j => gL.getD j.val 0) (fun j => giL.getD j.val 0) w) pI = true) :
    evalW gen w = 1 := by
  refine Subtype.ext (pkw_inj (n := 22) (w := 5) (by norm_num) ?_)
  rw [coe_evalW, pkw_evalW, OneMemClass.coe_one, pk_one']
  simp only [pk_gen, pk_geni]
  exact Nat.eq_of_beq_eq_true h

theorem coe_eq_upk {σ : Perm (Fin 22)} {G : Nat} (h : pkw 5 σ = G) : ⇑σ = upk22 G :=
  h ▸ (upk22_pkw σ).symm

end CertificateChecks.KernelL34

end
