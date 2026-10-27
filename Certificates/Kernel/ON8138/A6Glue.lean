
module

public import CFSG.Certificates.Kernel.ON8138.Sound
public import Certificates.Kernel.ON8138.A6

public section

namespace CertificateChecks.KernelON8138

open CFSG.KC.ON8138 CFSG.KD.ON8138 CFSG.RankThree.Native.ONTriple Equiv

theorem pd_eq (c i : ℕ) : pd c i = c / 8 ^ i % 8 := rfl

theorem pd_penc (σ : Perm (Fin 6)) (i : Fin 6) : pd (penc σ) i.val = (σ i).val := by
  have h0 := (σ 0).isLt
  have h1 := (σ 1).isLt
  have h2 := (σ 2).isLt
  have h3 := (σ 3).isLt
  have h4 := (σ 4).isLt
  have h5 := (σ 5).isLt
  rw [pd_eq]
  unfold penc
  fin_cases i <;> simp <;> omega

theorem penc_lt (σ : Perm (Fin 6)) : penc σ < 8 ^ 6 := by
  have h0 := (σ 0).isLt
  have h1 := (σ 1).isLt
  have h2 := (σ 2).isLt
  have h3 := (σ 3).isLt
  have h4 := (σ 4).isLt
  have h5 := (σ 5).isLt
  unfold penc
  norm_num
  omega

theorem penc_sum (σ : Perm (Fin 6)) :
    penc σ = ∑ k ∈ Finset.range 6, pd (penc σ) k * 8 ^ k := by
  conv_lhs => rw [← Nat.mod_eq_of_lt (penc_lt σ), mod_pow_eq_sum 8]
  rfl

theorem pcomp_rec (a b n : ℕ) :
    (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun i acc => Nat.add acc (Nat.mul (pd a (pd b i)) (Nat.pow (nat_lit 8) i))) n : ℕ) =
      ∑ k ∈ Finset.range n, pd a (pd b k) * 8 ^ k := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih]
    rfl

theorem pcomp_eq (a b : ℕ) : pcomp a b = ∑ k ∈ Finset.range 6, pd a (pd b k) * 8 ^ k :=
  pcomp_rec a b 6

theorem penc_mul (σ τ : Perm (Fin 6)) : penc (σ * τ) = pcomp (penc σ) (penc τ) := by
  rw [penc_sum (σ * τ), pcomp_eq]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k < 6 := Finset.mem_range.1 hk
  have e := pd_penc (σ * τ) ⟨k, hk'⟩
  have e2 := pd_penc τ ⟨k, hk'⟩
  simp only at e e2
  rw [e, e2, pd_penc σ (τ ⟨k, hk'⟩), Perm.mul_apply]

theorem penc_inj {σ τ : Perm (Fin 6)} (h : penc σ = penc τ) : σ = τ := by
  ext i
  rw [← pd_penc, h, pd_penc]

theorem penc_one : penc 1 = pid := rfl

theorem penc_pow (σ : Perm (Fin 6)) (k : ℕ) : penc (σ ^ k) = ppow (penc σ) k := by
  induction k with
  | zero => exact penc_one
  | succ k ih =>
    rw [pow_succ, penc_mul, ih]
    rfl

theorem penc_evW (u₁ u₂ : Perm (Fin 6)) (w : List ℕ) :
    penc (evW u₁ u₂ w) = pevW (penc u₁) (penc u₂) w := by
  induction w with
  | nil => exact penc_one
  | cons l w ih =>
    have e : pevW (penc u₁) (penc u₂) (l :: w) =
      pcomp (Bool.rec (penc u₂) (penc u₁) (Nat.beq l 0)) (pevW (penc u₁) (penc u₂) w) := rfl
    rw [e, ← ih, evW, List.map_cons, List.prod_cons, ← evW, penc_mul]
    congr 1
    cases l with
    | zero => rfl
    | succ l => rfl

theorem penc_lits : penc (sY 0) = 181826 ∧ penc (sY 1) = 120898 ∧ penc s4 = 5475 ∧
    penc sK1 = 180867 ∧ penc sK2 = 71709 := by
  decide

theorem a6_rigid' : ∀ u₁ u₂ : Perm (Fin 6), u₁ ^ 3 = 1 → u₂ ^ 3 = 1 → (u₁ * u₂) ^ 5 = 1 →
    evW u₁ u₂ Wy0 = sY 0 → evW u₁ u₂ Wy1 = sY 1 → evW u₁ u₂ Wt4 = s4 →
      u₁ = sK1 ∧ u₂ = sK2 := by
  intro u₁ u₂ h1 h2 h3 h4 h5 h6
  obtain ⟨i, hi, hpi⟩ := (anyK_iff _ _).1 (cubes u₁ h1)
  obtain ⟨j, hj, hpj⟩ := (anyK_iff _ _).1 (cubes u₂ h2)
  have hpi := Nat.eq_of_beq_eq_true hpi
  have hpj := Nat.eq_of_beq_eq_true hpj
  obtain ⟨l0, l1, l4, k1, k2⟩ := penc_lits
  have H := a6K
  unfold a6OK at H
  rw [allK_iff] at H
  have H := H i hi
  rw [allK_iff] at H
  have H := H j hj
  rw [strictN_eq, strictN_eq, hpi, hpj, ← penc_mul, ← penc_pow, h3, penc_one, ← penc_evW,
    ← penc_evW, ← penc_evW, h4, h5, h6, l0, l1, l4] at H
  simp only [orK_eq, notK_eq, andK_eq, Nat.beq_refl, Bool.not_true, Bool.false_or,
    Bool.and_eq_true, Nat.beq_eq] at H
  exact ⟨penc_inj (H.1.trans k1.symm), penc_inj (H.2.trans k2.symm)⟩

end CertificateChecks.KernelON8138

end
