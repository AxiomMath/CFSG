
module

public import Certificates.Kernel.J4Count.Fix11Base

public import CFSG.Sporadic.Schreier.J4SElevenBase1
public import CFSG.Adapters.ProjectiveSpecialLinear

@[expose] public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Count

open CFSG.Sporadic.J4 CFSG.Sporadic.J4Schreier CFSG.Sporadic.GLQ MulAction
open CFSG.KC.J4Slp CFSG.KS.SporSch.J4B CFSG.KC.J4Q CFSG.KD.J4Q
open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CertificateChecks.KernelSporSch

section Run

theorem qx_fix : qx • p₁ = p₁ := by
  have e := inv_smul_toRow rep_qx P1K
  rw [chk_facts.1, inv_smul_eq_iff] at e
  exact e.symm

theorem qz_move : qz • p₁ ≠ p₁ := by
  intro hf
  have e := inv_smul_toRow rep_qz P1K
  have hinv : qz⁻¹ • p₁ = p₁ := by rw [inv_smul_eq_iff, hf]
  rw [hinv] at e
  have e2 : toVecD 112 P1K = toVecD 112 (O.vmul P1K QZn.1) := congrArg ofRow e
  rw [toVecD_eq_iff, Nat.mod_eq_of_lt P1K_lt] at e2
  exact chk_facts.2 e2.symm

theorem p1_eq : m₁⁻¹ • v = p₁ := by
  have hP := wordP_ok' J4Real.hK J4InvP.pA J4InvP.pB wordP1 (by decide)
  have e := inv_smul_toRow (rep_wordP (rep_a matFacts) (rep_b matFacts) wordP1) rootBits
  rw [vec_pair J4Real.hK hP] at e
  exact e

theorem p1_mem : p₁ ∈ orbit J v := ⟨m₁⁻¹, p1_eq⟩

theorem qx_ne_one' : qx ≠ 1 := by
  intro h
  apply qz_ne_one
  rw [qz, h, commutatorElement_one_left]

theorem orderOf_qx' : orderOf qx = 11 := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  exact orderOf_eq_prime qx_pow_eleven qx_ne_one'

end Run

section Main

theorem qz_pow_not_fix' {k : ℕ} (hk : ¬ 11 ∣ k) : qz ^ k • p₁ ≠ p₁ := by
  intro h
  have hpos : 0 < k % 11 := Nat.pos_of_ne_zero fun h0 => hk (Nat.dvd_of_mod_eq_zero h0)
  have hinv : ∀ m < 11, 0 < m → ∃ t < 11, m * t % 11 = 1 := by decide
  obtain ⟨t, htl, ht⟩ := hinv (k % 11) (Nat.mod_lt _ (by norm_num)) hpos
  have hkt : k * t % 11 = 1 := by rw [Nat.mul_mod, Nat.mod_eq_of_lt htl]; exact ht
  have e : qz = (qz ^ k) ^ t := by
    rw [← pow_mul, pow_eq_pow_mod _ qz_pow_eleven, hkt, pow_one]
  have hmem : qz ^ k ∈ stabilizer J p₁ := h
  have : qz ∈ stabilizer J p₁ := by
    rw [e]
    exact Subgroup.pow_mem _ hmem t
  exact qz_move this

theorem orderOf_h1 : orderOf h₁ = 11 := by
  rw [← orderOf_qx']
  obtain ⟨c, hc⟩ := isConj_iff.1 isConj_qx_h1
  rw [← hc]
  exact orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective qx

theorem qz_pow_mem (k : ℕ) : qz ^ k • p₁ ∈ fixX := by
  refine ⟨?_, ?_⟩
  · obtain ⟨g, hg⟩ := p1_mem
    refine ⟨qz ^ k * g, ?_⟩
    change (qz ^ k * g) • v = qz ^ k • p₁
    rw [mul_smul]
    exact congrArg (qz ^ k • ·) hg
  · rw [← mul_smul, ← commute_pow_qz qz_mul_qx, mul_smul, qx_fix]

theorem qz_pow_inj : Function.Injective fun k : Fin 11 => qz ^ (k : ℕ) • p₁ := by
  have aux : ∀ j k : ℕ, j < k → k < 11 → qz ^ j • p₁ = qz ^ k • p₁ → False := by
    intro j k hjk hk e
    have e2 : qz ^ j • (qz ^ (k - j) • p₁) = qz ^ j • p₁ := by
      rw [← mul_smul, ← pow_add, Nat.add_sub_cancel' hjk.le]
      exact e.symm
    exact qz_pow_not_fix' (k := k - j) (by omega) (smul_left_cancel _ e2)
  intro j k e
  by_contra hne
  rcases lt_or_gt_of_ne (fun h => hne (Fin.ext h)) with h | h
  · exact aux j k h k.isLt e
  · exact aux k j h j.isLt e.symm

end Main

end CertificateChecks.KernelJ4Count

end
