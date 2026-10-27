
module

public import Certificates.Kernel.Parrott946.Glue17b

set_option maxRecDepth 400000

public section

namespace CertificateChecks.Parrott946

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw.Orb CFSG.KC.OrbGroup CFSG.KC.A45Cls CFSG.KC.OrbFind
  CFSG.KC.Parrott946 CFSG.Certificates.Kernel.PkCV CFSG.ComponentClassification.CatFactsSmall.PSp43
  CFSG.RankThree.GF2n.Parrott CFSG.GH74.KGroups CertificateChecks.KernelA45 Subgroup

local notation "P45" => Equiv.Perm (Fin 45)

theorem eq22_of_mul17 {p q r s : ℕ} {gp gq gr gs : P45} (hp : PRep 45 6 p gp)
    (hq : PRep 45 6 q gq) (hr : PRep 45 6 r gr) (hs : PRep 45 6 s gs) (e : gp * gq = gr * gs) :
    eq22 45 6 (mask 6) p q r s = true := by
  unfold eq22
  rw [allN_iff]
  intro i hi
  have hq' : pg 6 (mask 6) q i = (gq ⟨i, hi⟩ : ℕ) := hq ⟨i, hi⟩
  have hs' : pg 6 (mask 6) s i = (gs ⟨i, hi⟩ : ℕ) := hs ⟨i, hi⟩
  rw [hq', hp (gq ⟨i, hi⟩), hs', hr (gs ⟨i, hi⟩)]
  have := congrArg (fun g : P45 => ((g ⟨i, hi⟩ : Fin 45) : ℕ)) e
  simp only [Equiv.Perm.mul_apply] at this
  rw [this]
  exact Nat.beq_refl _

theorem eq_of_eqP {P Q : ℕ} {g h : P45} (e : eqP 45 6 P Q = true) (hP : PRep 45 6 P g)
    (hQ : PRep 45 6 Q h) : g = h := by
  simpa using mul_eq_of_eq22 hP prep_pid hQ prep_pid e

theorem b5_facts : b5 * b5 * (b5 * b5) * b5 = 1 ∧ b5 ≠ 1 ∧ b5 * (u * v) = u * v * b5 ∧
    wv17 11 * b5 = b5 * b5 * wv17 11 ∧ t * (u * v) = u * v * t := by
  have h := c17_b5
  simp only [strictB_eq', Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  have hb := prep_b5
  have hb2 := prep_pc hb hb
  have hw := (prep_wE (k := 11) (by norm_num)).1
  refine ⟨eq_of_eqP h1 (prep_pc (prep_pc hb2 hb2) hb) prep_pid, fun e => ?_,
    comm_of_cmm hb prep_uv h3, mul_eq_of_eq22 hw hb hb2 hw h4, comm_of_cmm prep_t prep_uv h5⟩
  have h0 : eqP 45 6 (wE 10) (pidn 45 6) = true :=
    eq22_of_mul17 hb prep_pid prep_pid prep_pid (by rw [e])
  rw [h0] at h2
  exact absurd h2 (by decide)

theorem b5_pow_five : b5 ^ 5 = 1 := by
  rw [← b5_facts.1]
  simp only [pow_succ, pow_zero, one_mul, mul_assoc]

theorem b5_ne_one : b5 ≠ 1 := b5_facts.2.1

theorem b5_commutes : b5 * (u * v) = (u * v) * b5 := b5_facts.2.2.1

theorem rels17 : alpha2 * (beta2 * alpha2) = beta2 * 1 ∧ alpha2 * sigma1 = sigma1 * alpha2 ∧
    beta2 * sigma1 = sigma1 * beta2 ∧ sigma2 * sigma2 * sigma2 * 1 = 1 * 1 ∧
    u * v * (sigma1 * (sigma2 * sigma2)) = sigma1 * (sigma2 * sigma2) * (u * v) ∧
    v * beta * (v * beta) * 1 = 1 * 1 ∧
    t * (v * beta) * (t * (v * beta)) * 1 = u * t * 1 ∧
    u * t * (v * beta) = v * beta * (u * t) ∧
    v * beta * (sigma1 * sigma2) = sigma1 * sigma2 * (v * beta) := by
  have h := c17_rels
  simp only [strictB_eq', Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  have hvb := prep_pc prep_v prep_beta
  have hs22 := prep_pc prep_sg2 prep_sg2
  have htv := prep_pc prep_t hvb
  exact ⟨mul_eq_of_eq22 prep_a2 (prep_pc prep_b2 prep_a2) prep_b2 prep_pid h1,
    comm_of_cmm prep_a2 prep_sg1 h2, comm_of_cmm prep_b2 prep_sg1 h3,
    mul_eq_of_eq22 (prep_pc hs22 prep_sg2) prep_pid prep_pid prep_pid h4,
    comm_of_cmm prep_uv (prep_pc prep_sg1 hs22) h5,
    mul_eq_of_eq22 (prep_pc hvb hvb) prep_pid prep_pid prep_pid h6,
    mul_eq_of_eq22 (prep_pc htv htv) prep_pid prep_ut prep_pid h7,
    comm_of_cmm prep_ut hvb h8, comm_of_cmm hvb (prep_pc prep_sg1 prep_sg2) h9⟩

theorem q8_conj : beta2 * alpha2 * beta2⁻¹ = alpha2⁻¹ := by
  have h := rels17.1
  rw [mul_one] at h
  calc beta2 * alpha2 * beta2⁻¹ = alpha2⁻¹ * (alpha2 * (beta2 * alpha2)) * beta2⁻¹ := by group
    _ = alpha2⁻¹ := by rw [h]; group

theorem sigma2_inv_eq : sigma2⁻¹ = sigma2 * sigma2 := by
  have h := rels17.2.2.2.1
  rw [mul_one, mul_one] at h
  exact (eq_inv_of_mul_eq_one_left h).symm

theorem uv_commutes_s12i :
    (u * v) * (sigma1 * sigma2⁻¹) = (sigma1 * sigma2⁻¹) * (u * v) := by
  rw [sigma2_inv_eq]
  exact rels17.2.2.2.2.1

theorem vbeta_sq : (v * beta) * (v * beta) = 1 := by
  have h := rels17.2.2.2.2.2.1
  rwa [mul_one, mul_one] at h

theorem tvbeta_sq : (t * (v * beta)) * (t * (v * beta)) = u * t := by
  have h := rels17.2.2.2.2.2.2.1
  rwa [mul_one, mul_one] at h

end CertificateChecks.Parrott946

end
