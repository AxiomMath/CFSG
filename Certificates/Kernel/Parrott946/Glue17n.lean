
module

public import Certificates.Kernel.Parrott946.Glue17c
public import Certificates.Kernel.Parrott946.Glue17d

set_option maxRecDepth 400000

public section

namespace CertificateChecks.Parrott946

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw.Orb CFSG.KC.OrbGroup CFSG.KC.A45Cls CFSG.KC.OrbFind
  CFSG.KC.Parrott946 CFSG.KC.ConjOrb CFSG.Certificates.Kernel.PkCV
  CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.RankThree.GF2n.Parrott CFSG.GH74.KGroups
  CertificateChecks.KernelA45 Subgroup CFSG.Sporadic.SmallOddCore

local notation "P45" => Equiv.Perm (Fin 45)

theorem orderOf_b5 : orderOf b5 = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact orderOf_eq_prime b5_pow_five b5_ne_one

theorem five_dvd_cent {x : P45} (h : x * b5 = b5 * x) :
    5 ∣ Nat.card ↥(A ⊓ centralizer ({x} : Set P45)) := by
  rw [← orderOf_b5]
  exact Subgroup.orderOf_dvd_natCard _ (mem_inf.2 ⟨b5_memA, mem_centralizer_singleton_iff.2 h.symm⟩)

theorem no_ord3_comm_b5 {x : P45} (hx : x ∈ A)
    (h3 : x * x * x = 1) (h1 : x ≠ 1) : x * b5 ≠ b5 * x := by
  intro h
  have h5 := five_dvd_cent h
  rcases order_three_mem hx h3 h1 with (hm | hm) | hm
  · rw [class_card_cent hm, card_cent_s1] at h5
    omega
  · rw [class_card_cent hm, card_cent_s12] at h5
    omega
  · rw [class_card_cent hm, card_cent_s12i] at h5
    omega

theorem kuv_cover {y : P45} (hy : y ∈ conjClass A (u * v)) :
    ∃ i < 36, PRep 45 6 (KUV.T i) y := by
  obtain ⟨-, -, -, -, -, -, -, b0, b1, b2, br⟩ := c17_binds
  have ht : PRep 45 6 (KUV.T KUV.r0) (u * v) := by
    rw [br]
    exact prep_uv
  obtain ⟨c, hc, -, hcl', -⟩ := conjOrb_reps (g := gA') hn45 KUV.h (prep_gens b0 b1 b2) KUV.cl
    KUV.tr0 (by decide) ht ps_lt KUV.k
  have hr : c KUV.r0 = u * v := prep_eq (hc _ (by decide)) ht
  obtain ⟨g, hg, rfl⟩ := hy
  rw [← closure_gA] at hg
  have hO := conj_closed_A (O := {z | ∃ i < 36, c i = z}) (by
    rintro _ ⟨k, hk, rfl⟩ _ ⟨i, hi, rfl⟩
    obtain ⟨j, hj, e⟩ := hcl' i hi k hk
    exact ⟨j, hj, e.symm⟩) g hg (u * v) ⟨KUV.r0, by decide, hr⟩
  obtain ⟨i, hi, e⟩ := hO
  exact ⟨i, hi, by rw [← e]; exact hc i hi⟩

theorem inv_comm_b5 {x : P45} (hx : x ∈ A) (h2 : x * x = 1)
    (h1 : x ≠ 1) (h : x * b5 = b5 * x) : x = u * v := by
  have h5 := five_dvd_cent h
  rw [card_cent_eq hx h2 h1] at h5
  have hf : fixC x = 15 := by
    rcases fix_cases hx h2 h1 with e | e | e | e
    · rw [e] at h5
      exact absurd h5 (by decide)
    · rw [e] at h5
      exact absurd h5 (by decide)
    · exact e
    · rw [e] at h5
      exact absurd h5 (by decide)
  obtain ⟨c, hc, e⟩ := conj_of_fix hx h2 h1 uv_memA uv_inv.1 uv_inv.2 (by rw [hf, fixC_uv])
  obtain ⟨i, hi, hp⟩ := kuv_cover ⟨c, hc, e⟩
  have hk := c17_kuv
  rw [strictB_eq', strictB_eq'] at hk
  have hk' := allN_spec hk i hi
  rw [Bool.or_eq_true, Bool.not_eq_true'] at hk'
  rcases hk' with hk' | hk'
  · have hc' : cmm (KUV.T i) (wE 10) = true := eq22_of_mul17 hp prep_b5 prep_b5 hp h
    rw [hc'] at hk'
    exact absurd hk' (by decide)
  · rw [Nat.eq_of_beq_eq_true hk'] at hp
    exact prep_eq hp prep_uv

end CertificateChecks.Parrott946

end
