
module

public import Certificates.Kernel.J4Count.HOrderBase1

public import CFSG.Sporadic.Schreier.J4SNoCompCoverBase2
public import CFSG.Quasithin.H13.J4ClassesBase1
public import Certificates.Kernel.J4Count.HOrderBase

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Count

open CFSG.Sporadic.J4 CFSG.Sporadic.J4Schreier CFSG.Sporadic.J4Schreier.NoComp MulAction
open CFSG.Sporadic.SmallF2

theorem stab_ne_top : stabilizer J v ≠ ⊤ := by
  intro h
  have hm : (mRep 1)⁻¹ ∈ stabilizer J v := h ▸ Subgroup.mem_top _
  have e : (mRep 1)⁻¹ • v = (mRep 0)⁻¹ • v := by
    rw [mRep_zero, inv_one, one_smul]
    exact hm
  rw [mRep_inv_smul_v (by norm_num), mRep_inv_smul_v (by norm_num)] at e
  have e2 := congrArg fixCard e
  rw [fixCard_rep (by norm_num), fixCard_rep (by norm_num)] at e2
  exact absurd e2 (by decide)

theorem stab_eq_Kz : stabilizer J v = CertificateChecks.KernelJ4Hub.Kz :=
  (CertificateChecks.KernelJ4Hub.isCoatom_K.le_iff.1 Kz_le_stab).resolve_left stab_ne_top

theorem stabilizer_v_eq_Hj' : stabilizer J v = Hj :=
  le_antisymm (stab_eq_Kz.le.trans Kz_le_Hj) Hj_le_stab

theorem card_Hj' : Nat.card Hj = 501397585920 := by
  rw [← stabilizer_v_eq_Hj', stab_eq_Kz, card_Kz]

theorem card_H' : Nat.card H = 501397585920 := by
  have : Finite J := CertificateChecks.KernelJ4Hub.finite_J
  have hup : Nat.card H ≤ 501397585920 := by
    rw [← card_Kz, ← stab_eq_Kz]
    exact Subgroup.card_le_of_le H_le_stabilizer_v
  have hP : Nat.card P ≤ Nat.card K :=
    Nat.card_le_card_of_surjective _ ρK.rangeRestrict_surjective
  have h1 := card_N_mul_card_K_le
  have h2 := card_P_ge
  rw [card_N] at h1
  omega

theorem H_eq_Kz : H = CertificateChecks.KernelJ4Hub.Kz := by
  have : Finite J := CertificateChecks.KernelJ4Hub.finite_J
  exact Subgroup.eq_of_le_of_card_ge (stab_eq_Kz ▸ H_le_stabilizer_v) (by rw [card_H', card_Kz])

theorem stabilizer_v : stabilizer J v = H := stab_eq_Kz.trans H_eq_Kz.symm

theorem H_eq_Hj' : H = Hj := stabilizer_v.symm.trans stabilizer_v_eq_Hj'

theorem counting' : Nat.card ρH.ker = 2 ^ 11 ∧ ρH.range = P ∧ Nat.card P = 244823040 := by
  have : Finite J := CertificateChecks.KernelJ4Hub.finite_J
  have hk : 2 ^ 11 ≤ Nat.card ρH.ker := by
    rw [← card_N, ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe N_le_H).toEquiv]
    exact Subgroup.card_le_of_le N_le_ker_ρH
  have hr : Nat.card P ≤ Nat.card ρH.range := Subgroup.card_le_of_le P_le_range_ρH
  have hp := card_P_ge
  have hH := card_H'.le
  rw [← card_ker_mul_card_range ρH] at hH
  have hpos : 0 < Nat.card ρH.range := Nat.card_pos
  have e1 : Nat.card ρH.ker = 2 ^ 11 := by
    by_contra hne
    have : 2 ^ 11 + 1 ≤ Nat.card ρH.ker := by omega
    have := Nat.mul_le_mul this (hp.trans hr)
    omega
  rw [e1] at hH
  have e2 : Nat.card ρH.range = 244823040 := by omega
  have e3 : Nat.card P = 244823040 := by omega
  refine ⟨e1, ?_, e3⟩
  exact (Subgroup.eq_of_le_of_card_ge P_le_range_ρH (by rw [e2, e3])).symm

theorem ker_ρH' : ρH.ker = N.subgroupOf H := by
  refine (Subgroup.eq_of_le_of_card_ge N_le_ker_ρH ?_).symm
  rw [counting'.1, ← card_N, Nat.card_congr (Subgroup.subgroupOfEquivOfLe N_le_H).toEquiv]

theorem exists_mul_of_mem_H' {h : J} (hh : h ∈ H) : ∃ n ∈ N, ∃ k ∈ K, h = n * k := by
  obtain ⟨k, hk⟩ : ρH ⟨h, hh⟩ ∈ P := counting'.2.1 ▸ ⟨⟨h, hh⟩, rfl⟩
  rw [ρK_eq] at hk
  have hker : ⟨h, hh⟩ * (Subgroup.inclusion K_le_H k)⁻¹ ∈ ρH.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hk, mul_inv_cancel]
  rw [ker_ρH', Subgroup.mem_subgroupOf] at hker
  refine ⟨h * (k : J)⁻¹, hker, k, k.2, ?_⟩
  rw [inv_mul_cancel_right]

theorem conjOrbit_H_z' : conjOrbit H z = conjOrbit K z := by
  ext m
  constructor
  · rintro ⟨h, hh, rfl⟩
    obtain ⟨n, hn, c, hc, rfl⟩ := exists_mul_of_mem_H' hh
    refine ⟨c, hc, ?_⟩
    have hcz : c * z * c⁻¹ ∈ N := conj_mem_N_of_mem_K hc z_mem_N
    calc n * c * z * (n * c)⁻¹ = n * (c * z * c⁻¹) * n⁻¹ := by group
      _ = (c * z * c⁻¹) * n * n⁻¹ := by rw [CFSG.Quasithin.H13.J4Classes.N_comm' hn hcz]
      _ = c * z * c⁻¹ := by group
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c, K_le_H hc, rfl⟩

theorem ncard_class_e1' : (conjOrbit H z).ncard = 1771 := by
  rw [conjOrbit_H_z', ← CFSG.Quasithin.H13.J4Classes.η_one, conjOrbit_one]
  exact ncard_enum (fun i hi => bfsOK_lt orb1_ok hi) fun i hi k hk => bfsOK_ne orb1_ok hi hk

end CertificateChecks.KernelJ4Count

end
