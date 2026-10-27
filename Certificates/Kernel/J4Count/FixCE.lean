
module

public import Certificates.Kernel.J4Count.FixCEBase1

public import Certificates.Kernel.J4Count.Cent3
public import Certificates.Kernel.J4Count.FixC
public import Certificates.Kernel.J4Count.Suborb

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Count.FixCE

open CFSG.Sporadic.J4 CFSG.Sporadic.J4Schreier CFSG.Sporadic.J4Schreier.NoComp MulAction
open CFSG.Sporadic.SmallF2 (toVecD)
open CFSG.Sporadic.GLQ CFSG.KC.J4FixCE CFSG.KD.J4FixCE
open CFSG.KC.J4FixC (nth codeL toI walkK letM sN)
open CFSG.KC.J4Q (vecJ mulJ)
open CFSG.KD.J4Q (c rm one A B Bi)
open CertificateChecks.KernelSporSch CertificateChecks.KernelJ4Count
open CFSG.Quasithin.J4M2 (cE)

section Sizes

theorem card_Lj_mul (l : ℕ) : Nat.card (FixC.Lj l) * sz l = 501397585920 := by
  have : Finite H := finite_H
  have e := Subgroup.card_mul_index (MulAction.stabilizer H (qv l))
  rw [MulAction.index_stabilizer, card_H'] at e
  rw [FixC.card_Lj_stab]
  exact e

theorem nine_dvd : 9 ∣ Nat.card (FixC.Lj 3) := by
  have : Finite J := FixC.finite_J
  have hP : CFSG.KC.J4FixC.nth 0 CFSG.KD.J4FixC.NP 3 = 9 := by decide +kernel
  have h := FixC.card_PJ (l := 3) (by norm_num) (by rw [hP]; norm_num)
  have hd := Subgroup.card_dvd_of_le (FixC.PJ_le (l := 3) (by norm_num))
  rw [h, hP] at hd
  exact hd

theorem sz_two_three : sz 2 = 82575360 ∧ sz 3 = 54405120 := by
  obtain ⟨s0, s1, s4, s5, s6⟩ := sizes
  have ne : ∀ {l m : ℕ}, l < 7 → m < 7 → l ≠ m → ∀ {x : ℕ}, sz m = x → sz l ≠ x :=
    fun hl hm hlm x hx h => sz_ne hl hm hlm (h.trans hx.symm)
  have h3 : sz 3 ≠ 82575360 := by
    intro h
    have e := card_Lj_mul 3
    rw [h] at e
    have e2 : Nat.card (FixC.Lj 3) = 6072 := by
      have e3 : Nat.card (FixC.Lj 3) = 501397585920 / 82575360 := by
        rw [← e, Nat.mul_div_cancel _ (by norm_num)]
      rw [e3]
    have := nine_dvd
    rw [e2] at this
    norm_num at this
  exact sizes_rest _ (sz_mem (by norm_num)) _ (sz_mem (by norm_num))
    (ne (by norm_num) (by norm_num) (by norm_num) s0) (ne (by norm_num) (by norm_num) (by norm_num) s1)
    (ne (by norm_num) (by norm_num) (by norm_num) s4) (ne (by norm_num) (by norm_num) (by norm_num) s5)
    (ne (by norm_num) (by norm_num) (by norm_num) s6) (ne (by norm_num) (by norm_num) (by norm_num) s0)
    (ne (by norm_num) (by norm_num) (by norm_num) s1) (ne (by norm_num) (by norm_num) (by norm_num) s4)
    (ne (by norm_num) (by norm_num) (by norm_num) s5) (ne (by norm_num) (by norm_num) (by norm_num) s6)
    (sz_ne (by norm_num) (by norm_num) (by norm_num)) h3

theorem hsz : ∀ l < 7, (orbit H (qv l)).ncard = SZ.getD l 0 := by
  obtain ⟨s0, s1, s4, s5, s6⟩ := sizes
  obtain ⟨s2, s3⟩ := sz_two_three
  intro l hl
  interval_cases l
  · exact s0
  · exact s1
  · exact s2
  · exact s3
  · exact s4
  · exact s5
  · exact s6

theorem hcov : ∀ w ∈ orbit J v, ∃ l < 7, w ∈ orbit H (qv l) := fun _ hw => cover_qv hw

end Sizes

section Fix

theorem card_fix_cE_le : Nat.card {w : Row // w ∈ orbit J v ∧ cE • w = w} ≤ 737 :=
  FixC.card_fix_le_of hcov hsz cE_mem_H cE_pow_three' card_cent_N card_cent_H_le

end Fix

section Points

section W77

end W77

section Tree

end Tree

section All

open scoped Classical

theorem fix_cE_eq : ∀ w, w ∈ orbit J v ∧ cE • w = w → w ∈ ptSet :=
  (FixC.fix_eq_of_card hcov hsz cE_mem_H cE_pow_three' card_cent_N card_cent_H_le ptSet ptSet_fixed
    card_ptSet).1

theorem card_fix_cE : Nat.card {w : Row // w ∈ orbit J v ∧ cE • w = w} = 737 :=
  (FixC.fix_eq_of_card hcov hsz cE_mem_H cE_pow_three' card_cent_N card_cent_H_le ptSet ptSet_fixed
    card_ptSet).2

theorem card_stab_eq' :
    Nat.card ↥(stabilizer ↥(Subgroup.centralizer ({cE} : Set J)) v) =
      Nat.card ↥(Subgroup.centralizer {cE} ⊓ H) := by
  set C := Subgroup.centralizer ({cE} : Set J)
  have hsub : (C ⊓ H).subgroupOf C = stabilizer ↥C v := by
    ext ⟨x, hx⟩
    rw [Subgroup.mem_subgroupOf, mem_stabilizer_iff]
    constructor
    · rintro ⟨-, hxH⟩
      have : x ∈ stabilizer J v := by rw [stabilizer_v]; exact hxH
      exact this
    · intro h
      refine ⟨hx, ?_⟩
      have : x ∈ stabilizer J v := h
      rwa [stabilizer_v] at this
  rw [← hsub]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv

theorem orbit_card_le' : (orbit ↥(Subgroup.centralizer ({cE} : Set J)) v).ncard ≤ 77 := by
  set C := Subgroup.centralizer ({cE} : Set J) with hC
  have hOsub : ∀ p ∈ orbit ↥C v, p ∈ ptSet := by
    rintro _ ⟨⟨g, hg⟩, rfl⟩
    refine fix_cE_eq _ ⟨⟨g, rfl⟩, ?_⟩
    change cE • (g • v) = g • v
    rw [← mul_smul, (Subgroup.mem_centralizer_singleton_iff.1 hg).symm, mul_smul, cE_smul_v]
  have hS : ∀ i < 77, ptR i ∈ orbit ↥C v := by
    intro i hi
    obtain ⟨g, hgC, hg⟩ := ce_reach (by omega : i < 737)
    have e : ptRoot i = 0 := by simp [ptRoot, hi]
    rw [e, ptR_zero] at hg
    exact ⟨⟨g, hgC⟩, hg⟩
  have hsplit : ∀ q ∈ ptSet, ∃ i, i < 737 ∧ ptR i = q := fun q hq => by
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hq
    exact ⟨i, Finset.mem_range.1 hi, rfl⟩
  by_cases hT : ∃ i, 77 ≤ i ∧ i < 737 ∧ ptR i ∈ orbit ↥C v
  · exfalso
    obtain ⟨i, hi77, hi737, ⟨⟨k, hkC⟩, hki⟩⟩ := hT
    have hki' : k • v = ptR i := hki
    have hfull : ∀ q ∈ ptSet, q ∈ orbit ↥C v := by
      intro q hq
      obtain ⟨j, hj, rfl⟩ := hsplit q hq
      by_cases hj77 : j < 77
      · exact hS j hj77
      · obtain ⟨g', hg'C, hg'⟩ := ce_reach hj
        obtain ⟨g, hgC, hg⟩ := ce_reach hi737
        have r1 : ptRoot j = 77 := by simp [ptRoot, hj77]
        have r2 : ptRoot i = 77 := by simp [ptRoot]; omega
        rw [r1] at hg'
        rw [r2] at hg
        refine ⟨⟨g' * g⁻¹ * k, Subgroup.mul_mem _ (Subgroup.mul_mem _ hg'C
          (Subgroup.inv_mem _ hgC)) hkC⟩, ?_⟩
        change (g' * g⁻¹ * k) • v = ptR j
        rw [mul_smul, mul_smul, hki', ← hg, inv_smul_smul, hg']
    have heq : orbit ↥C v = ↑ptSet :=
      Set.Subset.antisymm (fun p hp => Finset.mem_coe.2 (hOsub p hp))
        (fun p hp => hfull p (Finset.mem_coe.1 hp))
    have hn : (orbit ↥C v).ncard = 737 := by
      rw [heq, Set.ncard_coe_finset, card_ptSet]
    have h1 := card_eq_orbit_mul_stab'
    rw [hn] at h1
    have h2 : 737 ∣ Nat.card J := (Dvd.intro _ h1.symm).trans (Subgroup.card_subgroup_dvd_card C)
    rw [CertificateChecks.KernelJ4Hub.card_J'] at h2
    exact absurd h2 (by norm_num)
  · push Not at hT
    have hsub : orbit ↥C v ⊆ ↑((Finset.range 77).image ptR) := by
      intro p hp
      obtain ⟨k, hk, rfl⟩ := hsplit _ (hOsub p hp)
      by_cases hk77 : k < 77
      · exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨k, Finset.mem_range.2 hk77, rfl⟩)
      · exact absurd hp (hT k (by omega) hk)
    calc (orbit ↥C v).ncard ≤ (↑((Finset.range 77).image ptR) : Set Row).ncard :=
          Set.ncard_le_ncard hsub (Finset.finite_toSet _)
      _ = ((Finset.range 77).image ptR).card := Set.ncard_coe_finset _
      _ ≤ 77 := by simpa using Finset.card_image_le (s := Finset.range 77) (f := ptR)

theorem card_centralizer_cE_le' :
    Nat.card ↥(Subgroup.centralizer ({cE} : Set J)) ≤ 2661120 := by
  rw [card_eq_orbit_mul_stab', card_stab_eq']
  calc (orbit ↥(Subgroup.centralizer ({cE} : Set J)) v).ncard *
        Nat.card ↥(Subgroup.centralizer {cE} ⊓ H) ≤ 77 * 34560 :=
        Nat.mul_le_mul orbit_card_le' card_cent_H_le
    _ = 2661120 := by norm_num

end All

end Points

end CertificateChecks.KernelJ4Count.FixCE

end
