module

public import Certificates.Kernel.Sporadic.Fi22.HypCBGlue
public import Certificates.Kernel.Sporadic.Fi22.Cent0
public import Certificates.Kernel.Sporadic.Fi22.Cent1
public import Certificates.Kernel.Sporadic.Fi22.Cent2
public import Certificates.Kernel.Sporadic.Fi22.Cent3
public import Certificates.Kernel.Sporadic.Fi22.Cent4
public import CFSG.Certificates.Kernel.Spor.CommCentSound
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Fi22Classes

public section

namespace CertificateChecks.KernelSpor.Fi22CI

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw.Orb CFSG.KC.CommBase CFSG.Monster.B.Fischer
open CFSG.ComponentClassification.M12Cover CFSG.Sporadic.Schreier CFSG.Sporadic.FischerOddCore
open CFSG.EvenSporadicStandard.HypOne.Fi22 CertificateChecks.KernelSpor.Fi22CB

theorem card_fix_conj {n : ℕ} (c r : Equiv.Perm (Fin n)) :
    (Finset.univ.filter fun p => (c * r * c⁻¹) p = p).card =
      (Finset.univ.filter fun p => r p = p).card := by
  refine Finset.card_equiv (c⁻¹ : Equiv.Perm (Fin n)) fun p => ?_
  rw [Finset.mem_filter, Finset.mem_filter, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
  simp only [Finset.mem_univ, true_and]
  constructor
  · intro h
    have := congrArg (c⁻¹ : Equiv.Perm (Fin n)) h
    simpa using this
  · intro h
    rw [h]
    simp

theorem prep_c {P Q : ℕ} {g h : Equiv.Perm (Fin 3510)} (hP : PRep 3510 12 P g)
    (hQ : PRep 3510 12 Q h) : PRep 3510 12 (Fi22X.c P Q) (g * h) :=
  prep_pcomp (by norm_num) hP hQ

theorem sq_ext {k : ℕ}
    (hk : k < 6) : fi22ExtRep k * fi22ExtRep k = 1 := by
  rw [← pow_two, ← orderOf_fi22ExtRep hk, pow_orderOf_eq_one]

theorem card_fix_mem_Ts
    {y : Equiv.Perm (Fin 3510)} (hy : y ∈ fi22R) (hyy : y * y = 1) (hy1 : y ≠ 1) :
    (Finset.univ.filter fun p => y p = p).card ∈ Ts := by
  have h2 : orderOf y = 2 := orderOf_eq_prime (by rw [pow_two]; exact hyy) hy1
  obtain ⟨r, hr, c, -, rfl⟩ := cover_R y hy h2
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hr
  have hj6 := List.mem_range.1 hj
  rw [card_fix_conj, ← fixCnt_eq (prep_ext hj6)]
  have h := tsAll
  rw [tsOK, allN_iff] at h
  exact memL_iff.1 (h j hj6)

theorem centerInv_of_centChk
    {M : ℕ → ℕ} {T : ℕ} (hl : lettersOK M T = true)
    {B : List BaseRec} {PF ZF DF RF : ℕ} (hc : centChk M B PF ZF DF RF = true)
    {t : Equiv.Perm (Fin 3510)} (ht : PRep 3510 12 T t) (htt : t * t = 1)
    {H : Subgroup (Equiv.Perm (Fin 3510))} (hPH : fi22P ≤ H) (hHR : H ≤ fi22R) (htR : t ∈ fi22R) :
    ∀ z ∈ H, z * z = 1 → z * t = t * z → (∀ y ∈ H, y * t = t * y → z * y = y * z) →
      z = 1 ∨ z = t := by
  intro x hxH hxx hxt hxc
  simp only [lettersOK, bAnd_eq, Bool.and_eq_true, Nat.beq_eq] at hl
  obtain ⟨hcn, e2, hp0, hp1, s0, s1, c0, c1⟩ := hl
  rw [allN_iff] at hcn
  obtain ⟨g₁, m1, r1⟩ := Fi22R1.exists_mem_P (hcn 0 (by norm_num)) hp0 s0
  obtain ⟨g₂, m2, r2⟩ := Fi22R1.exists_mem_P (hcn 1 (by norm_num)) hp1 s1
  have comm : ∀ {P : ℕ} {h : Equiv.Perm (Fin 3510)}, PRep 3510 12 P h →
      Fi22X.c P T = Fi22X.c T P → h * t = t * h :=
    fun hP e => prep_unique (prep_c hP ht) (by rw [e]; exact prep_c ht hP)
  have k1 := comm r1 c0
  have k2 := comm r2 c1
  have hL : ∀ z < 5, PRep 3510 12 (M z) (letterPerm g₁ g₂ t z) := by
    intro z hz
    interval_cases z
    · exact r1
    · exact r2
    · rw [e2]
      exact ht
    · exact prep_inv_of_permOK r1 hp0
    · exact prep_inv_of_permOK r2 hp1
  have hx : ∀ z < 5, Commute x (letterPerm g₁ g₂ t z) := by
    intro z hz
    have a1 : Commute x g₁ := hxc g₁ (hPH m1) k1
    have a2 : Commute x g₂ := hxc g₂ (hPH m2) k2
    interval_cases z
    · exact a1
    · exact a2
    · exact hxt
    · exact a1.inv_right
    · exact a2.inv_right
  have hτ : ∀ z < 5, Commute (letterPerm g₁ g₂ t 2) (letterPerm g₁ g₂ t z) := by
    intro z hz
    have a1 : Commute t g₁ := k1.symm
    have a2 : Commute t g₂ := k2.symm
    interval_cases z
    · exact a1
    · exact a2
    · exact Commute.refl t
    · exact a1.inv_right
    · exact a2.inv_right
  have hT : ∀ y : Equiv.Perm (Fin 3510), (y = x ∨ y = x * letterPerm g₁ g₂ t 2) → y ≠ 1 →
      (Finset.univ.filter fun p => y p = p).card ∈ Ts := by
    rintro y (rfl | rfl) hy1
    · exact card_fix_mem_Ts (hHR hxH) hxx hy1
    · change x * t ≠ 1 at hy1
      change (Finset.univ.filter fun p => (x * t) p = p).card ∈ Ts
      refine card_fix_mem_Ts (fi22R.mul_mem (hHR hxH) htR) ?_ hy1
      calc x * t * (x * t) = x * (t * x) * t := by group
        _ = x * (x * t) * t := by rw [hxt]
        _ = (x * x) * (t * t) := by group
        _ = 1 := by rw [hxx, htt, one_mul]
  exact eq_one_or_of_centFixOK (tI := 2) hL hx hτ hxx hT hc

theorem centerInv_P :
    ∀ k < 3, ∀ z ∈ fi22P, z * z = 1 → z * fi22ExtRep k = fi22ExtRep k * z →
      (∀ y ∈ fi22P, y * fi22ExtRep k = fi22ExtRep k * y → z * y = y * z) →
      z = 1 ∨ z = fi22ExtRep k := by
  intro k hk
  have htR := fi22P_le_R (CTUC_Fi22_all_extension_involutions_covered.1 k hk)
  have htt := sq_ext (k := k) (by omega)
  have ht := prep_ext (k := k) (by omega)
  interval_cases k
  · rw [show (21 : ℕ) + 0 = 21 from rfl] at ht
    exact centerInv_of_centChk Fi22CI0.lettersAll Fi22CI0.centAll ht htt le_rfl fi22P_le_R htR
  · rw [show (21 : ℕ) + 1 = 22 from rfl] at ht
    exact centerInv_of_centChk Fi22CI1.lettersAll Fi22CI1.centAll ht htt le_rfl fi22P_le_R htR
  · rw [show (21 : ℕ) + 2 = 23 from rfl] at ht
    exact centerInv_of_centChk Fi22CI2.lettersAll Fi22CI2.centAll ht htt le_rfl fi22P_le_R htR

theorem centerInv_R :
    ∀ k, 3 ≤ k → k < 5 → ∀ z ∈ fi22R, z * z = 1 → z * fi22ExtRep k = fi22ExtRep k * z →
      (∀ y ∈ fi22R, y * fi22ExtRep k = fi22ExtRep k * y → z * y = y * z) →
      z = 1 ∨ z = fi22ExtRep k := by
  intro k hk3 hk
  have htR := (CTUC_Fi22_all_extension_involutions_covered.2.1 (k - 3) (by omega)).1
  rw [show 3 + (k - 3) = k by omega] at htR
  have htt := sq_ext (k := k) (by omega)
  have ht := prep_ext (k := k) (by omega)
  obtain rfl | rfl : k = 3 ∨ k = 4 := by omega
  · rw [show (21 : ℕ) + 3 = 24 from rfl] at ht
    exact centerInv_of_centChk Fi22CI3.lettersAll Fi22CI3.centAll ht htt fi22P_le_R le_rfl htR
  · rw [show (21 : ℕ) + 4 = 25 from rfl] at ht
    exact centerInv_of_centChk Fi22CI4.lettersAll Fi22CI4.centAll ht htt fi22P_le_R le_rfl htR

end CertificateChecks.KernelSpor.Fi22CI

end
