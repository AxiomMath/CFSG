module

public import Certificates.Kernel.Sporadic.Suz.Cent25610C0
public import Certificates.Kernel.Sporadic.Suz.Cent25610C1
public import Certificates.Kernel.Sporadic.Suz.Umov25610
public import CFSG.Certificates.Kernel.Spor.CommCentSound
public import CFSG.Certificates.Kernel.Spor.MulHSound
public import CFSG.Certificates.Kernel.Enum.ZCSound
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Suz

public section

namespace CertificateChecks.KernelSpor.SuzCI

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KC.CommBase
open CFSG.Sporadic.SuzOddCore CFSG.EvenSporadicStandard.HypOne.Suz

@[expose] def letterPerm (g₁ g₂ t : Equiv.Perm (Fin 1782)) (z : ℕ) : Equiv.Perm (Fin 1782) :=
  [g₁, g₂, t, g₁⁻¹, g₂⁻¹].getD z 1

theorem prep_c {P Q : ℕ} {g h : Equiv.Perm (Fin 1782)} (hP : PRep 1782 11 P g)
    (hQ : PRep 1782 11 Q h) : PRep 1782 11 (c P Q) (g * h) :=
  prep_pcomp (by norm_num) hP hQ

theorem prep_tP {i : ℕ} (hi : i < 4) :
    PRep 1782 11 (SuzTP i) (suzInv i) := by
  have h := rep_suzInv hi
  rw [(OddCore.rep_facts hi).1] at h
  exact prep_of_rep h

theorem exists_mem_M
    {a ai : ℕ} (hc : cn a = true) (hp : permOK 1782 11 (mask 11) (1782 * 11) a ai = true)
    (hs : Suz2306.sift a = true) : ∃ g ∈ suzM, PRep 1782 11 a g ∧ PRep 1782 11 ai g⁻¹ := by
  obtain ⟨g, hg, hgi⟩ := CFSG.KC.EnumSound.permOK_perm hp
  refine ⟨g, (inM_iff (rep_unpack hg)).1 ?_, hg, hgi⟩
  rw [OddCore.inM_eq rfl hc]
  exact hs

theorem card_fix_conj (c r : Equiv.Perm (Fin 1782)) :
    (Finset.univ.filter fun p => (c * r * c⁻¹) p = p).card =
      (Finset.univ.filter fun p => r p = p).card := by
  refine Finset.card_equiv (c⁻¹ : Equiv.Perm (Fin 1782)) fun p => ?_
  rw [Finset.mem_filter, Finset.mem_filter, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
  simp only [Finset.mem_univ, true_and]
  constructor
  · intro h
    have := congrArg (c⁻¹ : Equiv.Perm (Fin 1782)) h
    simpa using this
  · intro h
    rw [h]
    simp

theorem card_fix_mem_Ts
    {y : Equiv.Perm (Fin 1782)} (hy : y ∈ suzM) (hyy : y * y = 1) (hy1 : y ≠ 1) :
    (Finset.univ.filter fun p => y p = p).card ∈ Ts := by
  have h2 : orderOf y = 2 := orderOf_eq_prime (by rw [pow_two]; exact hyy) hy1
  obtain ⟨r, hr, c, -, rfl⟩ := cover_suzM y hy h2
  rw [card_fix_conj]
  have h := tsAll
  rw [tsOK, allN_iff] at h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [← fixCnt_eq (prep_tP (i := 0) (by norm_num))]
    exact memL_iff.1 (h 0 (by norm_num))
  · rw [← fixCnt_eq (prep_tP (i := 1) (by norm_num))]
    exact memL_iff.1 (h 1 (by norm_num))

theorem centerInv_of_centChk
    {M : ℕ → ℕ} {T : ℕ} (hl : lettersOK M T = true)
    {B : List BaseRec} {PF ZF DF RF : ℕ} (hc : centChk M B PF ZF DF RF = true)
    {t : Equiv.Perm (Fin 1782)} (ht : PRep 1782 11 T t) (htt : t * t = 1) (htM : t ∈ suzM) :
    ∀ z ∈ suzM, z * z = 1 → z * t = t * z → (∀ y ∈ suzM, y * t = t * y → z * y = y * z) →
      z = 1 ∨ z = t := by
  intro x hxM hxx hxt hxc
  simp only [lettersOK, bAnd_eq, Bool.and_eq_true, Nat.beq_eq] at hl
  obtain ⟨hcn, e2, hp0, hp1, s0, s1, c0, c1⟩ := hl
  rw [allN_iff] at hcn
  obtain ⟨g₁, m1, r1, -⟩ := exists_mem_M (hcn 0 (by norm_num)) hp0 s0
  obtain ⟨g₂, m2, r2, -⟩ := exists_mem_M (hcn 1 (by norm_num)) hp1 s1
  have comm : ∀ {P : ℕ} {h : Equiv.Perm (Fin 1782)}, PRep 1782 11 P h →
      c P T = c T P → h * t = t * h :=
    fun hP e => prep_unique (prep_c hP ht) (by rw [e]; exact prep_c ht hP)
  have k1 := comm r1 c0
  have k2 := comm r2 c1
  have hL : ∀ z < 5, PRep 1782 11 (M z) (letterPerm g₁ g₂ t z) := by
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
    have a1 : Commute x g₁ := hxc g₁ m1 k1
    have a2 : Commute x g₂ := hxc g₂ m2 k2
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
  have hT : ∀ y : Equiv.Perm (Fin 1782), (y = x ∨ y = x * letterPerm g₁ g₂ t 2) → y ≠ 1 →
      (Finset.univ.filter fun p => y p = p).card ∈ Ts := by
    rintro y (rfl | rfl) hy1
    · exact card_fix_mem_Ts hxM hxx hy1
    · change x * t ≠ 1 at hy1
      change (Finset.univ.filter fun p => (x * t) p = p).card ∈ Ts
      refine card_fix_mem_Ts (suzM.mul_mem hxM htM) ?_ hy1
      calc x * t * (x * t) = x * (t * x) * t := by group
        _ = x * (x * t) * t := by rw [hxt]
        _ = (x * x) * (t * t) := by group
        _ = 1 := by rw [hxx, htt, one_mul]
  exact eq_one_or_of_centFixOK (tI := 2) hL hx hτ hxx hT hc

theorem centerInv_rep :
    ∀ i < 2, ∀ z ∈ suzM, z * z = 1 → z * suzInv i = suzInv i * z →
      (∀ y ∈ suzM, y * suzInv i = suzInv i * y → z * y = y * z) → z = 1 ∨ z = suzInv i := by
  intro i hi
  have htt := suzInv_sq (i := i) (by omega)
  have ht := prep_tP (i := i) (by omega)
  interval_cases i
  · exact centerInv_of_centChk SuzCI0.lettersAll SuzCI0.centAll ht htt
      ((inM_iff (rep_suzInv (by norm_num))).1 invT_check.2.1)
  · exact centerInv_of_centChk SuzCI1.lettersAll SuzCI1.centAll ht htt
      ((inM_iff (rep_suzInv (by norm_num))).1 invT_check.2.2.1)

theorem exists_commuting_of_umovK
    {L T T' : ℕ} (h : umovK L T T' = true) {t t' : Equiv.Perm (Fin 1782)}
    (ht : PRep 1782 11 T t) (ht' : PRep 1782 11 T' t') :
    ∃ x ∈ suzM, (x * t * x⁻¹) * t' = t' * (x * t * x⁻¹) := by
  simp only [umovK, bAnd_eq, Bool.and_eq_true, CFSG.KS.MulH.strictB_eq'', Nat.beq_eq] at h
  obtain ⟨hL, -, pL, sL, -, -, e⟩ := h
  obtain ⟨g, hg, rg, rgi⟩ := exists_mem_M hL pL sL
  have rC := prep_c (prep_c rg ht) rgi
  exact ⟨g, hg, prep_unique (prep_c rC ht') (by rw [e]; exact prep_c ht' rC)⟩

theorem exists_commuting_rep :
    ∀ i < 2, ∀ j < 4,
      ∃ x ∈ suzM, (x * suzInv i * x⁻¹) * suzInv j = suzInv j * (x * suzInv i * x⁻¹) := by
  intro i hi j hj
  exact exists_commuting_of_umovK (allN_spec (allN_spec umAll i hi) j hj) (prep_tP (by omega))
    (prep_tP hj)

end CertificateChecks.KernelSpor.SuzCI

end
