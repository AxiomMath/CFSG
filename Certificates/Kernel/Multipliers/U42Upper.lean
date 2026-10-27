module

public import Certificates.Kernel.Multipliers.U42Rels
public import Certificates.Kernel.Multipliers.Quot
public import Certificates.Kernel.Misc.Coset.C10011
public import Certificates.Kernel.Misc.Coset.XU42HA.All

public section

namespace CertificateChecks.KernelU42

open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.U42 CFSG.CosetTable CFSG.KC.MiscCoset
  CFSG.Certificates.CosetEnumeration CertificateChecks.KernelMult

theorem card_le : Finite (PG 2 coverWs) ∧ Nat.card (PG 2 coverWs) ≤ 51840 := by
  have hc : z 4 ∈ Subgroup.center (PG 2 coverWs) := z_central (by omega)
  have : (Subgroup.zpowers (z 4)).Normal :=
    Subgroup.normal_of_le_center ((Subgroup.zpowers_le).mpr hc)
  have hfo : IsOfFinOrder (z 4) := isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by norm_num, z4_sq⟩
  have : Finite (Subgroup.zpowers (z 4)) := finite_zpowers.mpr hfo
  obtain ⟨f₁, c₁⟩ := CertificateChecks.KernelMiscCoset.C10011.card_le
  obtain ⟨f, c⟩ := card_le_mul_of_relators rels coverWs (Subgroup.zpowers (z 4)) (fun r hr => by
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hr
    have hk' : k < 5 := by simpa [rels] using hk
    have key : z k ∈ Subgroup.zpowers (z 4) := by
      rcases Nat.lt_or_ge k 4 with h4 | h4
      · rw [z_eq_one h4]
        exact Subgroup.one_mem _
      · rw [show k = 4 by omega]
        exact Subgroup.mem_zpowers _
    simpa only [z, List.getD_eq_getElem _ _ hk] using key)
  have h2 : Nat.card (Subgroup.zpowers (z 4)) ≤ 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_le_of_pow_eq_one (by norm_num) z4_sq
  exact ⟨f, c.trans ((Nat.mul_le_mul c₁ h2).trans (by norm_num))⟩

theorem hR : codes rels = CFSG.KAct.XU42H.R := by decide +kernel
theorem hW : codes ((List.finRange 2).map fun i => (i, false) :: commWords (coverPairs i)) ++
    codes ([] : List (List (Fin 2 × Bool))) = CFSG.KAct.XU42H.W := by decide +kernel
theorem hC : relZ.map letterCode = CFSG.KAct.XU42H.C0 := by decide +kernel

theorem bounds : Finite (PG 2 (coverWords rels fun i => commWords (coverPairs i))) ∧
    Nat.card (PG 2 (coverWords rels fun i => commWords (coverPairs i))) ≤ 51840 ∧
    2 ∣ orderOf (PresentedGroup.mk {r : FreeGroup (Fin 2) | r ∈ (coverWords rels
      fun i => commWords (coverPairs i)).map FreeGroup.mk} (FreeGroup.mk relZ)) := by
  obtain ⟨f, c⟩ := card_le
  have hpt := Act.coverPointOK_sound rels (fun i => commWords (coverPairs i))
    ([] : List (List (Fin 2 × Bool))) hR hW
    (Act.coverPointOK_of_allR CFSG.KAct.XU42H.all)
  have hc : Act.cycleOK CFSG.KAct.XU42H.A (Nat.add 2 2) (relZ.map letterCode) 2 = true := by
    rw [hC]
    exact CFSG.KAct.XU42H.cyc0
  have := Act.cycleOK_sound ((coverWords rels fun i => commWords (coverPairs i)) ++ []) rfl
    (by norm_num) hpt relZ hc
  rw [List.append_nil] at this
  exact ⟨f, c, this⟩

end CertificateChecks.KernelU42

end
