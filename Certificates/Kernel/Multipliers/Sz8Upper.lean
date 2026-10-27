module

public import Certificates.Kernel.Multipliers.Sz8Rels
public import Certificates.Kernel.Multipliers.Quot
public import Certificates.Kernel.Misc.Coset.C10008
public import Certificates.Kernel.Misc.Coset.XSz8HA.All
public import CFSG.LieType.Multipliers.KernelStructure

set_option maxRecDepth 100000

public section

namespace CertificateChecks.KernelSz8

open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.Sz8 CFSG.CosetTable CFSG.KC.MiscCoset
  CFSG.Certificates.CosetEnumeration CertificateChecks.KernelMult

noncomputable def zHom : Multiplicative (ZMod 2) × Multiplicative (ZMod 2) →* PG 2 coverWs :=
  MonoidHom.noncommCoprod (powHom (z 4) 2 (z_sq (by omega) (by omega)))
    (powHom (z 5) 2 (z_sq (by omega) (by omega)))
    fun _ _ => Commute.pow_pow
      (Commute.symm (Subgroup.mem_center_iff.mp (z_central (k := 4) (by omega)) (z 5))) _ _

theorem card_le : Finite (PG 2 coverWs) ∧ Nat.card (PG 2 coverWs) ≤ 116480 := by
  have hc : zHom.range ≤ Subgroup.center (PG 2 coverWs) := by
    rintro _ ⟨⟨i, j⟩, rfl⟩
    simp only [zHom, powHom, MonoidHom.noncommCoprod_apply, MonoidHom.coe_mk, OneHom.coe_mk]
    exact mul_mem (pow_mem (z_central (by omega)) _) (pow_mem (z_central (by omega)) _)
  have : zHom.range.Normal := Subgroup.normal_of_le_center hc
  have : Finite zHom.range := Set.finite_range _ |>.to_subtype
  obtain ⟨f₁, c₁⟩ := CertificateChecks.KernelMiscCoset.C10008.card_le
  have h4 : z 4 ∈ zHom.range := ⟨(Multiplicative.ofAdd 1, 1), by
    simp only [zHom, powHom, MonoidHom.noncommCoprod_apply, MonoidHom.coe_mk, OneHom.coe_mk,
      toAdd_ofAdd, toAdd_one, ZMod.val_zero, pow_zero, mul_one]
    exact pow_one (z 4)⟩
  have h5 : z 5 ∈ zHom.range := ⟨(1, Multiplicative.ofAdd 1), by
    simp only [zHom, powHom, MonoidHom.noncommCoprod_apply, MonoidHom.coe_mk, OneHom.coe_mk,
      toAdd_ofAdd, toAdd_one, ZMod.val_zero, pow_zero, one_mul]
    exact pow_one (z 5)⟩
  obtain ⟨f, c⟩ := card_le_mul_of_relators rels coverWs zHom.range (fun r hr => by
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hr
    have hk' : k < 6 := by
      have : rels.length = 6 := by decide +kernel
      omega
    have key : z k ∈ zHom.range := by
      rcases Nat.lt_or_ge k 4 with h | h
      · rw [z_eq_one h]
        exact Subgroup.one_mem _
      · rcases Nat.lt_or_ge k 5 with h' | h'
        · rw [show k = 4 by omega]
          exact h4
        · rw [show k = 5 by omega]
          exact h5
    simpa only [z, List.getD_eq_getElem _ _ hk] using key)
  have h2 : Nat.card zHom.range ≤ 4 :=
    (Nat.card_le_card_of_surjective _ (MonoidHom.rangeRestrict_surjective _)).trans
      (by simp [Nat.card_eq_fintype_card])
  exact ⟨f, c.trans ((Nat.mul_le_mul c₁ h2).trans (by norm_num))⟩

theorem hR : codes rels = CFSG.KAct.XSz8H.R := by decide +kernel
theorem hW : codes ((List.finRange 2).map fun i => (i, false) :: wWord i) ++
    codes ([] : List (List (Fin 2 × Bool))) = CFSG.KAct.XSz8H.W := by decide +kernel
theorem hC : kerWords.map (fun p => p.1.map letterCode) = [CFSG.KAct.XSz8H.C0,
    CFSG.KAct.XSz8H.C1, CFSG.KAct.XSz8H.C2, CFSG.KAct.XSz8H.C3, CFSG.KAct.XSz8H.C4,
    CFSG.KAct.XSz8H.C5] := by decide +kernel

theorem two_dvd : ∀ u, (u, 2) ∈ kerWords →
    2 ∣ orderOf (PresentedGroup.mk (wordSet (coverWords rels wWord)) (FreeGroup.mk u)) := by
  have hpt := Act.coverPointOK_sound rels wWord ([] : List (List (Fin 2 × Bool))) hR hW
    (Act.coverPointOK_of_allR CFSG.KAct.XSz8H.all)
  intro u hu
  have hm : u.map letterCode ∈ [CFSG.KAct.XSz8H.C0, CFSG.KAct.XSz8H.C1, CFSG.KAct.XSz8H.C2,
      CFSG.KAct.XSz8H.C3, CFSG.KAct.XSz8H.C4, CFSG.KAct.XSz8H.C5] := by
    rw [← hC]
    exact List.mem_map.2 ⟨(u, 2), hu, rfl⟩
  have hc : Act.cycleOK CFSG.KAct.XSz8H.A (Nat.add 2 2) (u.map letterCode) 2 = true := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with e | e | e | e | e | e <;> rw [e]
    · exact CFSG.KAct.XSz8H.cyc0
    · exact CFSG.KAct.XSz8H.cyc1
    · exact CFSG.KAct.XSz8H.cyc2
    · exact CFSG.KAct.XSz8H.cyc3
    · exact CFSG.KAct.XSz8H.cyc4
    · exact CFSG.KAct.XSz8H.cyc5
  have := Act.cycleOK_sound (coverWords rels wWord ++ []) rfl (by norm_num) hpt u hc
  rw [List.append_nil] at this
  exact this

end CertificateChecks.KernelSz8

end
