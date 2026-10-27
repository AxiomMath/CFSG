module

public import Certificates.Kernel.J4Hub.FamGrp
public import Certificates.Kernel.J4Hub.Ord
public import Certificates.Kernel.J4Hub.Loc
import Certificates.Kernel.J4.Assemble
import Certificates.Kernel.J4.ChecksFix
import Certificates.Kernel.J4.ChecksPts
import Certificates.Kernel.J4.ChecksMFix
import CFSG.Certificates.Kernel.J4.KShapeSound
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelJ4Hub

open CFSG.KC.Ord CFSG.KS.Ord CFSG.KS.J4Hub CFSG.Sporadic.J4 CFSG.Certificates CFSG.Certificates.J4R

noncomputable abbrev Hxyt : Subgroup J := Subgroup.closure {X, Y, T}

theorem letJ_mem {x : ℕ × Bool} : letJ x ∈ Hxyt := by
  have hg : ∀ g, gen g ∈ Hxyt := by
    intro g
    unfold gen
    split_ifs
    · exact Subgroup.subset_closure (Set.mem_insert _ _)
    · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
    · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
  unfold letJ
  split_ifs
  · exact hg _
  · exact Hxyt.inv_mem (hg _)

theorem word_mem (l : List (ℕ × Bool)) : (l.map letJ).prod ∈ Hxyt := by
  apply Subgroup.list_prod_mem
  intro z hz
  obtain ⟨x, -, rfl⟩ := List.mem_map.1 hz
  exact letJ_mem

theorem bound_xyt : Finite Hxyt ∧ Nat.card Hxyt ≤ 86775571046077562880 := by
  obtain ⟨hf, hc⟩ := j4Ok_sound' CertificateChecks.KernelBounds.J4.j4_ok CertificateChecks.KernelBounds.J4.fix_ok
    CertificateChecks.KernelBounds.J4.pts_ok CertificateChecks.KernelBounds.J4.mfix_ok
    CFSG.Certificates.J4KShape.wrec_len (by decide +kernel)
    CertificateChecks.KernelBounds.j4_hN X Y T (mul_eq_one_iff_inv_eq.mpr T_inv) hR_XYT
  exact ⟨hf, hc.trans (Nat.le_of_eq (Nat.eq_of_beq_eq_true (by quickRfl)))⟩

theorem conj_parts : FM CFSG.KD.FamJ4.Cm * FM CFSG.KD.FamJ4.Ci = 1 ∧
    FM (CFSG.KD.FamJ4.RW 1) * FM CFSG.KD.FamJ4.Cm = FM CFSG.KD.FamJ4.Cm * FM (CFSG.KD.FamJ4.RW 206) ∧
    FM (CFSG.KD.FamJ4.RW 2) * FM CFSG.KD.FamJ4.Cm = FM CFSG.KD.FamJ4.Cm * FM (CFSG.KD.FamJ4.RW 238) := by
  have hA := conj_sound' (hnb := rfl) CFSG.KD.FamJ4.consts fam_v1 (fam_valid (by norm_num) (by norm_num))
    CFSG.KD.FamJ4.conjA
  have hB := conj_sound' (hnb := rfl) CFSG.KD.FamJ4.consts fam_v2 (fam_valid (by norm_num) (by norm_num))
    CFSG.KD.FamJ4.conjB
  exact ⟨hA.1, hA.2, hB.2⟩

@[expose] noncomputable def cU : GL (Fin 112) (ZMod 2) :=
  ⟨FM CFSG.KD.FamJ4.Cm, FM CFSG.KD.FamJ4.Ci, conj_parts.1, mul_eq_one_comm.1 conj_parts.1⟩

theorem conj_eq {u v : GL (Fin 112) (ZMod 2)} (h : (u : Matrix (Fin 112) (Fin 112) (ZMod 2)) * FM CFSG.KD.FamJ4.Cm =
      FM CFSG.KD.FamJ4.Cm * (v : Matrix (Fin 112) (Fin 112) (ZMod 2))) : u = cU * v * cU⁻¹ := by
  have h' : u * cU = cU * v := Units.ext h
  rw [← h', mul_inv_cancel_right]

noncomputable abbrev Hg : Subgroup (GL (Fin 112) (ZMod 2)) := Hxyt.map J.subtype

theorem J_le_conj : J ≤ Hg.map (MulAut.conj cU).toMonoidHom := by
  rw [Subgroup.closure_le]
  have hmem : ∀ {r : ℕ}, 0 < r → r < 239 → feJ r ∈ Hxyt → ∀ {u : GL (Fin 112) (ZMod 2)},
      (u : Matrix (Fin 112) (Fin 112) (ZMod 2)) * FM CFSG.KD.FamJ4.Cm =
        FM CFSG.KD.FamJ4.Cm * FM (CFSG.KD.FamJ4.RW r) → u ∈ Hg.map (MulAut.conj cU).toMonoidHom := by
    intro r h0 h1 hr u hu
    refine ⟨(feJ r : GL (Fin 112) (ZMod 2)), ⟨feJ r, hr, rfl⟩, ?_⟩
    rw [conj_eq (u := u) (v := (feJ r : GL (Fin 112) (ZMod 2))) (by rw [hu, ← feJ_val h0 h1])]
    rfl
  rintro _ (rfl | rfl)
  · exact hmem (by norm_num) (by norm_num) (ap_val ▸ word_mem apList)
      (by rw [gA_val', matA, fam_A]; exact conj_parts.2.1)
  · exact hmem (by norm_num) (by norm_num) (bp_val ▸ word_mem bpList)
      (by rw [gB_val', matB, fam_B]; exact conj_parts.2.2)

theorem finite_J : Finite J := by
  have := bound_xyt.1
  have : Finite (Hg.map (MulAut.conj cU).toMonoidHom) := inferInstance
  exact Finite.of_injective _ (Subgroup.inclusion_injective J_le_conj)

theorem card_J_le_xyt : Nat.card J ≤ Nat.card Hxyt := by
  have := bound_xyt.1
  calc Nat.card J ≤ Nat.card (Hg.map (MulAut.conj cU).toMonoidHom) :=
        Subgroup.card_le_of_le J_le_conj
    _ = Nat.card Hg := Subgroup.card_map_of_injective (MulAut.conj cU).injective
    _ = Nat.card Hxyt := Subgroup.card_map_of_injective J.subtype_injective

theorem card_J' : Nat.card J = 86775571046077562880 := by
  have hf := finite_J
  have hpos : 0 < Nat.card J := Nat.card_pos
  have h1 := card_J_le_xyt.trans bound_xyt.2
  exact le_antisymm h1 (Nat.le_of_dvd hpos card_dvd)

theorem xyt_top : Hxyt = ⊤ := by
  have hf := finite_J
  apply Subgroup.eq_top_of_card_eq
  apply le_antisymm (Subgroup.card_le_card_group _)
  exact card_J_le_xyt

end CertificateChecks.KernelJ4Hub

end
