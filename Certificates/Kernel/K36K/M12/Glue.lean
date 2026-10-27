module

public import Certificates.Kernel.K36K.M12.Checks
public import CFSG.Certificates.Kernel.K36K.Planes
public import CFSG.Certificates.Kernel.K36K.M12Exc

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelK36K.M12

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.MaxD2 CFSG.KD.K36K CFSG.KD.CoreD2K CFSG.Blueprint
  CFSG.ComponentClassification.PSL3Four CFSG.LocalAnalysis.UniquenessCase.UCK.Spor
  Certificates.K36Spor

theorem tab0 : TabRep (unpack 12 4 (GP 0)) (List.formPerm [0, 3] * List.formPerm [2, 9] *
    List.formPerm [4, 10] * List.formPerm [5, 11] : Equiv.Perm (Fin 12)) :=
  ⟨size_u _, fun x => by
    rw [get_u x.2]
    revert x
    decide +kernel⟩

theorem tab1 : TabRep (unpack 12 4 (GP 1)) (List.formPerm [0, 7, 8] * List.formPerm [1, 2, 3] *
    List.formPerm [4, 11, 10] * List.formPerm [5, 9, 6] : Equiv.Perm (Fin 12)) :=
  ⟨size_u _, fun x => by
    rw [get_u x.2]
    revert x
    decide +kernel⟩

theorem hyps0 : PHyps0 12 4 m12SData GP GPI GT GTI RE.G RE.GI RE.T RE.PL RE.POS RE.SRT RE.SRI
    RE.cnt 27 27 where
  hn := k_sz
  hgens := k_gens
  hh := k_eh
  hsl := by
    rw [← Nat.eq_of_beq_eq_true k_ek]
    exact k_esl
  hlen := by rw [Nat.eq_of_beq_eq_true k_ecnt]
  hcnt := by
    rw [Nat.eq_of_beq_eq_true k_ecnt]
    rfl
  hnab := k_nab
  hcen := k_cen
  hlines := k_lines

theorem planes_M12 : ∃ E : Subgroup ↥NativeSporadic.M12,
    Nat.card E = 27 ∧ ∀ A : Subgroup ↥NativeSporadic.M12, A ≤ E → CFSG.Open.IsElemAbelian 3 A →
      Nat.card A = 9 → PlaneOK A := by
  have hab : Subgroup.closure {(List.formPerm [0, 3] * List.formPerm [2, 9] *
      List.formPerm [4, 10] * List.formPerm [5, 11] : Equiv.Perm (Fin 12)),
      List.formPerm [0, 7, 8] * List.formPerm [1, 2, 3] * List.formPerm [4, 11, 10] *
        List.formPerm [5, 9, 6]} = NativeSporadic.M12 := rfl
  obtain ⟨e, L, he, hL, hGT, hgP, hLG, hzp, -, hvs, E, hEc, hEG, hE⟩ :=
    planes_three_idx hyps0 Nat.prime_three tab0 tab1
  rw [hab] at he hLG hEG
  refine ⟨E.subgroupOf NativeSporadic.M12,
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEG).toEquiv).trans (hEc.trans (by decide)),
    fun A hAE hAe hAc => ?_⟩
  set A0 : Subgroup (Equiv.Perm (Fin 12)) := A.map NativeSporadic.M12.subtype with hA0
  have hA0E : A0 ≤ E := by
    rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.mem_subgroupOf.1 (hAE hx)
  have hA0c : Nat.card A0 = m12SData.base.p ^ 2 := by
    rw [hA0, Subgroup.card_map_of_injective NativeSporadic.M12.subtype_injective, hAc]
    decide
  obtain ⟨i, hi, hYA⟩ := hE A0 hA0E (CFSG.Open.IsElemAbelian.map hAe _) hA0c
  have hAY : ∀ x : ↥NativeSporadic.M12, x ∈ A ↔ (x : Equiv.Perm (Fin 12)) ∈
      Subgroup.closure ({e 0, e (m12SData.ys.getD i 0)} : Set (Equiv.Perm (Fin 12))) := by
    intro x
    rw [hYA]
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x', hx', hxx⟩
      rwa [← Subtype.ext hxx]
  have hYG : Subgroup.closure ({e 0, e (m12SData.ys.getD i 0)} : Set (Equiv.Perm (Fin 12))) ≤
      NativeSporadic.M12 := by
    rw [Subgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨(he 0 (by decide)).2, (he _ (hvs i hi).1).2⟩
  have hAc' : Nat.card A = 3 ^ 2 := hAc
  have hi4 : i < 4 := hi
  interval_cases i
  · exact m12_exc_planeOK (X := mX0) k_sz hab (fun k hk => (he k hk).1) k_gp tab0 tab1
      (he 0 (by decide)).1 (he _ (hvs 0 hi).1).1 (he 0 (by decide)).2 (he _ (hvs 0 hi).1).2 hzp
      (hvs 0 hi).2.1 (hvs 0 hi).2.2 k0_exc k0_h
      (by
        rw [← Nat.eq_of_beq_eq_true k0_nk]
        exact k0_sl)
      (Nat.le_of_ble_eq_true k0_cnt) k0_N k0_fix3 k0_W k0_O hAY hAe hAc'
  · exact m12_exc_planeOK (X := mX1) k_sz hab (fun k hk => (he k hk).1) k_gp tab0 tab1
      (he 0 (by decide)).1 (he _ (hvs 1 hi).1).1 (he 0 (by decide)).2 (he _ (hvs 1 hi).1).2 hzp
      (hvs 1 hi).2.1 (hvs 1 hi).2.2 k1_exc k1_h
      (by
        rw [← Nat.eq_of_beq_eq_true k1_nk]
        exact k1_sl)
      (Nat.le_of_ble_eq_true k1_cnt) k1_N k1_fix3 k1_W k1_O hAY hAe hAc'
  · obtain ⟨Γ, hΓL, habΓ, hΓ⟩ :=
      gen_sound k_sz (fun k hk => (he k hk).1) hL hGT hgP tab0 tab1 k_cent k_words 0 (by decide)
    exact planeOK_of_gen_facts hAY hYG (fun g hg => hLG g (hΓL hg))
      ((Subgroup.closure_le _).2 habΓ) hΓ
  · obtain ⟨Γ, hΓL, habΓ, hΓ⟩ :=
      gen_sound k_sz (fun k hk => (he k hk).1) hL hGT hgP tab0 tab1 k_cent k_words 1 (by decide)
    exact planeOK_of_gen_facts hAY hYG (fun g hg => hLG g (hΓL hg))
      ((Subgroup.closure_le _).2 habΓ) hΓ

end CertificateChecks.KernelK36K.M12

end
