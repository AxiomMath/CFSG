
module

public import Certificates.Kernel.SolMax.SixGen
public import CFSG.Certificates.Kernel.SolMaxSixGenSound
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSixGenBase

public section

namespace CertificateChecks.KernelSolMax.SixGen

open CFSG Subgroup Equiv
open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.ComponentClassification.SolMax.SixGen CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim
  CFSG.KS.PEnum

theorem ce_enum : enumOK 9 cgTabs (penumRec 9 4 CE.cnt CE.T CE.PL) = true ∧
    (penumRec 9 4 CE.cnt CE.T CE.PL).tabs.size = 288 := by
  obtain ⟨a1, a2, a3⟩ := (by simpa only [bAnd_iff] using k_hd :
    gensK cgTabs 9 4 CE.k CE.G = true ∧ Nat.beq CE.cnt 288 = true ∧
      penumHdK (pidn 9 4) CE.cnt 288 CE.T CE.PL = true)
  have e : CE.cnt = 288 := Nat.eq_of_beq_eq_true a2
  have hs := penumK_left_sound (cap := 288) (by decide) (gensOK_of a1) a3
    (fun i hi => penumSl_spec k_sl i (Nat.zero_le _) (by omega) hi)
  refine ⟨hs.2, ?_⟩
  rw [penumRec_eq, Array.size_ofFn, e]

theorem entry_wit {e : Swaps × List Swaps} (he : e ∈ entries) :
    ∃ T S : List (List ℕ), ∃ C : List ℕ, entryWitK e T S C = true := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
  have h := k_wit
  unfold sixGenWitK at h
  have h2 := List.all_eq_true.1 h i (List.mem_range.2 hi)
  rw [List.getD_eq_getElem _ _ hi] at h2
  exact ⟨_, _, _, h2⟩

theorem fact22257 {u v : Perm (Fin 9)} (hu2 : u * u = 1) (hv2 : v * v = 1) (huv : u * v = v * u)
    (hu6 : u.support.card = 6) :
    alternatingGroup (Fin 9) ≤ (centralizer {u} ⊓ alternatingGroup (Fin 9)) ⊔
      (centralizer {v} ⊓ alternatingGroup (Fin 9)) ⊔
      (centralizer {u * v} ⊓ alternatingGroup (Fin 9)) := by
  classical
  have hcov := k_cov
  rw [Bool.and_eq_true] at hcov
  obtain ⟨hcg, hcov⟩ := hcov
  obtain ⟨hok, hsz⟩ := ce_enum
  set u₀' := permOf u₀ with hu₀'
  have hEC := enumerates_of_list hok
  have hCle : closure {a | ∃ l ∈ centGens, a = permOf l} ≤ centralizer {u₀'} := by
    rw [closure_le]
    rintro a ⟨l, hl, rfl⟩
    have h1 := List.all_eq_true.1 hcg l hl
    exact mem_centralizer_singleton_iff.mpr (commute_of_commutes h1)
  have hCeq : closure {a | ∃ l ∈ centGens, a = permOf l} = centralizer {u₀'} := by
    refine Subgroup.eq_of_le_of_card_ge hCle ?_
    rw [card_centralizer_u₀, hEC.card, Array.length_toList, hsz]
  have hct : u.cycleType = u₀'.cycleType := by
    rw [cycleType_of_mul_self (k := 3) hu2 (by norm_num) hu6,
      cycleType_of_mul_self (k := 3) u₀_mul_self (by norm_num) card_support_u₀]
  obtain ⟨π, hπ⟩ := isConj_iff.mp (Perm.isConj_iff_cycleType_eq.mpr hct)
  set v' := π * v * π⁻¹ with hv'def
  have hv'C : v' ∈ centralizer {u₀'} := by
    rw [mem_centralizer_singleton_iff, ← hπ, hv'def]
    calc π * v * π⁻¹ * (π * u * π⁻¹) = π * (v * u) * π⁻¹ := by group
      _ = π * (u * v) * π⁻¹ := by rw [huv]
      _ = π * u * π⁻¹ * (π * v * π⁻¹) := by group
  have hv'2 : v' * v' = 1 := by
    rw [hv'def]
    calc π * v * π⁻¹ * (π * v * π⁻¹) = π * (v * v) * π⁻¹ := by group
      _ = 1 := by rw [hv2]; group
  rw [← hCeq] at hv'C
  obtain ⟨t, ht, htv⟩ := hEC.complete v' hv'C
  unfold coverK at hcov
  have h1 := List.all_eq_true.1 hcov t ht
  have htt : (comp 9 t t == idTab 9) = true := by
    rw [beq_iff_eq]
    exact (htv.comp htv).tab_eq (by rw [hv'2]; exact TabRep.idTab)
  rw [htt, Bool.not_true, Bool.false_or, List.contains_iff_mem, List.mem_map] at h1
  obtain ⟨e, he, het⟩ := h1
  have hev : permOf e.1 = v' := (tabRep_tabOf (permOf e.1)).perm_eq (het ▸ htv)
  obtain ⟨T, S, C, hw⟩ := entry_wit he
  have hAeq := closure_eq_alternatingGroup_of_entryWitK hw
  have hgs : entryCommK e = true := by
    unfold entryWitK at hw
    simp only [Bool.and_eq_true] at hw
    exact hw.1.1
  set Sg := (centralizer {u₀'} ⊓ alternatingGroup (Fin 9)) ⊔
    (centralizer {v'} ⊓ alternatingGroup (Fin 9)) ⊔
    (centralizer {u₀' * v'} ⊓ alternatingGroup (Fin 9)) with hSgdef
  have hA' : alternatingGroup (Fin 9) ≤ Sg := by
    rw [← hAeq, closure_le]
    rintro a ⟨l, hl, rfl⟩
    have haA : permOf l ∈ alternatingGroup (Fin 9) := by
      rw [← hAeq]
      exact subset_closure ⟨l, hl, rfl⟩
    unfold entryCommK at hgs
    rw [List.all_eq_true] at hgs
    have h2 := hgs (tabOf (permOf l)) (List.mem_map.mpr ⟨l, hl, rfl⟩)
    rw [Bool.or_eq_true, Bool.or_eq_true] at h2
    rcases h2 with (h2 | h2) | h2
    · exact mem_sup_left (mem_sup_left (mem_inf.mpr
        ⟨mem_centralizer_singleton_iff.mpr (commute_of_commutes h2), haA⟩))
    · have h2' := commute_of_commutes h2
      rw [hev] at h2'
      exact mem_sup_left (mem_sup_right (mem_inf.mpr
        ⟨mem_centralizer_singleton_iff.mpr h2', haA⟩))
    · have h3 : commutes (tabOf (permOf l)) (tabOf (u₀' * v')) = true := by
        have h4 : tabOf (u₀' * v') = comp 9 (tabOf u₀') (tabOf (permOf e.1)) := by
          rw [hev]
          exact (tabRep_tabOf _).tab_eq ((tabRep_tabOf u₀').comp (tabRep_tabOf v'))
        rw [h4]
        exact h2
      exact mem_sup_right (mem_inf.mpr
        ⟨mem_centralizer_singleton_iff.mpr (commute_of_commutes h3), haA⟩)
  set φ : Perm (Fin 9) →* Perm (Fin 9) := (MulAut.conj π⁻¹).toMonoidHom with hφdef
  have hφ : ∀ x, φ x = π⁻¹ * x * π := fun x => by simp [hφdef]
  have hpiece : ∀ y z : Perm (Fin 9), π⁻¹ * y * π = z →
      centralizer {y} ⊓ alternatingGroup (Fin 9) ≤
        (centralizer {z} ⊓ alternatingGroup (Fin 9)).comap φ := by
    intro y z hyz x hx
    obtain ⟨hxy, hxA⟩ := mem_inf.mp hx
    rw [mem_centralizer_singleton_iff] at hxy
    rw [mem_comap, hφ, mem_inf, mem_centralizer_singleton_iff, ← hyz]
    refine ⟨?_, (alternatingGroup.normal (α := Fin 9)).conj_mem x hxA π⁻¹ |> fun h => by
      simpa [mul_assoc] using h⟩
    calc π⁻¹ * x * π * (π⁻¹ * y * π) = π⁻¹ * (x * y) * π := by group
      _ = π⁻¹ * (y * x) * π := by rw [hxy]
      _ = π⁻¹ * y * π * (π⁻¹ * x * π) := by group
  have hu' : π⁻¹ * u₀' * π = u := by rw [← hπ]; group
  have hv'' : π⁻¹ * v' * π = v := by rw [hv'def]; group
  have huv' : π⁻¹ * (u₀' * v') * π = u * v := by rw [← hu', ← hv'']; group
  have hSg : Sg ≤ ((centralizer {u} ⊓ alternatingGroup (Fin 9)) ⊔
      (centralizer {v} ⊓ alternatingGroup (Fin 9)) ⊔
      (centralizer {u * v} ⊓ alternatingGroup (Fin 9))).comap φ :=
    sup_le (sup_le ((hpiece _ _ hu').trans (comap_mono (le_sup_left.trans le_sup_left)))
      ((hpiece _ _ hv'').trans (comap_mono (le_sup_right.trans le_sup_left))))
      ((hpiece _ _ huv').trans (comap_mono le_sup_right))
  intro w hw
  have hw' : π * w * π⁻¹ ∈ alternatingGroup (Fin 9) :=
    (alternatingGroup.normal (α := Fin 9)).conj_mem w hw π
  have h5 := hSg (hA' hw')
  rw [mem_comap, hφ, show π⁻¹ * (π * w * π⁻¹) * π = w by group] at h5
  exact h5

end CertificateChecks.KernelSolMax.SixGen

end
