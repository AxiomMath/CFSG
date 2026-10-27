
module

public import Certificates.Kernel.He7223.GlueOrd

public section

set_option maxRecDepth 400000

#kss_strof CertificateChecks.KernelHe7223.W5S CFSG.Quasithin.KGC31.He.w5W
#kss_strof CertificateChecks.KernelHe7223.W7S CFSG.Quasithin.KGC31.He.w7W

namespace CertificateChecks.KernelHe7223

open CFSG.KC.Enum CFSG.KS CFSG.KC.WordPts CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.He
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.HeldB CFSG.Sporadic.Schreier
  CertificateChecks.KernelSchreierFam.He725

theorem w5W_eq : w5W = eW.take 4 := by
  rw [W5S.eq, decodeWs_ofList (by decide) (ascii_of_all (by decide +kernel)), eW_eq]
  decide +kernel

theorem w7W_eq : w7W = qW.take 3 := by
  rw [W7S.eq, decodeWs_ofList (by decide) (ascii_of_all (by decide +kernel)), qW_eq]
  decide +kernel

theorem ok_of_letters {w : List ℤ} (h : lettersOK 2 w = true) :
    ∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ 2 := by
  intro l hl
  have h' := List.all_eq_true.1 h l hl
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at h'
  exact h'

theorem words_ok : ∀ w ∈ eW ++ qW ++ lsGenW ++ njW, ∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ 2 := by
  intro w hw
  simp only [List.mem_append] at hw
  rcases hw with ((h | h) | h) | h
  · exact ok_of_letters (eW_letters2 w h)
  · exact ok_of_letters (qW_letters2 w h)
  · obtain ⟨j, hj, rfl⟩ := lsGenW_cases h
    exact ok_of_letters (LG_letters j hj)
  · rw [njW_eq, List.mem_cons, List.mem_singleton] at h
    rcases h with rfl | rfl
    · exact ok_of_letters (GW_letters2 4 (by norm_num))
    · exact ok_of_letters (GW_letters2 5 (by norm_num))

theorem heE_eq' :
    eSub ebasis_E = heE := eSub_eq_closure ebasis_E

theorem heQ_eq' :
    eSub ebasis_Q = heQ := eSub_eq_closure ebasis_Q

theorem cent_heE :
    ∀ x ∈ heAutGroup, (∀ i : Fin 4, x * elt (eW.getD i []) = elt (eW.getD i []) * x) →
      x ∈ heE := fun _ hx hc => heE_eq' ▸ cent_E hx hc

theorem cent_heQ :
    ∀ x ∈ heAutGroup, (∀ i : Fin 3, x * elt (qW.getD i []) = elt (qW.getD i []) * x) →
      x ∈ heQ := fun _ hx hc => heQ_eq' ▸ cent_Q hx hc

theorem mem_normE
    {x : Equiv.Perm (Fin 8330)} (hx : x ∈ eNorm ebasis_E) :
    x ∈ Subgroup.normalizer (heE : Set (Equiv.Perm (Fin 8330))) := by
  rw [← heE_eq']
  exact hx

theorem mem_normQ
    {x : Equiv.Perm (Fin 8330)} (hx : x ∈ eNorm ebasis_Q) :
    x ∈ Subgroup.normalizer (heQ : Set (Equiv.Perm (Fin 8330))) := by
  rw [← heQ_eq']
  exact hx

theorem nsGrp_le :
    nsGrp ≤ heP ⊓ Subgroup.normalizer (heE : Set (Equiv.Perm (Fin 8330))) := by
  refine (Subgroup.closure_le _).mpr fun x hx => ?_
  rcases hx with ⟨j, rfl⟩ | ⟨i, rfl⟩
  · fin_cases j
    · refine ⟨?_, mem_normE nsGen_mem_eNorm.1⟩
      change elt (nsW.getD 6 []) ∈ heP
      rw [nsW_eq.1]
      exact elt_mem_heP (GW_letters2 0 (by norm_num))
    · refine ⟨?_, mem_normE nsGen_mem_eNorm.2⟩
      change elt (nsW.getD 11 []) ∈ heP
      rw [nsW_eq.2]
      exact elt_mem_heP (GW_letters2 1 (by norm_num))
  · exact ⟨elt_mem_heP (getD_letters eW_letters2 (by rw [eW_len]; exact i.2)),
      Subgroup.le_normalizer (Subgroup.subset_closure ⟨i, rfl⟩)⟩

theorem n7Grp_le :
    n7Grp ≤ heP ⊓ Subgroup.normalizer (heQ : Set (Equiv.Perm (Fin 8330))) := by
  refine (Subgroup.closure_le _).mpr fun x hx => ?_
  rcases hx with ⟨j, rfl⟩ | ⟨i, rfl⟩
  · fin_cases j
    · refine ⟨?_, mem_normQ n7Gen_mem_eNorm.1⟩
      change elt (n7W.getD 3 []) ∈ heP
      rw [n7W_eq.1]
      exact elt_mem_heP (GW_letters2 2 (by norm_num))
    · refine ⟨?_, mem_normQ n7Gen_mem_eNorm.2⟩
      change elt (n7W.getD 9 []) ∈ heP
      rw [n7W_eq.2]
      exact elt_mem_heP (GW_letters2 3 (by norm_num))
  · exact ⟨elt_mem_heP (getD_letters qW_letters2 (by rw [qW_len]; exact i.2)),
      Subgroup.le_normalizer (Subgroup.subset_closure ⟨i, rfl⟩)⟩

theorem lGrp_le :
    lGrp ≤ Subgroup.normalizer (heE : Set (Equiv.Perm (Fin 8330))) := by
  refine (Subgroup.closure_le _).mpr fun x hx => ?_
  obtain ⟨w, hw, rfl⟩ := hx
  exact mem_normE (lsGen_mem_eNorm w hw)

theorem nj_le :
    ∀ n ∈ njW, elt n ∈ Subgroup.normalizer (heE : Set (Equiv.Perm (Fin 8330))) :=
  fun n hn => mem_normE (nj_mem_eNorm n hn)

theorem heE_le_lGrp :
    heE ≤ lGrp :=
  (Subgroup.closure_le _).mpr fun _ ⟨i, hi⟩ => hi ▸ E_le_lGrp i

theorem E_fix :
    ∀ i : Fin 6, ∀ p : Fin 8330, (p : ℕ) ∈ bB → elt (eW.getD i []) p = p :=
  fun i p hp => E_fix_bB i i.2 p hp

end CertificateChecks.KernelHe7223

end
