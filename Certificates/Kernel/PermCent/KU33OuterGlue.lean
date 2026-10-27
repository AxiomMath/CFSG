module

public import Certificates.Kernel.PermCent.KU33Outer
public import Certificates.Kernel.PermCent.KU33
public import CFSG.Certificates.Kernel.PermCent.OuterRepOSound
public import CFSG.Certificates.Kernel.PermCent.SylowListSound
public import CFSG.Certificates.Kernel.PermCent.U33Sound
public import CFSG.GH74.KGroups.U33Tables

public section

namespace CFSG.Certificates.Kernel.PkCV.U33R.OuterGlue

open Subgroup CFSG.GH74.KGroups CFSG.GH74.KGroups.U33 CFSG.Sporadic.Schreier
  CFSG.Certificates.Kernel.PkCV.SylL CFSG.Certificates.Kernel.PkCV.OutR
  CFSG.Certificates.Kernel.PkCV.U33R.KOut

theorem QP_closure' : QP.originalSubgroup = closure {σ | σ ∈ gP.map ev} := by
  rw [QP_closure]
  congr 1
  ext σ
  simp [gP, ev_cOf]

theorem memP (w : List Nat) : ev (wordC gP w) ∈ QP.originalSubgroup := by
  rw [QP_closure']
  exact ev_wordC_mem gP w

theorem memP_map (W : List (List Nat)) : ∀ c ∈ W.map (wordC gP), ev c ∈ QP.originalSubgroup := by
  intro c hc
  obtain ⟨w, -, rfl⟩ := List.mem_map.1 hc
  exact memP w

theorem listA :
    ∀ x ∈ QA.originalSubgroup, ∃ y ∈ elemsC QA, ev y = x := by
  intro x hx
  have h := (mem_elemsT QA QA_ok x).2 hx
  rw [elemsT_eq_elemsC] at h
  exact List.mem_map.1 h

theorem listS :
    ∀ x ∈ QS.originalSubgroup, ∃ y ∈ elemsC QS, ev y = x := by
  intro x hx
  have h := (mem_elemsT QS QS_ok x).2 hx
  rw [elemsT_eq_elemsC] at h
  exact List.mem_map.1 h

theorem listS_mem :
    ∀ y ∈ elemsC QS, ev y ∈ QS.originalSubgroup :=
  fun y hy => (mem_elemsT QS QS_ok _).1 (by rw [elemsT_eq_elemsC]; exact List.mem_map_of_mem hy)

theorem QS_gen : QS.originalSubgroup ≤ closure {σ | σ ∈ gS.map ev} := by
  rw [QS_closure]
  apply le_of_eq
  congr 1
  ext σ
  simp [gS, ev_cOf]

theorem gS_mem : ∀ g ∈ gS, ev g ∈ QS.originalSubgroup := by
  intro g hg
  rw [QS_closure]
  apply Subgroup.subset_closure
  simp only [gS, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp [ev_cOf]

theorem inP_mem :
    ∀ y, inP y = true → ev y ∈ QP.originalSubgroup := fun y h =>
  (mem_iff_sift QP QP_ok _).2 (by rw [sift_ev]; exact h)

theorem hn : ∀ g ∈ QA.originalSubgroup,
    ∀ x ∈ QP.originalSubgroup, g * x * g⁻¹ ∈ QP.originalSubgroup := by
  rw [QA_closure, QP_closure]
  exact conj_AP

theorem pu_mem : pu ∈ QP.originalSubgroup := by
  have h := inP_mem _ kOut.2
  rwa [tI, ev_cOf] at h

theorem outer_conj {τ : Equiv.Perm (Fin 28)}
    (hτ : τ ∈ QA.originalSubgroup) (hτ2 : τ ^ 2 = 1) (hτP : τ ∉ QP.originalSubgroup) :
    ∃ g ∈ QA.originalSubgroup, g * τ * g⁻¹ = ev tO := by
  have hτ1 : τ ≠ 1 := fun h => hτP (h ▸ one_mem _)
  have hA := hτ
  rw [QA_closure] at hA
  obtain ⟨r, hr, g, hg, rfl⟩ := invol_A τ hA (orderOf_eq_prime hτ2 hτ1)
  rw [← QA_closure] at hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact absurd (hn g hg _ pu_mem) hτP
  · exact ⟨g⁻¹, inv_mem hg, by rw [tO, ev_cOf]; group⟩

theorem inner_conj {v : Equiv.Perm (Fin 28)}
    (hv : v ∈ QP.originalSubgroup) (hv2 : v ^ 2 = 1) (hv1 : v ≠ 1) :
    ∃ g ∈ QA.originalSubgroup, g * v * g⁻¹ = ev tI := by
  have hP := hv
  rw [QP_closure] at hP
  obtain ⟨g, hg, rfl⟩ := invol_P v hP (orderOf_eq_prime hv2 hv1)
  rw [← QA_closure] at hg
  exact ⟨g⁻¹, inv_mem hg, by rw [tI, ev_cOf]; group⟩

theorem u33_outCent3 :
    ∀ τ ∈ QA.originalSubgroup, τ ^ 2 = 1 → τ ∉ QP.originalSubgroup →
      ∀ ψ ∈ QA.originalSubgroup, (∀ c ∈ QP.originalSubgroup, c ^ 3 = 1 → c * τ = τ * c →
        ψ * c = c * ψ) → ψ = 1 ∨ ψ = τ := by
  intro τ hτ h2 hτP
  obtain ⟨g, hg, hgτ⟩ := outer_conj hτ h2 hτP
  refine outCent3At_of_conj hn hg ?_
  rw [hgτ]
  exact outCent3_of_pass listA kSubO (memP_map csOW) (passO_split kPass).1

theorem u33_bang :
    ∀ τ ∈ QA.originalSubgroup, τ ^ 2 = 1 → τ ∉ QP.originalSubgroup →
      ∃ l ∈ QP.originalSubgroup, ∃ c₁ ∈ QP.originalSubgroup, ∃ c₂ ∈ QP.originalSubgroup,
        c₁ ^ 3 = 1 ∧ c₂ ^ 3 = 1 ∧ c₁ ≠ 1 ∧ c₂ ≠ 1 ∧ c₁ * τ = τ * c₁ ∧ c₂ * τ = τ * c₂ ∧
        (c₁ * c₂) ^ 2 = 1 ∧ c₁ * c₂ ≠ 1 ∧ τ * l * τ⁻¹ * l⁻¹ = c₁ * c₂ := by
  intro τ hτ h2 hτP
  obtain ⟨g, hg, hgτ⟩ := outer_conj hτ h2 hτP
  refine bangAt_of_conj hn hg ?_
  rw [hgτ]
  exact bang_of_check (memP _) (memP _) (memP _) kBang

theorem u33_innerSq :
    ∀ v ∈ QP.originalSubgroup, v ^ 2 = 1 → v ≠ 1 → ∀ ψ ∈ QA.originalSubgroup,
      (∀ c ∈ QP.originalSubgroup, c ^ 3 = 1 → c * v = v * c → ψ * c = c * ψ) →
      (ψ ^ 2 = 1 ∨ ψ ^ 2 = v) ∧ (ψ ∈ QP.originalSubgroup → ψ ^ 2 = 1 → ψ = 1 ∨ ψ = v) := by
  intro v hv h2 h1
  obtain ⟨g, hg, hgv⟩ := inner_conj hv h2 h1
  refine innerSqAt_of_conj hn hg ?_
  rw [hgv]
  exact innerSq_of_pass listA kSubI (memP_map csIW) (passO_split kPass).2.1

theorem u33_sylCent :
    ∀ ψ ∈ QA.originalSubgroup, (∀ q ∈ QS.originalSubgroup, q * ψ = ψ * q) →
      ψ ∈ QS.originalSubgroup :=
  sylCent_of_pass listA listS_mem gS_mem (passO_split kPass).2.2.1

theorem u33_word :
    ∃ a ∈ QP.originalSubgroup, ∃ b ∈ QP.originalSubgroup, a ^ 3 = 1 ∧ b ^ 3 = 1 ∧ a ≠ 1 ∧
      b ≠ 1 ∧ a * s0 = s0 * a ∧ b * s0 = s0 * b ∧ (a * b) ^ 3 = s0 := by
  have h := word_of_check (memP _) (memP _) kWord
  rwa [ev_cOf] at h

theorem u33_sylSq :
    ∀ ψ ∈ QA.originalSubgroup, ψ ∉ QP.originalSubgroup →
      (∀ q ∈ QS.originalSubgroup, ψ * q * ψ⁻¹ ∈ QS.originalSubgroup) →
      ∀ v ∈ QS.originalSubgroup, v ^ 2 = 1 → v ≠ 1 →
      (∀ c ∈ QP.originalSubgroup, c ^ 3 = 1 → c * v = v * c → ψ * c = c * ψ) → ψ ^ 2 = v →
      ∀ q ∈ QS.originalSubgroup, q * v = v * q :=
  sylSqO_of_pass listA gS_mem listS QS_gen inP_mem (passO_split kPass).2.2.2

theorem u33_conj4 :
    ∀ a ∈ QS.originalSubgroup, a ^ 4 = 1 → a ^ 2 ≠ 1 →
      (∀ c ∈ QP.originalSubgroup, c ^ 3 = 1 → c * a ^ 2 = a ^ 2 * c → c * a = a * c) →
      ∃ k ∈ QP.originalSubgroup, k⁻¹ * a * k ∈ QS.originalSubgroup ∧
        ∀ y ∈ QS.originalSubgroup, y * (k⁻¹ * a * k) = (k⁻¹ * a * k) * y :=
  conj4K_of_check listS listS_mem (memP_map refsW) (memP_map ksW) kConj4

theorem u33_exists3 :
    t0 ∈ QP.originalSubgroup ∧ t0 ≠ 1 ∧ t0 ^ 2 = 1 ∧
      ∃ c ∈ QP.originalSubgroup, c ^ 3 = 1 ∧ c ≠ 1 ∧ c * t0 = t0 * c := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := kE3
  simp only [powOneC_eq, eq22C_eq, decide_eq_true_eq, decide_eq_false_iff_not] at h2 h3 h4 h5 h6
  have ht := inP_mem _ h1
  rw [ev_cOf] at ht
  refine ⟨ht, fun e => h3 ((ev_eq_one_iff _).1 (by rw [ev_cOf]; exact e)), ?_, ev e3, memP _,
    (ev_pow_eq_one_iff _ 3).2 h4, fun e => h5 ((ev_eq_one_iff _).1 e), ?_⟩
  · have h := (ev_pow_eq_one_iff (cOf t0) 2).2 h2
    rwa [ev_cOf] at h
  · have h := (ev_comm_iff e3 (cOf t0)).2 h6
    rwa [ev_cOf] at h

theorem u33_exp :
    ∀ x ∈ QP.originalSubgroup, x ^ 27 = 1 → x ^ 3 = 1 := by
  have h : CFSG.LieType.ChevTwo.OppCl.U33Fin.checkExp () = true := by
    rw [CFSG.Certificates.Kernel.PkCV.U33T.exp_eq]
    exact CFSG.Certificates.Kernel.PkCV.U33T.kExp
  unfold CFSG.LieType.ChevTwo.OppCl.U33Fin.checkExp CFSG.LieType.ChevTwo.OppCl.U33Fin.elems at h
  intro x hx h27
  have h1 := List.all_eq_true.1 h x ((mem_elemsT QP QP_ok x).2 hx)
  simpa [h27] using h1

theorem u33_inner3 :
    ∀ g ∈ QA.originalSubgroup, g ^ 3 = 1 → g ∈ QP.originalSubgroup := by
  intro τ hτ h3
  have hle : QP.originalSubgroup ≤ QA.originalSubgroup := by
    rw [QP_closure, QA_closure]
    exact P_le_A
  have hidx : (QP.originalSubgroup.subgroupOf QA.originalSubgroup).index = 2 := by
    have h1 := Subgroup.card_mul_index (QP.originalSubgroup.subgroupOf QA.originalSubgroup)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, card_group QP QP_ok,
      QP_valid.2, card_group QA QA_ok, QA_valid.2] at h1
    omega
  have : (QP.originalSubgroup.subgroupOf QA.originalSubgroup).Normal :=
    Subgroup.normal_of_index_eq_two hidx
  set t : QA.originalSubgroup := ⟨τ, hτ⟩
  have h2 := Subgroup.pow_index_mem (QP.originalSubgroup.subgroupOf QA.originalSubgroup) t
  rw [hidx] at h2
  have ht : t ^ 3 = 1 := Subtype.ext (by simpa [t] using h3)
  have he : t = (t ^ 2) ^ 2 * (t ^ 3)⁻¹ := by group
  have hmem : t ∈ QP.originalSubgroup.subgroupOf QA.originalSubgroup := by
    rw [he, ht, inv_one, mul_one]
    exact pow_mem h2 _
  exact Subgroup.mem_subgroupOf.1 hmem

end CFSG.Certificates.Kernel.PkCV.U33R.OuterGlue

end
