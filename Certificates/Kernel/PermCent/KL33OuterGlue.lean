module

public import Certificates.Kernel.PermCent.KL33Outer
public import Certificates.Kernel.PermCent.KL33Glue
public import CFSG.Certificates.Kernel.PermCent.OuterRepSound
public import CFSG.GH74.KGroups.L33Tables

public section

namespace CFSG.Certificates.Kernel.PkCV.L33R.OuterGlue

open Subgroup CFSG.GH74.KGroups CFSG.GH74.KGroups.L33 CFSG.Sporadic.Schreier
  CFSG.Certificates.Kernel.PkCV.SylL CFSG.Certificates.Kernel.PkCV.OutR
  CFSG.Certificates.Kernel.PkCV.L33R.KOut CFSG.Certificates.Kernel.PkCV.L33R.KSyl
  CFSG.Certificates.Kernel.PkCV.L33R.Glue

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

theorem memA (w : List Nat) : ev (wordC gA3 w) ∈ QA.originalSubgroup := by
  rw [QA_closure]
  exact ev_wordC_mem gA3 w

theorem PA_mem : ev (cOf PA) ∈ QP.originalSubgroup := by
  rw [ev_cOf, QP_closure]
  exact Subgroup.subset_closure (Set.mem_insert _ _)

theorem tO_not_mem : ev tO ∉ QP.originalSubgroup := by
  intro h
  have h1 := (mem_iff_sift QP QP_ok _).1 h
  rw [sift_ev, kOut] at h1
  exact Bool.false_ne_true h1

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

theorem listS_mem : ∀ y ∈ elemsC QS, ev y ∈ QS.originalSubgroup :=
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
  rcases hg with rfl | rfl <;> simp [ev_cOf]


theorem not_mem_of_conj {g x : Equiv.Perm (Fin 26)}
    (hg : g ∈ QA.originalSubgroup) (hx : x ∉ QP.originalSubgroup) :
    g * x * g⁻¹ ∉ QP.originalSubgroup := fun h =>
  hx ((conj_mem_iff l33_conj_mem hg x).1 (by rwa [MulAut.conj_apply]))

theorem l33_outCent3 :
    ∀ τ ∈ QA.originalSubgroup, τ ^ 2 = 1 → τ ∉ QP.originalSubgroup →
      ∀ ψ ∈ QA.originalSubgroup, (∀ c ∈ QP.originalSubgroup, c ^ 3 = 1 → c * τ = τ * c →
        ψ * c = c * ψ) → ψ = 1 ∨ ψ = τ := by
  have key := l33_invol
    (fun x => x ∉ QP.originalSubgroup → OutCent3At QP.originalSubgroup QA.originalSubgroup x)
    (fun g hg _ _ h hx => outCent3At_of_conj l33_conj_mem hg (h (not_mem_of_conj hg hx)))
    (fun ρ hρ => by
      simp only [reps, List.mem_cons, List.not_mem_nil, or_false] at hρ
      rcases hρ with rfl | rfl
      · exact fun h => absurd PA_mem h
      · exact fun _ => outCent3_of_pass listA kSubO (memP_map csOW) (pass_split kPass).1)
  intro τ hτ h2 hτP
  exact key τ hτ h2 (fun e => hτP (e ▸ one_mem _)) hτP

theorem l33_bang :
    ∀ τ ∈ QA.originalSubgroup, τ ^ 2 = 1 → τ ∉ QP.originalSubgroup →
      ∃ l ∈ QP.originalSubgroup, ∃ c₁ ∈ QP.originalSubgroup, ∃ c₂ ∈ QP.originalSubgroup,
        c₁ ^ 3 = 1 ∧ c₂ ^ 3 = 1 ∧ c₁ ≠ 1 ∧ c₂ ≠ 1 ∧ c₁ * τ = τ * c₁ ∧ c₂ * τ = τ * c₂ ∧
        (c₁ * c₂) ^ 2 = 1 ∧ c₁ * c₂ ≠ 1 ∧ τ * l * τ⁻¹ * l⁻¹ = c₁ * c₂ := by
  have key := l33_invol (fun x => x ∉ QP.originalSubgroup → BangAt QP.originalSubgroup x)
    (fun g hg _ _ h hx => bangAt_of_conj l33_conj_mem hg (h (not_mem_of_conj hg hx)))
    (fun ρ hρ => by
      simp only [reps, List.mem_cons, List.not_mem_nil, or_false] at hρ
      rcases hρ with rfl | rfl
      · exact fun h => absurd PA_mem h
      · exact fun _ => bang_of_check (memP _) (memP _) (memP _) kBang)
  intro τ hτ h2 hτP
  exact key τ hτ h2 (fun e => hτP (e ▸ one_mem _)) hτP

theorem l33_innerSq :
    ∀ v ∈ QP.originalSubgroup, v ^ 2 = 1 → v ≠ 1 → ∀ ψ ∈ QA.originalSubgroup,
      (∀ c ∈ QP.originalSubgroup, c ^ 3 = 1 → c * v = v * c → ψ * c = c * ψ) →
      (ψ ^ 2 = 1 ∨ ψ ^ 2 = v) ∧ (ψ ∈ QP.originalSubgroup → ψ ^ 2 = 1 → ψ = 1 ∨ ψ = v) := by
  have key := l33_invol
    (fun x => x ∈ QP.originalSubgroup → InnerSqAt QP.originalSubgroup QA.originalSubgroup x)
    (fun g hg x _ h hx => innerSqAt_of_conj l33_conj_mem hg (h (l33_conj_mem g hg x hx)))
    (fun ρ hρ => by
      simp only [reps, List.mem_cons, List.not_mem_nil, or_false] at hρ
      rcases hρ with rfl | rfl
      · exact fun _ => innerSq_of_pass listA kSubI (memP_map csIW) (pass_split kPass).2.1
      · exact fun h => absurd h tO_not_mem)
  intro v hv h2 h1
  exact key v (QP_le_QA hv) h2 h1 hv

theorem l33_cyc :
    ∀ v ∈ QP.originalSubgroup, v ^ 2 = 1 → v ≠ 1 → ∃ φ ∈ QA.originalSubgroup,
      ∀ ψ ∈ QA.originalSubgroup, (∀ c ∈ QP.originalSubgroup, c ^ 3 = 1 → c * v = v * c →
        ψ * c = c * ψ) → ∃ k : ℕ, ψ = φ ^ k := by
  have key := l33_invol
    (fun x => x ∈ QP.originalSubgroup → CycAt QP.originalSubgroup QA.originalSubgroup x)
    (fun g hg x _ h hx => cycAt_of_conj l33_conj_mem hg (h (l33_conj_mem g hg x hx)))
    (fun ρ hρ => by
      simp only [reps, List.mem_cons, List.not_mem_nil, or_false] at hρ
      rcases hρ with rfl | rfl
      · refine fun _ => cyc_of_pass (φ := phi) listA kSubI (memP_map csIW) (memA _)
          (fun p hp => ?_) (pass_split kPass).2.2.1
        obtain ⟨k, -, rfl⟩ := List.mem_map.1 hp
        exact ⟨k, rfl⟩
      · exact fun h => absurd h tO_not_mem)
  intro v hv h2 h1
  exact key v (QP_le_QA hv) h2 h1 hv

theorem l33_sylCent :
    ∀ ψ ∈ QA.originalSubgroup, (∀ q ∈ QS.originalSubgroup, q * ψ = ψ * q) →
      ψ ∈ QS.originalSubgroup :=
  sylCent_of_pass listA listS_mem gS_mem (pass_split kPass).2.2.2.1

theorem l33_word :
    ∃ a ∈ QP.originalSubgroup, ∃ b ∈ QP.originalSubgroup, a ^ 3 = 1 ∧ b ^ 3 = 1 ∧ a ≠ 1 ∧
      b ≠ 1 ∧ a * s0 = s0 * a ∧ b * s0 = s0 * b ∧ (a * b) ^ 3 = s0 := by
  have h := word_of_check (memP _) (memP _) kWord
  rwa [ev_cOf] at h

theorem l33_sylSq :
    ∀ ψ ∈ QA.originalSubgroup, ψ ∉ QP.originalSubgroup →
      (∀ q ∈ QS.originalSubgroup, ψ * q * ψ⁻¹ ∈ QS.originalSubgroup) →
      ∀ v ∈ QS.originalSubgroup, v ^ 2 = 1 → v ≠ 1 →
      (∀ c ∈ QP.originalSubgroup, c ^ 3 = 1 → c * v = v * c → ψ * c = c * ψ) → ψ ^ 2 = v →
      ∀ q ∈ QS.originalSubgroup, q * v = v * q :=
  sylSq_of_pass listA gS_mem listS QS_gen (pass_split kPass).2.2.2.2

theorem l33_conj4 :
    ∀ a ∈ QS.originalSubgroup, a ^ 4 = 1 → a ^ 2 ≠ 1 →
      (∀ c ∈ QP.originalSubgroup, c ^ 3 = 1 → c * a ^ 2 = a ^ 2 * c → c * a = a * c) →
      ∃ k ∈ QP.originalSubgroup, k⁻¹ * a * k ∈ QS.originalSubgroup ∧
        ∀ y ∈ QS.originalSubgroup, y * (k⁻¹ * a * k) = (k⁻¹ * a * k) * y :=
  conj4_of_check listS (fun c hc => by
    simp only [refs, List.mem_cons, List.not_mem_nil, or_false] at hc
    rw [hc]
    exact memP _) kConj4

end CFSG.Certificates.Kernel.PkCV.L33R.OuterGlue

end
