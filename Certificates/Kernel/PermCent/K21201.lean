module

public import Certificates.Data.Kernel.PermCent.U33Twin
public import CFSG.Certificates.Kernel.PermCent.KGrpOddConjSound
public import Certificates.Data.Kernel.PermCent.KGrpC
import Certificates.Kernel.PermCent.K5097
import Certificates.Kernel.Misc.KGroups.U33Valid

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CFSG.Certificates.Kernel.PkCV.U33T

open CFSG.GH74.KGroups.U33

section

variable {G : Type} [Group G] [DecidableEq G]

@[expose] def elemAtG (C : List G) (d e : G) : Bool :=
  decide (e = 1) || decide (e = d) || !decide (e * d = d * e) ||
    C.any fun c => !decide (e * (c * e * c⁻¹) = c * e * c⁻¹ * e)

@[expose] def phiG (LA LP : List G) (d : G) : Bool :=
  (LA.filter fun e => decide (e * e = 1)).all
    (elemAtG (LP.filter fun c => decide (c * d = d * c)) d)

theorem phiG_iff (LA LP : List G) (d : G) : phiG LA LP d = true ↔
    ∀ e ∈ LA, e * e = 1 → e ≠ 1 → e ≠ d → e * d = d * e →
      ∃ c ∈ LP, c * d = d * c ∧ e * (c * e * c⁻¹) ≠ c * e * c⁻¹ * e := by
  unfold phiG elemAtG
  simp only [List.all_eq_true, List.mem_filter, decide_eq_true_eq, Bool.or_eq_true,
    Bool.not_eq_true', decide_eq_false_iff_not, List.any_eq_true, and_imp]
  constructor
  · intro h e he he2 h1 h2 h3
    rcases h e he he2 with ((h4 | h4) | h4) | h4
    · exact absurd h4 h1
    · exact absurd h4 h2
    · exact absurd h3 h4
    · obtain ⟨c, ⟨hc, hcd⟩, hne⟩ := h4
      exact ⟨c, hc, hcd, hne⟩
  · intro h e he he2
    by_cases h1 : e = 1
    · exact Or.inl (Or.inl (Or.inl h1))
    by_cases h2 : e = d
    · exact Or.inl (Or.inl (Or.inr h2))
    by_cases h3 : e * d = d * e
    · obtain ⟨c, hc, hcd, hne⟩ := h e he he2 h1 h2 h3
      exact Or.inr ⟨c, ⟨hc, hcd⟩, hne⟩
    · exact Or.inl (Or.inr h3)

omit [DecidableEq G] in
theorem conj_eq_conj_iff (g x y : G) : g * x * g⁻¹ = g * y * g⁻¹ ↔ x = y := by
  constructor
  · intro h
    calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
      _ = g⁻¹ * (g * y * g⁻¹) * g := by rw [h]
      _ = y := by group
  · rintro rfl; rfl

theorem phiG_conj (LA LP : List G) (hA : ∀ e g, e ∈ LA → g ∈ LP → g⁻¹ * e * g ∈ LA)
    (hP : ∀ c g, c ∈ LP → g ∈ LP → g * c * g⁻¹ ∈ LP) {g d : G} (hg : g ∈ LP)
    (h : phiG LA LP d = true) : phiG LA LP (g * d * g⁻¹) = true := by
  rw [phiG_iff] at h ⊢
  intro e' he' he2 h1 h2 h3
  have ee : e' = g * (g⁻¹ * e' * g) * g⁻¹ := by group
  set e := g⁻¹ * e' * g with hedef
  have heA : e ∈ LA := hA e' g he' hg
  rw [ee] at he2 h1 h2 h3 ⊢
  have he2' : e * e = 1 := by
    rw [← conj_eq_conj_iff g]
    calc g * (e * e) * g⁻¹ = g * e * g⁻¹ * (g * e * g⁻¹) := by group
      _ = 1 := he2
      _ = g * 1 * g⁻¹ := by group
  have h1' : e ≠ 1 := fun h => h1 (by rw [h]; group)
  have h2' : e ≠ d := fun h => h2 (by rw [h])
  have h3' : e * d = d * e := by
    rw [← conj_eq_conj_iff g]
    calc g * (e * d) * g⁻¹ = g * e * g⁻¹ * (g * d * g⁻¹) := by group
      _ = g * d * g⁻¹ * (g * e * g⁻¹) := h3
      _ = g * (d * e) * g⁻¹ := by group
  obtain ⟨c, hc, hcd, hne⟩ := h e heA he2' h1' h2' h3'
  refine ⟨g * c * g⁻¹, hP c g hc hg, ?_, ?_⟩
  · calc g * c * g⁻¹ * (g * d * g⁻¹) = g * (c * d) * g⁻¹ := by group
      _ = g * (d * c) * g⁻¹ := by rw [hcd]
      _ = g * d * g⁻¹ * (g * c * g⁻¹) := by group
  · intro hh
    apply hne
    rw [← conj_eq_conj_iff g]
    calc g * (e * (c * e * c⁻¹)) * g⁻¹
        = g * e * g⁻¹ * (g * c * g⁻¹ * (g * e * g⁻¹) * (g * c * g⁻¹)⁻¹) := by group
      _ = g * c * g⁻¹ * (g * e * g⁻¹) * (g * c * g⁻¹)⁻¹ * (g * e * g⁻¹) := hh
      _ = g * (c * e * c⁻¹ * e) * g⁻¹ := by group


end

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Certificates.Kernel.PkCV.KGrp

@[expose] noncomputable def dK : CV 28 := ((elemsC QP).filter invOC).headD 1

theorem kR1 : (elemsC QP).length = 63 * (centL (elemsC QP) dK).length := by decide +kernel

theorem kR2 : ((elemsC QP).filter invOC).length = 63 := by decide +kernel

theorem kR3 : dK ∈ (elemsC QP).filter invOC := by decide +kernel

theorem kR4 : phiG (elemsC QA) (elemsC QP) dK = true := by decide +kernel

theorem k21201 : elemC = true := by
  have hP : ValidSchreier QP := CertificateChecks.KernelMisc.U33PC.valid
  have hA : ValidSchreier QA := CertificateChecks.KernelMisc.U33AC.valid
  have hle : QP.originalSubgroup ≤ QA.originalSubgroup := by
    rw [QP, QA, certificate_originalSubgroup, certificate_originalSubgroup, Subgroup.closure_le]
    intro g hg
    apply Subgroup.subset_closure
    simp only [Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false] at hg ⊢
    rcases hg with rfl | rfl <;> simp
  have hPA : ∀ g, g ∈ elemsC QP → g ∈ elemsC QA := fun g hg =>
    (mem_elemsC QA hA g).2 (hle ((mem_elemsC QP hP g).1 hg))
  have hAc : ∀ e g, e ∈ elemsC QA → g ∈ elemsC QP → g⁻¹ * e * g ∈ elemsC QA := by
    intro e g he hg
    have h := conj_mem_elemsC QA hA (hPA _ (inv_memC QP hP hg)) he
    rwa [inv_inv] at h
  have hPc : ∀ c g, c ∈ elemsC QP → g ∈ elemsC QP → g * c * g⁻¹ ∈ elemsC QP :=
    fun c g hc hg => conj_mem_elemsC QP hP hg hc
  have hm := List.mem_filter.1 kR3
  have hcl := K5097.conj_one_class QP hP dK 63 kR1 kR2 hm.1 hm.2
  show ((elemsC QP).all fun d => !decide (d * d = 1) || decide (d = 1) ||
    phiG (elemsC QA) (elemsC QP) d) = true
  rw [List.all_eq_true]
  intro d hd
  by_cases h1 : d * d = 1
  · by_cases h2 : d = 1
    · rw [decide_eq_true h1, decide_eq_true h2]
      rfl
    · have hi : invOC d = true := by
        unfold invOC
        rw [← powOneC_eq', pow_two, decide_eq_true h1, decide_eq_false h2]
        rfl
      obtain ⟨r, hr, g, hg, rfl⟩ := hcl d (List.mem_filter.2 ⟨hd, hi⟩)
      rw [List.mem_singleton] at hr
      subst hr
      rw [phiG_conj (elemsC QA) (elemsC QP) hAc hPc hg kR4, Bool.or_true]
  · rw [decide_eq_false h1]
    rfl

end CFSG.Certificates.Kernel.PkCV.U33T
