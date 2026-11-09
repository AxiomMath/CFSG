module

public import Certificates.Data.Kernel.PermCent.SmallF3Twin
public import CFSG.GH74.KGroups.L33Inputs
public import CFSG.Certificates.Kernel.PermCent.KGrpOddConjSound
public import Certificates.Data.Kernel.PermCent.KGrpC
import CFSG.GH74.KGroups.L33
import Certificates.Kernel.PermCent.ClassCount

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CFSG.Certificates.Kernel.PkCV.SmallF3T.K442375

open CFSG.GH74.KGroups.L33

section

variable {G : Type} [Group G]

@[expose] def psiG (LP : List G) (q3 : G → Bool) (cm : G → G → Bool) (pw : G → Bool) (τ : G) : Bool :=
  ((LP.filter q3).filter fun u => cm τ u).all fun u =>
    (LP.filter fun c => cm τ c).any fun c => !pw (u * (c * u * c⁻¹))

variable [DecidableEq G] in
theorem psiG_iff (LP : List G) (q3 : G → Bool) (cm : G → G → Bool) (pw : G → Bool) (τ : G)
    (hcm : ∀ a b, cm a b = decide (a * b = b * a)) :
    psiG LP q3 cm pw τ = true ↔ ∀ u ∈ LP, q3 u = true → τ * u = u * τ →
      ∃ c ∈ LP, τ * c = c * τ ∧ pw (u * (c * u * c⁻¹)) = false := by
  unfold psiG
  simp only [List.all_eq_true, List.any_eq_true, List.mem_filter, hcm, decide_eq_true_eq,
    Bool.not_eq_true', and_imp, and_assoc]

variable [DecidableEq G] in
theorem psiG_conj (LP : List G) (q3 : G → Bool) (cm : G → G → Bool) (pw : G → Bool)
    (hcm : ∀ a b, cm a b = decide (a * b = b * a)) (hq3 : ∀ g x, q3 (g * x * g⁻¹) = q3 x)
    (hpw : ∀ g x, pw (g * x * g⁻¹) = pw x)
    (hP : ∀ c g, c ∈ LP → g ∈ LP → g * c * g⁻¹ ∈ LP) (hPi : ∀ g, g ∈ LP → g⁻¹ ∈ LP)
    {g τ : G} (hg : g ∈ LP) (h : psiG LP q3 cm pw τ = true) :
    psiG LP q3 cm pw (g * τ * g⁻¹) = true := by
  rw [psiG_iff LP q3 cm pw _ hcm] at h ⊢
  intro u' hu' hq hcomm
  have hu'eq : u' = g * (g⁻¹ * u' * g) * g⁻¹ := by group
  have hu : g⁻¹ * u' * g ∈ LP := by
    have := hP u' g⁻¹ hu' (hPi g hg)
    rwa [inv_inv] at this
  have hqu : q3 (g⁻¹ * u' * g) = true := by
    have := hq3 g⁻¹ u'
    rw [inv_inv] at this
    rw [this]
    exact hq
  have hc : τ * (g⁻¹ * u' * g) = g⁻¹ * u' * g * τ := by
    calc τ * (g⁻¹ * u' * g) = g⁻¹ * (g * τ * g⁻¹ * u') * g := by group
      _ = g⁻¹ * (u' * (g * τ * g⁻¹)) * g := by rw [hcomm]
      _ = g⁻¹ * u' * g * τ := by group
  obtain ⟨c, hcP, hcτ, hpwc⟩ := h _ hu hqu hc
  refine ⟨g * c * g⁻¹, hP c g hcP hg, ?_, ?_⟩
  · calc g * τ * g⁻¹ * (g * c * g⁻¹) = g * (τ * c) * g⁻¹ := by group
      _ = g * (c * τ) * g⁻¹ := by rw [hcτ]
      _ = g * c * g⁻¹ * (g * τ * g⁻¹) := by group
  · set u := g⁻¹ * u' * g
    have e : u' * (g * c * g⁻¹ * u' * (g * c * g⁻¹)⁻¹) = g * (u * (c * u * c⁻¹)) * g⁻¹ := by
      rw [hu'eq]
      group
    rw [e, hpw]
    exact hpwc


end

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Certificates.Kernel.PkCV
  CFSG.Certificates.Kernel.PkCV.KGrp

@[expose] noncomputable def q3C (u : CV 26) : Bool := powOneC u 3 && !decide (u = 1)

@[expose] noncomputable def cmC (a b : CV 26) : Bool := eq22C a b b a

@[expose] noncomputable def pwC (x : CV 26) : Bool := powOneC x 27

@[expose] noncomputable def aK : CV 26 := ((elemsC QP).filter invOC).headD 1

@[expose] noncomputable def bK : CV 26 :=
  ((elemsC QA).filter fun τ => invOC τ && !siftC QP τ 0).headD 1

theorem kFa : psiG (elemsC QP) q3C cmC pwC aK = true := by decide +kernel

theorem kFb : psiG (elemsC QP) q3C cmC pwC bK = true := by decide +kernel

theorem kF1 : (elemsC QP).length = 117 * (centL (elemsC QP) aK).length := by decide +kernel

theorem kF2 : (elemsC QP).length = 234 * (centL (elemsC QP) bK).length := by decide +kernel

theorem kF3 : ((elemsC QA).filter invOC).length = 117 + 234 := by decide +kernel

theorem kF4 : aK ∈ (elemsC QP).filter invOC := by decide +kernel

theorem kF5 : bK ∈ (elemsC QA).filter fun τ => invOC τ && !siftC QP τ 0 := by decide +kernel

theorem conj_ne_one (g y : CV 26) : g * y * g⁻¹ = 1 ↔ y = 1 :=
  ⟨fun h => by simpa [mul_assoc] using congrArg (fun z => g⁻¹ * z * g) h, fun h => by simp [h]⟩

theorem q3C_conj (g x : CV 26) : q3C (g * x * g⁻¹) = q3C x := by
  unfold q3C
  simp only [← powOneC_eq', conj_pow, conj_ne_one]

theorem pwC_conj (g x : CV 26) : pwC (g * x * g⁻¹) = pwC x := by
  unfold pwC
  simp only [← powOneC_eq', conj_pow, conj_ne_one]

@[expose] noncomputable def invsP : List (CV 26) := (elemsC QP).filter invOC

@[expose] noncomputable def uA : CV 26 :=
  ((elemsC QP).filter fun u => q3C u && invsP.any (cmC u)).headD 1

@[expose] noncomputable def uB : CV 26 :=
  ((elemsC QP).filter fun u => q3C u && !invsP.any (cmC u)).headD 1

@[expose] noncomputable def phiU (u : CV 26) : Bool :=
  (elemsC QP).any fun c => !pwC (u * (c * u * c⁻¹))

theorem kU1 : uA ∈ (elemsC QP).filter q3C := by decide +kernel

theorem kU2 : uB ∈ (elemsC QP).filter q3C := by decide +kernel

theorem kU3 : (elemsC QP).length = 104 * (centL (elemsC QP) uA).length := by decide +kernel

theorem kU4 : (elemsC QP).length = 624 * (centL (elemsC QP) uB).length := by decide +kernel

theorem kU5 : ((elemsC QP).filter q3C).length = 104 + 624 := by decide +kernel

theorem kU6 : phiU uA = true := by decide +kernel

theorem kU7 : phiU uB = true := by decide +kernel

theorem phiU_conj (hPc : ∀ c g, c ∈ elemsC QP → g ∈ elemsC QP → g * c * g⁻¹ ∈ elemsC QP)
    {g u : CV 26} (hg : g ∈ elemsC QP) (h : phiU u = true) : phiU (g * u * g⁻¹) = true := by
  unfold phiU at h ⊢
  rw [List.any_eq_true] at h ⊢
  obtain ⟨c, hc, hpw⟩ := h
  refine ⟨g * c * g⁻¹, hPc c g hc hg, ?_⟩
  have e : g * u * g⁻¹ * (g * c * g⁻¹ * (g * u * g⁻¹) * (g * c * g⁻¹)⁻¹) =
      g * (u * (c * u * c⁻¹)) * g⁻¹ := by group
  rw [e, pwC_conj]
  exact hpw

theorem kF0 : psiG (elemsC QP) q3C cmC pwC 1 = true := by
  have hP : ValidSchreier QP := CFSG.GH74.KGroups.L33.QP_ok
  have hcm : ∀ a b : CV 26, cmC a b = decide (a * b = b * a) := fun a b => eq22C_eq a b b a
  have hPc : ∀ c g, c ∈ elemsC QP → g ∈ elemsC QP → g * c * g⁻¹ ∈ elemsC QP :=
    fun c g hc hg => conj_mem_elemsC QP hP hg hc
  have hpos : ∀ r, 0 < (centL (elemsC QP) r).length := fun r =>
    List.length_pos_of_mem ((mem_centL _ r 1).2 ⟨one_memC QP hP, by group⟩)
  have hcard : ∀ r k, (elemsC QP).length = k * (centL (elemsC QP) r).length →
      ((elemsC QP).map fun g => g * r * g⁻¹).toFinset.card = k := fun r k hk =>
    Nat.eq_of_mul_eq_mul_right (hpos r) ((card_conj_mul QP hP r).trans hk)
  have h1 := List.mem_filter.1 kU1
  have h2 := List.mem_filter.1 kU2
  have hcov := ClassCount.cover_two_classes (elemsC QP) q3C (nodup_elemsC QP hP)
    (fun _ _ hg hh => mul_memC QP hP hg hh) (fun _ hg => inv_memC QP hP hg) q3C_conj uA uB
    104 624 (hcard uA 104 kU3) (hcard uB 624 kU4) kU5 (by decide) h1.1 h2.1 h1.2 h2.2
  rw [psiG_iff _ _ _ _ _ hcm]
  intro u hu hq _
  obtain ⟨g, hg, hor⟩ := hcov u (List.mem_filter.2 ⟨hu, hq⟩)
  have hphi : phiU u = true := by
    rcases hor with rfl | rfl
    · exact phiU_conj hPc hg kU6
    · exact phiU_conj hPc hg kU7
  unfold phiU at hphi
  rw [List.any_eq_true] at hphi
  obtain ⟨c, hc, hpw⟩ := hphi
  exact ⟨c, hc, by group, by simpa using hpw⟩

theorem k442375 : fhO3C (elemsC QA) (elemsC QP) = true := by
  have hA : ValidSchreier QA := CFSG.GH74.KGroups.L33.QA_ok
  have hP : ValidSchreier QP := CFSG.GH74.KGroups.L33.QP_ok
  have hle : QP.originalSubgroup ≤ QA.originalSubgroup := by
    rw [QP, QA, certificate_originalSubgroup, certificate_originalSubgroup, Subgroup.closure_le]
    intro g hg
    apply Subgroup.subset_closure
    simp only [Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false] at hg ⊢
    rcases hg with rfl | rfl <;> simp
  have hPA : ∀ g, g ∈ elemsC QP → g ∈ elemsC QA := fun g hg =>
    (mem_elemsC QA hA g).2 (hle ((mem_elemsC QP hP g).1 hg))
  have hcm : ∀ a b : CV 26, cmC a b = decide (a * b = b * a) := fun a b => eq22C_eq a b b a
  have hPc : ∀ c g, c ∈ elemsC QP → g ∈ elemsC QP → g * c * g⁻¹ ∈ elemsC QP :=
    fun c g hc hg => conj_mem_elemsC QP hP hg hc
  have hPi : ∀ g, g ∈ elemsC QP → g⁻¹ ∈ elemsC QP := fun g hg => inv_memC QP hP hg
  have ha := List.mem_filter.1 kF4
  have hb := List.mem_filter.1 kF5
  obtain ⟨hbi, hbs⟩ := Bool.and_eq_true_iff.1 hb.2
  have hbP : bK ∉ elemsC QP := fun h => by
    have h1 := (CFSG.GH74.KGroups.mem_iff_sift QP hP _).1 ((mem_elemsC QP hP _).1 h)
    have hs : siftC QP bK 0 = false := by simpa using hbs
    rw [sift_ev, hs] at h1
    exact Bool.false_ne_true h1
  have hcl := conj_of_count QA QP hA hP hle aK bK 117 234 kF1 kF2 kF3 (hPA _ ha.1) hb.1 ha.2 hbi
    ha.1 hbP
  show ((elemsC QA).filter fun τ => powOneC τ 2).all (psiG (elemsC QP) q3C cmC pwC) = true
  rw [List.all_eq_true]
  intro τ hτ
  rw [List.mem_filter] at hτ
  by_cases h1 : τ = 1
  · subst h1
    exact kF0
  · have hi : invOC τ = true := by
      unfold invOC
      rw [hτ.2, decide_eq_false h1]
      rfl
    obtain ⟨r, hr, g, hg, rfl⟩ := hcl τ (List.mem_filter.2 ⟨hτ.1, hi⟩)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact psiG_conj _ _ _ _ hcm q3C_conj pwC_conj hPc hPi hg kFa
    · exact psiG_conj _ _ _ _ hcm q3C_conj pwC_conj hPc hPi hg kFb

end CFSG.Certificates.Kernel.PkCV.SmallF3T.K442375

end
