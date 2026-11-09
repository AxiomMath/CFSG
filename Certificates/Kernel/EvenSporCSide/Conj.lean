module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CSide.ModelCheck

public section

namespace CertificateChecks.KernelCSide

open CFSG.EvenSporadicStandard.HNRecog.CSide

@[expose] def r3 : SL2 := ⟨!![0, 1; 1, 1], by rw [Matrix.det_fin_two_of]; decide⟩

@[expose] def r5 : SL2 := ⟨!![0, 1; 1, F4.omega], by rw [Matrix.det_fin_two_of]; decide⟩

@[expose] def r5b : SL2 := ⟨!![0, 1; 1, F4.omega * F4.omega], by rw [Matrix.det_fin_two_of]; decide⟩

@[expose] def t2 : SL2 := ⟨!![1, 1; 0, 1], by rw [Matrix.det_fin_two_of]; decide⟩

theorem actFun_inv_act (c : SL2 × SL2) (M : V0) : actFun c (actFun c⁻¹ M) = M := by
  rw [← actFun_mul, mul_inv_cancel, actFun_one]

theorem actFun_act_inv (c : SL2 × SL2) (M : V0) : actFun c⁻¹ (actFun c M) = M := by
  rw [← actFun_mul, inv_mul_cancel, actFun_one]

theorem actFun_add (c : SL2 × SL2) (M N : V0) : actFun c (M + N) = actFun c M + actFun c N :=
  (actLinEquiv c).map_add M N

theorem actFun_zero (c : SL2 × SL2) : actFun c 0 = 0 := (actLinEquiv c).map_zero

theorem q0Fun_actFun (c : SL2 × SL2) (M : V0) : q0Fun (actFun c M) = q0Fun M := by
  simp only [q0Fun, det0_actFun]

theorem q0Polar_actFun (c : SL2 × SL2) (M N : V0) :
    q0Polar (actFun c M) (actFun c N) = q0Polar M N := by
  have h1 := q0Fun_add (actFun c M) (actFun c N)
  have h2 := q0Fun_add M N
  rw [← actFun_add, q0Fun_actFun, q0Fun_actFun, q0Fun_actFun, h2] at h1
  exact (add_left_cancel h1).symm

theorem mem_fix_conj {c g : SL2 × SL2} {M : V0} :
    M ∈ cSideFix (c * g * c⁻¹) ↔ actFun c⁻¹ M ∈ cSideFix g := by
  simp only [cSideFix, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    have e : c⁻¹ * (c * g * c⁻¹) = g * c⁻¹ := by
      rw [← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [← actFun_mul, ← e, actFun_mul, h]
  · intro h
    rw [actFun_mul, actFun_mul, h, actFun_inv_act]

theorem card_fix_conj (c g : SL2 × SL2) : (cSideFix (c * g * c⁻¹)).card = (cSideFix g).card := by
  refine Finset.card_bij' (fun M _ => actFun c⁻¹ M) (fun N _ => actFun c N) ?_ ?_ ?_ ?_
  · intro M hM
    exact mem_fix_conj.1 hM
  · intro N hN
    apply mem_fix_conj.2
    rwa [actFun_act_inv]
  · intro M _
    exact actFun_inv_act c M
  · intro N _
    exact actFun_act_inv c N

theorem zero_conj {c g : SL2 × SL2} (h : ∀ M ∈ cSideFix g, M = 0) :
    ∀ M ∈ cSideFix (c * g * c⁻¹), M = 0 := fun M hM => by
  rw [← actFun_inv_act c M, h _ (mem_fix_conj.1 hM), actFun_zero]

theorem nondeg_conj {c g : SL2 × SL2} (h : cSideNondegOn (cSideFix g)) :
    cSideNondegOn (cSideFix (c * g * c⁻¹)) := by
  intro M hM hM0
  have hne : actFun c⁻¹ M ≠ 0 := fun e => hM0 (by rw [← actFun_inv_act c M, e, actFun_zero])
  obtain ⟨N, hN, hP⟩ := h _ (mem_fix_conj.1 hM) hne
  refine ⟨actFun c N, mem_fix_conj.2 (by rwa [actFun_act_inv]), ?_⟩
  rw [← actFun_inv_act c M, q0Polar_actFun]
  exact hP

theorem plane_conj {c g : SL2 × SL2} (h : cSidePlaneOn (cSideFix g)) :
    cSidePlaneOn (cSideFix (c * g * c⁻¹)) := by
  obtain ⟨M, hM, N, hN, hM0, hN0, hMN, hMq, hNq, hP⟩ := h
  have inj : ∀ X Y : V0, actFun c X = actFun c Y → X = Y := fun X Y e => by
    rw [← actFun_act_inv c X, e, actFun_act_inv]
  refine ⟨actFun c M, mem_fix_conj.2 (by rwa [actFun_act_inv]), actFun c N,
    mem_fix_conj.2 (by rwa [actFun_act_inv]), fun e => hM0 (inj _ _ (by rw [e, actFun_zero])),
    fun e => hN0 (inj _ _ (by rw [e, actFun_zero])), fun e => hMN (inj _ _ e), ?_, ?_, ?_⟩
  · rwa [q0Fun_actFun]
  · rwa [q0Fun_actFun]
  · rwa [q0Polar_actFun]

theorem conj_of_mul {r a h : SL2} (e : h * r = a * h) : h * r * h⁻¹ = a := by
  rw [e, mul_inv_cancel_right]

theorem prod_conj {g : SL2 × SL2} {r s h k : SL2} (eh : h * r = g.1 * h) (ek : k * s = g.2 * k) :
    (h, k) * (r, s) * (h, k)⁻¹ = g :=
  Prod.ext (conj_of_mul eh) (conj_of_mul ek)

end CertificateChecks.KernelCSide
