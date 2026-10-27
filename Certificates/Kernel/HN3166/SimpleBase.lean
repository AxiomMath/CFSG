
module

public import Certificates.Kernel.HN3166.CardBase
public import Certificates.Kernel.HN3166.Alg
public import CFSG.Sporadic.HN.CoprimeSimple

@[expose] public section

namespace CertificateChecks.KernelHN

open CFSG.Sporadic.F5 CFSG.Sporadic.HN

local notation "Dt" => CFSG.Sporadic.HN.Native.hnData

theorem a_sq : a Dt ^ 2 = 1 := by
  apply mat_injective Dt
  rw [mat_pow', mat_a' det_mA, mA_sq, mat_one']

theorem b_cube : b Dt ^ 3 = 1 := by
  apply mat_injective Dt
  rw [mat_pow', mat_b' det_mB, mB_cube, mat_one']

theorem center_J : Subgroup.center (J Dt) = ⊥ := by
  obtain ⟨g, hg⟩ := orderOf_x
  have hx : (a Dt * (g⁻¹ * b Dt * g)) ^ 19 = 1 := by rw [← hg]; exact pow_orderOf_eq_one _
  exact center_J_eq_bot (by decide) mA_sq mB_cube (by norm_num) hx commutant_scalar

theorem simple_of_facts {D : CFSG.Sporadic.F5.Native.F5Data} {g : J D} (ha : a D ^ 2 = 1)
    (hb : b D ^ 3 = 1) (hx : orderOf (a D * (g⁻¹ * b D * g)) = 19)
    (hZ : Subgroup.center (J D) = ⊥) (hc : Nat.card (J D) = 273030912000000) :
    IsSimpleGroup (J D) := by
  have : Finite (J D) := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  refine isSimpleGroup_of_conjProd (by norm_num) (closure_ab D) ha hb hx ?_ hZ ?_
  · rw [hc]
    norm_num
  · rw [hc]
    exact hn_GL_condition

end CertificateChecks.KernelHN

end
