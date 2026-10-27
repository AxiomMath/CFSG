
module

public import Certificates.Kernel.F4Planes.TwRows
public import Certificates.Kernel.F4Planes.E6Glue
public import CFSG.Certificates.Kernel.F4Planes.TwRowSound
import CFSG.Certificates.Kernel.Common.ForallTree
import all CFSG.LieType.SeitzGeneration.ExcHighThree.TwE6TwoBase
public import CFSG.Sporadic.ThSchreier.GlobalData
public import CFSG.LieType.SeitzGeneration.ExcHighThree.E6Two
public import CFSG.Sporadic.ThSchreier.LocalOrbitBase1
public import Certificates.Certificate14949Base

public section

namespace CFSG.KC.F4PlanesTw

open CFSG.LieType.SeitzGeneration.ExcHighThree CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LocalAnalysis.ComponentInitial
open CFSG.LieType.SeitzGeneration.ExcHighThree.TwE6Two (Setup tmat iota Xw0 Xw1 hasBits2_Xw0
  hasBits2_Xw1 exists_omega closure_conj_eq_top_gen)
open CFSG.LieType.SeitzGeneration.ExcHighThree.TwClose (letterBits2)
open CFSG.KC.F4Planes (sF q4F q5F pres_F exists_conj_le_of_card plane_conj planeR ch14950plAll)

#kc_forall_tree ch14946twAll (fun r => CFSG.KC.F4PlanesTw.rowAtT CFSG.KD.F4PlanesE6.IP
  CFSG.KD.F4PlanesTw.X8 CFSG.KD.F4PlanesTw.X9 CFSG.KD.F4PlanesE6.pS6 CFSG.KD.F4Planes.PR
  CFSG.KD.F4PlanesTw.ij CFSG.KD.F4PlanesTw.gens CFSG.KD.F4PlanesTw.zs r = true) 67
  CFSG.KD.F4PlanesTw.ch14946tw.r

theorem x89_ok :
    ((letterBits2 8).a % 2 ^ 6084 = fa CFSG.KD.F4PlanesTw.X8 / 2 ^ 192 % 2 ^ 6084 ∧
      (letterBits2 8).b % 2 ^ 6084 = fb CFSG.KD.F4PlanesTw.X8 / 2 ^ 192 % 2 ^ 6084) ∧
    ((letterBits2 9).a % 2 ^ 6084 = fa CFSG.KD.F4PlanesTw.X9 / 2 ^ 192 % 2 ^ 6084 ∧
      (letterBits2 9).b % 2 ^ 6084 = fb CFSG.KD.F4PlanesTw.X9 / 2 ^ 192 % 2 ^ 6084) := by
  decide +kernel

section Pins

variable {k K : Type} [Field k] [Finite k] [Field K] [Finite K] [Algebra k K] [CharP k 2]
  [CharP K 2] (σ : K ≃+* K) (S : Setup k K σ)

theorem hasP_X8 : HasP K S.ω (tmat (Xw0 σ S.hK S.hσ S.ω)) CFSG.KD.F4PlanesTw.X8 :=
  hasP_of_bits2 (hasBits2_Xw0 σ S.hK S.hσ S.hω) x89_ok.1

theorem hasP_X9 : HasP K S.ω (tmat (Xw1 σ S.hK S.hσ S.ω)) CFSG.KD.F4PlanesTw.X9 :=
  hasP_of_bits2 (hasBits2_Xw1 σ S.hK S.hσ S.hω) x89_ok.2

end Pins

theorem twCloseAtTwo_kernel : TwE6Two.TwCloseAtTwo := by
  intro K _ _ σ k _ _ _ hfix hK hσ hk E₃ hE3 hE9
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (k := 2)
    (by norm_num) hK
  have : CharP k 2 := finite_field_prime_power_characteristic Nat.prime_two (k := 1)
    (le_refl 1) (by simpa using hk)
  have hK4 : Nat.card K = 4 := by simpa using hK
  obtain ⟨ω, hω⟩ := exists_omega hK4
  let S : Setup k K σ := ⟨ω, hω, hfix, hK4, hσ⟩
  have hp := pres_F k
  have hm := CFSG.KC.F4Syl3.modelOK_of_chk CFSG.KD.F4Syl3.model_ok
  set P := Subgroup.closure (CFSG.KC.F4Syl3.gensP (CFSG.KC.F4Planes.sF k) (q4F k) (q5F k))
  have hP : Nat.card P = 3 ^ 6 := (CFSG.KC.F4Syl3.card_P hp hm).trans (by norm_num)
  have hG : Nat.card (adjointGroup ReeTag.F4.tag k) = 3311126603366400 := by
    have h := CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_F4 (K := k)
    rw [hk] at h
    exact h.trans (by norm_num [CFSG.Open.ordF4])
  have hidx : ¬ 3 ∣ P.index := by
    intro hd
    have h := P.card_mul_index
    rw [hP, hG] at h
    omega
  obtain ⟨g, hg⟩ := exists_conj_le_of_card hP hidx hE9
  have hinj : Function.Injective (MulAut.conj g).toMonoidHom := fun a b h =>
    (MulAut.conj g).injective h
  have hE₁9 : Nat.card (E₃.map (MulAut.conj g).toMonoidHom) = 9 :=
    (Subgroup.card_map_of_injective hinj).trans hE9
  have hE₁3 : ∀ x ∈ E₃.map (MulAut.conj g).toMonoidHom, x ^ 3 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    exact (map_pow (MulAut.conj g).toMonoidHom x 3).symm.trans
      ((congrArg _ (hE3 x hx)).trans (map_one _))
  obtain ⟨r, hr, z₀, -, hz₀⟩ := plane_conj hp hm CFSG.KD.F4Syl3.cover_ok CFSG.KD.F4Planes.tab_ok
    CFSG.KD.F4Planes.om_ok CFSG.KD.F4Planes.rep_ok ch14950plAll hg hE₁3 hE₁9
  obtain ⟨g, z, hz⟩ : ∃ g z : adjointGroup Tag.F4 k, E₃.map (MulAut.conj g).toMonoidHom =
      (planeR (CFSG.KC.F4Planes.sF k) (q4F k) (q5F k) CFSG.KD.F4Planes.PR r).map (MulAut.conj z).toMonoidHom :=
    ⟨g, z₀, hz₀⟩
  obtain ⟨e₀, he₀, he₀1, hcl₀⟩ := rowAtT_sound σ S
    (fun c hc => (CFSG.KC.F4PlanesE6.hasBitsS_iotaL k hc).1) (hasP_X8 σ S) (hasP_X9 σ S)
    (CFSG.KC.F4PlanesE6.hasBitsS_iota_sF k) (CFSG.KC.F4PlanesE6.hasBitsS_iota_q4F k)
    (CFSG.KC.F4PlanesE6.hasBitsS_iota_q5F k) (ch14946twAll r hr)
  have hmem : z * e₀ * z⁻¹ ∈ E₃.map (MulAut.conj g).toMonoidHom := by
    rw [hz]
    exact ⟨e₀, he₀, rfl⟩
  obtain ⟨x, hxE, hxe⟩ := hmem
  have hx : x = (g⁻¹ * z) * e₀ * (g⁻¹ * z)⁻¹ := by
    have h1 : g * x * g⁻¹ = z * e₀ * z⁻¹ := hxe
    calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
      _ = (g⁻¹ * z) * e₀ * (g⁻¹ * z)⁻¹ := by rw [h1]; group
  refine ⟨x, hxE, ?_, ?_⟩
  · rw [hx]
    intro h
    apply he₀1
    calc e₀ = (g⁻¹ * z)⁻¹ * ((g⁻¹ * z) * e₀ * (g⁻¹ * z)⁻¹) * (g⁻¹ * z) := by group
      _ = 1 := by rw [h]; group
  · rw [hx]
    have hk' : iota σ S.hfix (g⁻¹ * z)⁻¹ ∈ (iota σ S.hfix).range := ⟨_, rfl⟩
    have := closure_conj_eq_top_gen (iota σ S.hfix).range (iota σ S.hfix (g⁻¹ * z)⁻¹) hk'
      (iota σ S.hfix e₀) hcl₀
    have e : (iota σ S.hfix (g⁻¹ * z)⁻¹)⁻¹ * iota σ S.hfix e₀ * iota σ S.hfix (g⁻¹ * z)⁻¹ =
        iota σ S.hfix ((g⁻¹ * z) * e₀ * (g⁻¹ * z)⁻¹) := by
      rw [map_mul, map_mul, ← map_inv]
      simp
    rw [e] at this
    exact this

end CFSG.KC.F4PlanesTw

end
