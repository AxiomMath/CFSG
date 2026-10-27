
module

public import Certificates.Kernel.F4Planes.E6Rows
public import Certificates.Kernel.F4Planes.Glue
public import CFSG.Certificates.Kernel.F4Planes.E6RowSound
import CFSG.Certificates.Kernel.Common.ForallTree
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcE8Rank1
public import CFSG.GH74.Statements
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.E8.MPart
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Transport
public import CFSG.HardMathSupport.Lang.AnisoE6.CatBridge
public import CFSG.RankThree.Chevalley.SteinbergBNNoninnerComponentNodes
public import CFSG.RankThree.Chevalley.SteinbergCFOddE7E8NoninnerComponent
public import CFSG.RankThree.PartOne.KE.A1Fixed
public import CFSG.RankThree.PartOne.KE.Basic
public import CFSG.RankThree.PartOne.KE.D4LayerAlgebraic
public import CFSG.RankThree.PartOne.KE.E7FiveBlock
public import CFSG.RankThree.PartOne.KE.E8FourA1Family
public import CFSG.RankThree.PartOne.KE.E8NineData
public import CFSG.RankThree.PartOne.KE.NativeCyclicMain
public import CFSG.RankThree.PartOne.KF4.EvenDescent
public import CFSG.RankThree.PartOne.KGD.D4QA1
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

namespace CFSG.KC.F4PlanesE6

open CFSG.KC.E6Salt CFSG.LieType.SeitzGeneration.ExcHighThree CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LocalAnalysis.ComponentInitial
open CFSG.KC.F4Planes (sF q4F q5F pres_F exists_conj_le_of_card plane_conj planeR ch14950plAll)

#kc_forall_tree ch14949rwAll (fun r => CFSG.KC.F4PlanesE6.rowAt CFSG.KD.F4PlanesE6.LP
  CFSG.KD.F4PlanesE6.IP CFSG.KD.F4PlanesE6.IPi CFSG.KD.F4PlanesE6.pS6 CFSG.KD.F4Planes.PR
  CFSG.KD.F4PlanesE6.ij CFSG.KD.F4PlanesE6.gens CFSG.KD.F4PlanesE6.tgs r = true) 67
  CFSG.KD.F4PlanesE6.ch14949rw.r

theorem iw_ok : ∀ c < 8, decW 4 (CFSG.KD.F4PlanesE6.iw.getD c 0) (CFSG.KD.F4PlanesE6.il.getD c 0) =
    CFSG.LieType.SeitzGeneration.ExcHighThree.E6Two.f4ToE6Letter c := by
  decide +kernel

section Pins

variable (K : Type) [Field K] [CharP K 2]

theorem hasBitsS_iotaL {c : ℕ} (hc : c < 8) :
    HasBitsS K (iotaL K c) (letT CFSG.KD.F4PlanesE6.IP c) ∧
      HasBitsS K (iotaL K c)⁻¹ (letT CFSG.KD.F4PlanesE6.IPi c) :=
  iota_sound CFSG.KD.F4PlanesE6.let_ok CFSG.KD.F4PlanesE6.iota_ok iw_ok hc

theorem hasBitsS_iota_sF (i : Fin 4) :
    HasBitsS K (embE6F4 K (CFSG.KC.F4Planes.sF K i)) (CFSG.KD.F4PlanesE6.pS6.getD i 0) :=
  pinE_sound (fun c hc => (hasBitsS_iotaL K hc).1) CFSG.KD.F4PlanesE6.pin6_ok
    (by omega : i.val < 6)

theorem hasBitsS_iota_q4F :
    HasBitsS K (embE6F4 K (q4F K)) (CFSG.KD.F4PlanesE6.pS6.getD 4 0) :=
  pinE_sound (fun c hc => (hasBitsS_iotaL K hc).1) CFSG.KD.F4PlanesE6.pin6_ok (by decide : 4 < 6)

theorem hasBitsS_iota_q5F :
    HasBitsS K (embE6F4 K (q5F K)) (CFSG.KD.F4PlanesE6.pS6.getD 5 0) :=
  pinE_sound (fun c hc => (hasBitsS_iotaL K hc).1) CFSG.KD.F4PlanesE6.pin6_ok (by decide : 5 < 6)

end Pins

theorem e6CloseAtTwo_kernel : E6Two.E6CloseAtTwo := by
  intro K _ _ hK E₃ hE3 hE9
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (k := 1)
    (le_refl 1) (by simpa using hK)
  have hp := pres_F K
  have hm := CFSG.KC.F4Syl3.modelOK_of_chk CFSG.KD.F4Syl3.model_ok
  set P := Subgroup.closure (CFSG.KC.F4Syl3.gensP (CFSG.KC.F4Planes.sF K) (q4F K) (q5F K))
  have hP : Nat.card P = 3 ^ 6 := (CFSG.KC.F4Syl3.card_P hp hm).trans (by norm_num)
  have hG : Nat.card (adjointGroup ReeTag.F4.tag K) = 3311126603366400 := by
    have h := CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_F4 (K := K)
    rw [hK] at h
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
  obtain ⟨g, z, hz⟩ : ∃ g z : adjointGroup Tag.F4 K, E₃.map (MulAut.conj g).toMonoidHom =
      (planeR (CFSG.KC.F4Planes.sF K) (q4F K) (q5F K) CFSG.KD.F4Planes.PR r).map (MulAut.conj z).toMonoidHom :=
    ⟨g, z₀, hz₀⟩
  obtain ⟨e₀, he₀, he₀1, hcl₀⟩ := rowAt_sound hK CFSG.KD.F4PlanesE6.let_ok
    (fun c hc => hasBitsS_iotaL K hc) (hasBitsS_iota_sF K) (hasBitsS_iota_q4F K)
    (hasBitsS_iota_q5F K) (ch14949rwAll r hr)
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
    have hk : embE6F4 K (g⁻¹ * z)⁻¹ ∈ (embE6F4 K).range := ⟨_, rfl⟩
    have := closure_conj_eq_top K (embE6F4 K).range (embE6F4 K (g⁻¹ * z)⁻¹) hk (embE6F4 K e₀) hcl₀
    have e : (embE6F4 K (g⁻¹ * z)⁻¹)⁻¹ * embE6F4 K e₀ * embE6F4 K (g⁻¹ * z)⁻¹ =
        embE6F4 K ((g⁻¹ * z) * e₀ * (g⁻¹ * z)⁻¹) := by
      rw [map_mul, map_mul, ← map_inv]
      simp
    rw [e] at this
    exact this

end CFSG.KC.F4PlanesE6

end
