
module

public import Certificates.Kernel.GammaU.CensusConf
public import Certificates.Kernel.GammaU.CensusCfgOK
public import CFSG.Certificates.Kernel.GammaUCensusCfgSound

set_option maxRecDepth 100000

public section

local notation "GL" => CFSG.GF2Type.Smith1979.GammaU.V12 ≃ₗ[ZMod 2] CFSG.GF2Type.Smith1979.GammaU.V12

namespace CFSG.KD.GUCC

open CFSG.KC.IF4C CFSG.KC.IF4R CFSG.KC.GUC CFSG.KD.IF4L CFSG.KC.IF4L

theorem inv_spec : (∀ n < 4, mulP (look TE n) (look TEi n) = idP) ∧
    ∀ j < 108, mulP (look DT j) (look DTi j) = idP := by
  have h := cc16966c_inv
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  rw [h3] at h1
  exact ⟨invOK_spec _ _ h1, invOK_spec _ _ h2⟩

theorem isP_T {n j : Nat} (hn : n < 4) (hj : j < 108) {T : GL}
    (hT : IsP T (mulP (look TE n) (look DT j))) : IsP T⁻¹ (mulP (look DTi j) (look TEi n)) := by
  obtain ⟨A, hA⟩ := IsP.exists_of_mul (inv_spec.1 n hn)
  obtain ⟨B, hB⟩ := IsP.exists_of_mul (inv_spec.2 j hj)
  rw [IsP.inj hT (IsP.mul hA hB), mul_inv_rev]
  exact IsP.mul (IsP.inv hB (inv_spec.2 j hj)) (IsP.inv hA (inv_spec.1 n hn))

theorem mem_TB {c : Nat} (hc : c < 32) {U : GL} (hU : U ∈ pGrp (five CFSG.KD.GUC0.CG c))
    {a b : Nat} (hab : IsP U (mulP a b)) : ∃ m < 32, look TB (32 * c + m) = mulP a b := by
  have h := (allBelow_iff _ _).1 CFSG.KD.GUCB.cb16966_cg c hc
  rw [Bool.and_eq_true] at h
  have hex := CFSG.KD.GUCB.exists_isP_cg c hc
  have hF := forall₂_autP hex
  have he : pGrp (five CFSG.KD.GUC0.CG c) =
      Subgroup.closure {U | U ∈ (five CFSG.KD.GUC0.CG c).map autP} := by
    unfold pGrp
    congr 1
    ext U
    simp only [Set.mem_setOf_eq, List.mem_map]
    constructor
    · rintro ⟨g, hg, hU⟩
      exact ⟨g, hg, IsP.inj (isP_autP (hex g hg)) hU⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨g, hg, isP_autP (hex g hg)⟩
  rw [he] at hU
  obtain ⟨m, hm, rfl⟩ := (mem_closure_iff (commInv_of hF h.1)).1 hU
  have hm' : m < 32 := by simpa [five] using hm
  have hs := isP_subG hF m
  obtain ⟨g, k, hgk⟩ : ∃ g k, subP (five CFSG.KD.GUC0.CG c) m = mulP g k := ⟨_, _, rfl⟩
  rw [hgk] at hs
  refine ⟨m, hm', ?_⟩
  rw [tbOK_spec cc16966c_tb c hc m hm', hgk]
  exact mulP_eq_of_isP' hs hab

end CFSG.KD.GUCC

namespace CFSG.KD.GUC0

open CFSG.KC.IF4C CFSG.KC.IF4R CFSG.KC.GUC CFSG.KD.GUCC

theorem cfg_complete {n j c : Nat} (hn : n < 4) (hj : j < 108) (hc : c < 32) {T S : GL}
    (hT : IsP T (mulP (look TE n) (look DT j))) (hS : IsP S S0)
    (ha : ap12 (mulP (look DTi j) (look TEi n)) 3072 ∈
      CFSG.GF2Type.Smith1979.GammaU.spanList CFSG.GF2Type.Smith1979.GammaU.StepA.d0)
    (hs : T⁻¹ * S * T ∈ pGrp (five CG c)) :
    ∃ X < 384, look FT X = mulP (look TE n) (look DT j) ∧ fld FC X = c := by
  have hp : pairs0 n = true := cc16966c_p0all n hn
  unfold pairs0 at hp
  rcases pairOK_spec ((allBelow_iff _ _).1 hp j hj) ha c hc with h | h
  · have hu : IsP (T⁻¹ * S * T)
        (mulP (mulP (look DTi j) (look TEi n)) (mulP S0 (mulP (look TE n) (look DT j)))) := by
      rw [mul_assoc]
      exact IsP.mul (isP_T hn hj hT) (IsP.mul hS hT)
    obtain ⟨m, hm, e⟩ := mem_TB hc hs hu
    exact absurd e (h m hm)
  · exact ⟨_, h.1, h.2.1, h.2.2⟩

end CFSG.KD.GUC0

namespace CFSG.KD.GUC1

open CFSG.KC.IF4C CFSG.KC.IF4R CFSG.KC.GUC CFSG.KD.GUCC

theorem cfg_complete {n j c : Nat} (hn : n < 4) (hj : j < 108) (hc : c < 32) {T S : GL}
    (hT : IsP T (mulP (look TE n) (look DT j))) (hS : IsP S S0)
    (ha : ap12 (mulP (look DTi j) (look TEi n)) 3072 ∈
      CFSG.GF2Type.Smith1979.GammaU.spanList CFSG.GF2Type.Smith1979.GammaU.StepA.d0)
    (hs : T⁻¹ * S * T ∈ pGrp (five CG c)) :
    ∃ X < 384, look FT X = mulP (look TE n) (look DT j) ∧ fld FC X = c := by
  have hp : pairs1 n = true := cc16966c_p1all n hn
  unfold pairs1 at hp
  rw [cg_eq.1] at hs
  rcases pairOK_spec ((allBelow_iff _ _).1 hp j hj) ha c hc with h | h
  · have hu : IsP (T⁻¹ * S * T)
        (mulP (mulP (look DTi j) (look TEi n)) (mulP S0 (mulP (look TE n) (look DT j)))) := by
      rw [mul_assoc]
      exact IsP.mul (isP_T hn hj hT) (IsP.mul hS hT)
    obtain ⟨m, hm, e⟩ := mem_TB hc hs hu
    exact absurd e (h m hm)
  · exact ⟨_, h.1, h.2.1, h.2.2⟩

end CFSG.KD.GUC1

end
