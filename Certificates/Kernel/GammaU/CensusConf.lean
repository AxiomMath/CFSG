
module

public import Certificates.Kernel.GammaU.CensusFacts
public import Certificates.Kernel.GammaU.CensusBridgeOK
public import Certificates.Kernel.IdxFour.AutP
public import Mathlib.Data.List.GetD
public import CFSG.Certificates.Kernel.GammaUCensusConj
public import CFSG.Certificates.Kernel.GammaUSigmaSoundBase

set_option maxRecDepth 100000

public section

local notation "GL" => CFSG.GF2Type.Smith1979.GammaU.V12 ≃ₗ[ZMod 2] CFSG.GF2Type.Smith1979.GammaU.V12

namespace CFSG.KD.GUCB

open CFSG.KC.IF4C CFSG.KC.IF4R CFSG.KC.GUC CFSG.KD.IF4L CFSG.KC.IF4L CFSG.KC.GUS
open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA

theorem cg_inv : ∀ l < 160, mulP (look CFSG.KD.GUC0.CG l) (look CFSG.KD.GUC0.CGI l) = idP := by
  have h := CFSG.KD.GUC0.cc16966a_inv
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  exact invOK_spec _ _ h.1.2

theorem exists_isP_cg : ∀ c < 32, ∀ g ∈ five CFSG.KD.GUC0.CG c, ∃ U, IsP U g := by
  intro c hc g hg
  obtain ⟨l, hl, rfl⟩ := mem_five.1 hg
  exact IsP.exists_of_mul (cg_inv _ (by omega))

theorem card_pGrp : ∀ c < 32, Nat.card (pGrp (five CFSG.KD.GUC0.CG c)) = 32 := by
  intro c hc
  have h := (allBelow_iff _ _).1 cb16966_cg c hc
  rw [Bool.and_eq_true] at h
  have hex := exists_isP_cg c hc
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
  have hl : ((five CFSG.KD.GUC0.CG c).map autP).length = 5 := by simp [five]
  rw [he, card_closure (commInv_of hF h.1) (ne_one_of_subOK hF (by simp [five]) h.2), hl]
  rfl

theorem linP_cg {c l : Nat} (hc : c < 32) (hl : l < 5) (v : V12) :
    linP (look CFSG.KD.GUC0.CG (5 * c + l)) v = linOfRows ((ResPair.compGens c).getD l #[]) v := by
  obtain ⟨hk0, hb, -⟩ := cb16966_rows
  have hget : (ResPair.compGens c).getD l #[] =
      if c.testBit l then mulR k0 cBasis[l]! else cBasis[l]! := by
    simp [ResPair.compGens, List.getD_eq_getElem?_getD, hl]
  rw [cb16966_gens c hc l hl, hget]
  cases c.testBit l
  · exact linP_eq_of_rowsP (rowsP_packR (hb l hl)) v
  · change linP (mulP (packR k0) (packR cBasis[l]!)) v = linOfRows (mulR k0 cBasis[l]!) v
    rw [linP_mulP, linP_eq_of_rowsP (rowsP_packR (hb l hl)),
      linP_eq_of_rowsP (rowsP_packR hk0), linOfRows_mulR]

theorem length_compGens (c : Nat) : (ResPair.compGens c).length = 5 := by
  simp [ResPair.compGens]

theorem pGrp_eq_genGrp {c : Nat} (hc : c < 32) :
    pGrp (five CFSG.KD.GUC0.CG c) = Viol.genGrp (ResPair.compGens c) := by
  unfold pGrp Viol.genGrp Viol.GenSet
  congr 1
  ext U
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨g, hg, hU⟩
    obtain ⟨l, hl, rfl⟩ := mem_five.1 hg
    refine ⟨(ResPair.compGens c).getD l #[], ?_, fun x => (hU x).trans (linP_cg hc hl x)⟩
    rw [List.getD_eq_getElem _ _ (by rw [length_compGens]; exact hl)]
    exact List.getElem_mem _
  · rintro ⟨r, hr, hU⟩
    obtain ⟨l, hl, rfl⟩ := List.getElem_of_mem hr
    have hl5 : l < 5 := by rw [← length_compGens c]; exact hl
    refine ⟨_, mem_five.2 ⟨l, hl5, rfl⟩, fun x => ?_⟩
    rw [hU x, linP_cg hc hl5 x, List.getD_eq_getElem _ _ hl]

theorem isP_TH_iff (U : GL) : IsP U CFSG.KD.GUC0.TH ↔ ∀ v, U v = linOfRows theta0R v := by
  rw [cb16966_th]
  exact isP_packR cb16966_rows.2.2 U

end CFSG.KD.GUCB

namespace CFSG.KD.GUC0

open CFSG.KC.IF4C CFSG.KC.IF4R CFSG.KC.GUC CFSG.KD.IF4L

theorem inv_spec : (∀ X < 384, mulP (look FT X) (look FTi X) = idP) ∧
    (∀ k < NC, mulP (look CS k) (look CSI k) = idP) ∧ mulP TH (mulP TH TH) = idP := by
  have h := cc16966a_inv
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  exact ⟨invOK_spec _ _ h.1.1.1, invOK_spec _ _ h.1.1.2, h.2⟩

theorem len_spec :
    ED.length = 384 ∧ OR.length = 11 ∧ CN.length = NC ∧ ∀ X < 384, fld FC X < 32 := by
  have h := cc16966a_len
  simp only [Bool.and_eq_true, Nat.beq_eq, allBelow_iff, Nat.blt_eq, lenN_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

@[expose] noncomputable def TX (X : Nat) : GL := autP (look FT X)

@[expose] noncomputable def θA : GL := autP TH

theorem isP_TX {X : Nat} (hX : X < 384) : IsP (TX X) (look FT X) :=
  isP_autP (IsP.exists_of_mul (inv_spec.1 X hX))

theorem isP_θA : IsP θA TH := isP_autP (IsP.exists_of_mul inv_spec.2.2)

theorem confR_conj : ∀ X < 384, ∃ h : GL,
    confR CG FC 0 TX θA X = (confR CG FC 0 TX θA (fld LB X)).map (MulAut.conj h).toMonoidHom := by
  obtain ⟨hED, -, hNC, hFC⟩ := len_spec
  have hE := entOK_of_blk (K := 24) (by rw [hED]) cc16966a_blkall
  rw [hED] at hE
  exact confR_conj_root hE cc16966a_cn hNC inv_spec.2.1 inv_spec.1
    (CFSG.KD.GUCB.exists_isP_cg 0 (by norm_num))
    (fun X hX => CFSG.KD.GUCB.exists_isP_cg _ (hFC X hX))
    (fun X hX => CFSG.KD.GUCB.card_pGrp _ (hFC X hX)) (fun X hX => isP_TX hX) isP_θA

theorem confR_eq_lGrp {X G : Nat} (hX : X < 384) (h : candOK CG FT FTi FC TH 0 X G = true) :
    lGrp G 11 = confR CG FC 0 TX θA X :=
  lGrp_eq_confR h (fun l hl => IsP.exists_of_mul (CFSG.KD.GUCB.cg_inv _ (by
    have := len_spec.2.2.2 X hX
    omega))) (isP_TX hX) (IsP.inv (isP_TX hX) (inv_spec.1 X hX)) isP_θA

theorem ar_lt : AR < 384 := by decide +kernel

theorem census_s0 : ∀ X < 384, (Nat.card (confR CG FC 0 TX θA X) = 1152 ↔ fld LB X = AR) ∧
    (fld LB X = AR →
      ∃ h : GL, confR CG FC 0 TX θA X = (lGrp AG 11).map (MulAut.conj h).toMonoidHom) := by
  have hAR : lGrp AG 11 = confR CG FC 0 TX θA AR := confR_eq_lGrp ar_lt kgens_spec.2.2.2.2
  have hrej : ∀ r ∈ OR, Nat.card (confR CG FC 0 TX θA r) ≠ 1152 := by
    intro r hr
    obtain ⟨q, hq, rfl⟩ := List.getElem_of_mem hr
    have hq11 : q < 11 := by rw [← len_spec.2.1]; exact hq
    have h := cc16966a_orball q hq11
    unfold orb at h
    rw [Bool.and_eq_true, nthD_eq, nthD_eq] at h
    rw [← List.getD_eq_getElem _ 0 hq, ← confR_eq_lGrp (or_lt q hq11) h.1]
    exact card_OG q hq11
  have hc := classify confR_conj cc16966a_lab hrej (by rw [← hAR]; exact card_AG)
  intro X hX
  refine ⟨(hc X hX).1, fun ha => ?_⟩
  rw [hAR]
  exact (hc X hX).2 ha

end CFSG.KD.GUC0

namespace CFSG.KD.GUC1

open CFSG.KC.IF4C CFSG.KC.IF4R CFSG.KC.GUC CFSG.KD.IF4L

theorem cg_eq : CG = CFSG.KD.GUC0.CG ∧ TH = CFSG.KD.GUC0.TH := by
  have h := CFSG.KD.GUCB.cb16966_eq
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  exact ⟨h.1.1, h.2⟩

theorem inv_spec : (∀ X < 384, mulP (look FT X) (look FTi X) = idP) ∧
    (∀ k < NC, mulP (look CS k) (look CSI k) = idP) ∧
    (∀ l < 160, mulP (look CG l) (look CGI l) = idP) ∧ mulP TH (mulP TH TH) = idP := by
  have h := cc16966b_inv
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  exact ⟨invOK_spec _ _ h.1.1.1, invOK_spec _ _ h.1.1.2, invOK_spec _ _ h.1.2, h.2⟩

theorem len_spec :
    ED.length = 384 ∧ OR.length = 11 ∧ CN.length = NC ∧ ∀ X < 384, fld FC X < 32 := by
  have h := cc16966b_len
  simp only [Bool.and_eq_true, Nat.beq_eq, allBelow_iff, Nat.blt_eq, lenN_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem exists_isP_cg : ∀ c < 32, ∀ g ∈ five CG c, ∃ U, IsP U g := by
  rw [cg_eq.1]
  exact CFSG.KD.GUCB.exists_isP_cg

theorem card_pGrp : ∀ c < 32, Nat.card (pGrp (five CG c)) = 32 := by
  rw [cg_eq.1]
  exact CFSG.KD.GUCB.card_pGrp

@[expose] noncomputable def TX (X : Nat) : GL := autP (look FT X)

@[expose] noncomputable def θA : GL := autP TH

theorem isP_TX {X : Nat} (hX : X < 384) : IsP (TX X) (look FT X) :=
  isP_autP (IsP.exists_of_mul (inv_spec.1 X hX))

theorem isP_θA : IsP θA TH := isP_autP (IsP.exists_of_mul inv_spec.2.2.2)

theorem confR_conj : ∀ X < 384, ∃ h : GL,
    confR CG FC 1 TX θA X = (confR CG FC 1 TX θA (fld LB X)).map (MulAut.conj h).toMonoidHom := by
  obtain ⟨hED, -, hNC, hFC⟩ := len_spec
  have hE := entOK_of_blk (K := 24) (by rw [hED]) cc16966b_blkall
  rw [hED] at hE
  exact confR_conj_root hE cc16966b_cn hNC inv_spec.2.1 inv_spec.1 (exists_isP_cg 1 (by norm_num))
    (fun X hX => exists_isP_cg _ (hFC X hX)) (fun X hX => card_pGrp _ (hFC X hX))
    (fun X hX => isP_TX hX) isP_θA

theorem confR_eq_lGrp {X G : Nat} (hX : X < 384) (h : candOK CG FT FTi FC TH 1 X G = true) :
    lGrp G 11 = confR CG FC 1 TX θA X :=
  lGrp_eq_confR h (fun l hl => IsP.exists_of_mul (inv_spec.2.2.1 _ (by
    have := len_spec.2.2.2 X hX
    omega))) (isP_TX hX) (IsP.inv (isP_TX hX) (inv_spec.1 X hX)) isP_θA

theorem ar_lt : AR < 384 := by decide +kernel

theorem census_s0 : ∀ X < 384, (Nat.card (confR CG FC 1 TX θA X) = 1152 ↔ fld LB X = AR) ∧
    (fld LB X = AR →
      ∃ h : GL, confR CG FC 1 TX θA X = (lGrp AG 11).map (MulAut.conj h).toMonoidHom) := by
  have hAR : lGrp AG 11 = confR CG FC 1 TX θA AR := confR_eq_lGrp ar_lt kgens_spec.2.2.2.2
  have hrej : ∀ r ∈ OR, Nat.card (confR CG FC 1 TX θA r) ≠ 1152 := by
    intro r hr
    obtain ⟨q, hq, rfl⟩ := List.getElem_of_mem hr
    have hq11 : q < 11 := by rw [← len_spec.2.1]; exact hq
    have h := cc16966b_orball q hq11
    unfold orb at h
    rw [Bool.and_eq_true, nthD_eq, nthD_eq] at h
    rw [← List.getD_eq_getElem _ 0 hq, ← confR_eq_lGrp (or_lt q hq11) h.1]
    exact card_OG q hq11
  have hc := classify confR_conj cc16966b_lab hrej (by rw [← hAR]; exact card_AG)
  intro X hX
  refine ⟨(hc X hX).1, fun ha => ?_⟩
  rw [hAR]
  exact (hc X hX).2 ha

end CFSG.KD.GUC1

end
