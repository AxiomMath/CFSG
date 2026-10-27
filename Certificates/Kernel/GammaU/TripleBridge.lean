module

public import Certificates.Kernel.GammaU.BaseBridge
public import Certificates.Kernel.GammaU.Norm

set_option maxRecDepth 100000

public section

local notation "GL" => CFSG.GF2Type.Smith1979.GammaU.V12 ≃ₗ[ZMod 2] CFSG.GF2Type.Smith1979.GammaU.V12

namespace CFSG.KD.GUBB

open CFSG.KC.IF4C CFSG.KC.IF4R CFSG.KC.GUC CFSG.KC.GUV
open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA

theorem ch16969a_um : ∀ r ∈ unitaryElts 0, r ∈ ResPair.hyp10 0 ∨
    ∃ q < 12, rowsP (subQ CFSG.KD.GUT0.L (nthD 0 CFSG.KD.GUT0.UM q)) = r := by
  decide +kernel

theorem ch16969b_um : ∀ r ∈ unitaryElts 1, r ∈ ResPair.hyp10 1 ∨
    ∃ q < 12, rowsP (subQ CFSG.KD.GUT1.L (nthD 0 CFSG.KD.GUT1.UM q)) = r := by
  decide +kernel

theorem rowsConj_of {C : GL} {c s s0 : Nat} (hC : IsP C c) (h : mulP s c = mulP c s0) :
    RowsConj C (rowsP s) (rowsP s0) := by
  intro y
  have e := congrArg (fun m => linP m y) h
  simp only [linP_mulP] at e
  change linP s0 y = C⁻¹ (linP s (C y))
  rw [hC y, e, ← hC, inv_apply_apply]

theorem tripleFacts : ∀ i, i = 0 ∨ i = 1 → TripleFacts i := by
  rintro i (rfl | rfl)
  · refine ⟨_, TD, 108, te0, ⟨CFSG.KD.GUSB.s0_mem_0, frameTr, colTr0⟩, fun r hr hrH => ?_⟩
    obtain ⟨q, hq, rfl⟩ := (ch16969a_um r hr).resolve_left hrH
    obtain ⟨C, hC, -, hCm, hcomm, -⟩ := CFSG.KD.GUT0.triple_s0 (x := 0) (by norm_num) hq
    obtain ⟨h1, h2, h3, h4⟩ := CFSG.KD.GUN0.nl_mem hCm
    refine ⟨C, ⟨h1, h2, h3, h4⟩, rowsConj_of hC hcomm, cfgAll0 fun X hX hl => ?_⟩
    obtain ⟨x, hx, rfl⟩ := List.getElem_of_mem (CFSG.KD.GUT0.ar_mem hX hl)
    have hx12 : x < 12 := by rw [← CFSG.KD.GUT0.lists_spec.2.1]; exact hx
    obtain ⟨C', hC', -, -, -, hv⟩ := CFSG.KD.GUT0.triple_s0 hx12 hq
    rw [IsP.inj hC' hC, nthD_eq, List.getD_eq_getElem _ _ hx] at hv
    exact hv
  · refine ⟨_, TD, 108, te0, ⟨CFSG.KD.GUSB.s0_mem_1, frameTr, colTr1⟩, fun r hr hrH => ?_⟩
    obtain ⟨q, hq, rfl⟩ := (ch16969b_um r hr).resolve_left hrH
    obtain ⟨C, hC, -, hCm, hcomm, -⟩ := CFSG.KD.GUT1.triple_s0 (x := 0) (by norm_num) hq
    obtain ⟨h1, h2, h3, h4⟩ := CFSG.KD.GUN1.nl_mem hCm
    refine ⟨C, ⟨h1, h2, h3, h4⟩, rowsConj_of hC hcomm, cfgAll1 fun X hX hl => ?_⟩
    obtain ⟨x, hx, rfl⟩ := List.getElem_of_mem (CFSG.KD.GUT1.ar_mem hX hl)
    have hx4 : x < 4 := by rw [← CFSG.KD.GUT1.lists_spec.2.1]; exact hx
    obtain ⟨C', hC', -, -, -, hv⟩ := CFSG.KD.GUT1.triple_s0 hx4 hq
    rw [IsP.inj hC' hC, nthD_eq, List.getD_eq_getElem _ _ hx] at hv
    exact hv

end CFSG.KD.GUBB

end
