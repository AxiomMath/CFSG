module

public import Certificates.Kernel.OmegaEight.C3006D
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.OmegaEight.C3006S
import Mathlib.Tactic.FinCases

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelO8.C3006

open CFSG.EvenSmallLie.OmegaEight CFSG.EvenSmallLie.OmegaEight.Cover CFSG.KC.CycTab CFSG.KC.CycTabW

theorem genArrs_cyc_0 :
    ((genArrs[(0 : Fin 8).val]!).toList == (List.range 360).map (cycsS 360 (genCycles 0))) = true := by
  quickRfl

theorem genArrs_cyc_1 :
    ((genArrs[(1 : Fin 8).val]!).toList == (List.range 360).map (cycsS 360 (genCycles 1))) = true := by
  quickRfl

theorem genArrs_cyc_2 :
    ((genArrs[(2 : Fin 8).val]!).toList == (List.range 360).map (cycsS 360 (genCycles 2))) = true := by
  quickRfl

theorem genArrs_cyc_3 :
    ((genArrs[(3 : Fin 8).val]!).toList == (List.range 360).map (cycsS 360 (genCycles 3))) = true := by
  quickRfl

theorem genArrs_cyc_4 :
    ((genArrs[(4 : Fin 8).val]!).toList == (List.range 360).map (cycsS 360 (genCycles 4))) = true := by
  quickRfl

theorem genArrs_cyc_5 :
    ((genArrs[(5 : Fin 8).val]!).toList == (List.range 360).map (cycsS 360 (genCycles 5))) = true := by
  quickRfl

theorem genArrs_cyc_6 :
    ((genArrs[(6 : Fin 8).val]!).toList == (List.range 360).map (cycsS 360 (genCycles 6))) = true := by
  quickRfl

theorem genArrs_cyc_7 :
    ((genArrs[(7 : Fin 8).val]!).toList == (List.range 360).map (cycsS 360 (genCycles 7))) = true := by
  quickRfl

theorem genArrs_cyc : ((List.finRange 8).all fun j =>
    (genArrs[(j : ℕ)]!).toList == (List.range 360).map (cycsK 360 (genCycles j))) = true := by
  simp only [← cycsS_eq, List.all_eq_true, List.mem_finRange, true_implies]
  intro j
  fin_cases j
  exacts [genArrs_cyc_0, genArrs_cyc_1, genArrs_cyc_2, genArrs_cyc_3, genArrs_cyc_4, genArrs_cyc_5,
    genArrs_cyc_6, genArrs_cyc_7]

theorem tabX : tabsOKW 360 9 D.TX (fun r x => cycsK 360 (csX.getD r []) x) 8 = true := by
  quickRfl

theorem tabA : tabsOKW 360 9 D.TA (fun i x => wordW 360 9 D.TX (gcX.getD i []) x) 4 = true := by
  quickRfl

theorem tabR : tabsOKW 240 8 D.TR (fun i x => cycsK 240 (csR.getD i []) x) 4 = true := by
  quickRfl

end CertificateChecks.KernelO8.C3006

end
