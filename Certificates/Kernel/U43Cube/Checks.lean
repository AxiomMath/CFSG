module

public import Certificates.Kernel.U43Cube.Data
public import Certificates.Kernel.CU43Aut.Cls
public import Certificates.Data.Kernel.Spor.KeyWord
public import Certificates.Data.Kernel.Spor.ConjRun
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.U43CoverData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU43Cube

open CFSG.EvenSporadicStandard.HSStd.U43
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.KeyWord CFSG.KS.ConjRun
open CertificateChecks.KernelU43B CertificateChecks.KernelCU43Aut

@[expose] noncomputable def KP : Nat := 9438208

@[expose] noncomputable def cjS (k : Nat) (T : Nat → Nat) (N lo len : Nat) : Bool :=
  cjSlK 10 (mask 10) 14 3 1073741823 (cgK 7 C.S C.SI) (cgiK 7 C.S C.SI) KP (YP k) T N lo len

@[expose] noncomputable def syS (lo len : Nat) : Bool :=
  sySlK 10 (mask 10) 3 3 14 4 1073741823 SGP (cgK 7 C.S C.SI) YP KP EP 729 lo len

theorem kBind : bindListK 820 10 (YP 0) yAArr.toList = true ∧
    bindListK 820 10 (YP 1) yBArr.toList = true ∧
    bindListK 820 10 (YP 2) yCArr.toList = true ∧
    bindListK 820 10 (YP 3) yDArr.toList = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> quickRfl

theorem kY : allN 4 (fun k => bAnd(cK (YP k), bAnd(inPK (YP k),
    bAnd(Nat.beq (ppow (YP k) 3) (pidn 820 10), bIf(Nat.beq (YP k) (pidn 820 10), false, true))))) =
    true := by
  quickRfl

theorem kZ : bAnd(cK (Z0P 0), bAnd(cK (H0P 0), bAnd(inPK (H0P 0),
    bAnd(Nat.beq (pc (H0P 0) (YP 0)) (pc (Z0P 0) (H0P 0)),
    bAnd(cK (Z3P 0), bAnd(cK (H3P 0), bAnd(inPK (H3P 0),
    Nat.beq (pc (H3P 0) (YP 3)) (pc (Z3P 0) (H3P 0))))))))) = true := by
  quickRfl

theorem kU0 : ubOK (Z0P 0) O0P 5832 = true := by quickRfl
theorem kU3 : ubOK (Z3P 0) O3P 81 = true := by quickRfl

theorem kL0 : lbOK (Z0P 0) G0P T0P 12 2 5832 = true := by quickRfl
theorem kL1 : lbOK (YP 1) G1P T1P 12 2 972 = true := by quickRfl
theorem kL2 : lbOK (YP 2) G2P T2P 9 2 972 = true := by quickRfl
theorem kL3 : lbOK (Z3P 0) G3P T3P 12 2 81 = true := by quickRfl

theorem kC1_0 : cjS 1 C1P 3360 0 1120 = true := by quickRfl
theorem kC1_1 : cjS 1 C1P 3360 1120 1120 = true := by quickRfl
theorem kC1_2 : cjS 1 C1P 3360 2240 1120 = true := by quickRfl
theorem kC2_0 : cjS 2 C2P 3360 0 1120 = true := by quickRfl
theorem kC2_1 : cjS 2 C2P 3360 1120 1120 = true := by quickRfl
theorem kC2_2 : cjS 2 C2P 3360 2240 1120 = true := by quickRfl

theorem kG : allN 3 (fun j => bAnd(cK (SGP j), inPK (SGP j))) = true := by quickRfl

theorem kS_0 : syS 0 243 = true := by quickRfl
theorem kS_1 : syS 243 243 = true := by quickRfl
theorem kS_2 : syS 486 243 = true := by quickRfl

end CertificateChecks.KernelU43Cube

end
