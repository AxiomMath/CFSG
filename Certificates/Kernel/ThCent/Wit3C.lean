module

public import Certificates.Data.Kernel.ThCent.Defs
public import Certificates.Data.Kernel.ThCent.Pin
public import Certificates.Kernel.ThCent.Data3C
public import CFSG.Certificates.Kernel.Th.S.Data.Sm_Sel
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabThCensusInputs

public section

namespace CFSG.KD.ThCent.W3

open CFSG.KC.Th CFSG.KC.ThCent

theorem w3C : witOK ThS.RBf ThS.c ThS.rm ThS.ONE ThS.Bi ThS.GRf ThS.IRf Z3C hw3C hn3C tw3C tn3C =
    true := by decide +kernel
theorem w3D : witOK ThS.RBf ThS.c ThS.rm ThS.ONE ThS.Bi ThS.GRf ThS.IRf Z3C hw3D hn3D tw3D tn3D =
    true := by decide +kernel

theorem d3C : codes4 tw3C tn3C = C3C.word := by decide +kernel
theorem d3D : codes4 tw3D tn3D = C3D.word := by decide +kernel

theorem u3C : Nat.beq (runPk ThS.c ThS.rm ThS.ONE
    CFSG.HardMathSupport.Dickson.I271.TabThNative.progU
    (initPk (ThS.RBf 1) (ThS.RBf 2) ThS.ONE) 22) Z3C = true := by
  decide +kernel

end CFSG.KD.ThCent.W3

end
