module

public import Certificates.Kernel.ThCensus.Data
public import Certificates.Kernel.ThCent.Data
public import Certificates.Data.Kernel.ThCent.Pin
public import CFSG.Certificates.Kernel.Th.S.Data.Sm_Sel
public import CFSG.Certificates.Kernel.Th.S.Data.Sm_const
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabThCensusInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelThCensus

open CFSG.KC.Th CFSG.KC.ThCent CFSG.KD.ThCensus CFSG.KD

theorem ch17305J :
    andB (Nat.beq (RB 1) (ThS.RBf 1)) (andB (Nat.beq (RB 2) (ThS.RBf 2))
      (andB (Nat.beq (RB regZ) ThCent.W.Z3B) (andB (Nat.beq (RB regS) ThCent.W.Z3A)
        (Nat.beq (runPk ThS.c ThS.rm ThS.ONE CFSG.HardMathSupport.Dickson.I271.TabThNative.progU
          (initPk (ThS.RBf 1) (ThS.RBf 2) ThS.ONE) 22) (RB regU))))) = true := by
  quickRfl

theorem neg17305_pinS : BigS.notB (Nat.beq (RB regS) ThCent.W.Z3B) = true := by
  quickRfl

theorem neg17305_pinU : BigS.notB (Nat.beq (runPk ThS.c ThS.rm ThS.ONE
    CFSG.HardMathSupport.Dickson.I271.TabThNative.progU
    (initPk (ThS.RBf 1) (ThS.RBf 2) ThS.ONE) 21) (RB regU)) = true := by
  quickRfl

end CertificateChecks.KernelThCensus

end
