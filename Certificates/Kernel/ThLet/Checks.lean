module

public import Certificates.Data.Kernel.ThLet.Defs
public import CFSG.Certificates.Kernel.Th.S.Data.Sm_Sel
public import CFSG.Certificates.Kernel.Th.S.Data.Sm_const
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabThCentSInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelThLet

open CFSG.KC.Th CFSG.KC.ThCent CFSG.KC.ThLet CFSG.KD CFSG.HardMathSupport.Dickson.I271.TabThNative

@[expose] noncomputable def letOK17308 (R : Nat → Nat) : Bool :=
  andB (relsOK ThS.c ThS.rm ThS.ONE (fun k => R (eIdx k)) (fun k => R (eiIdx k))
      CFSG.GH74.QTGen4.Recog.G23.g23Words)
    (andB (pairsOK ThS.c ThS.rm ThS.ONE (R 11) (fun k => R (eIdx k)) (fun k => R (eiIdx k)) 6)
      (BigS.notB (Nat.beq (mulB ThS.c ThS.rm (R (eIdx 0)) ThS.ONE) ThS.ONE)))

theorem ch17308 :
    runK ThS.c ThS.rm ThS.ONE progE (initPk (ThS.RBf 1) (ThS.RBf 2) ThS.ONE) letOK17308 = true := by
  quickRfl

end CertificateChecks.KernelThLet

end
