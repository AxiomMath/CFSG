module

public import Certificates.Kernel.LocalComp.B0SuzData
public import Certificates.Kernel.LocalComp.B0SuzMat
public import Certificates.Kernel.Sporadic.OddCore.Suz2302
public import Certificates.Data.Kernel.B0SuzK
public import Certificates.Data.Kernel.BfsPin
public import Certificates.Data.SuzTwoAExtension
public import CFSG.Certificates.Kernel.LocalCompUnpack
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3Q0SuzTests
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option Elab.async false

namespace CertificateChecks.KernelLC.Tau1379103

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.HexaK CFSG.KC.B0SuzK CFSG.KC.BfsPin
open CFSG.ComponentClassification.AS81.SuzB0 CFSG.Sporadic.SuzOddCore CFSG.PSL3Four.Native
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.OddCore CertificateChecks.KernelLC
open CFSG.KLie.CT (notB)

@[expose] noncomputable def TAU : Nat :=
  wordK 1782 11 (mask 11) (pidn 1782 11) triS triSI tauWord

@[expose] noncomputable def TM : Nat := packA 7 (tauMatTab ()).toList

theorem kWord : wordEqK 1782 11 (mask 11) (pidn 1782 11) triS triSI 3 tauWord TAU = true := by
  quickRfl

theorem kTau : (Nat.beq (mul 1782 11 TAU (SuzInvT1.F 0)) (mul 1782 11 (SuzInvT1.F 0) TAU) &&
    bindArrK (tauMatTab ()) 64 7 TM && canonK 64 7 (mask 7) (64 * 7) TM) = true := by
  quickRfl

theorem kQ0 : q0K (SuzInvT1.F 0) TAU SuzB0Q.F SuzB0QP tauAct SuzB0M.N SuzB0M.T TM = true := by
  quickRfl

end CertificateChecks.KernelLC.Tau1379103

end
