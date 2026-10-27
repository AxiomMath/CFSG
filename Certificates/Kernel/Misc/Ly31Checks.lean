module

public import Certificates.Kernel.SporSch.Ly.BSData
public import Certificates.Data.Kernel.SporSch.LyMat
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.LyThirtyOneCheck
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLy31

open CFSG.KC.Ord CFSG.KD.OrdLy CFSG.KS.SporSch.LyM CertificateChecks.KernelSporSch.LyBS
open CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic

@[expose] noncomputable def CW : Nat := wordR 5 12 1332 111 8 L H CM RM GS GSI ONE ly31Word

@[expose] noncomputable def CWi : Nat := wordR 5 12 1332 111 8 L H CM RM GS GSI ONE ly31WordInv

@[expose] noncomputable def PK : Nat := mul A (mul (mul CW A) CWi)

theorem ok31 : (Nat.beq (mul CW CWi) ONE &&
    Nat.beq (powR 5 12 1332 111 8 L H CM RM ONE PK 31) ONE && !(Nat.beq PK ONE)) = true := by
  quickRfl

end CertificateChecks.KernelLy31

end
