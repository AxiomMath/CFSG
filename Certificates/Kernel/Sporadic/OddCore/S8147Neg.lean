module

public import Certificates.Kernel.Sporadic.OddCore.S8147C
public import Certificates.Kernel.Sporadic.OddCore.S8147KD
public import Certificates.Data.Kernel.BfsPinSlice
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.S8147

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.PEnum CFSG.KC.BfsPin CFSG.KC.B3S3K
open CertificateChecks.KernelSpor

theorem negPre : Bool.not (preChk (SFvT.F 6) (SFvT.F 6)) = true := by quickRfl

theorem negKey : Bool.not (keyCommK (SFD0.G 0) (SFD0.G 1)) = true := by quickRfl

theorem negCnt : Bool.not (dChk (SFvT.F 6) (SFvT.F 7) 2 SFD0.G 360 SFD0.T 3600 SFC0.T 6) = true := by
  quickRfl

theorem negPow : Bool.not (powChk 2 SFD0.G 3600 SFC0.T (SFvT.F 1)) = true := by quickRfl

theorem negOrb : Bool.not (oChk [0, 225, 211, 1263, 1557] 2 SFD0.G SFO0.G) = true := by quickRfl

theorem negCover : Bool.not (strictB (Nat.succ (r32 SFQW 3)) fun c =>
    bAnd(Nat.blt (Nat.div c 8) 6, bAnd(Nat.blt (Nat.mod c 8) 5,
      Nat.beq (SFQ.T 3) (pw 1782 11 (SFvT.F (Nat.div c 8)) (Nat.mod c 8))))) = true := by quickRfl

theorem negRun : Bool.not (runSl 1782 11 2 SFD1.G SFD1.T SFD1.E 20 (fun s => Nat.succ (SFD1.C s)) 0) =
    true := by quickRfl

end CertificateChecks.KernelSpor.S8147

end
