module

public import Certificates.Kernel.Sporadic.OddCore.S2307D
public import Certificates.Kernel.Sporadic.OddCore.SuzFusion
public import Certificates.Kernel.Sporadic.OddCore.Suz2302
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.S2307

open CFSG.Sporadic.SuzOddCore CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum
open CFSG.KS.Mathieu CertificateChecks.KernelSpor CertificateChecks.KernelSpor.OddCore CertificateChecks.KernelSpor.Suz2306

@[expose] noncomputable def inTK (G : Nat) : Bool :=
  bIf(msift G, true, msift (pcomp 1782 11 (mask 11) V G))

theorem gb : allN 11 (fun g => Nat.beq (SSE.G g) (SuzFusT.F g)) = true := by quickRfl

theorem inG : allN 11 (fun g => inTK (SuzFusT.F g)) = true := by quickRfl

theorem inC : allN 21 (fun r => inTK (SuzFusT.F (Nat.add 12 (Nat.mul 2 r)))) = true := by quickRfl

theorem reps : allN 21 (fun r => Nat.beq (SSE.T (r32 SSF.L (r32 SSF.O r)))
    (SuzFusT.F (Nat.add 11 (Nat.mul 2 r)))) = true := by quickRfl

theorem rep21 : Nat.beq (r32 SSF.L (r32 SSF.O 21)) 0 = true := by quickRfl

theorem conjs : allN 21 (fun r => Nat.beq (pcomp 1782 11 (mask 11)
    (pcomp 1782 11 (mask 11) (SuzFusT.F (Nat.add 12 (Nat.mul 2 r))) (SuzTP (nget invFusionCases r)))
    (pinvS 1782 11 (mask 11) (SuzFusT.F (Nat.add 12 (Nat.mul 2 r)))))
    (SuzFusT.F (Nat.add 11 (Nat.mul 2 r)))) = true := by
  quickRfl

theorem sizes : allN 22 (fun c => Nat.beq (Nat.sub (r32 SSF.O (Nat.succ c)) (r32 SSF.O c))
    (nIf(Nat.blt c 21, nget invFusionSizes c, 1))) = true := by quickRfl

theorem cases_lt : allN 21 (fun r => Nat.blt (nget invFusionCases r) 4) = true := by quickRfl

end CertificateChecks.KernelSpor.S2307

end
