module

public import Certificates.Kernel.Sporadic.OddCore.S2307K
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.S2307

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.PEnum CFSG.KS.BaseEq CFSG.KS.EnumBase
open CertificateChecks.KernelSpor

theorem negRec : Bool.not (recK 1782 11 (mask 11) 11 SSE.G
    (fun k => nIf(Nat.beq k 5, SSE.T 6, SSE.T k)) SSE.PL 5) = true := by quickRfl

theorem negLeft : Bool.not (leftK 11 (mask 11) bp 11 16384 SSE.G SSE.T
    (fun r => nIf(Nat.beq r 0, Nat.succ (SSE.POS r), SSE.POS r)) 0) = true := by quickRfl

theorem negLex : Bool.not (lexPosK 11 16384 (fun _ => 0) SSE.POS 1) = true := by quickRfl

theorem negKeys : Bool.not (CFSG.KC.BfsPin.keysSK 1782 11 [0] 16384 SSE.T SK) = true := by quickRfl

theorem negCnt : Bool.not (Nat.beq (cntN 16384 (fun k => bIf(Nat.beq k (nat_lit 0), false,
    sqFixK 11 (mask 11) bp (SSE.T k)))) 912) = true := by quickRfl

theorem negClass : Bool.not (classK 11 (mask 11) bp 11 16384 SSE.G SSE.GI SSE.T
    (fun i => nIf(Nat.beq i (r32 SSF.O 5), r32 SSF.L (Nat.succ i), r32 SSF.L i)) (r32 SSF.P)
    (r32 SSF.G) (r32 SSF.Q) (r32 SSF.O) (r32 SSF.MK) (r32 SSF.PX) 5) = true := by quickRfl

theorem negConj : Bool.not (classK 11 (mask 11) bp 11 16384 SSE.G SSE.GI SSE.T (r32 SSF.L)
    (r32 SSF.P) (r32 SSF.G) (fun i => nIf(Nat.beq i (Nat.mul (r32 SSF.O 7) 11),
      Nat.succ (r32 SSF.Q i), r32 SSF.Q i)) (r32 SSF.O) (r32 SSF.MK) (r32 SSF.PX) 7) = true := by
  quickRfl

theorem negCover : Bool.not (coverK 11 (mask 11) bp 22 SSE.T (r32 SSF.L) (r32 SSF.O) (r32 SSF.MK)
    (fun k => Nat.succ (r32 SSF.PX k)) 0) = true := by quickRfl

end CertificateChecks.KernelSpor.S2307

end
