module

public import Certificates.Kernel.LocalComp.L34KLData
public import Certificates.Kernel.LocalComp.L34NDefs
public import Certificates.Kernel.LocalComp.L34SChk
public import Certificates.Data.Kernel.L34KLW
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.L34KL

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K CFSG.KC.L34Norm
open CFSG.KC.L34KLW CertificateChecks.KernelLC.L34N
open CFSG.KLie.CT (andB orB notB)

@[expose] noncomputable def wit (M : Nat) (Y T : Nat → Nat) : Bool :=
  strictB (pidn 42 6) fun e => allN 7755 fun q =>
    klEnt 42 6 9 AP e (K 0) (K 1) L34R.T M Q (fun j => L34S.T (Y j)) (fun j => L34S.T (T j)) q (J q)

theorem kW : wit 24 QS TS = true := by quickRfl

theorem kWB : allN 24 (fun j => andB (Nat.blt (QS j) 20160) (Nat.blt (TS j) 20160)) = true := by
  quickRfl

theorem kOne : strictB (pidn 42 6) (fun e => andB (q4Pt 42 6 9 AP (K 0) (K 1) e (L34S.T (QS 0)))
    (tauPt 42 6 e (K 0) (K 1) e (L34S.T (TS 0)))) = true := by quickRfl

theorem kA : andB (andB (Nat.blt (PA 0) 20160) (Nat.blt (PA 1) 20160))
    (andB (Nat.beq (L34S.T (PA 0)) (K 0)) (Nat.beq (L34S.T (PA 1)) (K 1))) = true := by quickRfl

theorem kAB : andB (andB (o3Pt 42 6 (pidn 42 6) (K 0)) (o3Pt 42 6 (pidn 42 6) (K 1)))
    (andB (commPt 42 6 (K 0) (K 1))
      (allN 9 fun i => allN 9 fun j => orB (Nat.beq i j) (notB (Nat.beq (AP i) (AP j))))) = true := by
  quickRfl

end CertificateChecks.KernelLC.L34KL

end
