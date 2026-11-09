module

public import Certificates.Kernel.Sporadic.OddCore.S129062D
public import Certificates.Data.Kernel.L34K
public import Certificates.Data.Kernel.Spor.BaseEq
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.S129062

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.L34K CFSG.KS.PEnum CFSG.KS.BaseEq
open CFSG.KLie.CT (andB orB notB)

@[expose] noncomputable def sqInv (k : Nat) : Bool :=
  andB (sqFixK 11 (mask 11) [0, 1] (SSE.T k)) (notB (Nat.beq k 0))

@[expose] noncomputable def ix (j : Nat) : Nat := r32 S129I j

@[expose] noncomputable def col (j : Nat) : Nat := pg 6 (mask 6) (S129C.F 0) j

@[expose] noncomputable def cntBeq (f : Nat → Bool) (N m : Nat) : Bool :=
  Nat.beq (CFSG.KC.HeAutK.cntR f 0 N) m

theorem kCnt : cntBeq sqInv 16384 911 = true := by
  quickRfl

theorem kIdx : allN 911 (fun j => strictB (ix j) fun k =>
    andB (Nat.blt k 16384) (andB (orB (Nat.beq (Nat.succ j) 911) (Nat.blt k (ix (Nat.succ j))))
      (sqInv k))) = true := by
  quickRfl

theorem kRank : allN 911 (fun i => strictB (col i) fun c =>
    andB (Nat.blt c 63) (allN 911 fun j =>
      orB (Nat.ble j i) (orB (notB (Nat.beq (col j) c))
        (notB (commPt 1782 11 (SSE.T (ix i)) (SSE.T (ix j))))))) = true := by
  quickRfl

end CertificateChecks.KernelSpor.S129062

end
