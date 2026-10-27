module

public import Certificates.Kernel.NT44.Pack
public import Certificates.Kernel.NT44.Pack2
public import Certificates.Data.Kernel.Misc.ArrEnum
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option profiler true
set_option profiler.threshold 200

namespace CertificateChecks.KernelNT44

open CFSG.GH74.GLS.NT44.PermutationNative CFSG.KC.Misc.ArrEnum
open CFSG.KC.Enum (pg)
open CFSG.KS (mask)
open CFSG.KC.LQT.P (allN)

@[expose] noncomputable def restrAt (Pts G H : Nat) : Bool :=
  allN 448 fun x => Nat.beq (pg 12 (mask 12) Pts (pg 9 (mask 9) H x))
    (pg 12 (mask 12) G (pg 12 (mask 12) Pts x))

theorem nt44_pts_bind : arrBind (pts ()) 448 12 (nt44Pts 0) = true := by quickRfl

theorem nt44_restr_ks : allN 2 (fun i => restrAt (nt44Pts 0) (nt44KS i) (nt44SK i)) = true := by
  quickRfl

theorem nt44_restr_p0 : allN 9 (fun i => restrAt (nt44Pts 0) (nt44P0 i) (nt44SP i)) = true := by
  quickRfl

end CertificateChecks.KernelNT44

end
