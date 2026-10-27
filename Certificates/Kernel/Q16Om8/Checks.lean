module

public import Certificates.Kernel.Q16Om8.Data
public import Certificates.Kernel.LocalComp.Omega1Chain
public import Certificates.Data.Kernel.Misc.ArrEnum
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelQ16Om8

open CFSG.KC.Enum CFSG.KS CFSG.KC.BfsPin CFSG.KC.Q16BK CFSG.KC.Misc.ArrEnum

@[expose] noncomputable def CS.SK : List Nat := (List.range 4096).map CS.SKT

theorem nums : (Nat.beq CS.ng 4 && Nat.beq CS.N 4096) = true := by quickRfl

theorem gens : allN 4 (fun k => allN 120 fun i => Nat.beq (pg 7 127 (CS.G k) i)
    (pg 9 511 (CertificateChecks.KernelLC.W3185.Om1.S (2 * k)) i)) = true := by
  quickRfl

theorem perm : allN 4 (fun k => permB 120 7 (CS.G k)) = true := by quickRfl

theorem keys : keysSK 120 7 [0, 8, 24] CS.N CS.T CS.SK = true := by quickRfl

theorem q16 : q16BK 120 7 [0, 8, 24] CS.N CS.T CS.nR CS.RI CS.C CS.W = true := by quickRfl

end CertificateChecks.KernelQ16Om8

end
