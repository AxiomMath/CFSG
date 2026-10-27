module

public import Certificates.Kernel.MaxD2.TitsD.Enum
public import Certificates.Kernel.MaxD2.TitsD.Data
public import Certificates.Kernel.MaxD2.TitsD.TransData
public import Certificates.Data.Kernel.MaxD2.Check
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option trace.profiler true
set_option trace.profiler.threshold 1000

namespace CertificateChecks.KernelMaxD2.TitsD

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.MaxD2 CFSG.KS.PEnum

theorem k_cj : allN 25 (fun r => bIf(Nat.beq (RE.T r) (pidn 1755 11), true,
    bAnd(Nat.blt (r32 CJ r) NE.cnt, Nat.beq (RE.T r) (pcomp 1755 11 (mask 11)
      (pcomp 1755 11 (mask 11) (NE.T (r32 CJ r)) (RE.G 0)) (NE.T (r32 INV (r32 CJ r))))))) =
    true := by quickRfl

theorem k_nc : bAnd(Nat.blt (r32 NC 0) NE.k, bAnd(Nat.blt (r32 NC 1) NE.k,
    notInK RE.cnt RE.T (pcomp 1755 11 (mask 11) (pcomp 1755 11 (mask 11)
      (pcomp 1755 11 (mask 11) (NE.G (r32 NC 0)) (NE.G (r32 NC 1))) (NGI (r32 NC 0)))
      (NGI (r32 NC 1))))) = true := by quickRfl

end CertificateChecks.KernelMaxD2.TitsD

end
