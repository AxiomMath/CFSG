module

public import Certificates.Kernel.McLAS.NoThreeData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMcLAS

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.McLNT
open CertificateChecks.KernelSpor CertificateChecks.KernelCensus

theorem noThr_base : bAnd(Nat.blt (r32 NoThrJ (nat_lit 0)) (nat_lit 128),
    bAnd(Nat.blt (r32 NoThrJ (nat_lit 1)) (nat_lit 128),
    bAnd(Nat.beq MN.Q1a.cnt (nat_lit 112), bAnd(Nat.beq MN.Q1e.cnt (nat_lit 1120),
    allN 3 (fun j => bAnd(canonK 275 9 (mask 9) (275 * 9) (NoThrG j),
      bAnd(canonK 275 9 (mask 9) (275 * 9) (NoThrGI j),
      bAnd(invEqK 275 9 (mask 9) (275 * 9) (NoThrG j) (NoThrGI j),
      bAnd(siftK 275 9 (mask 9) (275 * 9) (pidn 275 9) McLC.LR McLC.TRI McLC.BP 5 0 (NoThrG j),
        Nat.beq (pc (NoThrG j) (pc (McLCT.F 4) (NoThrGI j))) (noThrU j)))))))))) = true := by
  quickRfl

end CertificateChecks.KernelMcLAS

end
