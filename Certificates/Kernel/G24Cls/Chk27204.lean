module

public import Certificates.Kernel.G24Cls.Pack27204
public import Certificates.Kernel.G24Cls.Chk27203
public import Certificates.Data.Kernel.G24Out
public import Certificates.Data.Kernel.PackSet
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option profiler true
set_option profiler.threshold 100

namespace CertificateChecks.KernelG24.Out27204

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.G24Tri CFSG.KC.G24Key
  CertificateChecks.KernelG24.Tri27206 CertificateChecks.KernelG24.Cls27203

theorem kCanO : (canonK 1365 11 (mask 11) (1365 * 11) (TAU 0) &&
    allN 2 (fun j => canonK 1365 11 (mask 11) (1365 * 11) (LC.S j))) = true := by quickRfl
theorem kInvO : (invEqK 1365 11 (mask 11) (1365 * 11) (PK 7) (PK 7) &&
    invEqK 1365 11 (mask 11) (1365 * 11) (TAU 0) (TAU 1)) = true := by quickRfl
theorem kSignO : CFSG.KC.Pack.signK 1365 11 (mask 11) (PK 7) (SG 0) 651 = true := by quickRfl
theorem kSiftO : (allN 2 (fun j =>
      siftK 1365 11 (mask 11) (1365 * 11) (pidn 1365 11) LC.LR LC.TRI LC.BP 3 0
        (pcomp 1365 11 (mask 11) (PK 7) (pcomp 1365 11 (mask 11) (LC.S j) (PK 7)))) &&
    siftK 1365 11 (mask 11) (1365 * 11) (pidn 1365 11) LC.LR LC.TRI LC.BP 3 0
      (pcomp 1365 11 (mask 11) (PK 7) (TAU 0))) = true := by quickRfl
theorem kFix : fixK LC.S 6 1365 = true := by quickRfl
theorem kNrm : (allN 8 (fun j => Nat.blt (t12 MJ j) 4096 &&
      ptsK (fun b => ap (TAU 0) (ap (RG j) (ap (TAU 1) b))) (keyT (t12 MJ j))) &&
    (Nat.blt (t12 MJ 8) 4096 &&
      ptsK (fun b => ap (TAU 0) (ap (TAU 0) b)) (keyT (t12 MJ 8)))) = true := by quickRfl
theorem kScan : allN (nat_lit 4096) (fun k =>
    recO gT TP TG (nat_lit 8) (TAU 0) (LC.S 0) (LC.SI 1) (PK 7) k (TR k)) = true := by quickRfl

end CertificateChecks.KernelG24.Out27204

end
