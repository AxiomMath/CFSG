module

public import Certificates.Data.Kernel.Misc.F2BfsRec
import CFSG.Certificates.Kernel.Common.F2Bfs
import CFSG.Certificates.Kernel.Common.Cover
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelHe7223

open CFSG.KC.F2BfsRec

@[expose] def NS : List Nat := [64729137305, 49696008179]

@[expose] def LS : List Nat := [65199327425, 25307838368, 55161072120]

@[expose] def N7 : List Nat := [46881, 27935]

@[expose] def BB : List Nat := [34427118096, 34427404368, 4563673632]

@[expose] noncomputable def gen (L : List Nat) (j : Nat) : Nat := L.getD j 0

end CertificateChecks.KernelHe7223

#kc_f2bfs CertificateChecks.KernelHe7223.ENS 6 CertificateChecks.KernelHe7223.NS 4096 6 12
#kc_f2bfs CertificateChecks.KernelHe7223.ELS 6 CertificateChecks.KernelHe7223.LS 4096 6 12
#kc_f2bfs CertificateChecks.KernelHe7223.EN7 4 CertificateChecks.KernelHe7223.N7 4096 6 12
#kc_f2bfs CertificateChecks.KernelHe7223.EBB 6 CertificateChecks.KernelHe7223.BB 4096 6 12

namespace CertificateChecks.KernelHe7223

open CFSG.KC.F2BfsRec

theorem ch7223ns_head : headK 6 12 6 2 ENS.CF = true := by quickRfl

theorem ch7223ns_recs : ∀ t < 2160, recK 6 12 6 2 ENS.CF (gen NS) 2160 t = true := by
  kc_cover 64

theorem ch7223ls_head : headK 6 12 6 3 ELS.CF = true := by quickRfl

theorem ch7223ls_recs : ∀ t < 1080, recK 6 12 6 3 ELS.CF (gen LS) 1080 t = true := by
  kc_cover 64

theorem ch7223n7_head : headK 4 12 6 2 EN7.CF = true := by quickRfl

theorem ch7223n7_recs : ∀ t < 1344, recK 4 12 6 2 EN7.CF (gen N7) 1344 t = true := by
  kc_cover 64

theorem ch7223bb_head : headK 6 12 6 3 EBB.CF = true := by quickRfl

theorem ch7223bb_recs : ∀ t < 360, recK 6 12 6 3 EBB.CF (gen BB) 360 t = true := by
  kc_cover 64

end CertificateChecks.KernelHe7223

end
