module

public import Certificates.Kernel.LocalComp.L34RData
public import Certificates.Kernel.LocalComp.L34SData
public import Certificates.Data.Kernel.L34KuAct
import Certificates.Kernel.Sporadic.ON.Gen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.L34Scan

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34Scan
open CertificateChecks.KernelLC.L34X
open CFSG.KLie.CT (notB)

@[expose] noncomputable def ku (s : Nat) : Bool :=
  strictB (pidn 42 6) fun e => strictB (RP 3) fun r =>
    scanSl (kuK 42 6 r 72 L34C4.P e) L34R.T 1344 s

theorem kCanon4 : allN 72 (fun c => canonK 42 6 (mask 6) (42 * 6) (L34C4.P c)) = true := by
  quickRfl

theorem kNegKu : notB (kuK 42 6 (pidn 42 6) 0 L34C4.P (pidn 42 6) (L34R.G 0)) = true := by
  quickRfl

end CertificateChecks.KernelLC.L34Scan

#kon_slices CertificateChecks.KernelLC.L34Scan.ku 0 180
#kon_join CertificateChecks.KernelLC.L34Scan.kuAll CertificateChecks.KernelLC.L34Scan.ku 180

end
