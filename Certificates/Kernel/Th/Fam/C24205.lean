module

public import Certificates.Kernel.Th.Fam.K
public import Certificates.Kernel.Th.Fam.LocalTE
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.LocalDataTh.TransvData

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelTh.Fam

open CFSG.KC.Th.Expr CertificateChecks.KernelTh.Fam.Local

theorem ok24205 : (List.range 15).all (fun e => (List.range 16).all fun c =>
    CFSG.KC.Th.BigS.notB (Nat.beq ((peT (e + 1)).pk thK) ((aelT c).pk thK))) = true := by
  quickRfl

end CertificateChecks.KernelTh.Fam

end
