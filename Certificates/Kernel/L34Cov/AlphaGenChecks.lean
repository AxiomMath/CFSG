module

public import Certificates.Data.Kernel.L34Cov.AlphaGen
public import Certificates.Kernel.L34Cov.Words
public import Certificates.Kernel.L34Cov.Checks
public import Certificates.Kernel.L34W.Tabs
public import CFSG.Certificates.Kernel.Common.EachTrue

public section

namespace CertificateChecks.KernelL34Cov

open CFSG.KC CFSG.KC.L34Cov CFSG.KC.L34W CertificateChecks.KernelL34W

#kc_each CertificateChecks.KernelL34Cov.ch22219ag a
  (fun i => alGensOK VT CFSG.KD.L34F4a.Tab CFSG.KD.L34F4b.Tab FW TwC.codes AlX.F
    (UAC.codes.getD i []) (UBC.codes.getD i []) i) 0 36

theorem ch22219ag_neg : (!alGensOK VT CFSG.KD.L34F4a.Tab CFSG.KD.L34F4b.Tab FW TwC.codes
    (fun r => cond (Nat.beq r 0) (Nat.add (AlX.F 0) (Nat.shiftLeft 1 12)) (AlX.F r))
    (UAC.codes.getD 0 []) (UBC.codes.getD 0 []) 0) = true := by
  decide +kernel

end CertificateChecks.KernelL34Cov

end
