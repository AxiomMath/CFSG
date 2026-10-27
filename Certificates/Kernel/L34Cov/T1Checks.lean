module

public import Certificates.Data.Kernel.L34Cov.T1
public import Certificates.Kernel.L34Cov.Words
public import Certificates.Kernel.L34Cov.Checks
public import Certificates.Kernel.L34W.Tabs
public import CFSG.Certificates.Kernel.Common.EachTrue

public section

namespace CertificateChecks.KernelL34Cov

open CFSG.KC CFSG.KC.L34Cov CFSG.KC.L34W CertificateChecks.KernelL34W

#kc_each CertificateChecks.KernelL34Cov.ch22219t1c c
  (fun k => t1colsOK VT CFSG.KD.L34F4a.Tab CFSG.KD.L34F4b.Tab T1X.F TwC.codes k) 0 64

theorem t1zero_k : Mono.allR 0 64 (t1zeroOK T1X.F) = true := by decide +kernel

#kc_each CertificateChecks.KernelL34Cov.ch22219t1a a
  (fun k => Mono.allR 0 64 (t1clsOK T1X.F k)) 0 64

theorem reach_k : reachM T1X.F 5 = 2 ^ 64 - 1 := by decide +kernel

theorem t1col_neg : (!t1colOK VT CFSG.KD.L34F4a.Tab CFSG.KD.L34F4b.Tab
    (fun r => cond (Nat.beq r 0) (Nat.add (T1X.F 0) (Nat.shiftLeft 1 12)) (T1X.F r)) TwC.codes 0 1) =
    true := by
  decide +kernel

theorem t1cl_neg : (!Mono.allR 0 64 (t1clsOK
    (fun r => cond (Nat.beq r 3) (Nat.add (T1X.F 3) (Nat.shiftLeft 12 12)) (T1X.F r)) 3)) = true := by
  decide +kernel

theorem reach_neg : (!Nat.beq (reachM (fun r => cond (Nat.beq r 0) 0 (T1X.F r)) 5) (2 ^ 64 - 1)) =
    true := by
  decide +kernel

end CertificateChecks.KernelL34Cov

end
