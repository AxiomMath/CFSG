module

public import Certificates.Kernel.Sporadic.OddCore.SuzC1EZS
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

theorem CertificateChecks.KernelSpor.SuzC1EZ.kA4 :
    Nat.beq (CFSG.KS.PEnum.cntK CertificateChecks.KernelSpor.SuzC1EZ.a4q 3) 12 = true := by
  quickRfl

theorem CertificateChecks.KernelSpor.SuzC1EZ.kY :
    Nat.beq (CFSG.KS.PEnum.cntK CertificateChecks.KernelSpor.SuzC1EZ.yq 3) 24 = true := by
  quickRfl

end
