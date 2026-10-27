module

public import Certificates.Kernel.EvenBN.K27580D
public import Certificates.Kernel.SporSch.Tits.GenAll5
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kst_all5 CertificateChecks.KernelEvenBN.E32.SIA 1755 11 8 2 CertificateChecks.KernelSpor.TitsS.LR
  CertificateChecks.KernelSpor.TitsS.TR CertificateChecks.KernelEvenBN.E32.QI

namespace CertificateChecks.KernelEvenBN.E32

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CertificateChecks.KernelSpor

theorem mI : Nat.beq (maskOf SI.C) SI.M = true := by quickRfl
theorem aI : ascK (tot5 TitsS.LR) SI.C 0 = true := by quickRfl
theorem zI : zipK (fun c l => Nat.beq (prodCode 1755 11 (mask 11) (1755 * 11) TitsS.LR TitsS.TR c) l)
    SI.C SI.L = true := by quickRfl

end CertificateChecks.KernelEvenBN.E32

end
