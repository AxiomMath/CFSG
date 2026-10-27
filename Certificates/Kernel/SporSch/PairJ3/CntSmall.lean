module

public import Certificates.Kernel.SporSch.PairJ3.CntFns
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.SporSch.PairClTSound
public import CFSG.Certificates.Kernel.SporSch.PairKSound

public section

set_option maxRecDepth 400000

#kss_b2 CertificateChecks.KernelSporSch.PJ3Cn CertificateChecks.KernelSporSch.PJ3Cn.s2B 0 4 4
#kss_b2all CertificateChecks.KernelSporSch.PJ3Cn CertificateChecks.KernelSporSch.PJ3Cn.s2B 4 4
#kss_b2 CertificateChecks.KernelSporSch.PJ3Cn CertificateChecks.KernelSporSch.PJ3Cn.s3B 0 3 3
#kss_b2all CertificateChecks.KernelSporSch.PJ3Cn CertificateChecks.KernelSporSch.PJ3Cn.s3B 3 3
#kss_b2 CertificateChecks.KernelSporSch.PJ3Cn CertificateChecks.KernelSporSch.PJ3Cn.bindB 0 4 6
#kss_b2all CertificateChecks.KernelSporSch.PJ3Cn CertificateChecks.KernelSporSch.PJ3Cn.bindB 4 6

namespace CertificateChecks.KernelSporSch.PJ3Cn

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CertificateChecks.KernelSporSch

theorem reps : repsB = true := by quickRfl
theorem c0 : Nat.beq (rcnt (PJ3.LR 0)) 6156 = true := by quickRfl
theorem vT : Nat.beq (sumN 36 PJ3N.VT) 1920 = true := by quickRfl
theorem vA : Nat.beq (sumN 36 PJ3N.VA) 1080 = true := by quickRfl
theorem vB : Nat.beq (sumN 36 PJ3N.VB) 243 = true := by quickRfl
theorem vZ : Nat.beq (sumN 36 PJ3N.VZ) 19 = true := by quickRfl
theorem vZ2 : Nat.beq (sumN 36 PJ3N.VZ2) 0 = true := by quickRfl
theorem sZ : Nat.beq (sumN 52 PJ3N.SZ) 57 = true := by quickRfl
theorem sZ2 : Nat.beq (sumN 52 PJ3N.SZ2) 57 = true := by quickRfl

end CertificateChecks.KernelSporSch.PJ3Cn

end
