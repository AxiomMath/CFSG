module

public import Certificates.Kernel.SporSch.PairHe.CntFns
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kss_b2 CertificateChecks.KernelSporSch.PHeCn CertificateChecks.KernelSporSch.PHeCn.bindB 0 2 10
#kss_b2all CertificateChecks.KernelSporSch.PHeCn CertificateChecks.KernelSporSch.PHeCn.bindB 2 10

namespace CertificateChecks.KernelSporSch.PHeCn

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CertificateChecks.KernelSporSch
open CertificateChecks.KernelSpor

theorem reps : repsB = true := by quickRfl
theorem fix : fixB = true := by quickRfl
theorem c0 : Nat.beq (rcnt (HeC.LR 0)) 8330 = true := by quickRfl
theorem sA : Nat.beq (sumN 56 PHeN.SC0) 17 = true := by quickRfl
theorem sA3 : Nat.beq (sumN 56 PHeN.SC1) 17 = true := by quickRfl

end CertificateChecks.KernelSporSch.PHeCn

end
