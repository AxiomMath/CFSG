module

public import Certificates.Kernel.SporSch.PairHS.CntFns
public import Certificates.Kernel.SporSch.Ru.RowsGen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kss_b2 CertificateChecks.KernelSporSch.PHSCn CertificateChecks.KernelSporSch.PHSCn.s2B 0 8 8
#kss_b2all CertificateChecks.KernelSporSch.PHSCn CertificateChecks.KernelSporSch.PHSCn.s2B 8 8
#kss_b2 CertificateChecks.KernelSporSch.PHSCn CertificateChecks.KernelSporSch.PHSCn.srt2 0 8 8
#kss_b2all CertificateChecks.KernelSporSch.PHSCn CertificateChecks.KernelSporSch.PHSCn.srt2 8 8
#kss_b2 CertificateChecks.KernelSporSch.PHSCn CertificateChecks.KernelSporSch.PHSCn.s5B 0 5 5
#kss_b2all CertificateChecks.KernelSporSch.PHSCn CertificateChecks.KernelSporSch.PHSCn.s5B 5 5
#kss_b2 CertificateChecks.KernelSporSch.PHSCn CertificateChecks.KernelSporSch.PHSCn.srt5 0 5 5
#kss_b2all CertificateChecks.KernelSporSch.PHSCn CertificateChecks.KernelSporSch.PHSCn.srt5 5 5
#kss_b2 CertificateChecks.KernelSporSch.PHSCn CertificateChecks.KernelSporSch.PHSCn.bindB 0 7 5
#kss_b2all CertificateChecks.KernelSporSch.PHSCn CertificateChecks.KernelSporSch.PHSCn.bindB 7 5
#kss_each CertificateChecks.KernelSporSch.PHSCn.WB CertificateChecks.KernelSporSch.PHSCn.wordB 5

namespace CertificateChecks.KernelSporSch.PHSCn

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CertificateChecks.KernelSporSch

theorem reps : repsB = true := by quickRfl
theorem gens : gensB = true := by quickRfl
theorem c0 : Nat.beq (rcnt (PHSC.LR 0)) 3850 = true := by quickRfl
theorem vA : Nat.beq (sumN 25 PHSN.V0) 500 = true := by quickRfl
theorem vB : Nat.beq (sumN 25 PHSN.V1) 300 = true := by quickRfl
theorem vC : Nat.beq (sumN 25 PHSN.V2) 25 = true := by quickRfl
theorem vZ : Nat.beq (sumN 25 PHSN.V3) 11 = true := by quickRfl
theorem vZI : Nat.beq (sumN 25 PHSN.V4) 0 = true := by quickRfl
theorem sA : Nat.beq (sumN 12 PHSN.SC0) 110 = true := by quickRfl
theorem sB : Nat.beq (sumN 32 PHSN.SC1) 22 = true := by quickRfl
theorem sAI : Nat.beq (sumN 12 PHSN.SC2) 110 = true := by quickRfl
theorem sBI : Nat.beq (sumN 32 PHSN.SC3) 22 = true := by quickRfl

end CertificateChecks.KernelSporSch.PHSCn

end
