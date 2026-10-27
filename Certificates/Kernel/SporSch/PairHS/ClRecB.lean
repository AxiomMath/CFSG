module

public import Certificates.Kernel.SporSch.PairHS.ClFns
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kss_b2 CertificateChecks.KernelSporSch.PHSCl CertificateChecks.KernelSporSch.PHSCl.recB 0 31 8
#kss_b2all CertificateChecks.KernelSporSch.PHSCl CertificateChecks.KernelSporSch.PHSCl.recB 31 8
#kss_b2 CertificateChecks.KernelSporSch.PHSCl CertificateChecks.KernelSporSch.PHSCl.srtB 0 31 8
#kss_b2all CertificateChecks.KernelSporSch.PHSCl CertificateChecks.KernelSporSch.PHSCl.srtB 31 8
#kss_b2 CertificateChecks.KernelSporSch.PHSCl CertificateChecks.KernelSporSch.PHSCl.jsrt 0 42 8
#kss_b2all CertificateChecks.KernelSporSch.PHSCl CertificateChecks.KernelSporSch.PHSCl.jsrt 42 8

namespace CertificateChecks.KernelSporSch.PHSCl

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CertificateChecks.KernelSporSch

theorem canonB : canonL 3850 12 RPB = true := by quickRfl
theorem stB : startNFT 3850 12 8 PHST.NR PHST.NR PHST.LT PHST.PT PHST.QT 4
    (wordKey 3850 12 CFSG.Sporadic.Schreier.PairHS.bs RPB) (XB 0) = true := by quickRfl
theorem kB : Nat.beq (KB 0) (wordKey 3850 12 CFSG.Sporadic.Schreier.PairHS.bs RPB) = true := by
  quickRfl
theorem cB0 : Nat.beq (PHSU.C 0) 1 = true := by quickRfl
theorem cBN : Nat.beq (PHSU.C (Nat.mul 61 8)) PHSU.c = true := by quickRfl
theorem cBSz : Nat.beq PHSU.c 15400 = true := by quickRfl

end CertificateChecks.KernelSporSch.PHSCl

end
