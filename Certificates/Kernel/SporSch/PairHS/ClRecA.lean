module

public import Certificates.Kernel.SporSch.PairHS.ClFns
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kss_b2 CertificateChecks.KernelSporSch.PHSCl CertificateChecks.KernelSporSch.PHSCl.recA 0 12 8
#kss_b2all CertificateChecks.KernelSporSch.PHSCl CertificateChecks.KernelSporSch.PHSCl.recA 12 8
#kss_b2 CertificateChecks.KernelSporSch.PHSCl CertificateChecks.KernelSporSch.PHSCl.srtA 0 12 8
#kss_b2all CertificateChecks.KernelSporSch.PHSCl CertificateChecks.KernelSporSch.PHSCl.srtA 12 8

namespace CertificateChecks.KernelSporSch.PHSCl

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CertificateChecks.KernelSporSch

theorem canonA : canonL 3850 12 RPA = true := by quickRfl
theorem ltbs : ltL 3850 CFSG.Sporadic.Schreier.PairHS.bs = true := by quickRfl
theorem stA : startNFT 3850 12 8 PHST.NR PHST.NR PHST.LT PHST.PT PHST.QT 4
    (wordKey 3850 12 CFSG.Sporadic.Schreier.PairHS.bs RPA) (XA 0) = true := by quickRfl
theorem kA : Nat.beq (KA 0) (wordKey 3850 12 CFSG.Sporadic.Schreier.PairHS.bs RPA) = true := by
  quickRfl
theorem cA0 : Nat.beq (PHST.C 0) 1 = true := by quickRfl
theorem cAN : Nat.beq (PHST.C (Nat.mul 23 8)) PHST.c = true := by quickRfl
theorem cASz : Nat.beq PHST.c 5775 = true := by quickRfl

end CertificateChecks.KernelSporSch.PHSCl

end
