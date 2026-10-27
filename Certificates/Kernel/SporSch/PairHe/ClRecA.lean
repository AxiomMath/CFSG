module

public import Certificates.Kernel.SporSch.PairHe.ClFns
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kss_b2 CertificateChecks.KernelSporSch.PHeCl CertificateChecks.KernelSporSch.PHeCl.recA 0 49 8
#kss_b2all CertificateChecks.KernelSporSch.PHeCl CertificateChecks.KernelSporSch.PHeCl.recA 49 8
#kss_b2 CertificateChecks.KernelSporSch.PHeCl CertificateChecks.KernelSporSch.PHeCl.srtA 0 49 8
#kss_b2all CertificateChecks.KernelSporSch.PHeCl CertificateChecks.KernelSporSch.PHeCl.srtA 49 8

namespace CertificateChecks.KernelSporSch.PHeCl

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CertificateChecks.KernelSporSch
open CertificateChecks.KernelSpor

theorem canonA : canonL 8330 14 RPA = true := by quickRfl
theorem ltbs : ltL 8330 CFSG.Sporadic.Schreier.PairHe.bs = true := by quickRfl
theorem stA : startNFT 8330 14 9 PHeT.NR PHeT.NR PHeT.LT PHeT.PT PHeT.QT 5
    (wordKey 8330 14 CFSG.Sporadic.Schreier.PairHe.bs RPA) (XA 0) = true := by quickRfl
theorem kA : Nat.beq (KA 0) (wordKey 8330 14 CFSG.Sporadic.Schreier.PairHe.bs RPA) = true := by
  quickRfl
theorem cA0 : Nat.beq (PHeT.C 0) 1 = true := by quickRfl
theorem cAN : Nat.beq (PHeT.C (Nat.mul 98 8)) PHeT.c = true := by quickRfl
theorem cASz : Nat.beq PHeT.c 24990 = true := by quickRfl

end CertificateChecks.KernelSporSch.PHeCl

end
