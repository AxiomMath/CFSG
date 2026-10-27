module

public import Certificates.Kernel.SporSch.PairHe.ClFns
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kss_b2 CertificateChecks.KernelSporSch.PHeCl CertificateChecks.KernelSporSch.PHeCl.recB 0 53 8

namespace CertificateChecks.KernelSporSch.PHeCl

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CertificateChecks.KernelSporSch
open CertificateChecks.KernelSpor

theorem canonB : canonL 8330 14 RPB = true := by quickRfl
theorem stB : startNFT 8330 14 9 PHeT.NR PHeT.NR PHeT.LT PHeT.PT PHeT.QT 5
    (wordKey 8330 14 CFSG.Sporadic.Schreier.PairHe.bs RPB) (XB 0) = true := by quickRfl
theorem kB : Nat.beq (KB 0) (wordKey 8330 14 CFSG.Sporadic.Schreier.PairHe.bs RPB) = true := by
  quickRfl
theorem cB0 : Nat.beq (PHeU.C 0) 1 = true := by quickRfl
theorem cBN : Nat.beq (PHeU.C (Nat.mul 733 8)) PHeU.c = true := by quickRfl
theorem cBSz : Nat.beq PHeU.c 187425 = true := by quickRfl

end CertificateChecks.KernelSporSch.PHeCl

end
