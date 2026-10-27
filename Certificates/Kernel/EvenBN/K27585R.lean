module

public import Certificates.Kernel.EvenBN.K27585D
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option trace.profiler true
set_option trace.profiler.threshold 1000

namespace CertificateChecks.KernelEvenBN.Five

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CertificateChecks.KernelSpor
open Certificates.TitsAschbacherParrott Certificates.TitsAschbacherFive Certificates.MaxD2Perm

theorem lK : (lettersK 2 deltaAWord && lettersK 2 deltaBWord && lettersK 2 titsDData.uW) = true := by
  quickRfl

theorem cK : (canonK 1755 11 (mask 11) (1755 * 11) (wTP deltaAWord) &&
    canonK 1755 11 (mask 11) (1755 * 11) (wTP deltaBWord) &&
    canonK 1755 11 (mask 11) (1755 * 11) (wTP titsDData.uW)) = true := by quickRfl

theorem rel : (Nat.beq (pc U2 X) (pc (ppw X 3) U2) &&
    Nat.beq (pc U2 U2) (pc CertificateChecks.KernelSporSch.TitsZ (V 2)) &&
    Nat.beq (pc Dl (wTP titsDData.uW)) (pc X Dl)) = true := by quickRfl

end CertificateChecks.KernelEvenBN.Five

end
