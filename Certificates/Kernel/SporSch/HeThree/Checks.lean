module

public import Certificates.Kernel.SporSch.HeThree.Wit
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.HeThree

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CertificateChecks.KernelSporSch
open CertificateChecks.KernelSpor CertificateChecks.KernelSporSch.HeCn

@[expose] noncomputable def ry0 (s : Nat) : Bool := ry 0 s
@[expose] noncomputable def ry1 (s : Nat) : Bool := ry 1 s
@[expose] noncomputable def cj0 (s : Nat) : Bool := cj 0 s
@[expose] noncomputable def cj1 (s : Nat) : Bool := cj 1 s

theorem kRX0 : rx 0 = true := by quickRfl
theorem kRX1 : rx 1 = true := by quickRfl
theorem kXP0 : permOK 8330 14 (mask 14) (8330 * 14) (X 0) (XI 0) = true := by quickRfl
theorem kXP1 : permOK 8330 14 (mask 14) (8330 * 14) (X 1) (XI 1) = true := by quickRfl
theorem kF0 : nfValidK 5 HeC.LR (F 0) = true := by quickRfl
theorem kF1 : nfValidK 5 HeC.LR (F 1) = true := by quickRfl
theorem kG0 : vldH (G 0) = true := by quickRfl
theorem kG1 : vldH (G 1) = true := by quickRfl
theorem kO0 : ordPL bsH (pmR (RY 0)) 3 = true := by quickRfl
theorem kO1 : ordPL bsH (pmR (RY 1)) 3 = true := by quickRfl
theorem kSum0 : Nat.beq (sumN 8330 (V 0)) 7560 = true := by quickRfl
theorem kSum1 : Nat.beq (sumN 8330 (V 1)) 504 = true := by quickRfl
theorem kQ : qOK = true := by quickRfl
theorem kQL : qLines = true := by quickRfl
theorem kQH : qTrans = true := by quickRfl
theorem kS00 : sOK 0 2 8 280 = true := by quickRfl
theorem kS05 : sOK 0 5 5 280 = true := by quickRfl
theorem kS07 : sOK 0 7 7 280 = true := by quickRfl
theorem kS12 : sOK 1 2 8 56 = true := by quickRfl
theorem kS17 : sOK 1 7 7 56 = true := by quickRfl
theorem kGW : gOK = true := by quickRfl
theorem kQW : qwOK = true := by quickRfl
theorem kS3 : s3OK = true := by quickRfl
theorem kCW : cwOK = true := by quickRfl

end CertificateChecks.KernelSporSch.HeThree

#kss_each CertificateChecks.KernelSporSch.HeThree.GBc CertificateChecks.KernelSporSch.HeThree.gb 49

#kss_each CertificateChecks.KernelSporSch.HeThree.RY0c CertificateChecks.KernelSporSch.HeThree.ry0 49
#kss_each CertificateChecks.KernelSporSch.HeThree.RY1c CertificateChecks.KernelSporSch.HeThree.ry1 49
#kss_each CertificateChecks.KernelSporSch.HeThree.CJ0c CertificateChecks.KernelSporSch.HeThree.cj0 49
#kss_each CertificateChecks.KernelSporSch.HeThree.CJ1c CertificateChecks.KernelSporSch.HeThree.cj1 49

end
