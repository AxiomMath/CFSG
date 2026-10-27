module

public import Certificates.Kernel.Fi22U.UnitaryOrb
public import Certificates.Kernel.Fi22U.M693Orb
public import Certificates.Kernel.Fi22U.Words
public import Certificates.Kernel.Sporadic.Fi22.R3150M
public import Certificates.Kernel.Sporadic.Fi22.F1OuterS
public import Certificates.Kernel.Sporadic.Fi22.F1OuterT
public import Certificates.Data.Kernel.Fi22U.Restrict
public import Certificates.Data.Kernel.Spor.Prim
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi22U.MK

open CFSG.KC.Fi22U CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CertificateChecks.KernelSpor
  CertificateChecks.KernelFi22U

theorem u0 : wordEqK 693 10 (mask 10) (pidn 693 10) Fi22UO.S Fi22UO.SI 49 (wOf W693.w0)
    (Fi22O693T.L 64) = true := by decide +kernel

theorem u1 : wordEqK 693 10 (mask 10) (pidn 693 10) Fi22UO.S Fi22UO.SI 49 (wOf W693.w1)
    (Fi22O693T.L 65) = true := by decide +kernel

theorem u2 : wordEqK 693 10 (mask 10) (pidn 693 10) Fi22UO.S Fi22UO.SI 49 (wOf W693.w2)
    (Fi22O693T.L 66) = true := by decide +kernel

theorem m0 : wordEqK 3510 12 (mask 12) (pidn 3510 12) Fi22MR.S Fi22MR.SI 17 (wOf W3510.w0)
    (Fi22OutT.L 147) = true := by decide +kernel

theorem m1 : wordEqK 3510 12 (mask 12) (pidn 3510 12) Fi22MR.S Fi22MR.SI 17 (wOf W3510.w1)
    (Fi22OutT.L 148) = true := by decide +kernel

theorem m2 : wordEqK 3510 12 (mask 12) (pidn 3510 12) Fi22MR.S Fi22MR.SI 17 (wOf W3510.w2)
    (Fi22OutT.L 149) = true := by decide +kernel

theorem m3 : wordEqK 3510 12 (mask 12) (pidn 3510 12) Fi22MR.S Fi22MR.SI 17 (wOf W3510.w3)
    (Fi22OutT.L 150) = true := by decide +kernel

theorem mz : wordEqK 3510 12 (mask 12) (pidn 3510 12) Fi22MR.S Fi22MR.SI 17
    (wOf (commC W3510.w0 W3510.w1 W3510.w2 W3510.w3)) (Fi22OutT.L 1) = true := by decide +kernel

theorem sOK : allN 15 (fun j => Nat.beq (Fi22O693T.L (64 + j)) (Fi22MO.S j)) = true := by
  decide +kernel

theorem bOK : allN 5 (fun t => Nat.beq (#[0, 1, 3, 9, 45][t]!) (pg 10 (mask 10) Fi22MO.BP t)) =
    true := by
  decide +kernel

theorem inv : invOK (Fi22O693T.L 0) Inv693.inv0 = true := by decide +kernel

theorem restrict : ∀ k < 3, restrictOK (Fi22O693T.L 0) Inv693.inv0 (Fi22O693T.L (64 + k))
    (Fi22OutT.L (3 + k)) (Fi22OMP.F 0) = true := by
  decide +kernel

theorem fix : fixOK (Fi22OutT.L 1) (Fi22OMP.F 0) = true := by decide +kernel

theorem distinct : distinctOK (Fi22OMP.F 0) = true := by decide +kernel

end CertificateChecks.KernelFi22U.MK

end
