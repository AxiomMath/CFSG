module

public import Certificates.Kernel.HMathieu.T12
public import Certificates.Data.Kernel.HMathieu.PermThree
public import CFSG.Quasithin.Background.HNPrimeMathieuInputs
import all Init.Data.Array.Basic
import all Init.Data.List.Basic
public import CFSG.Quasithin.H13.A5M12SylInputs

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelHMathieu.Perm7120

open CFSG.KC.HMathieu CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H13.A5.M22Hat
  CFSG.Quasithin.H13.A5.M12 CFSG.Quasithin.H.MathieuLat CertificateChecks.KernelHMathieu

theorem aut : inAutOK y12 = true := by decide +kernel

theorem pair : okPair y12 (invArr y12) = true := by decide +kernel

theorem cube : pow24 y12 3 = id24 := by decide +kernel

theorem ne_one : y12 ≠ id24 := by decide +kernel

theorem unpk_y : unpk (pkL y12.toList) = y12 := by decide +kernel

theorem unpk_w1 : unpk (pkL (invArr y12).toList) = invArr y12 := by decide +kernel

theorem unpk_w2 : unpk (pkL (pow24 (invArr y12) 2).toList) = pow24 (invArr y12) 2 := by
  decide +kernel

theorem vp : vpK (pkL (invArr y12).toList) = true ∧
    vpK (pkL (pow24 (invArr y12) 2).toList) = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem k : permThreeK T12.E (pkL y12.toList) (pkL (invArr y12).toList)
    (pkL (pow24 (invArr y12) 2).toList) = true := by decide +kernel

end CertificateChecks.KernelHMathieu.Perm7120

end
