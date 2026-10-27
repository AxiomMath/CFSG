module

public import Certificates.Kernel.HMathieu.T22
public import Certificates.Data.Kernel.HMathieu.PermThree
public import CFSG.Quasithin.Background.HNPrimeMathieuInputs
import all Init.Data.Array.Basic
import all Init.Data.List.Basic

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelHMathieu.Perm7119

open CFSG.KC.HMathieu CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H13.A5.M22Hat
  CFSG.Quasithin.H.MathieuLat CertificateChecks.KernelHMathieu

theorem aut : inAutOK y22 = true := by decide +kernel

theorem fix01 : y22[0]! = 0 ∧ y22[1]! = 1 := by decide +kernel

theorem cube : pow24 y22 3 = id24 := by decide +kernel

theorem ne_one : y22 ≠ id24 := by decide +kernel

theorem unpk_y : unpk (pkL y22.toList) = y22 := by decide +kernel

theorem unpk_w1 : unpk (pkL (invArr y22).toList) = invArr y22 := by decide +kernel

theorem unpk_w2 : unpk (pkL (pow24 (invArr y22) 2).toList) = pow24 (invArr y22) 2 := by
  decide +kernel

theorem vp : vpK (pkL (invArr y22).toList) = true ∧
    vpK (pkL (pow24 (invArr y22) 2).toList) = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem k : permThreeK T22.E (pkL y22.toList) (pkL (invArr y22).toList)
    (pkL (pow24 (invArr y22) 2).toList) = true := by decide +kernel

end CertificateChecks.KernelHMathieu.Perm7119

end
