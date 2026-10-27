module

public import Certificates.Kernel.M11Local.Checks
public import Certificates.Data.ONanSmallM11
public import CFSG.Certificates.Kernel.Misc.PermClosSound

public section

namespace CertificateChecks.KernelM11Local

open CFSG.KC.Misc.Clos CFSG.KC.M11L Certificates.ONanSmallM11 CFSG.Sporadic.Mathieu

theorem pcode_m11x : pcode m11x = xK := by decide +kernel

theorem pcode_m11y : pcode m11y = yK := by decide +kernel

theorem pcode_m11s : pcode m11s = sK := by decide +kernel

theorem pcode_m11gA : pcode m11gA = aK := by decide +kernel

theorem pcode_m11gB : pcode m11gB = bK := by decide +kernel

theorem m11K_codes :
    m11K (pcode m11x) (pcode m11y) (pcode m11s) (pcode m11gA) (pcode m11gB) wx wy ws = true := by
  rw [pcode_m11x, pcode_m11y, pcode_m11s, pcode_m11gA, pcode_m11gB]
  exact m11K_ok

end CertificateChecks.KernelM11Local

end
