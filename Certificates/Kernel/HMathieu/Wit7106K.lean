module

public import Certificates.Data.Kernel.HMathieu.Wit22K
public import Certificates.Data.Kernel.MathieuAut.InAutK
public import Certificates.Kernel.HMathieu.T22
import all Init.Data.Array.Basic
import all Init.Data.List.Basic

public section

namespace CertificateChecks.KernelHMathieu

open CFSG.KS.MathieuAut CFSG.KC.Enum CFSG.KC.HMathieu CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H13.A5.M22Hat

theorem k7106_memK : (pool22.all fun a =>
    a.size == 24 && inAutK a && (a[0]! == 0 && a[1]! == 1)) = true := by
  decide +kernel

theorem k7106_pool : ((List.range 6).all fun i =>
    vpK (poolP.getD i 0) && vpK (poolI.getD i 0) && unpk (poolP.getD i 0) == pool22[i]! &&
      unpk (poolI.getD i 0) == invArr pool22[i]!) = true := by
  decide +kernel

theorem k7106_witK : chk7106K T22.E 0 = true := by
  decide +kernel

end CertificateChecks.KernelHMathieu

end
