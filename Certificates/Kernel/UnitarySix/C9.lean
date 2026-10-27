module

public import Certificates.Kernel.UnitarySix.Yamada
public import CFSG.Certificates.Kernel.U6Sound3000
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.C9NativeInputs
public import Certificates.Certificate3180
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelU6

open CFSG.KC.U6

theorem k3142 : check3142K U.LT aWK = true := by quickRfl

theorem cert3142 : CFSG.EvenSmallLie.UnitarySix.sumCheck = true := by
  have h := sound3142 letters_eq aW_eq k3142
  have e : aGensG CFSG.EvenSmallLie.UnitarySix.u62Letters CFSG.EvenSmallLie.UnitarySix.aWords =
      CFSG.EvenSmallLie.UnitarySix.aGens := rfl
  unfold sumCheckG c3G j3G at h
  rw [e] at h
  unfold CFSG.EvenSmallLie.UnitarySix.sumCheck CFSG.EvenSmallLie.UnitarySix.c3
    CFSG.EvenSmallLie.UnitarySix.j3
  exact h

end CertificateChecks.KernelU6

end
