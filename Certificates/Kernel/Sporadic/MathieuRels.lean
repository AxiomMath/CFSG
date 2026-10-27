module

public import CFSG.Certificates.Kernel.Spor.RelSound
public import CFSG.Certificates.Kernel.Bounds.M23.Binding
public import CFSG.Certificates.Kernel.Bounds.M24Alt.Binding
public import CFSG.Sporadic.Bridge.M23SurjInputs
public import CFSG.Sporadic.Bridge.M24SurjInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Sporadic.Bridge.TwoGen
public import CFSG.Sporadic.M23.M23Group
public import CFSG.Sporadic.Presentation.M23
public import CFSG.Sporadic.Presentation.M24Exact
public import CFSG.Sporadic.Schreier.M23

public section

namespace CertificateChecks.KernelSpor.MathieuRels

open CFSG.Sporadic.Bridge.TwoGen.Native CFSG.KS.Rel

theorem m23K : relK 23 5 CFSG.Sporadic.Bridge.M23.tabA CFSG.Sporadic.Bridge.M23.tabA
    CFSG.Sporadic.Bridge.M23.tabBi CFSG.Sporadic.Bridge.M23.tabB CFSG.KBRoute.M23.rels = true := by
  quickRfl

theorem m24K : relK 24 5 CFSG.Sporadic.Mathieu.Native.m24Data.tA
    CFSG.Sporadic.Mathieu.Native.m24Data.tA CFSG.Sporadic.Bridge.M24.tabBi
    CFSG.Sporadic.Mathieu.Native.m24Data.tB CFSG.KBAlt.M24.rels = true := by
  quickRfl

theorem m23 : relCheck 23 CFSG.Sporadic.Bridge.M23.tabA CFSG.Sporadic.Bridge.M23.tabA
    CFSG.Sporadic.Bridge.M23.tabBi CFSG.Sporadic.Bridge.M23.tabB
    TauCeti.Sporadic.m23Presentation.relatorLetters = true := by
  rw [CFSG.KBRoute.M23.rels_eq]
  exact relK_sound m23K

theorem m24 : relCheck 24 CFSG.Sporadic.Mathieu.Native.m24Data.tA
    CFSG.Sporadic.Mathieu.Native.m24Data.tA CFSG.Sporadic.Bridge.M24.tabBi
    CFSG.Sporadic.Mathieu.Native.m24Data.tB TauCeti.Sporadic.m24Presentation.relatorLetters =
    true := by
  rw [CFSG.KBAlt.M24.rels_eq]
  exact relK_sound m24K

end CertificateChecks.KernelSpor.MathieuRels

end
