module

public import Certificates.Kernel.GMS78.W
public import CFSG.Sporadic.Bridge.VecSurj
public import Certificates.Data.CFSGNative.Ru.Data
public import Certificates.Data.GMS78RuPi7RuData

public section

namespace CertificateChecks.KernelGMS78.W

open CFSG in
open CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.VecSurj CFSG.ComponentClassification.GMS78.RuPi7 in
theorem certificate : (∀ r ∈ pi7Rels, wordProd (img pi7RuSpec (seedG CFSG.Sporadic.Ru.Native.ruData))
      (r.map fun l => (l.1.val, l.2)) = 1) ∧
    CFSG.Sporadic.Th.wordG (imgG pi7RuSpec (seedG CFSG.Sporadic.Ru.Native.ruData))
        pi7RuSurjWords[0]! = CFSG.Sporadic.SmallF2.a CFSG.Sporadic.Ru.Native.ruData ∧
    CFSG.Sporadic.Th.wordG (imgG pi7RuSpec (seedG CFSG.Sporadic.Ru.Native.ruData))
        pi7RuSurjWords[1]! = CFSG.Sporadic.SmallF2.b CFSG.Sporadic.Ru.Native.ruData :=
  ⟨pi7Rels_hold, by simpa [phi] using surj (i := 0) (by norm_num),
    by simpa [phi] using surj (i := 1) (by norm_num)⟩

end CertificateChecks.KernelGMS78.W

end
