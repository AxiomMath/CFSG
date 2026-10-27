module

public import CFSG.Certificates.Kernel.Spor.RawSound
public import CFSG.Certificates.Kernel.Misc.HexFlatSound
public import Certificates.Data.CFSGNative.MonsterB.Co2Data
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Data
public meta import Certificates.Kernel.Sporadic.RawGen
import Certificates.Kernel.Misc.Perm.HexCmd

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelMonB.Co2V CFSG.Monster.B.Co2.Native.vectorsHex
#kmisc_hexflat CertificateChecks.KernelMonB.Co2V CFSG.Monster.B.Co2.Native.vectorsHex 6 2300 24 1

public section

namespace CertificateChecks.KernelMonB

open CFSG.KS.Raw CFSG.KC.Enum

theorem vectors_eq : CFSG.Monster.B.Co2.Native.vectors () = unpack 2300 24 (Co2V.F 0) := by
  have h := CFSG.KC.Misc.HexFlat.hexTable_sound Co2V.all 0 (by decide)
  rw [← Co2V.eq] at h
  exact h

theorem vectors_contains {t : Nat} (ht : t < 2300) :
    (CFSG.Monster.B.Co2.Native.vectors ()).contains (pg 24 (CFSG.KS.mask 24) (Co2V.F 0) t) =
      true := by
  rw [vectors_eq, Array.contains_iff_mem, unpack, Array.mem_ofFn]
  exact ⟨⟨t, ht⟩, rfl⟩

end CertificateChecks.KernelMonB

end
