module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.Certificates.Kernel.Misc.HexFlatSound
public import CFSG.Sporadic.Schreier.TitsArrays
meta import CFSG.Sporadic.Schreier.TitsData
public import CFSG.Certificates.Kernel.Spor.RawSound

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelMisc.TitsText CFSG.Sporadic.Schreier.Tits.titsPerm1755Text

#kmisc_hexflat CertificateChecks.KernelMisc.TitsText CFSG.Sporadic.Schreier.Tits.titsPerm1755Text
  3 1755 11 96

namespace CertificateChecks.KernelMisc.TitsText

open CFSG.Sporadic.Schreier.Tits CFSG.KS.Raw

theorem titsArr1755_eq {L : Nat} (hL : L < 96) : titsArr1755 L = unpack 1755 11 (F L) := by
  have h := CFSG.KC.Misc.HexFlat.hexTable_sound all L hL
  have e : titsArr1755 L =
      CFSG.Monster.B.Co2.Native.hexTable 3 1755 (1755 * L) titsPerm1755Text := by
    delta titsArr1755 CFSG.Monster.B.Co2.Native.hexTable titsBytes1755
    exact rfl
  rw [e]
  simpa only [← eq] using h

theorem titsDerivedArrs_get {j : Nat} (hj : j < 13) :
    titsDerivedArrs[j]! = unpack 1755 11 (F (18 + j)) := by
  rw [titsDerivedArrs, titsField1755, getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn,
    titsArr1755_eq (by omega)]

end CertificateChecks.KernelMisc.TitsText

end
