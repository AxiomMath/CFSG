
module

public import Certificates.Kernel.Sporadic.RawGen
public import CFSG.Certificates.Kernel.Spor.TextAtSound
public import CFSG.Certificates.Kernel.BfsPinSound
public import CFSG.Sporadic.FischerOddCore.Fi22ExtCheckBase
public import CFSG.Monster.B.Fischer.Fi22OuterCheckBase
meta import CFSG.Sporadic.FischerOddCore.Fi22ExtCheckBase
meta import CFSG.Monster.B.Fischer.Fi22OuterCheckBase
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.BfsPinUnpack
public meta import CFSG.Sporadic.FischerOddCore.Fi22ExtCheckInputs

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSpor.Fi22ExtT CFSG.Sporadic.FischerOddCore.fi22Ext3510Text

#ks_chars CertificateChecks.KernelSpor.Fi22OutT CFSG.Monster.B.Fischer.fi22Outer3510Text

namespace CertificateChecks.KernelSpor.Fi22E2073

meta def rowE : Array Nat := CFSG.Sporadic.FischerOddCore.fi22ExtArr 23

end CertificateChecks.KernelSpor.Fi22E2073

#ks_perm CertificateChecks.KernelSpor.Fi22E2073.E 12 CertificateChecks.KernelSpor.Fi22E2073.rowE

namespace CertificateChecks.KernelSpor.Fi22E2073

open CFSG.KC.Enum CFSG.KS CFSG.KS.Text CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KS.Raw
open CFSG.Sporadic.FischerOddCore CFSG.Monster.B.Fischer CFSG.Monster.B.Co2.Native

theorem asciiE : asciiK (Fi22ExtT.chars.take ((23 + 1) * (3 * 3510 + 1))) = true := by
  quickRfl

theorem asciiO : asciiK (Fi22OutT.chars.take ((1 + 1) * (3 * 3510 + 1))) = true := by
  quickRfl

theorem lineE : lineK 3 3510 12 E (Fi22ExtT.chars.drop (23 * (3 * 3510 + 1))) = true := by
  quickRfl

theorem lineO : lineK 3 3510 12 E (Fi22OutT.chars.drop (1 * (3 * 3510 + 1))) = true := by
  quickRfl

theorem canonE : canonK 3510 12 (mask 12) (3510 * 12) E = true := by
  quickRfl

theorem line_eq {s : String} {cs : List Char} (hs : s = String.ofList cs) {L : Nat}
    (ha : asciiK (cs.take ((L + 1) * (3 * 3510 + 1))) = true) (h : lineK 3 3510 12 E (cs.drop (L * (3 * 3510 + 1))) = true) :
    hexLine s.toUTF8 3 3510 L = CFSG.KS.Raw.unpack 3510 12 E := by
  subst hs
  have hl := lineK_sound ha h
  apply Array.ext
  · simp [hexLine, CFSG.KS.Raw.unpack]
  · intro i h1 h2
    simp only [hexLine, CFSG.KS.Raw.unpack, Array.getElem_ofFn]
    exact hl i (by simpa [hexLine] using h1)

theorem extE : fi22ExtArr 23 = CFSG.KS.Raw.unpack 3510 12 E :=
  line_eq Fi22ExtT.eq asciiE lineE

theorem outE : (fi22OuterStrong3510 1)[0]! = CFSG.KS.Raw.unpack 3510 12 E := by
  have hl : fi22OuterLine3510 1 0 = 1 := by decide
  unfold fi22OuterStrong3510
  rw [getElem!_pos _ 0 (by simp [fi22OuterLines3510]), Array.getElem_ofFn]
  change fi22OuterArr3510 (fi22OuterLine3510 1 0) = _
  rw [hl]
  exact line_eq Fi22OutT.eq asciiO lineO

theorem facts : eqA 3510 (fi22ExtArr 23) (fi22OuterStrong3510 1)[0]! = true := by
  rw [extE, outE, eqA_unpack canonE canonE, Nat.beq_refl]

end CertificateChecks.KernelSpor.Fi22E2073

end
