
module

public import Certificates.Kernel.SporSch.Ru.Pts
public import Certificates.Kernel.SporSch.Ru.Gens
public import CFSG.Certificates.Kernel.SporSch.RuEnumSound
public import CFSG.Sporadic.Schreier.RuCheckSylowInputs
meta import CFSG.Sporadic.Schreier.RuCheckSylowInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.RuF

open CFSG.Sporadic.RuSchreier CFSG.Monster.B.Co2.Native

meta def fM : Array Nat := ruF

meta def fposM : Array Nat := ruFPos

meta def zfM : Array Nat := ruZF

end CertificateChecks.KernelSporSch.RuF

#ks_perm CertificateChecks.KernelSporSch.RuF.F 12 CertificateChecks.KernelSporSch.RuF.fM
#ks_perm CertificateChecks.KernelSporSch.RuF.FPOS 12 CertificateChecks.KernelSporSch.RuF.fposM
#ks_perm CertificateChecks.KernelSporSch.RuF.ZF 11 CertificateChecks.KernelSporSch.RuF.zfM

namespace CertificateChecks.KernelSporSch.RuF

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.Sporadic.RuSchreier
  CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CertificateChecks.KernelSporSch
  CertificateChecks.KernelSporSch.RuG

theorem fK : hexPackK 3 4060 10120 8120 1920 12 F RuPts.chars = true := by quickRfl
theorem posF : posK 4060 1920 12 F FPOS = true := by quickRfl
theorem fLt : allN 1920 (fun i => Nat.blt (pg 12 (mask 12) F i) 4060) = true := by quickRfl
theorem zCanon : canonK 4060 12 (mask 12) (4060 * 12) Z = true := by quickRfl
theorem zF : resK 1920 12 11 F FPOS Z ZF = true := by quickRfl

theorem f_eq : ruF = unpack 1920 12 F := by
  have h := hexPackK_sound (by norm_num) (by norm_num) fK
  rw [← RuPts.eq] at h
  apply Array.ext
  · simp [ruF, ruPtList, ruPtsOffsets, unpack]
  · intro i h1 h2
    have hi : i < 1920 := by simpa [unpack] using h2
    simp only [ruF, ruPtList, unpack, Array.getElem_ofFn]
    have e := h i hi
    rw [show 3 * (8120 + i) = 3 * ((ruPtsOffsets.getD 7 (0, 0)).1 + i) from rfl] at e
    exact e

theorem fpos_eq : ruFPos = unpack 4060 12 FPOS := by
  rw [ruFPos, f_eq]
  exact posK_sound posF

theorem zf_eq : ruZF = unpack 1920 11 ZF := by
  rw [ruZF, fpos_eq, f_eq, z_eq]
  exact resK_sound (fun i hi => by simpa [Nat.blt_eq] using allN_spec fLt i hi) zCanon zF

end CertificateChecks.KernelSporSch.RuF

end
