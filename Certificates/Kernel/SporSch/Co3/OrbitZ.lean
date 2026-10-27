module

public import Certificates.Kernel.SporSch.GenSetReplay
public import Certificates.Kernel.Sporadic.Co3.C
public import CFSG.Sporadic.Schreier.Co3OrbitZCheckInputs
meta import CFSG.Sporadic.Schreier.Co3OrbitZCheckInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kss_setreplay CertificateChecks.KernelSporSch.Co3OZ 276 9 CFSG.Sporadic.Schreier.Co3.co3OrigArrs
  CFSG.Sporadic.Schreier.Co3.co3IzNat 170775 10 32 128

namespace CertificateChecks.KernelSporSch.Co3OrbZ

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch
open CFSG.Sporadic.Schreier.Co3 CFSG.Sporadic.Schreier.Co3.Native CFSG.Certificates.Native
open CertificateChecks.KernelSpor CertificateChecks.KernelSporSch

theorem perm : allN 2 (fun k => permOK 276 9 (mask 9) (276 * 9) (Co3OZ.G k) (Co3OZ.GI k)) = true := by
  quickRfl

theorem gens : allN 2 (fun k => Nat.beq (Co3OZ.G k) (Co3C.S k)) = true := by quickRfl

theorem start : startK 9 36 (rowGet Co3OZ.XT 352 0) co3IzNat = true := by quickRfl

theorem c0 : Nat.beq (Co3OZ.C 0) 1 = true := by quickRfl

theorem cN : Nat.beq (Co3OZ.C 17152) 170775 = true := by quickRfl

theorem extract_get {S : Array (Array Nat)} {k j : Nat} (hj : j < k) (hk : k ≤ S.size) :
    (S.extract 0 k)[j]! = S[j]! := by
  rw [getElem!_pos (S.extract 0 k) j (by simp; omega), getElem!_pos S j (by omega)]
  simp

end CertificateChecks.KernelSporSch.Co3OrbZ

end
