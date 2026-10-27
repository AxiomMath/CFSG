
module

public import Certificates.Kernel.Sporadic.RawGenSch
public import Certificates.Kernel.Sporadic.ON.Gen
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.Certificates.Kernel.Spor.TextAtSound
public import CFSG.Sporadic.FischerOddCore.Fi22ExtSylowCheckInputs
public meta import CFSG.Sporadic.FischerOddCore.Fi22ExtSylowCheckInputs
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.NormNum
public import CFSG.Certificates.Kernel.Spor.RawSound

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSpor.Fi22E256T CFSG.Sporadic.FischerOddCore.fi22Ext256Text

#ks_chars CertificateChecks.KernelSpor.Fi22DT CFSG.Sporadic.FischerOddCore.fi22ExtSmallPointsHex

namespace CertificateChecks.KernelSpor.Fi22X

meta def rows256M : Array (Array Nat) := (Array.range 18).map CFSG.Sporadic.FischerOddCore.fi22ExtArr256

meta def dM : Array (Array Nat) := #[CFSG.Sporadic.FischerOddCore.fi22ExtDArr]

meta def strongSM : Array (Array Nat) := CFSG.Sporadic.FischerOddCore.fi22ExtSmallStrong

meta def baseSM : Array Nat := #[0, 1, 2, 3, 4, 6]

end CertificateChecks.KernelSpor.Fi22X

#kmisc_packarrs CertificateChecks.KernelSpor.Fi22X.R256 CertificateChecks.KernelSpor.Fi22X.rows256M 9

#kmisc_packarrs CertificateChecks.KernelSpor.Fi22X.DPT CertificateChecks.KernelSpor.Fi22X.dM 12

#ks_rawchain_sl2 CertificateChecks.KernelSpor.Fi22SC 256 9 8 64 0
  CertificateChecks.KernelSpor.Fi22X.strongSM CertificateChecks.KernelSpor.Fi22X.baseSM 10
  CFSG.Sporadic.FischerOddCore.fi22ExtSmallDerivations

namespace CertificateChecks.KernelSpor.Fi22X

open CFSG.KC.Enum CFSG.KS CFSG.KS.Text CFSG.KS.Raw
open CFSG.Sporadic.FischerOddCore CFSG.Monster.B.Fischer CFSG.Monster.B.Co2.Native

@[expose] noncomputable def DP : Nat := DPT 0

@[expose] noncomputable def line256OK (L : Nat) : Bool :=
  bAnd(asciiK (Fi22E256T.chars.take (Nat.mul (Nat.succ L) (nat_lit 513))),
    lineK 2 256 9 (R256 L) (Fi22E256T.chars.drop (Nat.mul L (nat_lit 513))))

end CertificateChecks.KernelSpor.Fi22X

#kon_slices CertificateChecks.KernelSpor.Fi22X.line256OK 0 18

#kon_join CertificateChecks.KernelSpor.Fi22X.line256All CertificateChecks.KernelSpor.Fi22X.line256OK 18

namespace CertificateChecks.KernelSpor.Fi22X

open CFSG.KC.Enum CFSG.KS CFSG.KS.Text CFSG.KS.Raw
open CFSG.Sporadic.FischerOddCore CFSG.Monster.B.Fischer CFSG.Monster.B.Co2.Native

theorem dOK : bAnd(asciiK (Fi22DT.chars.take (Nat.mul (nat_lit 1) (nat_lit 769))),
    lineK 3 256 12 DP (Fi22DT.chars.drop (nat_lit 0))) = true := by quickRfl

theorem ext256_eq {L : Nat} (hL : L < 18) : fi22ExtArr256 L = unpack 256 9 (R256 L) := by
  obtain ⟨ha, hk⟩ := (bAnd_iff (asciiK (Fi22E256T.chars.take (Nat.mul (Nat.succ L) (nat_lit 513))))
    (lineK 2 256 9 (R256 L) (Fi22E256T.chars.drop (Nat.mul L (nat_lit 513))))).1 (line256All L hL)
  have hl := lineK_sound ha hk
  unfold fi22ExtArr256 fi22ExtBytes256
  rw [Fi22E256T.eq]
  apply Array.ext
  · simp [hexLine, CFSG.KS.Raw.unpack]
  · intro i h1 h2
    simp only [hexLine, CFSG.KS.Raw.unpack, Array.getElem_ofFn]
    exact hl i (by simpa [hexLine] using h1)

theorem dArr_size : fi22ExtDArr.size = 256 := by
  simp [fi22ExtDArr, fi22ExtSmallPointsNat, hex3List]

theorem dArr_get {i : Nat} (hi : i < 256) : fi22ExtDArr[i]! = pg 12 (mask 12) DP i := by
  obtain ⟨ha, hk⟩ := (bAnd_iff (asciiK (Fi22DT.chars.take (Nat.mul (nat_lit 1) (nat_lit 769))))
    (lineK 3 256 12 DP (Fi22DT.chars.drop (nat_lit 0)))).1 dOK
  have hl := lineK_sound (L := 0) ha hk i hi
  rw [← hl]
  unfold fi22ExtDArr fi22ExtSmallPointsNat hex3List
  rw [Fi22DT.eq]
  simp [hi]

theorem sOK : allN 18 (fun j => Nat.beq (Fi22SC.S j) (R256 j)) = true := by quickRfl
theorem baseOK : allN 6 (fun t => Nat.beq (#[0, 1, 2, 3, 4, 6] : Array Nat)[t]! (pg 9 (mask 9) Fi22SC.BP t)) =
    true := by quickRfl
theorem permS : allN 18 (fun j => permOK 256 9 (mask 9) (256 * 9) (Fi22SC.S j) (Fi22SC.SI j)) = true := by
  quickRfl

theorem bindsS : Binds 256 9 Fi22SC.S 18 6 Fi22SC.BP fi22ExtSmallStrong #[0, 1, 2, 3, 4, 6] := by
  refine ⟨by norm_num, by norm_num, by norm_num, by simp [fi22ExtSmallStrong], fun j hj => ?_,
    by simp, fun t ht => Nat.eq_of_beq_eq_true (allN_spec baseOK t ht)⟩
  rw [fi22ExtSmallStrong, getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn,
    ext256_eq hj, ← Nat.eq_of_beq_eq_true (allN_spec sOK j hj)]

end CertificateChecks.KernelSpor.Fi22X

end
