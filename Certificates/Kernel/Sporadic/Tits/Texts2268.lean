module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.Certificates.Kernel.Misc.HexFlatSound
public import CFSG.Certificates.Kernel.Misc.PairCountSound
public import CFSG.Certificates.Kernel.Spor.PrimSound
public import CFSG.Certificates.Kernel.Spor.Loops
public import CFSG.Sporadic.Schreier.TitsLocalCheckInputs
meta import CFSG.Sporadic.Schreier.TitsData
import CFSG.Sporadic.Schreier.TitsArrays
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSpor.T8775 CFSG.Sporadic.Schreier.Tits.titsPerm8775Text
#kmisc_hexflat CertificateChecks.KernelSpor.T8775 CFSG.Sporadic.Schreier.Tits.titsPerm8775Text 4 8775 14 6
#ks_chars CertificateChecks.KernelSpor.T2925 CFSG.Sporadic.Schreier.Tits.titsPerm2925Text
#kmisc_hexflat CertificateChecks.KernelSpor.T2925 CFSG.Sporadic.Schreier.Tits.titsPerm2925Text 3 2925 12 6
#ks_chars CertificateChecks.KernelSpor.TMaps CFSG.Sporadic.Schreier.Tits.titsMapsText
#kmisc_hexflat CertificateChecks.KernelSpor.TMaps CFSG.Sporadic.Schreier.Tits.titsMapsText 3 8775 12 2

namespace CertificateChecks.KernelSpor.Tits2268

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.Sporadic.Schreier.Tits
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.KC.Misc.PairCount

theorem arr8775_eq {L : Nat} (hL : L < 6) : titsArr8775 L = unpack 8775 14 (T8775.F L) := by
  have h := CFSG.KC.Misc.HexFlat.hexTable_sound T8775.all L hL
  have e : titsArr8775 L = CFSG.Monster.B.Co2.Native.hexTable 4 8775 (8775 * L) titsPerm8775Text := by
    delta titsArr8775 CFSG.Monster.B.Co2.Native.hexTable titsBytes8775
    exact rfl
  rw [e]
  simpa only [← T8775.eq] using h

theorem arr2925_eq {L : Nat} (hL : L < 6) : titsArr2925 L = unpack 2925 12 (T2925.F L) := by
  have h := CFSG.KC.Misc.HexFlat.hexTable_sound T2925.all L hL
  have e : titsArr2925 L = CFSG.Monster.B.Co2.Native.hexTable 3 2925 (2925 * L) titsPerm2925Text := by
    delta titsArr2925 CFSG.Monster.B.Co2.Native.hexTable titsBytes2925
    exact rfl
  rw [e]
  simpa only [← T2925.eq] using h

theorem kappa_eq : titsKappaArr = unpack 8775 12 (TMaps.F 1) := by
  have h := CFSG.KC.Misc.HexFlat.hexTable_sound TMaps.all 1 (by norm_num)
  have e : titsKappaArr = CFSG.Monster.B.Co2.Native.hexTable 3 8775 (8775 * 1) titsMapsText := by
    delta titsKappaArr CFSG.Monster.B.Co2.Native.hexTable titsMapsBytes
    exact rfl
  rw [e]
  simpa only [← TMaps.eq] using h

theorem beta_eq : titsBetaArr = unpack 8775 12 (TMaps.F 0) := by
  have h := CFSG.KC.Misc.HexFlat.hexTable_sound TMaps.all 0 (by norm_num)
  rw [← TMaps.eq] at h
  rw [← h]
  delta titsBetaArr CFSG.Monster.B.Co2.Native.hexTable titsMapsBytes
  apply Array.ext (by simp)
  intro i h1 h2
  simp

theorem perm8775 : allN 6 (fun L => permOK 8775 14 (mask 14) (8775 * 14) (T8775.F L)
    (pinvS 8775 14 (mask 14) (T8775.F L))) = true := by quickRfl

theorem perm2925 : allN 6 (fun L => permOK 2925 12 (mask 12) (2925 * 12) (T2925.F L)
    (pinvS 2925 12 (mask 12) (T2925.F L))) = true := by quickRfl

theorem mapsOK : bAnd(allN 8775 (fun j => Nat.blt (pg 12 (mask 12) (TMaps.F 0) j) 1755),
    allN 8775 (fun j => Nat.blt (pg 12 (mask 12) (TMaps.F 1) j) 2925)) = true := by quickRfl

theorem allPerms_gen {n w : Nat} {A : Array (Array Nat)} {k : Nat} {P PI : Nat → Nat}
    (hs : A.size = k) (hA : ∀ j < k, A[j]! = unpack n w (P j))
    (hp : ∀ j < k, permOK n w (mask w) (n * w) (P j) (PI j) = true) :
    allPermsOK n A = true := by
  unfold allPermsOK
  rw [allLt_iff]
  intro j hj
  rw [hs] at hj
  have h := invEqK_sound (hp j hj)
  rw [hA j hj, h.1]
  exact h.2

theorem facts1 : allPermsOK 8775 titsFlagArrs = true ∧ allPermsOK 2925 titsAStarArrs = true ∧
    allPermsOK 8775 titsDFlagStored = true ∧ allPermsOK 2925 titsDStarStored = true ∧
    allLt 8775 (fun j => decide (titsBetaArr[j]! < 1755)) = true ∧
    allLt 8775 (fun j => decide (titsKappaArr[j]! < 2925)) = true := by
  obtain ⟨m0, m1⟩ := (bAnd_iff (allN 8775 (fun j => Nat.blt (pg 12 (mask 12) (TMaps.F 0) j) 1755))
    (allN 8775 (fun j => Nat.blt (pg 12 (mask 12) (TMaps.F 1) j) 2925))).1 mapsOK
  refine ⟨allPerms_gen (k := 4) (P := fun L => T8775.F L)
      (PI := fun L => pinvS 8775 14 (mask 14) (T8775.F L)) (by simp [titsFlagArrs])
      (fun j hj => ?_) (fun j hj => allN_spec perm8775 j (by omega)),
    allPerms_gen (k := 4) (P := fun L => T2925.F L)
      (PI := fun L => pinvS 2925 12 (mask 12) (T2925.F L)) (by simp [titsAStarArrs])
      (fun j hj => ?_) (fun j hj => allN_spec perm2925 j (by omega)),
    allPerms_gen (k := 2) (P := fun L => T8775.F (4 + L))
      (PI := fun L => pinvS 8775 14 (mask 14) (T8775.F (4 + L))) (by simp [titsDFlagStored])
      (fun j hj => ?_) (fun j hj => allN_spec perm8775 (4 + j) (by omega)),
    allPerms_gen (k := 2) (P := fun L => T2925.F (4 + L))
      (PI := fun L => pinvS 2925 12 (mask 12) (T2925.F (4 + L))) (by simp [titsDStarStored])
      (fun j hj => ?_) (fun j hj => allN_spec perm2925 (4 + j) (by omega)),
    ?_, ?_⟩
  · rw [titsFlagArrs, getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn, arr8775_eq (by omega)]
  · rw [titsAStarArrs, getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn, arr2925_eq (by omega)]
  · rw [titsDFlagStored, getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn,
      arr8775_eq (by omega)]
  · rw [titsDStarStored, getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn,
      arr2925_eq (by omega)]
  · rw [allLt_iff]
    intro j hj
    rw [beta_eq, unpack_get hj, decide_eq_true_eq]
    exact Nat.blt_eq ▸ allN_spec m0 j hj
  · rw [allLt_iff]
    intro j hj
    rw [kappa_eq, unpack_get hj, decide_eq_true_eq]
    exact Nat.blt_eq ▸ allN_spec m1 j hj

end CertificateChecks.KernelSpor.Tits2268

end
