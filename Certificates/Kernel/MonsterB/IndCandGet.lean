
module

public import Certificates.Kernel.MonsterB.IndTransData
public import Certificates.Kernel.MonsterB.IndCentral
public import Certificates.Kernel.MonsterB.IndOrbGlue

public section

namespace CertificateChecks.KernelMonB.IndCand

open CFSG.Monster.B.Fischer CFSG.KLie.CT CertificateChecks.KernelMonB
  CertificateChecks.KernelMonB.IndOrbGlue

@[expose] noncomputable def candF (k y : Nat) : Nat :=
  Bool.rec (Bool.rec (fget (ICe.F 0) y 12) (fget (ITr.F (k - 2)) y 12) (Nat.blt k 12))
    (fget (IG.F k) y 12) (Nat.blt k 2)

theorem trans_get {j y : Nat} (hj : j < 10) (hy : y < 3510) :
    (indTransGen j)[y]! = fget (ITr.F j) y 12 := by
  have h := CFSG.KC.Misc.HexFlat.hexTable3_sound ITr.all j hj
  rw [← ITr.eq] at h
  change (hexTable3 3510 (3510 * j) indTransGenHex)[y]! = _
  rw [h, CFSG.KS.Raw.Orb.unpack_get hy, pg_eq]

theorem central_get {y : Nat} (hy : y < 3510) : indCentral[y]! = fget (ICe.F 0) y 12 := by
  have h := CFSG.KC.Misc.HexFlat.hexTable3_sound ICe.all 0 (by norm_num)
  rw [← ICe.eq, Nat.mul_zero] at h
  change (hexTable3 3510 0 indCentralHex)[y]! = _
  rw [h, CFSG.KS.Raw.Orb.unpack_get hy, pg_eq]

theorem cand_get {k y : Nat} (hk : k < 13) (hy : y < 3510) : (indCandidate k)[y]! = candF k y := by
  unfold indCandidate candF
  by_cases h2 : k < 2
  · have hb : Nat.blt k 2 = true := by simpa using h2
    rw [if_pos h2, hb]
    exact gen_get h2 hy
  · have hb : Nat.blt k 2 = false := by
      rw [Bool.eq_false_iff, ne_eq, Nat.blt_eq]
      exact h2
    rw [if_neg h2, hb]
    by_cases h12 : k < 12
    · have hb' : Nat.blt k 12 = true := by simpa using h12
      rw [if_pos h12, hb']
      exact trans_get (by omega) hy
    · have hb' : Nat.blt k 12 = false := by
        rw [Bool.eq_false_iff, ne_eq, Nat.blt_eq]
        exact h12
      rw [if_neg h12, hb']
      exact central_get hy

end CertificateChecks.KernelMonB.IndCand

end
