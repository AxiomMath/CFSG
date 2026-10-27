module

public import Certificates.Kernel.Sporadic.OddCore.SqrtK26102
public import Certificates.Kernel.Sporadic.OddCore.MulHGlue

public section

namespace CertificateChecks.KernelSpor.SqrtK26102

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KS.MulH
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore.Native
open CFSG.EvenSporadicStandard.Fin76b.TC3H

theorem sqrt_of {n w u a y : Nat} {s : Bool} {sift : Table → Bool}
    (h : sqK n w u a y s = true)
    (hs : s = true → (sift (tabT (unpack n w y)) ||
      sift (tabT (unpack n w (pcomp n w (mask w) y u)))) = true) :
    sqrtOK n sift (tabT (unpack n w u)) (tabT (unpack n w a)) (tabT (unpack n w y)) = true := by
  unfold sqK at h
  simp only [bAnd_iff] at h
  obtain ⟨-, hu, ha, hy, hinv, hs', heq⟩ := h
  unfold sqrtOK
  rw [compT_unpack hy hu, compT_unpack hy hy, tblEq_unpack (canonK_pcomp hy hy) ha,
    permOK_unpack hy hinv, hs hs', heq]
  rfl

theorem sqK_canon {n w u a y : Nat} {s : Bool} (h : sqK n w u a y s = true) :
    canonK n w (mask w) (n * w) u = true ∧ canonK n w (mask w) (n * w) y = true := by
  unfold sqK at h
  simp only [bAnd_iff] at h
  exact ⟨h.2.1, h.2.2.2.1⟩

theorem j2Tbl_eq {k : Nat} (hk : k < 3) : j2Tbl k = tabT (unpack 315 9 (TC3HJ2T.F k)) := by
  have h : natArr (j2Tbl k) = unpack 315 9 (TC3HJ2T.F k) := by
    have h := CFSG.KC.Misc.HexFlat.hexT_sound TC3HJ2T.all (by norm_num) k hk
    rw [← TC3HJ2T.eq] at h
    exact h
  rw [← tabT_natArr (j2Tbl k), h]

theorem j3Tbl_eq {k : Nat} (hk : k < 2) : j3Tbl k = tabT (unpack 6156 13 (TC3HJ3P k)) := by
  have h : natArr (j3Tbl k) = unpack 6156 13 (TC3HJ3P k) := by
    have h := CFSG.KS.Join.hexT_join_sound (d := 4) (n₀ := 513) (w := 13) (c := 12) (N := 2)
      TC3HJ3T.all tc3h_join (by norm_num) k hk
    rw [← TC3HJ3T.eq] at h
    exact h
  rw [← tabT_natArr (j3Tbl k), h]

end CertificateChecks.KernelSpor.SqrtK26102
