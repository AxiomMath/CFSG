module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.Certificates.Kernel.Spor.HexAtSound
public import CFSG.Certificates.Kernel.Spor.PrimSound
public import CFSG.Sporadic.SuzOddCore.GraphArrays
meta import CFSG.Sporadic.SuzOddCore.GraphArrays
import all CFSG.Sporadic.SuzOddCore.GraphArrays
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.Sporadic.SuzOddCore.Arrays
meta import CFSG.Sporadic.SuzOddCore.Arrays

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSpor.SuzCenT CFSG.Sporadic.SuzOddCore.graphCenterText

namespace CertificateChecks.KernelSpor.OddCore

open CFSG.Sporadic.SuzOddCore

meta def rowsOfC (r : Nat) (t : Array Nat) : Array (Array Nat) :=
  (List.range r).toArray.map fun j => t.extract (32 * j) (32 * j + 32)

meta def cenRowsM : Array (Array Nat) :=
  ((List.range 9).toArray.map fun r => rowsOfC 715 (centerFull r)).flatten

meta def cenInvRowsM : Array (Array Nat) :=
  ((List.range 9).toArray.map fun r =>
    rowsOfC 715 (CFSG.Monster.B.Co2.Native.invCand 22880 (centerFull r))).flatten

meta def cenCompM : Array (Array Nat) := (List.range 9).toArray.map centerCompact

meta def cenCompInvM : Array (Array Nat) :=
  cenCompM.map (CFSG.Monster.B.Co2.Native.invCand 280)

end CertificateChecks.KernelSpor.OddCore

#kmisc_packarrs CertificateChecks.KernelSpor.SuzCenR CertificateChecks.KernelSpor.OddCore.cenRowsM 15

#kmisc_packarrs CertificateChecks.KernelSpor.SuzCenRI CertificateChecks.KernelSpor.OddCore.cenInvRowsM 15

#kmisc_packarrs CertificateChecks.KernelSpor.SuzCenC CertificateChecks.KernelSpor.OddCore.cenCompM 9

#kmisc_packarrs CertificateChecks.KernelSpor.SuzCenCI CertificateChecks.KernelSpor.OddCore.cenCompInvM 9

namespace CertificateChecks.KernelSpor.OddCore

open CFSG.Sporadic.SuzOddCore CFSG.KC.Enum CFSG.KS CFSG.KS.Row CFSG.KS.Raw CFSG.KS.Prim
open CFSG.KC.Misc.HexAt

@[expose] noncomputable def fullB (r : Nat) : Bool :=
  hexAtK SuzCenT.chars (Nat.mul 4 (Nat.mul 23090 r)) 4 32 15 715 (offF SuzCenR (Nat.mul 715 r))

@[expose] noncomputable def compB (r : Nat) : Bool :=
  hexAtK SuzCenT.chars (Nat.add (Nat.mul 92360 r) 91520) 3 280 9 1 (offF SuzCenC r)

theorem full0 : fullB 0 = true := by quickRfl
theorem full1 : fullB 1 = true := by quickRfl
theorem full2 : fullB 2 = true := by quickRfl
theorem full3 : fullB 3 = true := by quickRfl
theorem full4 : fullB 4 = true := by quickRfl
theorem full5 : fullB 5 = true := by quickRfl
theorem full6 : fullB 6 = true := by quickRfl
theorem full7 : fullB 7 = true := by quickRfl
theorem full8 : fullB 8 = true := by quickRfl

theorem comp0 : compB 0 = true := by quickRfl
theorem comp1 : compB 1 = true := by quickRfl
theorem comp2 : compB 2 = true := by quickRfl
theorem comp3 : compB 3 = true := by quickRfl
theorem comp4 : compB 4 = true := by quickRfl
theorem comp5 : compB 5 = true := by quickRfl
theorem comp6 : compB 6 = true := by quickRfl
theorem comp7 : compB 7 = true := by quickRfl
theorem comp8 : compB 8 = true := by quickRfl

theorem full_perms : allN 9 (fun r =>
    rpermK 22880 15 (mask 15) SuzCenR (Nat.mul 715 r) SuzCenRI (Nat.mul 715 r)) = true := by
  quickRfl

theorem comp_perms : allN 9 (fun r =>
    invEqK 280 9 (mask 9) (280 * 9) (SuzCenC r) (SuzCenCI r)) = true := by
  quickRfl

theorem fullB_all {r : Nat} (hr : r < 9) : fullB r = true := by
  interval_cases r
  exacts [full0, full1, full2, full3, full4, full5, full6, full7, full8]

theorem compB_all {r : Nat} (hr : r < 9) : compB r = true := by
  interval_cases r
  exacts [comp0, comp1, comp2, comp3, comp4, comp5, comp6, comp7, comp8]

theorem centerFull_eq {r : Nat} (hr : r < 9) :
    centerFull r = rowArr 22880 15 SuzCenR (715 * r) := by
  have h := hexTable_rowsAt (R := 715) (e := 23090 * r) (fullB_all hr)
  rw [← SuzCenT.eq] at h
  exact h

theorem centerCompact_eq {r : Nat} (hr : r < 9) : centerCompact r = unpack 280 9 (SuzCenC r) := by
  have h := hexAt_unpack (compB_all hr) (j := 0) (by decide)
  rw [← SuzCenT.eq] at h
  refine Eq.trans ?_ h
  apply Array.ext
  · simp [centerCompact]
  · intro x _ _
    simp only [centerCompact, Array.getElem_ofFn]
    have ex : 92360 * r + 91520 + 3 * x = Nat.add (Nat.mul 92360 r) 91520 + 3 * (280 * 0 + x) := by
      simp only [Nat.add_eq, Nat.mul_eq]
      omega
    rw [ex]

end CertificateChecks.KernelSpor.OddCore

end
