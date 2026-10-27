module

public import Certificates.Data.Kernel.CosetW.EnumW
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshLemma5Check

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelYoshQ

open CFSG.CosetTable CFSG.Certificates.CosetEnumeration CFSG.EvenSporadicStandard.M12Std.Yosh

set_option maxHeartbeats 0

@[expose] def six : List ℕ := [0, 1, 2, 3, 4, 5]

theorem b4 : checkW (mkParamsW (2 * 8) (invArrW 8) (codes (rel4 0 0))
      (codes ((subsetOf 8 six).map fun x => [(x, true)]))) 20000 4 = true ∧
    checkW (mkParamsW (2 * 8) (invArrW 8) (codes (rel4 0 1))
      (codes ((subsetOf 8 six).map fun x => [(x, true)]))) 20000 4 = true ∧
    checkW (mkParamsW (2 * 8) (invArrW 8) (codes (rel4 1 0))
      (codes ((subsetOf 8 six).map fun x => [(x, true)]))) 20000 4 = true ∧
    checkW (mkParamsW (2 * 8) (invArrW 8) (codes (rel4 1 1))
      (codes ((subsetOf 8 six).map fun x => [(x, true)]))) 20000 4 = true := by
  decide +kernel

theorem b4r : checkW (mkParamsW (2 * (subsetOf 8 six).length) (invArrW (subsetOf 8 six).length)
      (codes (restrictWords (subsetOf 8 six) (rel4 0 0)))
      (codes ((subsetOf (subsetOf 8 six).length []).map fun x => [(x, true)]))) 20000 384 = true := by
  decide +kernel

theorem b4eq : restrictWords (subsetOf 8 six) (rel4 0 1) = restrictWords (subsetOf 8 six) (rel4 0 0) ∧
    restrictWords (subsetOf 8 six) (rel4 1 0) = restrictWords (subsetOf 8 six) (rel4 0 0) ∧
    restrictWords (subsetOf 8 six) (rel4 1 1) = restrictWords (subsetOf 8 six) (rel4 0 0) := by
  decide +kernel

theorem bE : checkW (mkParamsW (2 * 6) (invArrW 6) (codes relE)
    (codes ((subsetOf 6 []).map fun x => [(x, true)]))) 20000 128 = true := by
  decide +kernel

theorem bN : checkW (mkParamsW (2 * 9) (invArrW 9) (codes (relN 0 0 0))
      (codes ((subsetOf 9 six).map fun x => [(x, true)]))) 20000 24 = true ∧
    checkW (mkParamsW (2 * 9) (invArrW 9) (codes (relN 0 0 1))
      (codes ((subsetOf 9 six).map fun x => [(x, true)]))) 20000 24 = true ∧
    checkW (mkParamsW (2 * 9) (invArrW 9) (codes (relN 1 1 0))
      (codes ((subsetOf 9 six).map fun x => [(x, true)]))) 20000 24 = true ∧
    checkW (mkParamsW (2 * 9) (invArrW 9) (codes (relN 1 1 1))
      (codes ((subsetOf 9 six).map fun x => [(x, true)]))) 20000 24 = true := by
  decide +kernel

theorem bNr : checkW (mkParamsW (2 * (subsetOf 9 six).length) (invArrW (subsetOf 9 six).length)
      (codes (restrictWords (subsetOf 9 six) (relN 0 0 0)))
      (codes ((subsetOf (subsetOf 9 six).length []).map fun x => [(x, true)]))) 20000 128 =
      true := by
  decide +kernel

theorem bNeq :
    restrictWords (subsetOf 9 six) (relN 0 0 1) = restrictWords (subsetOf 9 six) (relN 0 0 0) ∧
    restrictWords (subsetOf 9 six) (relN 1 1 0) = restrictWords (subsetOf 9 six) (relN 0 0 0) ∧
    restrictWords (subsetOf 9 six) (relN 1 1 1) = restrictWords (subsetOf 9 six) (relN 0 0 0) := by
  decide +kernel

end CertificateChecks.KernelYoshQ

end
