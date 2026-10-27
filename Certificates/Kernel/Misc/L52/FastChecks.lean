module

public import Certificates.Data.Kernel.Misc.L52Fast

public section

namespace CFSG.KD.L52

set_option maxRecDepth 100000

theorem l52fY1 : l52CheckYFN (l52YN 1) = true := by decide +kernel
theorem l52fY2 : l52CheckYFN (l52YN 2) = true := by decide +kernel
theorem l52fY3 : l52CheckYFN (l52YN 3) = true := by decide +kernel

theorem l52fO1 : mEqN (mPowN (l52YN 1) 7) mIdN = true := by decide +kernel
theorem l52fO2 : mEqN (mPowN (l52YN 2) 7) mIdN = true := by decide +kernel
theorem l52fO3 : mEqN (mPowN (l52YN 3) 7) mIdN = true := by decide +kernel

theorem l52CheckFN_ok : l52CheckFN = true := by
  simp only [l52CheckFN, List.all_cons, List.all_nil, l52fO1, l52fO2, l52fO3, l52fY1, l52fY2,
    l52fY3, Bool.and_true]

end CFSG.KD.L52

end
