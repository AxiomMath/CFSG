module

public import Certificates.Data.Kernel.TabBThreeL1Checks

public section

namespace CFSG.HardMathSupport.Dickson.I271.TabBThreeL1

open CFSG.Monster.B.Classical.E6Adjoint

theorem ch17575_levMask : levMaskOK levMask = true := by decide +kernel

theorem ch17575_lev_theta : lev 76 = 4 ∧ lev 77 = 0 := by decide +kernel

theorem ch17575_graded_0 : gradedRows brMask fbit 0 26 = true := by decide +kernel

theorem ch17575_graded_1 : gradedRows brMask fbit 26 26 = true := by decide +kernel

theorem ch17575_graded_2 : gradedRows brMask fbit 52 26 = true := by decide +kernel

theorem ch17575_adSq : adSqTestOK testB = true := by decide +kernel

theorem ch17575_piv_theta : pivOK brMask ch17575PivTheta = true ∧
    certMask ch17575PivTheta = levMask 1 ∧ ch17575PivTheta.all (fun p => decide (p.1 < 78) &&
      p.2.1 == 76 && decide (p.2.2 < 78) && lev p.2.2 == 3) = true := by
  decide +kernel

theorem ch17575_piv_test : pivOK brMask ch17575PivTest = true ∧
    certMask ch17575PivTest = levMask 1 ∧ ch17575PivTest.all (fun p => decide (p.1 < 78) &&
      testB.contains p.2.1 && decide (p.2.2 < 78)) = true := by
  decide +kernel

end CFSG.HardMathSupport.Dickson.I271.TabBThreeL1
