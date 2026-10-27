
module

public import CFSG.Certificates.Kernel.U6Gen
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.FischerNativeInputs

public section

namespace CertificateChecks.KernelU6

open CFSG.KC.U6 CFSG.EvenSmallLie.UnitarySix CFSG.F4.Native CFSG.Fischer.Native

theorem letterT_eq (k : ℕ) : letterT k = tvTableG uPts uPos tvGens[((k : ℤ) + 1).natAbs - 1]! := by
  unfold letterT CFSG.Sporadic.Fi22.Native.t46Gen tvTable tvTableG
  rfl

theorem tvTabs_eq : tvTabs = tvTabsG uPts uPos := by
  unfold tvTabs tvTabsG tvTable tvTableG
  rfl

theorem swapOK_eq : Fischer.swapOK = swapOKG uPts uPos := by
  unfold Fischer.swapOK swapOKG
  rw [tvTabs_eq]

theorem fixOK_eq : Fischer.fixOK = fixOKG fixA uPts uPos := by
  unfold Fischer.fixOK fixOKG
  rw [tvTabs_eq]

end CertificateChecks.KernelU6

end
