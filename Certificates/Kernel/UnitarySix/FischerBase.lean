
module

public import Certificates.Kernel.UnitarySix.Tables
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.FischerNativeInputs
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.HuntClassBraidInputs
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.NativeDataInputs
import CFSG.Certificates.Kernel.Common.Harness

@[expose] public section

namespace CertificateChecks.KernelU6

open CFSG.KC.U6 CFSG.EvenSmallLie.UnitarySix

theorem kFix : fixAK T.R (maskL fixA) = true := by quickRfl

theorem kJ1 : j1KC U.LT T.R aWK = true := by quickRfl

theorem fixA_lt : ∀ x ∈ fixA, x < 693 := by decide

open CFSG.EvenSmallLie.UnitarySix.Fischer in
theorem cert3145 : (swapOK = true)
    ∧ (fixOK = true) := by
  rw [swapOK_eq, fixOK_eq]
  exact sound3145 up_eq pos_eq kTables kSwap fixA_lt kFix

end CertificateChecks.KernelU6

end
