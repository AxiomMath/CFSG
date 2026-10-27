
module

public import Certificates.Kernel.UnitarySix.FischerBase

public import Certificates.Kernel.UnitarySix.Tables
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.FischerNativeInputs
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.HuntClassBraidInputs
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.NativeDataInputs
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.UnitarySix.Letters

public section

namespace CertificateChecks.KernelU6

open CFSG.KC.U6 CFSG.EvenSmallLie.UnitarySix

open CFSG.EvenSmallLie.UnitarySix.Hunt CFSG.Sporadic.Schreier CFSG.EvenSmallLie.UnitarySix
    CFSG.Fischer.Native in
open Certificates in
theorem cert3181 : 
      (braidOK tvTabs = true)
    ∧ (toTable j1 = tvTabs[(0 : Fin 693).val]!) := by
  rw [tvTabs_eq]
  exact sound3181 up_eq pos_eq letters_eq kTables kSwap aW_eq kJ1

end CertificateChecks.KernelU6

end
