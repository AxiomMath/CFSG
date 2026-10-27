
module

public import Certificates.Kernel.UnitarySix.YamadaBase

public import Certificates.Kernel.UnitarySix.Letters
public import CFSG.Certificates.Kernel.U6Sound3000
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaNativeData
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.NativeDataInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelU6

open CFSG.KC.U6 CFSG.EvenSmallLie.UnitarySix CFSG.EvenSmallLie.UnitarySix.Yamada

open Certificates in
open CFSG.EvenSmallLie.UnitarySix.Yamada in
theorem cert3000 : 
      (commCheck = true)
    ∧ (transCheck = true) :=
  sound3000 letters_eq aW_eq kW_eq oW_eq sW_eq (by decide) (by decide) k3000

end CertificateChecks.KernelU6

end
