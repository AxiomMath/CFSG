
module

public import Certificates.Kernel.UnitarySix.PolarBase

public import Certificates.Kernel.UnitarySix.Yamada
public import CFSG.Certificates.Kernel.U6Sound3004
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.NativeData
public import Certificates.Data.CFSGNative.Fischer.Polar
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.NativeDataInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelU6

open CFSG.KC.U6 CFSG.KC.S23 CFSG.EvenSmallLie.UnitarySix

open CFSG.EvenSmallLie.UnitarySix CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Schreier
    CFSG.Fischer.Native in
open Certificates in
theorem cert3004 : 
      aGens.all (fun g => (List.range 21).any fun i =>
        tblEq 693 (toTable g) tvTabs[beta[i]!]!) = true ∧
      tblEq 693 (toTable j1) tvTabs[beta[5]!]! = true := by
  rw [tvTabs_eq]
  exact sound3004 letters_eq up_eq pos_eq aW_eq kBeta (by decide) (by decide) (by decide) k3004

end CertificateChecks.KernelU6

end
