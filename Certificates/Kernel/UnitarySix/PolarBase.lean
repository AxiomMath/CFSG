
module

public import Certificates.Kernel.UnitarySix.YamadaBase
public import CFSG.Certificates.Kernel.U6Sound3004
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.NativeDataBase
public import Certificates.Data.CFSGNative.Fischer.Polar
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.NativeDataInputs
import CFSG.Certificates.Kernel.Common.Harness

@[expose] public section

namespace CertificateChecks.KernelU6

open CFSG.KC.U6 CFSG.KC.S23 CFSG.EvenSmallLie.UnitarySix

@[expose] noncomputable def BT : Nat := nat_lit 1701104651956941558744342744614808807877287566024896180302432828274972965006734493439951932268909599907567191386366986152848589

theorem kBeta : bindA BT 10 42 beta = true := by quickRfl

theorem k3004 : check3004 U.UP U.POS U.LT BT aWK = true := by quickRfl

end CertificateChecks.KernelU6

end
