module

public import Certificates.Kernel.KGC31M24.Defs
public import Certificates.Data.Kernel.KGC31PB

public section

namespace CertificateChecks.KernelKGC31M24

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.KGC31P
open CFSG.Quasithin.KGC31.M24 CertificateChecks.KernelSporSch

@[expose] noncomputable def sP : List Nat := sW.map pw
@[expose] noncomputable def etP : List Nat := etW.map pw
@[expose] noncomputable def b0P : Nat := pw (oW.headD [])
@[expose] noncomputable def b1P : Nat := pw (u6W.headD [])
@[expose] noncomputable def d4P : Nat := pw d4W
@[expose] noncomputable def d6P : Nat := pw d6W
@[expose] noncomputable def y5P : Nat := pw y5W
@[expose] noncomputable def y7P : Nat := pw y7W
@[expose] noncomputable def qtP : Nat := pw qtW
@[expose] noncomputable def njP : List Nat := njW.map pw
@[expose] noncomputable def mjP : List Nat := mjW.map pw
@[expose] noncomputable def kqP : List Nat := kqGenW.map pw
@[expose] noncomputable def rsP : List Nat := r2CosetW.map pw

@[expose] noncomputable def wcj (g y : List Int) : Nat := pcj 24 5 (pw g) (pinv 24 5 (pw g)) (pw y)

@[expose] noncomputable def cb0P : List Nat :=
  pfilterProducts 24 5 (fun _ => true) (trPL 24 5 M24C2.LR M24C2.TR 4) (pidn 24 5) []

@[expose] noncomputable def cb1P : List Nat :=
  pfilterProducts 24 5 (fun _ => true) (trPL 24 5 M24C1.LR M24C1.TR 3) (pidn 24 5) []

end CertificateChecks.KernelKGC31M24

end
