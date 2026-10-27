module

public import Certificates.Data.Kernel.Spor.MCount
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelSpor.M12Alt

#kc_repo #kc_json_gz CertificateChecks.KernelSpor.M12Alt
  "Certificates/Kernel/Sporadic/M12Alt/data/Data.json.gz" 33234 10931989320162976952
  (R0 : Nat) (Ri0 : Nat) (Bl0 : List Nat) (P0 : List Nat) (Lb0 : List Nat) (S0 : List Nat)
  (R1 : Nat) (Ri1 : Nat) (Bl1 : List Nat) (P1 : List Nat) (Lb1 : List Nat) (S1 : List Nat)
  (tA : List Nat) (tB : List Nat) (CS : List Nat)

@[expose] noncomputable def C0 : CFSG.KS.MEnum.ClassDatum := (0, 0, R0, Bl0, P0, Lb0, S0)

@[expose] noncomputable def C1 : CFSG.KS.MEnum.ClassDatum := (0, 0, R1, Bl1, P1, Lb1, S1)

@[expose] noncomputable def CL : List CFSG.KS.MEnum.ClassDatum :=
  [C0, C1]

@[expose] noncomputable def Rs : List (Nat × Nat) :=
  [(R0, Ri0), (R1, Ri1)]

@[expose] def W : List (List Int) :=
  [[1], [2], [-4, 3, 4], [-3, 5, 3], [-4, 5, 4], [-4, 6, 4], [-3, -4, 8, 4, 3], [-5, 4, 9, -4],
    [-5, -9, -3, -10, 6, -4], [-9, -6, -3, -11, -4, 3], [-8, -12, -10, -3, -12, -11, 3],
    [-8, -10, 11, -6, -8, -3, -12, 8, 4]]

end CertificateChecks.KernelSpor.M12Alt

end
