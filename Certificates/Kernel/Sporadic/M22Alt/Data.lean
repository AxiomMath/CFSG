module

public import Certificates.Data.Kernel.Spor.MCount
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelSpor.M22Alt

#kc_repo #kc_json_gz CertificateChecks.KernelSpor.M22Alt
  "Certificates/Kernel/Sporadic/M22Alt/data/Data.json.gz" 86384 6266398317398826742
  (R0 : Nat) (Ri0 : Nat) (Bl0 : List Nat) (P0 : List Nat) (Lb0 : List Nat) (S0 : List Nat)
  (tA : List Nat) (tB : List Nat) (CS : List Nat)

@[expose] noncomputable def C0 : CFSG.KS.MEnum.ClassDatum := (0, 0, R0, Bl0, P0, Lb0, S0)

@[expose] noncomputable def CL : List CFSG.KS.MEnum.ClassDatum :=
  [C0]

@[expose] noncomputable def Rs : List (Nat × Nat) :=
  [(R0, Ri0)]

@[expose] def W : List (List Int) :=
  [[1], [2], [4, 3, -4], [-3, -5, 3, 5, 3], [-4, -6, 3, 4, 3], [-4, -4, 7, 4],
    [8, -3, -4, -8, 3], [-7, -8, -3, -9, 4, 4], [-5, -9, -3, -9, 7, 4],
    [-10, 9, -8, -11, -3, -10, 11, 4], [-10, -12, -7, -12, -3, -10, 11, 4],
    [-9, -9, -5, -10, -3, -13, 9, 4], [-12, 14, -11, -7, -12, -3, 14, 10, 4]]

end CertificateChecks.KernelSpor.M22Alt

end
