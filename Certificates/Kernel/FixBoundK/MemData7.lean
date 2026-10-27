module

public import Certificates.Data.Kernel.FixBoundK.Member
public meta import CFSG.Certificates.Kernel.Common.JsonGz
public meta import CFSG.Certificates.Kernel.Common.Repo
public import CFSG.Certificates.Kernel.Common.JsonGz
public import CFSG.Certificates.Kernel.Common.Repo

set_option maxRecDepth 400000

public section

open CFSG.KC.FixBoundK in
#kc_repo #kc_json_gz CertificateChecks.KernelFixBoundK.Mem7
  "Certificates/Kernel/FixBoundK/data/Mem7.json.gz" 317886 1500481511653762553
  (lo : Nat) (gens : List (List (List Nat))) (reps : List Rep) (ch : List (Nat × List Mem))

end
