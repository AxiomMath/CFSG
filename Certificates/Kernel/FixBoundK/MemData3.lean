module

public import Certificates.Data.Kernel.FixBoundK.Member
public meta import CFSG.Certificates.Kernel.Common.JsonGz
public meta import CFSG.Certificates.Kernel.Common.Repo
public import CFSG.Certificates.Kernel.Common.JsonGz
public import CFSG.Certificates.Kernel.Common.Repo

set_option maxRecDepth 400000

public section

open CFSG.KC.FixBoundK in
#kc_repo #kc_json_gz CertificateChecks.KernelFixBoundK.Mem3
  "Certificates/Kernel/FixBoundK/data/Mem3.json.gz" 297930 11071079416233350149
  (lo : Nat) (gens : List (List (List Nat))) (reps : List Rep) (ch : List (Nat × List Mem))

end
