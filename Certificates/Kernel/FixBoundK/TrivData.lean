module

public import Certificates.Data.Kernel.FixBoundK.Triv
public meta import CFSG.Certificates.Kernel.Common.JsonGz
public meta import CFSG.Certificates.Kernel.Common.Repo
public import CFSG.Certificates.Kernel.Common.JsonGz
public import CFSG.Certificates.Kernel.Common.Repo

set_option maxRecDepth 400000

public section

#kc_repo #kc_json_gz CertificateChecks.KernelFixBoundK.TrivD
  "Certificates/Kernel/FixBoundK/data/Triv.json.gz" 29620 14314692314045157703
  (reps : List Nat) (k1s : List (List Nat)) (ws : List (List (Nat × List Nat)))

end
