module

public import Certificates.Data.Kernel.FixBoundK.Pairs
public meta import CFSG.Certificates.Kernel.Common.JsonGz
public meta import CFSG.Certificates.Kernel.Common.Repo
public import CFSG.Certificates.Kernel.Common.JsonGz
public import CFSG.Certificates.Kernel.Common.Repo

set_option maxRecDepth 400000

public section

open CFSG.KC.FixBoundK.Pair in
#kc_repo #kc_json CertificateChecks.KernelFixBoundK.PairD
  "Certificates/Kernel/FixBoundK/data/Pair.json" 1549567 18332793019749528568
  (lo : Nat) (src : List (Nat × List Item))

end
