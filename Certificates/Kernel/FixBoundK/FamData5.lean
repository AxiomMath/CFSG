module

public import Certificates.Data.Kernel.FixBoundK.Fam
public meta import CFSG.Certificates.Kernel.Common.JsonGz
public meta import CFSG.Certificates.Kernel.Common.Repo
public import CFSG.Certificates.Kernel.Common.JsonGz
public import CFSG.Certificates.Kernel.Common.Repo

set_option maxRecDepth 400000

public section

open CFSG.KC.FixBoundK in
#kc_repo #kc_json_gz CertificateChecks.KernelFixBoundK.FamData5
  "Certificates/Kernel/FixBoundK/data/Fam5.json.gz" 117716 16330182415854323244
  (fc : List (List FamC))

end
