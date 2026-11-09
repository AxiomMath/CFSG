module

public import Certificates.Data.Kernel.FixBoundK.Fix
public meta import CFSG.Certificates.Kernel.Common.JsonGz
public meta import CFSG.Certificates.Kernel.Common.Repo
public import CFSG.Certificates.Kernel.Common.JsonGz
public import CFSG.Certificates.Kernel.Common.Repo

set_option maxRecDepth 400000

public section

open CFSG.KC.FixBoundK in
#kc_repo #kc_json CertificateChecks.KernelFixBoundK.FixData
  "Certificates/Kernel/FixBoundK/data/Fix.json" 175436 17080779123319371480
  (fx : List (List FixD))

end
