module

public import Certificates.Kernel.SporSch.Ru.CNU
public import Certificates.Kernel.Sporadic.RawGenSchG
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 400000

#kc_repo #kc_json_gz CertificateChecks.KernelSporSch.RuCW
  "Certificates/Kernel/SporSch/Ru/data/CW.json.gz" 185 15709947840979375273
  (W : List (List Nat))

#kc_repo #kc_json_gz CertificateChecks.KernelSporSch.RuNW
  "Certificates/Kernel/SporSch/Ru/data/NW.json.gz" 241 13135850225790472426
  (W : List (List Nat))

#ks_rawchain_sl2_gsub CertificateChecks.KernelSporSch.RuCS (0 1)
  CertificateChecks.KernelSporSch.RuCW.W

#ks_rawchain_sl2_gsub CertificateChecks.KernelSporSch.RuNS (0 1)
  CertificateChecks.KernelSporSch.RuNW.W

end
