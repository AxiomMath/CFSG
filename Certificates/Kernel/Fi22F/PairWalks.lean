module

public import Certificates.Data.Kernel.Fi22F.Pairs
public import CFSG.Certificates.Kernel.Fi22.Bound.Data.P_Sel
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Harness

public section

#kc_repo #kc_json_gz CFSG.KD.FiFP "Certificates/Kernel/Fi22F/data/pairs.json.gz" 60461 14580433577841287009 (R : List Nat)

namespace CertificateChecks.KernelFi22F

open CFSG.KC.Fi22F.Walks CFSG.Sporadic.Presentation.Fi22Exact

theorem pw_ok : pwOK CFSG.KD.Fi22BP.blk (nat_lit 82571) allPairs CFSG.KD.FiFP.R 0 = true := by quickRfl

theorem neg_pw_shift : CFSG.KC.notB (pwOK CFSG.KD.Fi22BP.blk (nat_lit 82571) allPairs CFSG.KD.FiFP.R 1) = true := by
  quickRfl

end CertificateChecks.KernelFi22F

end
