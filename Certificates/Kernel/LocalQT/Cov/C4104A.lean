module

public import Certificates.Data.Kernel.LocalQT.CovT
public import Certificates.Kernel.LocalQT.Cov.D4104
public import Certificates.Kernel.Misc.Tits.Text
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

set_option maxRecDepth 400000

#kc_repo #kc_json CFSG.KD.LQT.C4104 "Certificates/Kernel/LocalQT/Cov/data/i4104.json" 75577 1193360069124907157
  (CGI : List Nat)

#kc_repo #kc_json CFSG.KD.LQT.C4104 "Certificates/Kernel/LocalQT/Cov/data/f4104.json" 40777 16720689177163288652
  (CFL : List Nat)

public section

namespace CFSG.KD.LQT.C4104

open CFSG.KC.LQT.Cov CFSG.KS CertificateChecks.KernelMisc.TitsText

@[expose] noncomputable def SG (j : Nat) : Nat := F (Nat.add 18 j)

@[expose] noncomputable def SGI (j : Nat) : Nat := CFSG.KC.LQT.Syl.getK CGI j 0

theorem kA : covTA 1755 11 13 SG SGI CTD P CFL 2048 = true := by quickRfl

end CFSG.KD.LQT.C4104

end
