module

public import Certificates.Kernel.J4M2.C7951Defs
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
public import Certificates.Kernel.J4M2.C4200

public section

set_option maxRecDepth 400000

#kc_repo #kc_json_gz CertificateChecks.KernelJ4M2 "Certificates/Kernel/J4M2/data/w7951.json.gz" 3570
  16134405471508997213
  (pt77W : List (Nat × Nat × Nat × Nat))

namespace CertificateChecks.KernelJ4M2

open CFSG.KC.J4Q CFSG.KD.J4Q

theorem pt77_chk : pt77K (tOf gL) pt77W = true := by decide +kernel

theorem pt77_neg : strictB (getN one (tOf gL) 1) (fun t =>
    andB (notB (pt77One t (0, 0, 0, 386848664545475321958349402390609)))
      (andB (notB (pt77One t (0, 1, 0, 386848664545475321958349402390608)))
        (notB (pt77One t (7, 0, 0, 386848664545475321958349402390608))))) = true := by
  decide +kernel

end CertificateChecks.KernelJ4M2

end
