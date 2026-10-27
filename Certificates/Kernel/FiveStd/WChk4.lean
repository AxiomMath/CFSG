module

public import Certificates.Data.Kernel.FiveStdKW4
public import Certificates.Kernel.FiveStd.Pl

public section

namespace CertificateChecks.FiveStd

open CFSG.KC.FiveStdK

set_option Elab.async false

@[expose] def WG (k : Nat) : Nat := if k = 3 then 29501 else 82001

theorem wr_rest : ∀ k < 4, gRestK (RK.getD k (0, 0)).1 (RK.getD k (0, 0)).2
    (TPc (if k = 3 then 2 else 0)).1 (TPc (if k = 3 then 2 else 0)).2 (WG k) = true := by
  decide +kernel

end CertificateChecks.FiveStd

end
