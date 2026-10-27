module

public import Certificates.Kernel.FiveStd.NChk
public import Certificates.Data.Kernel.FiveStdKW2

public section

namespace CertificateChecks.FiveStd

open CFSG.KC.FiveStdK

set_option Elab.async false

@[expose] def WV (k : Nat) : List Nat :=
  if k = 2 then [78876, 135443, 116567, 18815] else [78876, 79503, 80127, 80754]

theorem wn0 : nzK 78901 (HT 0) (WV 0) K1c = true := by decide +kernel

theorem wn1 : nzK 78926 (HT 0) (WV 0) K1c = true := by decide +kernel

theorem wn2 : nzK 79090 (HT 2) (WV 2) K1c = true := by decide +kernel

end CertificateChecks.FiveStd

end
