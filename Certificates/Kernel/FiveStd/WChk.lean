module

public import Certificates.Kernel.FiveStd.Cover
public import Certificates.Kernel.FiveStd.ClsData
public import Certificates.Data.Kernel.FiveStdKW

public section

namespace CertificateChecks.FiveStd

open CFSG.KC.FiveStdK

set_option Elab.async false

@[expose] def WT : List (Nat × Nat × Nat × Nat) :=
  [(409405, 82001, 78901, 412572), (415680, 82001, 78926, 409408), (415680, 29501, 79090, 409440)]

theorem wc_cls : WT.all (fun e => Nat.beq (cjK e.1 (invK e.1) e.2.1) e.2.2.1 &&
    Nat.beq (cjK e.2.2.2 (invK e.2.2.2) (RP.getD 2 0)) e.2.2.1) = true := by
  decide +kernel

theorem wc_sub0 : cenSubK (p2K K1c 78901) (CB.getD 2 0) (CM.getD 2 0) 412572 (invK 412572) = true := by
  decide +kernel

theorem wc_sub1 : cenSubK (p2K K1c 78926) (CB.getD 2 0) (CM.getD 2 0) 409408 (invK 409408) = true := by
  decide +kernel

theorem wc_sub2 : cenSubK (p2K K1c 79090) (CB.getD 2 0) (CM.getD 2 0) 409440 (invK 409440) = true := by
  decide +kernel

theorem wc_sup0 : cenSupK (p2K K1c 78901) 78901 = true := by decide +kernel

theorem wc_sup1 : cenSupK (p2K K1c 78926) 78926 = true := by decide +kernel

theorem wc_sup2 : cenSupK (p2K K1c 79090) 79090 = true := by decide +kernel

end CertificateChecks.FiveStd

end
