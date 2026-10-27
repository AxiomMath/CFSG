
module

public import Certificates.Data.Kernel.Parrott946.O3C
public import Certificates.Kernel.Parrott946.Cls
public import Certificates.Data.Kernel.OrbFind

set_option maxRecDepth 400000
set_option maxHeartbeats 0

public section

namespace CertificateChecks.Parrott946

open CFSG.KC.Enum CFSG.KS CFSG.KC.OrbFind CFSG.KC.Parrott946 CFSG.Certificates.Kernel.PkCV
  CFSG.RankThree.GF2n.Parrott CertificateChecks.KernelA45

theorem o3c_more :
    O3C.all (fun a => !(eq22C a (cOf o3b) (cOf o3b) a && eq22C a (cOf o3c) (cOf o3c) a) ||
      (Nat.beq a.1 (1 : CV 45).1 || Nat.beq a.1 (cOf sigma1).1 ||
        Nat.beq a.1 (cOf sigma1 * cOf sigma1).1)) = true ∧
    allN 6 (fun k => O3C.all fun a => O3C.any fun b =>
      eq22 45 6 (mask 6) (CZ.G k) a.1 b.1 (CZ.G k)) = true ∧
    O3C.all (fun a => Nat.beq a.1 (1 : CV 45).1 || Nat.beq a.1 (cOf sigma1).1 ||
      Nat.beq a.1 (cOf sigma1 * cOf sigma1).1 || memK 45 6 ps K12i.N K12i.T K12i.S a.1) = true := by
  decide +kernel

end CertificateChecks.Parrott946

end
