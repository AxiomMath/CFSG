module

public import Certificates.Kernel.A45Cls.Cls
public import Certificates.Kernel.A45Cls.Grp3
public import Certificates.Kernel.OmegaCY.Grp
public import Certificates.Data.Kernel.A45Cls.Defs
public import Certificates.Data.Kernel.OmegaCY.Gens
public import Certificates.Data.Kernel.PermCent.CV
public import Certificates.Data.OmegaT0

set_option maxRecDepth 400000
set_option maxHeartbeats 0

public section

namespace CertificateChecks.KernelA45

open CFSG.KC.Enum CFSG.KS CFSG.KC.OrbFind CFSG.KC.A45Cls CFSG.KC.OmegaCY
  CFSG.Certificates.Kernel.PkCV

@[expose] noncomputable def cyZ : ℕ := (cOf (Certificates.OmegaT0.z0 ())).1

theorem cyBinds : bindWs 45 6 3 KA.G B0Z.G b0W 0 = true ∧ B0Z.T 0 = pidn 45 6 := by
  decide +kernel

theorem cyB0 : allN 4 (fun k => inPts 45 6 64 TZ.T (B0Z.G k)) = true ∧
    allN 4 (fun k => isIdK 45 6 (pcomp 45 6 (mask 6) (B0Z.G k) (B0Z.G k))) = true ∧
    allN 4 (fun a => allN 4 fun b => eq22 45 6 (mask 6) (B0Z.G a) (B0Z.G b) (B0Z.G b) (B0Z.G a)) =
      true := by
  decide +kernel

theorem cyCase0 : caseK 45 6 B0Z.T BZ0.T cyZ cyIx0 cyTab = true := by decide +kernel

theorem cyCase1 : caseK 45 6 B0Z.T BZ1.T cyZ cyIx1 cyTab = true := by decide +kernel

theorem cyCase2 : caseK 45 6 B0Z.T BZ2.T cyZ cyIx2 cyTab = true := by decide +kernel

theorem cySearch : srch3 cyTab = true := by decide +kernel

end CertificateChecks.KernelA45

end
