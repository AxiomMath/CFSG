module

public import CFSG.Sporadic.Schreier.RuData
meta import CFSG.Sporadic.Schreier.RuData
public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Data.Kernel.Misc.HexDrop
public import Certificates.Data.Kernel.SporSch.RuTreeK
import Certificates.Kernel.Misc.Perm.HexCmd
import Certificates.Kernel.Misc.Perm.HexDropCmd
import CFSG.Certificates.Kernel.Common.Harness
public import Mathlib.Data.Set.Card
public import Mathlib.GroupTheory.Perm.Basic
meta import Mathlib.Data.Set.Card
meta import Mathlib.GroupTheory.Perm.Basic

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSporSch.RuTreeC5 CFSG.Sporadic.RuSchreier.ruTreeText5
#kmisc_hexflat CertificateChecks.KernelSporSch.RuTreeC5 CFSG.Sporadic.RuSchreier.ruTreeText5 6 16 24 3692
#kmisc_hexflat_drop CertificateChecks.KernelSporSch.RuTreeC5.R CertificateChecks.KernelSporSch.RuTreeC5
  CFSG.Sporadic.RuSchreier.ruTreeText5 354432 6 5 24 1

namespace CertificateChecks.KernelSporSch.RuTreeC5

open CFSG.KC.Misc.HexFlat CFSG.KS.RuTree

theorem tail : isNilK (dropL 0 (dropL 354462 chars)) = true := by quickRfl

end CertificateChecks.KernelSporSch.RuTreeC5

end
