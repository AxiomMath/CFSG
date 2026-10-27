module

public import CFSG.Sporadic.Schreier.RuData
meta import CFSG.Sporadic.Schreier.RuData
public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Data.Kernel.Misc.HexDrop
public import Certificates.Data.Kernel.SporSch.RuTreeK
import Certificates.Kernel.Misc.Perm.HexCmd
import CFSG.Certificates.Kernel.Common.Harness
public import Mathlib.Data.Set.Card
public import Mathlib.GroupTheory.Perm.Basic
meta import Mathlib.Data.Set.Card
meta import Mathlib.GroupTheory.Perm.Basic

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSporSch.RuTreeC0 CFSG.Sporadic.RuSchreier.ruTreeText0
#kmisc_hexflat CertificateChecks.KernelSporSch.RuTreeC0 CFSG.Sporadic.RuSchreier.ruTreeText0 6 91 24 15

namespace CertificateChecks.KernelSporSch.RuTreeC0

open CFSG.KC.Misc.HexFlat CFSG.KS.RuTree

theorem tail : isNilK (dropL 0 (dropL 8190 chars)) = true := by quickRfl

end CertificateChecks.KernelSporSch.RuTreeC0

end
