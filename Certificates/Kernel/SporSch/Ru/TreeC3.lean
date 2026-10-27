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

#ks_chars CertificateChecks.KernelSporSch.RuTreeC3 CFSG.Sporadic.RuSchreier.ruTreeText3
#kmisc_hexflat CertificateChecks.KernelSporSch.RuTreeC3 CFSG.Sporadic.RuSchreier.ruTreeText3 6 151 24 883

namespace CertificateChecks.KernelSporSch.RuTreeC3

open CFSG.KC.Misc.HexFlat CFSG.KS.RuTree

theorem tail : isNilK (dropL 399999 (dropL 399999 chars)) = true := by quickRfl

end CertificateChecks.KernelSporSch.RuTreeC3

end
