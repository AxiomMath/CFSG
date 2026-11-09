module

public import CFSG.Sporadic.Schreier.RuData
meta import CFSG.Sporadic.Schreier.RuData
public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Data.Kernel.Misc.HexDrop
public import Certificates.Data.Kernel.SporSch.RuTreeK
import Certificates.Kernel.Misc.Perm.HexTabCmd
import CFSG.Certificates.Kernel.Common.Harness
public import Mathlib.Data.Set.Card
public import Mathlib.GroupTheory.Perm.Basic
meta import Mathlib.Data.Set.Card
meta import Mathlib.GroupTheory.Perm.Basic

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSporSch.RuTreeC3 CFSG.Sporadic.RuSchreier.ruTreeText3
#kmisc_hexflat_tab CertificateChecks.KernelSporSch.RuTreeC3 CFSG.Sporadic.RuSchreier.ruTreeText3
  6 151 24 883

namespace CertificateChecks.KernelSporSch.RuTreeC3

open CFSG.KC.Misc.HexFlat CFSG.KS.RuTree

theorem p0 :
    CFSG.KC.Misc.HexFlat.run 6 151 24 111 F (dropL 0 (dropL 0 chars)) 0 0 0 0 0 =
      true := by quickRfl
theorem p1 :
    CFSG.KC.Misc.HexFlat.run 6 151 24 222 F (dropL 100566 (dropL 0 chars)) 111 0 0 0 0 =
      true := by quickRfl
theorem p2 :
    CFSG.KC.Misc.HexFlat.run 6 151 24 333 F (dropL 201132 (dropL 0 chars)) 222 0 0 0 0 =
      true := by quickRfl
theorem p3 :
    CFSG.KC.Misc.HexFlat.run 6 151 24 444 F (dropL 301698 (dropL 0 chars)) 333 0 0 0 0 =
      true := by quickRfl
theorem p4 :
    CFSG.KC.Misc.HexFlat.run 6 151 24 555 F (dropL 2265 (dropL 399999 chars)) 444 0 0 0 0 =
      true := by quickRfl
theorem p5 :
    CFSG.KC.Misc.HexFlat.run 6 151 24 666 F (dropL 102831 (dropL 399999 chars)) 555 0 0 0 0 =
      true := by quickRfl
theorem p6 :
    CFSG.KC.Misc.HexFlat.run 6 151 24 777 F (dropL 203397 (dropL 399999 chars)) 666 0 0 0 0 =
      true := by quickRfl
theorem p7 :
    CFSG.KC.Misc.HexFlat.run 6 151 24 883 F (dropL 303963 (dropL 399999 chars)) 777 0 0 0 0 =
      true := by quickRfl

theorem tail : isNilK (dropL 399999 (dropL 399999 chars)) = true := by quickRfl

end CertificateChecks.KernelSporSch.RuTreeC3

end
