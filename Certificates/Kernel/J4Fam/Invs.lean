module

public import Certificates.Kernel.J4Fam.Data
public import Certificates.Data.Kernel.J4Fam
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Common.Lce

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Fam

open CFSG.KC.J4Fam
open CFSG.EvenSporadicStandard.J4Std.DataLocal (invs)
open CFSG.KC (notB)

theorem invs_ok : (invs == INV) = true := by quickRfl

theorem invsOK_ok : invsOK INV = true := by quickRfl

theorem lens_ok : (CML.length == 191 && PTP.length == 191 && PTL.length == 191) = true := by
  quickRfl

theorem pp_ok : ppOK INV PP = true := by quickRfl

theorem tt_ok : ttOK INV TT = true := by quickRfl

theorem wall_ok : wallOK INV WALL = true := by quickRfl

theorem pl_ok : plOK PL = true := by quickRfl

end CertificateChecks.KernelJ4Fam
