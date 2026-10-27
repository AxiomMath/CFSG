module

public import Certificates.Kernel.FiveStd.ClsData
public import Certificates.Data.Kernel.FiveStdKDiag
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.FiveStd

open CFSG.KC.FiveStdK

set_option Elab.async false

@[expose] def A0 : Nat :=
  479866278907962577334562329861545800760302650108523072585390370482805007765520755636965155739526117541274048320803933818307641393206794083259744537550

@[expose] def A1 : Nat :=
  479725800223198485448674894180046899535548492761496346682948269862521355865296658342174957483284884056299734463191794454470190683180263592215507389425

theorem diag0 : dgOK A0 25 (CB.getD 0 0) 100 (RP.getD 0 0) (IV.getD 0 0) = true := by quickRfl

theorem diag1 : dgOK A1 25 (CB.getD 1 0) 100 (RP.getD 1 0) (IV.getD 1 0) = true := by quickRfl

theorem diag2 : noInvK (CB.getD 2 0) 600 = true := by quickRfl

end CertificateChecks.FiveStd

end
