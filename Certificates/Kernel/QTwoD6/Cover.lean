module

public import Certificates.Data.Kernel.QTwoD6K2
public import Certificates.Kernel.QTwoD6.Forms0
public import Certificates.Kernel.QTwoD6.Forms1
public import Certificates.Kernel.QTwoD6.Forms2
public import Certificates.Kernel.QTwoD6.FormsT

public section

open CFSG.KC.QTwoD6K CFSG.KD.QTwoD6

namespace CFSG.KD.QTwoD6

theorem qTwoD6_cov0 : covK 16128 forms0 1005 = true := by
  decide +kernel

theorem qTwoD6_cov1 : covK 16129 forms1 999 = true := by
  decide +kernel

theorem qTwoD6_cov2 : covK 127 forms2 999 = true := by
  decide +kernel

theorem qTwoD6_covT : covT formsT 1639 = true := by
  decide +kernel

theorem qTwoD6_sigInv : sigInvK = true := by
  decide +kernel

end CFSG.KD.QTwoD6

end
