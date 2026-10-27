module

public import Certificates.Data.Kernel.QP45W.W2
public import Certificates.Kernel.ONanSmall.P43P

public section

set_option maxRecDepth 100000

namespace Certificates.Kernel.QP45W

open CFSG.KC.QP45W Certificates.Kernel.ONanSmall

theorem ch21297_w2 : P43P.cents.all w2C = true := by decide +kernel

end Certificates.Kernel.QP45W
