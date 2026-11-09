module

public import Certificates.Data.Kernel.GL5B
public import Certificates.Kernel.GL5B.Data

public section

set_option maxRecDepth 200000
set_option Elab.async false

namespace CFSG.KC.GL5B

theorem ch778710_cov0 :
    covW CFSG.KD.GL5B.X0 CFSG.KD.GL5B.B CFSG.KD.GL5B.LW 0 1 CFSG.KD.GL5B.S0 = true := by
  decide +kernel

theorem ch778710_cov1 :
    covW CFSG.KD.GL5B.X0 CFSG.KD.GL5B.B CFSG.KD.GL5B.LW 1 4 CFSG.KD.GL5B.S1 = true := by
  decide +kernel

theorem ch778710_cov2 :
    covW CFSG.KD.GL5B.X0 CFSG.KD.GL5B.B CFSG.KD.GL5B.LW 2 6 CFSG.KD.GL5B.S2 = true := by
  decide +kernel

theorem ch778710_cov3 :
    covW CFSG.KD.GL5B.X0 CFSG.KD.GL5B.B CFSG.KD.GL5B.LW 3 20 CFSG.KD.GL5B.S3 = true := by
  decide +kernel

theorem ch778710_red : redOK CFSG.KD.GL5B.X0 = true := by decide +kernel

end CFSG.KC.GL5B

end
