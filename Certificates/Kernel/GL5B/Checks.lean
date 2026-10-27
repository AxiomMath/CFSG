module

public import Certificates.Data.Kernel.GL5B
public import Certificates.Kernel.GL5B.Data

public section

set_option maxRecDepth 200000

namespace CFSG.KC.GL5B

theorem ch778710_1 : allS chk1 = true := by decide +kernel

theorem ch778710_2 : allS chk2 = true := by decide +kernel

theorem ch778710_cov : coverOK CFSG.KD.GL5B.B CFSG.KD.GL5B.RO CFSG.KD.GL5B.LO = true := by
  decide +kernel

theorem ch778710_x0 : x0OK CFSG.KD.GL5B.X0 = true := by decide +kernel

theorem ch778710_cert : certsOK CFSG.KD.GL5B.X0 CFSG.KD.GL5B.B = true := by decide +kernel

end CFSG.KC.GL5B

end
