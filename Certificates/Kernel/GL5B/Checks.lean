module

public import Certificates.Data.Kernel.GL5B
public import Certificates.Kernel.GL5B.Data

public section

set_option maxRecDepth 200000
set_option Elab.async false

namespace CFSG.KC.GL5B

theorem ch778710_cuv : cuvOK = true := by decide +kernel

theorem ch778710_1 : sliceC chk1 = true := by decide +kernel

theorem ch778710_2 : sliceC chk2 = true := by decide +kernel

theorem ch778710_x0 : x0OK CFSG.KD.GL5B.X0 = true := by decide +kernel

theorem ch778710_cert : certsOK CFSG.KD.GL5B.X0 CFSG.KD.GL5B.B = true := by decide +kernel

end CFSG.KC.GL5B

end
