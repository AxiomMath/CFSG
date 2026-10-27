module

public import Certificates.Data.Kernel.E6Syl3
public import Certificates.Kernel.E6Syl3.Data

public section

namespace CFSG.KD.E6Syl3

open CFSG.KC.E6Syl3

theorem ch214105_tups : qTups gw = qt := by decide +kernel

theorem ch214105_q : qCheckWith gw qt = true := by decide +kernel

theorem ch214105_kinds : kindsCheck qt kw = true := by decide +kernel

end CFSG.KD.E6Syl3
