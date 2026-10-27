module

public import Certificates.Data.Kernel.QP45W.Defs
public import Certificates.Kernel.ONanSmall.Data.P43P

public section

set_option maxRecDepth 100000

namespace Certificates.Kernel.QP45W

open CFSG.KC.QP45W CFSG.ComponentClassification.CatFactsSmall.PSp43

theorem ch21296_pin : pinB = true := by decide +kernel

theorem ch21296_pinY : pinYB = true := by decide +kernel

theorem ch21296_conjX : conjT (T 0) = true := by decide +kernel

theorem ch21296_conjY : conjT (fd6 yRow) = true := by decide +kernel

theorem ch21296_ord3 : ord3T = true := by decide +kernel

theorem ch21296_moves : movesT = true := by decide +kernel

theorem ch21296_cents : CFSG.KD.ONS.P43P.C.map List.length = [576, 96] := by decide +kernel

end Certificates.Kernel.QP45W
