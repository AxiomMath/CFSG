module

public import Certificates.Data.Kernel.CTIBqBind
public import Certificates.Kernel.TwoE6.CTIBqData
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelTwoE6

open CFSG.KC.CTIBq

theorem kBinds : bindsK GR A6 A8 Q1 Q2 = true := by quickRfl

theorem kBindsN : bindsL GR CFSG.Monster.B.Bin.gramRows A6 (CFSG.Monster.B.CTIB.Native.liftImgsN 6)
    A8 (CFSG.Monster.B.CTIB.Native.liftImgsN 8) Q1 CFSG.Monster.B.Bin.quotRows1 Q2
    CFSG.Monster.B.Bin.quotRows2 = true := by
  quickRfl

theorem kFrame : frameCheck GR = true := by quickRfl

theorem kOdd1 : oddCheck GR Q1 Q2 3711077 3015616 1 6 y2aK 8 3 y2bK 4 3 37440 4112 = true := by
  quickRfl

theorem kOdd2 : oddCheck GR Q1 Q2 3711077 3015616 1 7 cy2aK 4 3 cy2bK 4 3 2096 4112 = true := by
  quickRfl

theorem kOdd3 : oddCheck GR Q1 Q2 3711077 3015616 32 7 y3aK 1 3 y3bK 2 3 102610 16 = true := by
  quickRfl

theorem k3128 : fgK GR A6 = true := by quickRfl

theorem k3140 : d8K GR A8 = true := by quickRfl

end CertificateChecks.KernelTwoE6

end
