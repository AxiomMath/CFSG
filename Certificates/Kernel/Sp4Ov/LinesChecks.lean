module

public import Certificates.Kernel.Sp4Ov.Data
public import Certificates.Kernel.Sp4Ov.LinesData
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

public section

namespace CFSG.KD.Sp4Ov

theorem ch7138_lines : linesOK D.lines = true := by quickRfl

theorem ch7138_line5 : lineK D.spec D.ov5 D.lines = true := by quickRfl

theorem ch7138_line9 : lineK D.spec D.ov9 D.lines = true := by quickRfl

theorem ch7138_quad5 : quadK D.spec D.ov5 D.lines = true := by quickRfl

theorem ch7138_quad9 : quadK D.spec D.ov9 D.lines = true := by quickRfl

end CFSG.KD.Sp4Ov

end
