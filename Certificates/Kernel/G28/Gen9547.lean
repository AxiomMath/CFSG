module

public import Certificates.Data.Kernel.G28.Defs
public import Certificates.Data.Item434G28
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace Certificates.Kernel.G28

open CFSG.KC.G28 CFSG.RankThree.PartTwo.Sec4.Item434G28

theorem gen9547 : genOKP (powP (wordP u9W) 3) (powP (wordP z9W) 3) genW.toList targetN.toList
    targetSteps.toList = true := by
  quickRfl

end Certificates.Kernel.G28

end
