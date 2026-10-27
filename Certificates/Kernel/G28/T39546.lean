module

public import Certificates.Data.Kernel.G28.T3
public import Certificates.Data.Item434G28
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace Certificates.Kernel.G28

open CFSG.KC.G28 CFSG.RankThree.PartTwo.Sec4.Item434G28

@[expose] def conjGen9546 : List ℕ :=
  [81, 9, 81, 2, 81, 62, 81, 152, 81, 122, 81, 103, 81, 182, 81, 92, 81, 212, 81, 32, 81, 28, 81,
    199, 81, 127, 81, 79, 81, 151, 81, 223, 81, 107, 81, 17, 81, 110, 81, 200, 81, 170, 81, 47, 81,
    112, 81, 211, 81, 40, 81, 124, 81, 176, 81, 52]

theorem t39546 : t3ChkP (wordP u9W) (wordP z9W) (wordP omegaW) conjW.toList conjGen9546 = true := by
  quickRfl

end Certificates.Kernel.G28

end
