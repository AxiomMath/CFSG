module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd
meta import Certificates.Data.W4RowHeE25
import CFSG.Assembly.LowTwoRankDefs

namespace CFSG.KD.W4E.HeE25

open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row in
meta def heWM : Array (Array Nat) :=
  #[heE25WX, heE25WY, heE25WM1, heE25WM2, heE25WM3, heE25WM4, heE25WM5, heE25WH0, heE25WH1,
    heE25WHU].flatMap fun wd => let p := heWordP wd; #[p.1, p.2]

end CFSG.KD.W4E.HeE25

public section

#kmisc_packarrs CFSG.KD.W4E.HeE25.W CFSG.KD.W4E.HeE25.heWM 14

end
