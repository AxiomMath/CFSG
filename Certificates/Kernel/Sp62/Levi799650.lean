module

public import Certificates.Data.Kernel.Sp62Levi
public import Certificates.Kernel.Sp62.Rec
public import Certificates.Data.Item434SmallTwoIII
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.Sp62

open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII

theorem levi3_ok :
    leviK REC (pk (zCode 0)) (pk (zCode 1)) (pk (zCode 2)) 6521 108 2 = true := by
  quickRfl

theorem levi4_ok :
    leviK REC (pk (zCode 0)) (pk (zCode 1)) (pk (zCode 2)) 6630 108 2 = true := by
  quickRfl

end CFSG.KD.Sp62

end
