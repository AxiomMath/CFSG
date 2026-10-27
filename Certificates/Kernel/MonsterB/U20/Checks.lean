module

public import Certificates.Data.Kernel.U20K
public import Certificates.Kernel.MonsterB.U20.Data
public import CFSG.Monster.B.TwoA.Unitary.TwentyData
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KC.U20

open CFSG.Monster.B.TwoA.Unitary

@[expose] def recList : List (Array Nat) :=
  u20Rows0.toList ++ u20Rows1.toList ++ u20Rows2.toList ++ u20Rows3.toList ++ u20Rows4.toList ++
    u20Rows5.toList ++ u20Rows6.toList ++ u20Rows7.toList

theorem gens_ok : gensK CFSG.KD.U20.G.c0 u20Gens.toList = true := by quickRfl

theorem flat_ok : flatK CFSG.KD.U20.F.c0 recList = true := by quickRfl

theorem words_ok : wordsK CFSG.KD.U20.G.c0 CFSG.KD.U20.F.c0 u20Words.toList = true := by quickRfl

theorem inv_ok : invK CFSG.KD.U20.F.c0 CFSG.KD.U20.D.c0 = true := by quickRfl

end CFSG.KC.U20

end
