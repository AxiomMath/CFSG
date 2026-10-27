module

import Certificates.Kernel.MonsterB.U20.Checks
import CFSG.Certificates.Kernel.Common.Harness

namespace CFSG.KC.U20.Neg

open CFSG.Monster.B.TwoA.Unitary

example : (!gensK (CFSG.KD.U20.G.c0.set 3 0) u20Gens.toList) = true := by quickRfl

example : (!gensK CFSG.KD.U20.G.c0.tail u20Gens.toList.tail.tail) = true := by quickRfl

example : (!flatK (CFSG.KD.U20.F.c0.set 7 (CFSG.KD.U20.F.c0[8]!)) recList) = true := by quickRfl

example : (!flatK (CFSG.KD.U20.F.c0.set 0 (2 ^ 400 + 1)) recList) = true := by quickRfl

example : (!wordsK CFSG.KD.U20.G.c0 CFSG.KD.U20.F.c0 (u20Words.toList.set 5 [1])) = true := by
  quickRfl

example : (!wordsK CFSG.KD.U20.G.c0 CFSG.KD.U20.F.c0 (u20Words.toList.set 0 [17])) = true := by
  quickRfl

example : (!invK CFSG.KD.U20.F.c0 (CFSG.KD.U20.D.c0.set 9 (CFSG.KD.U20.D.c0[10]!))) = true := by
  quickRfl

example : (!invK CFSG.KD.U20.F.c0 CFSG.KD.U20.D.c0.dropLast) = true := by quickRfl

end CFSG.KC.U20.Neg
