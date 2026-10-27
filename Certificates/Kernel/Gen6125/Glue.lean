module

public import Certificates.Kernel.Gen6125.Check
public import Certificates.Kernel.BalanceSC.Glue
public import CFSG.Certificates.Kernel.Gen6125Sound

public section

open CFSG.KC.Gen6125.Sound
open CFSG.OddStandard.Solomon75.AhatData (GenGood P0)

namespace CFSG.KD.G6125n8

theorem genGood : GenGood 8 (P0 8) true :=
  genGood_of_checks (by norm_num) (by norm_num) CFSG.KD.BalSC8.checks
    ⟨swG, lenG, bindG, ats, word, pairs⟩

end CFSG.KD.G6125n8

namespace CFSG.KD.G6125n11

theorem genGood : GenGood 11 (P0 11) false :=
  genGood_of_checks (by norm_num) (by norm_num) CFSG.KD.BalSC11.checks
    ⟨swG, lenG, bindG, ats, word, pairs⟩

end CFSG.KD.G6125n11

end
