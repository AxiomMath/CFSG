module

public import Certificates.Data.Kernel.KS228Sp62K
public import Certificates.Kernel.KS228Sp62.Rec
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.Sp62

theorem c12646tabK : (Nat.beq (recX R12646 17 0) ONE &&
    tableK R12646 (rmulSt (at2 R12646 0)) 17 30 1 1 1) = true := by quickRfl

theorem c12646tabX : (Nat.beq (recX R12646 48 0) ONE &&
    tableK R12646 (rmulSt (at2 R12646 2)) 48 2160 34 68 34) = true := by quickRfl

theorem c12646tabN : (Nat.beq (recX R12646 2209 0) ONE &&
    tableK R12646 (rmulSt (at2 R12646 4)) 2209 60 1 2 1) = true := by quickRfl

theorem c12646orbX : (Nat.beq (recX R12646 2270 0) (R12646 11) &&
    tableK R12646 (conjSt (at2 R12646 6) (at2 R12646 8)) 2270 672 11 21 11) = true := by quickRfl

theorem c12646cube : cube12646K R12646 17 30 1 = true := by quickRfl

theorem c12646norm : norm12646K R12646 48 2209 60 2160 34 = true := by quickRfl

end CFSG.KD.Sp62

end
