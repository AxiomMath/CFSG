module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Data.Kernel.Spor.Prim
public import CFSG.Certificates.Kernel.Spor.Loops
public import CFSG.Sporadic.SmallOddCore.HSData
public import CFSG.Sporadic.Schreier.PairHSCertInputs
meta import CFSG.Sporadic.SmallOddCore.HSData
meta import CFSG.Sporadic.Schreier.PairHSCertInputs
import CFSG.Certificates.Kernel.Common.Harness

namespace CFSG.KD.LQT.C4126

meta def hcInvM : Array (Array Nat) :=
  (List.range 43).toArray.map fun k => CFSG.Monster.B.Co2.Native.invCand 3850
    (CFSG.Sporadic.SmallOddCore.Native.natArr (CFSG.Sporadic.SmallOddCore.hsCentTbl k))

meta def hsInvM : Array (Array Nat) :=
  #[CFSG.Monster.B.Co2.Native.invCand 3850 CFSG.Sporadic.Schreier.hsStrongArrs[0]!,
    CFSG.Monster.B.Co2.Native.invCand 3850 CFSG.Sporadic.Schreier.hsStrongArrs[1]!]

end CFSG.KD.LQT.C4126

public section

set_option maxRecDepth 400000

#ks_chars CFSG.KD.LQT.C4126.HC CFSG.Sporadic.SmallOddCore.hsCentHex
#kmisc_hexflat CFSG.KD.LQT.C4126.HC CFSG.Sporadic.SmallOddCore.hsCentHex 3 3850 12 43
#ks_chars CFSG.KD.LQT.C4126.HS CFSG.Sporadic.Schreier.hsStrongHex
#kmisc_hexflat CFSG.KD.LQT.C4126.HS CFSG.Sporadic.Schreier.hsStrongHex 4 3850 12 2
#kmisc_packarrs CFSG.KD.LQT.C4126.HCI CFSG.KD.LQT.C4126.hcInvM 12
#kmisc_packarrs CFSG.KD.LQT.C4126.HSI CFSG.KD.LQT.C4126.hsInvM 12

namespace CFSG.KD.LQT.C4126

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier

theorem hc_perms : allN 43 (fun k =>
    invEqK 3850 12 (mask 12) (3850 * 12) (HC.F k) (HCI k)) = true := by quickRfl

theorem hs_perms : allN 2 (fun j =>
    invEqK 3850 12 (mask 12) (3850 * 12) (HS.F j) (HSI j)) = true := by quickRfl

end CFSG.KD.LQT.C4126

end
