module

public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Data.Kernel.FiveLocK
public import CFSG.RankThree.PartOne.KS.RuFiveData
meta import CFSG.RankThree.PartOne.KS.RuFiveData
meta import Certificates.Kernel.Sporadic.RawGen
import CFSG.Certificates.Kernel.Common.Harness
public import Std.Data.HashMap

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelMisc.RuFive.RF CFSG.RankThree.PartOne.ruFiveHex
#kmisc_hexflat CertificateChecks.KernelMisc.RuFive.RF CFSG.RankThree.PartOne.ruFiveHex 3 4060 12 33

namespace CertificateChecks.KernelMisc.RuFive

open CFSG.KC.Enum CFSG.KS CFSG.KC.Misc.ArrEnum CFSG.KC.FiveLocK

@[expose] noncomputable def L (j : Nat) : Nat := RF.F (Nat.add j 2)

@[expose] noncomputable def lineAt (rec : List Nat) (j : Nat) : Bool :=
  bIf(Nat.beq (Nat.mod (rec.getD j 0) 31) 0, bIf(commK 4060 12 (L j) (L 1), Nat.beq j 0, true),
    true)

theorem szOK' : CFSG.KS.Raw.szOK 4060 12 = true := by quickRfl

theorem permL : allN 31 (fun j => permB 4060 12 (L j)) = true := by quickRfl

theorem kComm : commK 4060 12 (L 0) (L 1) = true := by quickRfl

theorem kLines : allN 31 (lineAt CFSG.RankThree.PartOne.ruFiveRec) = true := by quickRfl

theorem negAll : (!allN 31 (lineAt ((List.range 31).map fun _ => 0))) = true := by quickRfl

theorem negSelf : (!lineAt (CFSG.RankThree.PartOne.ruFiveRec.set 1 0) 1) = true := by quickRfl

end CertificateChecks.KernelMisc.RuFive

end
