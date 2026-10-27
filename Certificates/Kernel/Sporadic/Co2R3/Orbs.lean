module

public import Certificates.Kernel.Sporadic.Co2R3.Data
public import Certificates.Data.Kernel.Co2R3K
public import Certificates.Data.CFSGNative.Co2Rank3.Data
public import Certificates.Data.Kernel.Misc.ArrEnum
public import Certificates.Data.Kernel.Spor.Raw
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Co2R3

open CFSG.KC.Enum CFSG.KC.Co2R3 CFSG.KD.Co2R3 CFSG.Sporadic.Co2Rank3.Native

@[expose] noncomputable def G0 (k : Nat) : Nat := PK (level1Idx.getD k (nat_lit 0))

@[expose] noncomputable def G1 (k : Nat) : Nat := PK (Nat.add (nat_lit 11) k)

@[expose] noncomputable def G2 (k : Nat) : Nat := PK (level2Idx.getD k (nat_lit 0))

theorem replay0 : orbReplayK 2300 10 G0 (PK 15) (PK 16) (PK 17) (PK 18) (PK 19) (PK 20) = true := by
  quickRfl

theorem replay1 : orbReplayK 2300 3 G1 (PK 21) (PK 22) (PK 23) (PK 24) (PK 25) (PK 26) = true := by
  quickRfl

theorem replay2 : orbReplayK 2300 8 G2 (PK 27) (PK 28) (PK 29) (PK 30) (PK 31) (PK 32) = true := by
  quickRfl

theorem rec0 : recK 10 G0 (PK 15) (PK 16) (PK 17) (PK 18) p0Roots = true := by quickRfl

theorem rec1 : recK 3 G1 (PK 21) (PK 22) (PK 23) (PK 24) stabRoots = true := by quickRfl

theorem rec2 : recK 8 G2 (PK 27) (PK 28) (PK 29) (PK 30) p01Roots = true := by quickRfl

theorem ll0 : llK 2300 M 0 (PK 15) [3] = true := by quickRfl

theorem ll3 : llK 2300 M 3 (PK 21) [0, 36, 4, 2] = true := by quickRfl

theorem ll1 : llK 2300 M 1 (PK 27) [4, 2] = true := by quickRfl

theorem cc3 : ccK M 0 3 378 = true := by quickRfl

theorem cc1 : ccK M 0 1 324 = true := by quickRfl

theorem perms : allN 11 (fun j => CFSG.KC.Misc.ArrEnum.permB 2300 12 (PK j)) = true := by quickRfl

theorem words : allN 3 (fun k => Nat.beq (CFSG.KS.Raw.wordK 2300 12 (CFSG.KS.mask 12)
    (pidn 2300 12) PK (fun h => CFSG.KS.pinvS 2300 12 (CFSG.KS.mask 12) (PK h))
    ((stabWords ()).getD k [])) (PK (Nat.add 11 k))) = true := by quickRfl

theorem idp : Nat.beq (PK 14) (pidn 2300 12) = true := by quickRfl

end CertificateChecks.KernelSpor.Co2R3

end
