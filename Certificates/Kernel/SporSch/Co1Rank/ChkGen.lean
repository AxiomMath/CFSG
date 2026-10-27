module

public import Certificates.Kernel.SporSch.Co1Rank.DagGen
public import Certificates.Kernel.SporSch.Co1Rank.TabB
public import Certificates.Kernel.SporSch.Co1Rank.TabC
public import Certificates.Kernel.Co1B.IotaData
public import Certificates.Data.Kernel.SporSch.Co1Heis
public import Certificates.Data.Kernel.SporSch.Co1MatW
public import Certificates.Data.Kernel.SporSch.Co1Cent
public import Certificates.Data.Kernel.Co1F2
public import Certificates.Data.Kernel.Co1B
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co1RankCheck
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.Co1RankGen

open CFSG.KC.Enum CFSG.KS.SporSch.M24 CFSG.KC.Co1F2 CFSG.KD.Co1B CFSG.KC.Co1RankCoord
  CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic CFSG.Sporadic.Co1Block

@[expose] noncomputable def IC : Nat := getL CFSG.KC.Co1B.oneK IRS 51

theorem kbB : (Nat.beq (RB.M 0) SA && Nat.beq (RB.M 1) SB) = true := by quickRfl

theorem kDB : dagWK RB.M RB.MI 2 RB.N (rankBD.map encWordK) = true := by quickRfl

theorem kGB : (Nat.beq Co1RankTabB.nG rankBIdx.length &&
    rankBIdx.all (fun j => decide (j < RB.N)) &&
    (List.range rankBIdx.length).all (fun g =>
      Nat.beq (CFSG.KC.Co1RankTab.getM Co1RankTabB.G g) (RB.M (rankBIdx.getD g 0))) &&
    Nat.beq Co1RankTabB.cM SA && Nat.beq Co1RankTabB.BS.length Co1RankTabB.d) = true := by
  quickRfl

theorem kCmB : (List.range 6).all (fun g =>
    Nat.beq (CFSG.KC.Co1B.mulWK (CFSG.KC.Co1RankTab.getM Co1RankTabB.G g) SA)
      (CFSG.KC.Co1B.mulWK SA (CFSG.KC.Co1RankTab.getM Co1RankTabB.G g))) = true := by quickRfl

theorem kRB :(!Nat.beq (rankRC 24 24 (Nat.xor SA CFSG.KC.Co1B.oneK)) 8) = true := by quickRfl

theorem kbC : (Nat.beq (C1.M 0) SA && Nat.beq (C1.M 1) SB && Nat.beq (C1.M 2) IC) = true := by
  quickRfl

theorem kDC1 : dagWK C1.M C1.MI 3 C1.N (twoCD1.map encWordK) = true := by quickRfl

theorem kIC : twoCBray.all (fun j => decide (3 < j) && decide (j ≤ C1.N)) = true := by quickRfl

theorem kBindC : bindK C1.M C2.M twoCBray = true := by quickRfl

theorem kDC2 : dagWK C2.M C2.MI twoCBray.length C2.N (rankCD2.map encWordK) = true := by quickRfl

theorem kGC : (Nat.beq Co1RankTabC.nG rankCIdx.length &&
    rankCIdx.all (fun j => decide (j < C2.N)) &&
    (List.range rankCIdx.length).all (fun g =>
      Nat.beq (CFSG.KC.Co1RankTab.getM Co1RankTabC.G g) (C2.M (rankCIdx.getD g 0))) &&
    Nat.beq Co1RankTabC.cM IC && Nat.beq Co1RankTabC.BS.length Co1RankTabC.d) = true := by
  quickRfl

theorem kCmC : (List.range rankCIdx.length).all (fun g =>
    Nat.beq (CFSG.KC.Co1B.mulWK (CFSG.KC.Co1RankTab.getM Co1RankTabC.G g) IC)
      (CFSG.KC.Co1B.mulWK IC (CFSG.KC.Co1RankTab.getM Co1RankTabC.G g))) = true := by quickRfl

theorem kdim : (Nat.beq Co1RankTabB.d 8 && Nat.beq Co1RankTabC.d 11) = true := by quickRfl

theorem kRC :(!Nat.beq (rankRC 24 24 (Nat.xor IC CFSG.KC.Co1B.oneK)) 8) = true := by quickRfl

end CFSG.KD.Co1RankGen

end
