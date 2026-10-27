module

public import Certificates.Kernel.S63K.GData
public import Certificates.Kernel.S63K.HBind
public import Certificates.Data.Kernel.S63K.GeoK
public import Certificates.Data.Kernel.S63K.OrbRun
public import Certificates.Data.Kernel.SporSch.Co1Bfs
public import Certificates.Data.D4HexGeoCheck
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelS63.GD

open CFSG.KC.S63K CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch.M24 CFSG.D4Hex CertificateChecks.KernelS63.HD

@[expose] noncomputable def tb (t i : Nat) : Nat := pg 12 (mask 12) (G t) i
@[expose] noncomputable def LTf (i : Nat) : Nat := pg 12 (mask 12) LT i
@[expose] noncomputable def PLf (i : Nat) : Nat := tb 0 i
@[expose] noncomputable def DY : Nat := G 8
@[expose] noncomputable def gG (j x : Nat) : Nat := if j < 8 then im j x else 0
@[expose] noncomputable def wF (ws : List String) (j x : Nat) : Nat :=
  if j < ws.length then (if x < 819 then ptW (hexDecode (ws.getD j "")) x else 0) else 0
@[expose] noncomputable def nb (x : Nat) : List Nat := nbrF LTf PLf x
@[expose] noncomputable def L0 (i : Nat) : Nat := tb 2 i
@[expose] noncomputable def R0 (i : Nat) : Nat := tb 3 i
@[expose] noncomputable def L1 (i : Nat) : Nat := tb 5 i
@[expose] noncomputable def R1 (i : Nat) : Nat := tb 6 i
@[expose] noncomputable def Ot (t i : Nat) : Nat := tb (9 + 5 * t) i
@[expose] noncomputable def Pat (t i : Nat) : Nat := tb (10 + 5 * t) i
@[expose] noncomputable def Lat (t i : Nat) : Nat := tb (11 + 5 * t) i
@[expose] noncomputable def Pst (t i : Nat) : Nat := tb (12 + 5 * t) i
@[expose] noncomputable def Wt (t i : Nat) : Nat := tb (13 + 5 * t) i

theorem bnd : bAnd(Nat.blt LT (2 ^ (12 * 7371)), bAnd(Nat.blt (G 0) (2 ^ (12 * 7371)),
    bAnd(Nat.blt (G 2) (2 ^ (12 * 3276)), bAnd(Nat.blt (G 3) (2 ^ (12 * 3276)),
    bAnd(Nat.blt (G 5) (2 ^ (12 * 3276)), bAnd(Nat.blt (G 6) (2 ^ (12 * 3276)),
    bAnd(Nat.blt (G 7) (2 ^ (12 * 12)), allN 8 fun j => Nat.blt (PA j) (2 ^ (12 * 819))))))))) =
    true := by
  quickRfl

theorem bndO : ([(9, 2457), (10, 2457), (11, 2457), (12, 3276), (14, 512), (15, 512), (16, 512),
    (17, 3276), (19, 768), (20, 768), (21, 768), (22, 3276), (24, 2048), (25, 2048), (26, 2048),
    (27, 3276)].all fun p : Nat × Nat => Nat.blt (G p.1) (2 ^ (12 * p.2))) = true := by
  quickRfl

theorem ptsK : ptsOKF LTf = true := by quickRfl

theorem pt0K : Nat.beq (LTf 0) 0 = true := by quickRfl

theorem incK : incOKF LTf PLf = true := by quickRfl

theorem meetK : meetOKF LTf PLf = true := by quickRfl

theorem rowK : (allN 819 fun p => allN 8 fun j =>
    Nat.blt (PLf (9 * p + j)) (PLf (9 * p + (j + 1)))) = true := by
  quickRfl

theorem consL0 : layConsK 3276 (tb 1) (tb 29) L0 R0 = true := by quickRfl

theorem runL0 : Nat.beq (layRunK 3276 (tb 1) (tb 29) L0 R0 nb 3277 0 1) 3276 = true := by
  quickRfl

theorem consL1 : layConsK 3276 (tb 4) (tb 30) L1 R1 = true := by quickRfl

theorem runL1 : Nat.beq (layRunK 3276 (tb 4) (tb 30) L1 R1 nb 3277 0 1) 3276 = true := by
  quickRfl

theorem rootL : bAnd(Nat.beq (tb 1 0) 0, Nat.beq (tb 4 0) 819) = true := by quickRfl

theorem layK0 : layOKF LTf PLf 0 L0 R0 = true := by quickRfl

theorem layK1 : layOKF LTf PLf 819 L1 R1 = true := by quickRfl

theorem lowY : lowK YC 0 DY = true := by quickRfl

theorem lenY : Nat.beq YC.length 819 = true := by quickRfl

theorem layY : (allN 819 fun x => Nat.beq (dg DY x) (L0 x)) = true := by quickRfl

theorem cycK : cycleOKF LTf PLf (fun i => (cycF L0 R0 nb).getD i 0) = true := by quickRfl

theorem cycLen : Nat.beq (cycF L0 R0 nb).length 12 = true := by quickRfl

theorem keyK : bfsDistK (keyF LTf) (tb 31) 2457 = true := by quickRfl

theorem consO : bAnd(orbConsK 3276 2457 (Ot 0) (Pst 0), bAnd(orbConsK 3276 512 (Ot 1) (Pst 1),
    bAnd(orbConsK 3276 768 (Ot 2) (Pst 2), orbConsK 3276 2048 (Ot 3) (Pst 3)))) = true := by
  quickRfl

theorem rootO : (allN 4 fun t => bAnd(Nat.beq (Pat t 0) 0, Nat.beq (Lat t 0) 0)) = true := by
  quickRfl

theorem rootO' : bAnd(Nat.beq (Ot 0 0) 819, bAnd(Nat.beq (Ot 1 0) hexB0,
    bAnd(Nat.beq (Ot 2 0) hexY0, Nat.beq (Ot 3 0) hexM0))) = true := by
  quickRfl

theorem runO0 : Nat.beq (orbRunK (Wt 0) (Pat 0) (Lat 0) 8 2458 0 1) 2457 = true := by quickRfl

theorem runO1 : Nat.beq (orbRunK (Wt 1) (Pat 1) (Lat 1) 3 513 0 1) 512 = true := by quickRfl

theorem runO2 : Nat.beq (orbRunK (Wt 2) (Pat 2) (Lat 2) 2 769 0 1) 768 = true := by quickRfl

theorem runO3 : Nat.beq (orbRunK (Wt 3) (Pat 3) (Lat 3) 2 2049 0 1) 2048 = true := by quickRfl

theorem actO0 : orbActF LTf gG 8 2457 (Ot 0) (Wt 0) = true := by quickRfl

theorem actO1 : orbActF LTf (wF hexHWords) 3 512 (Ot 1) (Wt 1) = true := by quickRfl

theorem actO2 : orbActF LTf (wF hexNWords) 2 768 (Ot 2) (Wt 2) = true := by quickRfl

theorem actO3 : orbActF LTf (wF hexNWords) 2 2048 (Ot 3) (Wt 3) = true := by quickRfl

theorem okO0 : orbOKRF 3276 8 (fun j y x => actOKF LTf (gG j) y x) 819 2457
    (fun x => decide (819 ≤ x) && decide (x < 3276)) (Ot 0) (Pat 0) (Lat 0) (Pst 0) = true := by
  quickRfl

theorem okO1 : orbOKRF 3276 3 (fun j y x => actOKF LTf (wF hexHWords j) y x) hexB0 512
    (fun x => L0 x == 6) (Ot 1) (Pat 1) (Lat 1) (Pst 1) = true := by
  quickRfl

theorem okO2 : orbOKRF 3276 2 (fun j y x => actOKF LTf (wF hexNWords j) y x) hexY0 768
    (fun x => L1 x == 5) (Ot 2) (Pat 2) (Lat 2) (Pst 2) = true := by
  quickRfl

theorem okO3 : orbOKRF 3276 2 (fun j y x => actOKF LTf (wF hexNWords j) y x) hexM0 2048
    (fun x => L1 x == 6) (Ot 3) (Pat 3) (Lat 3) (Pst 3) = true := by
  quickRfl

theorem wordsK : (hexWordsOK 8 hexHWords && hexWordsOK 8 hexPWords && hexWordsOK 8 hexNWords &&
    hexWordsOK 8 hexTWords) = true := by
  decide +kernel

theorem lenK : (hexHWords.length == 3 && hexPWords.length == 72 && hexNWords.length == 2 &&
    hexTWords.length == 6) = true := by
  decide +kernel

theorem ptLocK : (decide (hexB0 < 819) && decide (L0 hexB0 = 6) &&
    decide (((List.range 9).map fun k => PLf k).Nodup) &&
    (allN 3 fun i => wF hexHWords i 0 == 0) &&
    (allN 72 fun i => wF hexPWords i 0 == 0 && wF hexPWords i hexB0 == hexB0)) = true := by
  quickRfl

theorem ptPairK : ((List.range 9).all fun a => (List.range 9).all fun b => a == b ||
    (List.range 72).any fun i =>
      actOKF LTf (wF hexPWords i) (819 + PLf 0) (819 + PLf a) &&
        actOKF LTf (wF hexPWords i) (819 + PLf 1) (819 + PLf b)) = true := by
  quickRfl

theorem lnLocK : (decide (hexY0 < 819) && decide (L1 hexY0 = 5) && decide (819 ≤ hexM0) &&
    decide (hexM0 < 3276) && decide (L1 hexM0 = 6) &&
    (allN 2 fun i => actOKF LTf (wF hexNWords i) 819 819) &&
    (allN 6 fun i => actOKF LTf (wF hexTWords i) 819 819 &&
      actOKF LTf (wF hexTWords i) hexM0 hexM0) &&
    ((List.range 3).all fun a => (List.range 3).all fun b => a == b ||
      (List.range 6).any fun i => wF hexTWords i (LTf 0) == LTf a &&
        wF hexTWords i (LTf 1) == LTf b)) = true := by
  quickRfl

theorem neg : bAnd(bIf(Nat.beq (layRunK 3276 (tb 1) (tb 30) L0 R0 nb 3277 0 1) 3276, false, true),
    bAnd(bIf(orbActF LTf gG 8 2457 (Ot 0) (Wt 3), false, true),
    bAnd(bIf(incOKF LTf (fun i => PLf (i + 1)), false, true),
    bAnd(bIf(ptsOKF (fun i => LTf (i + 1)), false, true),
      bIf(cycleOKF LTf PLf (fun i => if i = 0 then 3275 else (cycF L0 R0 nb).getD i 0), false,
        true))))) = true := by
  quickRfl

end CertificateChecks.KernelS63.GD

end
