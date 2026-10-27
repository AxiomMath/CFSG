module

public import Certificates.Kernel.Tc.HeKDefs
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import Certificates.Data.Kernel.MonsterB.BfsReplay
public import Certificates.Data.Kernel.TcF

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelTc.He

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CFSG.KC.HeLoc CFSG.KC.TcF
  CFSG.KC.Misc.ArrEnum

theorem kN : bAnd(Nat.beq TQ.N 7560, bAnd(Nat.beq TK.N 1080, Nat.beq TY.N 27)) = true := by
  quickRfl

theorem kTreeQ : allN 7560 (fun i => bIf(Nat.beq i 0, true, treeAtK 2 TQ.P TQ.L i)) = true := by
  quickRfl

@[expose] noncomputable def edgeQB (j : Nat) : Bool :=
  allN 420 (fun i => edgeAtK gq q0 TQ.P TQ.L EQ 7560 7560 2 bs (Nat.add (Nat.mul 420 j) i))

@[expose] noncomputable def sortQB (j : Nat) : Bool :=
  allN 420 (fun i => sortAtK kq TQ.SK TQ.SKI 7560 (Nat.add (Nat.mul 420 j) i))

theorem kTreeK : allN 1080 (fun i => bIf(Nat.beq i 0, true, treeAtK 3 TK.P TK.L i)) = true := by
  quickRfl

theorem kTreeY : allN 27 (fun i => bIf(Nat.beq i 0, true, treeAtK 2 TY.P TY.L i)) = true := by
  quickRfl

theorem kReplayQ : CFSG.KC.Bfs.replayOK EQ 2 7560 = true := by quickRfl

theorem kReplayK : CFSG.KC.Bfs.replayOK EK 3 1080 = true := by quickRfl

theorem kReplayY : CFSG.KC.Bfs.replayOK EY 2 27 = true := by quickRfl

theorem kEdgeK : allN 1080 (edgeAtK gk q0 TK.P TK.L EK 1080 1080 3 bs) = true := by quickRfl

theorem kEdgeY : allN 27 (edgeAtK gy q0 TY.P TY.L EY 27 27 2 bs) = true := by quickRfl

theorem kSortK : allN 1080 (sortAtK kk TK.SK TK.SKI 1080) = true := by quickRfl

theorem kSortY : allN 27 (sortAtK ky TY.SK TY.SKI 27) = true := by quickRfl

theorem bS : ∀ j < 2, arrBind sig[j]! 7 4 (ES.G j) = true := by
  intro j hj
  interval_cases j <;> quickRfl

theorem nS : Nat.beq ES.ng 2 = true := by quickRfl

theorem pS : allN 2 (fun k => permB 7 4 (ES.G k)) = true := by quickRfl

theorem rest : tcRestF bs 7 (t 14) 2 gq cu cv cui cvi 3 gk rr ri sigF 7560 tq 1080 tk ES.N =
    true := by
  quickRfl

theorem cubeY : allN 27 (fun k => eqOnL bs (powF (ty k) 3) (fun y => y)) = true := by quickRfl

theorem restNeg : (!tcRestF bs 7 (t 14) 2 gq cu cv cui cvi 3 gk
    (fun j => rr (Nat.sub j (Nat.ble j 1).toNat)) (fun j => ri (Nat.sub j (Nat.ble j 1).toNat))
    sigF 7560 tq 1080 tk ES.N) = true := by
  quickRfl

theorem cubeNeg : (!eqOnL bs (powF (t 4) 3) (fun y => y)) = true := by quickRfl

end CertificateChecks.KernelTc.He

end
