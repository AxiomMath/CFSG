module

public import Certificates.Kernel.Tc.RuHex
public import Certificates.Kernel.Tc.RuTrees
public import Certificates.Data.Kernel.TcF
public import Certificates.Data.Kernel.HeLoc.Tree
public import Certificates.Data.Kernel.MonsterB.BfsReplay
public import Certificates.Data.Kernel.Misc.ArrEnum
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelTc.Ru

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CFSG.KC.HeLoc CFSG.KC.TcF
  CFSG.KC.Misc.ArrEnum CFSG.AGLEmbeddingD2.Wilson.ThetaSpor

@[expose] noncomputable def t3 (k x : Nat) : Nat := pg 12 (mask 12) (R3.F k) x

@[expose] noncomputable def i3 (k x : Nat) : Nat := pg 12 (mask 12) (I3 k) x

@[expose] noncomputable def tT (k x : Nat) : Nat := pg 12 (mask 12) (RT.F k) x

@[expose] noncomputable def iT (k x : Nat) : Nat := pg 12 (mask 12) (IT k) x

@[expose] def bs : List Nat := [0, 1, 2, 3]

@[expose] def q0 (_ : Nat) : Nat := 0

@[expose] noncomputable def gq (k x : Nat) : Nat := tT k x

@[expose] noncomputable def gk (k x : Nat) : Nat := nIf(Nat.beq k 2, t3 0 x, tT (Nat.add 6 k) x)

@[expose] noncomputable def gc (k x : Nat) : Nat := t3 (Nat.add 1 k) x

@[expose] noncomputable def cu (i x : Nat) : Nat := tT (Nat.add 2 (Nat.mul 2 i)) x
@[expose] noncomputable def cv (i x : Nat) : Nat := tT (Nat.add 3 (Nat.mul 2 i)) x
@[expose] noncomputable def cui (i x : Nat) : Nat := iT (Nat.add 2 (Nat.mul 2 i)) x
@[expose] noncomputable def cvi (i x : Nat) : Nat := iT (Nat.add 3 (Nat.mul 2 i)) x

@[expose] noncomputable def rr (j x : Nat) : Nat := nIf(Nat.beq j 0, x, tT (Nat.add 7 j) x)
@[expose] noncomputable def ri (j x : Nat) : Nat := nIf(Nat.beq j 0, x, iT (Nat.add 7 j) x)

@[expose] def sigF (i j : Nat) : Nat := (sig[i]!)[j]!

@[expose] noncomputable def EQ (i k : Nat) : Nat := fld(TQ.ER i, Nat.mul 16 k, 65535)
@[expose] noncomputable def EK (i k : Nat) : Nat := fld(TK.ER i, Nat.mul 16 k, 65535)
@[expose] noncomputable def EC (i k : Nat) : Nat := fld(TC.ER i, Nat.mul 16 k, 65535)

@[expose] noncomputable def tq (i x : Nat) : Nat := trV gq TQ.P TQ.L 1080 i x
@[expose] noncomputable def tk (i x : Nat) : Nat := trV gk TK.P TK.L 180 i x
@[expose] noncomputable def tc (i x : Nat) : Nat := trV gc TC.P TC.L 2160 i x

@[expose] noncomputable def kq (i : Nat) : Nat := keyV 4060 ruKeys (tq i)
@[expose] noncomputable def kk (i : Nat) : Nat := keyV 4060 ruKeys (tk i)
@[expose] noncomputable def kc (i : Nat) : Nat := keyV 4060 ruKeys (tc i)

theorem kN : bAnd(Nat.beq TQ.N 1080, bAnd(Nat.beq TK.N 180, Nat.beq TC.N 2160)) = true := by
  quickRfl

theorem kTreeQ : allN 1080 (fun i => bIf(Nat.beq i 0, true, treeAtK 2 TQ.P TQ.L i)) = true := by
  quickRfl

theorem kTreeK : allN 180 (fun i => bIf(Nat.beq i 0, true, treeAtK 3 TK.P TK.L i)) = true := by
  quickRfl

theorem kTreeC : allN 2160 (fun i => bIf(Nat.beq i 0, true, treeAtK 2 TC.P TC.L i)) = true := by
  quickRfl

theorem kReplayQ : CFSG.KC.Bfs.replayOK EQ 2 1080 = true := by quickRfl

theorem kReplayK : CFSG.KC.Bfs.replayOK EK 3 180 = true := by quickRfl

theorem kReplayC : CFSG.KC.Bfs.replayOK EC 2 2160 = true := by quickRfl

theorem kEdgeQ : allN 1080 (edgeAtK gq q0 TQ.P TQ.L EQ 1080 1080 2 bs) = true := by quickRfl

theorem kEdgeK : allN 180 (edgeAtK gk q0 TK.P TK.L EK 180 180 3 bs) = true := by quickRfl

theorem kEdgeC : allN 2160 (edgeAtK gc q0 TC.P TC.L EC 2160 2160 2 bs) = true := by quickRfl

theorem kSortQ : allN 1080 (sortAtK kq TQ.SK TQ.SKI 1080) = true := by quickRfl

theorem kSortK : allN 180 (sortAtK kk TK.SK TK.SKI 180) = true := by quickRfl

theorem kSortC : allN 2160 (sortAtK kc TC.SK TC.SKI 2160) = true := by quickRfl

theorem bS : ∀ j < 2, arrBind sig[j]! 6 3 (ES.G j) = true := by
  intro j hj
  interval_cases j <;> quickRfl

theorem nS : Nat.beq ES.ng 2 = true := by quickRfl

theorem pS : allN 2 (fun k => permB 6 3 (ES.G k)) = true := by quickRfl

theorem rest : tcRestF bs 6 (t3 0) 2 gq cu cv cui cvi 3 gk rr ri sigF 1080 tq 180 tk ES.N = true := by
  quickRfl

theorem inC : allN 2 (fun l => memF bs 2160 tc (gq l)) = true := by quickRfl

theorem normQ : allN 2 (fun k => allN 2 fun l =>
    memF bs 1080 tq (fun y => gc k (gq l (i3 (Nat.add 1 k) y)))) = true := by quickRfl

theorem restNeg : (!tcRestF bs 6 (t3 0) 2 gq cu cv cui cvi 3 gk
    (fun j => rr (Nat.sub j (Nat.ble j 1).toNat)) (fun j => ri (Nat.sub j (Nat.ble j 1).toNat))
    sigF 1080 tq 180 tk ES.N) = true := by
  quickRfl

end CertificateChecks.KernelTc.Ru

end
