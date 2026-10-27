module

public import Certificates.Kernel.RuThree.Chain
public import Certificates.Kernel.RuThree.Tab
public import Certificates.Kernel.RuThree.Data
public import Certificates.Kernel.Misc.RuInv.Data
public import Certificates.Kernel.SporSch.GenPerms
public import Certificates.Data.Kernel.HeLoc.Tree
public import Certificates.Data.Kernel.HeLoc.PTail
public import Certificates.Data.Kernel.MonsterB.BfsReplay
public import Certificates.Data.Kernel.Spor.Prim
public meta import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.RuThreeInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelRuThree

meta def cgiM : Array (Array Nat) :=
  CFSG.EvenSporadicStandard.RuStd.S2.ruThreeC0Gens.map (CFSG.Monster.B.Co2.Native.invCand 4060)

end CertificateChecks.KernelRuThree

#kss_perms CertificateChecks.KernelRuThree.CGI 12 CertificateChecks.KernelRuThree.cgiM

namespace CertificateChecks.KernelRuThree

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CFSG.KC.HeLoc CFSG.KS.Prim
  CFSG.EvenSporadicStandard.RuStd.S2

@[expose] def cWords : List (List Int) :=
  [[-9], [-5, 11, 5, -7, 6, -11, 9], [2, -10, -5, 2, 1, -4, -11, -9, 3, 10, 7, 7, -8, 9]]

@[expose] def bs : List Nat := ruThreeKeys

@[expose] def q0 (_ : Nat) : Nat := 0

@[expose] noncomputable def gC (k x : Nat) : Nat := pg 12 (mask 12) (CG k) x

@[expose] noncomputable def x0 (y : Nat) : Nat := gC 0 y

@[expose] noncomputable def CE (i k : Nat) : Nat := fld(C0.ER i, Nat.mul 16 k, 65535)

@[expose] noncomputable def cv (i x : Nat) : Nat := trV gC C0.P C0.L 2160 i x

@[expose] noncomputable def ckey (i : Nat) : Nat := keyV 4060 ruThreeKeys (cv i)

@[expose] noncomputable def fr (i : Nat) : Nat := FR.getD i 0

@[expose] noncomputable def relAt (r : Nat × Nat × Nat) : Bool :=
  bAnd(Nat.blt r.2.2 3, bAnd(Nat.blt r.1 7, bAnd(Nat.blt r.2.1 7,
    Nat.beq (powF x0 r.2.2 (ruThreeBaseArr[r.1]!)) (ruThreeBaseArr[r.2.1]!))))

theorem kBind : allN 9 (fun j => Nat.beq (R3.F j) (S3R.S (Nat.add 2 j))) = true := by quickRfl

theorem kGen0 : Nat.beq (S3R.S 0) CertificateChecks.KernelMisc.RuInv.AD.n0 = true := by quickRfl

theorem kGen1 : Nat.beq (S3R.S 1) CertificateChecks.KernelMisc.RuInv.AD.n1 = true := by quickRfl

theorem kPerm : allN 11 (fun j => permOK 4060 12 (mask 12) (4060 * 12) (S3R.S j) (S3R.SI j)) =
    true := by quickRfl

theorem kBase : allN 7 (fun t => Nat.beq ruThreeBaseArr[t]! (pg 12 (mask 12) S3R.BP t)) = true := by
  quickRfl

theorem kOrb : allN 7 (fun i => Nat.beq (rcnt (S3R.LR i)) ([4060, 2304, 650, 8, 3, 1, 1].getD i 0)) =
    true := by quickRfl

theorem kWord : allN 3 (fun k => bAnd(wordEqK 4060 12 (mask 12) (pidn 4060 12) S3R.S S3R.SI 11
    (cWords.getD k []) (CG k), invEqK 4060 12 (mask 12) (4060 * 12) (CG k) (CGI k))) = true := by
  quickRfl

theorem kN : Nat.beq C0.N 2160 = true := by quickRfl

theorem kTree : allN 2160 (fun i => bIf(Nat.beq i 0, true, treeAtK 3 C0.P C0.L i)) = true := by
  quickRfl

theorem kReplay : CFSG.KC.Bfs.replayOK CE 3 2160 = true := by quickRfl

theorem kEdge : allN 2160 (edgeAtK gC q0 C0.P C0.L CE 2160 2160 3 bs) = true := by quickRfl

theorem kSort : allN 2160 (sortAtK ckey C0.SK C0.SKI 2160) = true := by quickRfl

theorem kRels : ruThreeRels.all relAt = true := by quickRfl

theorem kComm : allN 3 (fun k => eqOnL bs (fun y => gC k (x0 y)) (fun y => x0 (gC k y))) = true := by
  quickRfl

theorem kFR : allN 7 (fun i => bIf(Nat.beq (fr i) 0, true,
    bAnd(Nat.blt (Nat.div (Nat.sub (fr i) 1) 8) i, bAnd(Nat.blt (Nat.mod (Nat.sub (fr i) 1) 8) 3,
      ruThreeRels.any fun r =>
        bAnd(Nat.beq r.1 (Nat.div (Nat.sub (fr i) 1) 8), bAnd(Nat.beq r.2.1 i,
          Nat.beq r.2.2 (Nat.mod (Nat.sub (fr i) 1) 8))))))) = true := by
  quickRfl

theorem kInv1 : (!eqOnL bs (gC 1) (fun y => y)) = true := by quickRfl

theorem kInv2 : eqOnL bs (fun y => gC 1 (gC 1 y)) (fun y => y) = true := by quickRfl

theorem kInv3 : CFSG.KC.LQT.P.anyN 4060 (fun p => Nat.beq (gC 1 p) p) = true := by quickRfl

theorem kTail : ptK 4060 12 11 T3R.NR T3R.NR T3R.LT T3R.PT T3R.QT S3R.LR fr ruThreeRels x0 bs
    ruThreeKeys ckey C0.SK 2160 7 0 (fun y => y) (fun y => y) (fun _ => 0) = true := by
  quickRfl

theorem kWordNeg : (!wordEqK 4060 12 (mask 12) (pidn 4060 12) S3R.S S3R.SI 11 (cWords.getD 1 [])
    (CG 2)) = true := by quickRfl

theorem kOrbNeg : (!allN 7 (fun i => Nat.beq (rcnt (S3R.LR i))
    ([4060, 2304, 650, 8, 3, 1, 2].getD i 0))) = true := by quickRfl

end CertificateChecks.KernelRuThree

end
