module

public import Certificates.Data.Kernel.O8.SAM
public import Certificates.Data.Kernel.O8.Ord
public import Certificates.Data.Kernel.Spor.Prim
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEightMinus.NativeData
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEightMinus.NativeSylowData
public import Certificates.Kernel.OmegaEight.SA3002Data
public import Certificates.Kernel.OmegaEight.Chains3002
public import Certificates.Kernel.OmegaEight.AutChainAM
public import Certificates.Kernel.OmegaEight.NatData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8

open CFSG.KC.Enum CFSG.KC.O8 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.EvenSmallLie.OmegaEightMinus

@[expose] def cwK (k : Nat) : List (List Nat) :=
  [[]] ++ (List.range k).map (fun a => [a]) ++
    (List.range k).flatMap (fun a => (List.range k).map fun b => [a, b]) ++
    (List.range k).flatMap (fun a => (List.range k).flatMap fun b =>
      (List.range k).map fun c => [a, b, c])

@[expose] noncomputable def pcM (p q : Nat) : Nat := pcomp 136 8 (mask 8) p q

@[expose] noncomputable def pinvM (p : Nat) : Nat := pinvS 136 8 (mask 8) p

@[expose] noncomputable def cnM (p : Nat) : Bool := canonK 136 8 (mask 8) (136 * 8) p

@[expose] noncomputable def pmM (p : Nat) : Bool := permOK 136 8 (mask 8) (136 * 8) p (pinvM p)

@[expose] noncomputable def pidM : Nat := pidn 136 8

@[expose] noncomputable def ppwM (p k : Nat) : Nat := ppow 136 8 (mask 8) pidM p k

@[expose] noncomputable def wOM (wd : List Int) : Nat := wordK 136 8 (mask 8) pidM OmM.S OmM.SI wd

@[expose] noncomputable def wAM (wd : List Int) : Nat := wordK 136 8 (mask 8) pidM AQM.S AQM.SI wd

@[expose] noncomputable def wSM (wd : List Int) : Nat := wordK 136 8 (mask 8) pidM SYM.S SYM.SI wd

@[expose] noncomputable def cjM (c x : Nat) : Nat := pcM (pcM c x) (pinvM c)

@[expose] noncomputable def at8 (P p : Nat) : Nat := pg (nat_lit 8) (nat_lit 255) P p

@[expose] noncomputable def mainKM (i : Nat) : Nat := wSM (mainWords.getD i [])

@[expose] def rgLenM (j : Nat) : Nat := (cent0Words.getD (repTypes.getD j 0) []).length

@[expose] noncomputable def rgKM (j l : Nat) : Nat :=
  nIf(Nat.blt l (rgLenM j),
    cjM (wAM (conjWords.getD j [])) (wOM ((cent0Words.getD (repTypes.getD j 0) []).getD l [])),
    wSM (repWords.getD j []))

@[expose] noncomputable def rgOKM (j l : Nat) : Bool :=
  bAnd(lettersK (nat_lit 19) (conjWords.getD j []),
  bAnd(lettersK (nat_lit 18) ((cent0Words.getD (repTypes.getD j 0) []).getD l []),
  bAnd(cnM (wAM (conjWords.getD j [])),
  bAnd(cnM (pinvM (wAM (conjWords.getD j []))),
  bAnd(pmM (wAM (conjWords.getD j [])),
  bAnd(cnM (wOM ((cent0Words.getD (repTypes.getD j 0) []).getD l [])),
  bAnd(cnM (wSM (repWords.getD j [])),
  bAnd(pmM (rgKM j l),
  bAnd(actsMK NSM NIM (rgKM j l) (saAtK rgT (Nat.add (Nat.mul (nat_lit 5) j) l)),
    actsMK NSM NIM (pinvM (rgKM j l)) (saAtK rgInvT (Nat.add (Nat.mul (nat_lit 5) j) l)))))))))))

@[expose] noncomputable def rgJM (j : Nat) : Bool :=
  allN (nat_lit 5) fun l => bIf(Nat.ble l (rgLenM j), rgOKM j l, true)

@[expose] noncomputable def fiveJM (j : Nat) : Bool :=
  allN (nat_lit 8192) (fiveAt saCodes yIdxT rgT rgInvT (cwK (Nat.succ (rgLenM j))) j)

theorem kGenOmM : allN 10 (fun j => Nat.beq (OmM.S j) (AM.S j)) = true := by quickRfl
theorem kGenAQM : allN 11 (fun j => Nat.beq (AQM.S j) (AM.S j)) = true := by quickRfl
theorem kGenSYM : allN 6 (fun j => Nat.beq (SYM.S j) (AM.S (sylowIdx.getD j 0))) = true := by quickRfl

theorem kIdM : Nat.beq (saAtK saCodes 0) idK = true := by quickRfl
theorem kTreeM : allN 8192 (saTreeAtG 6 saMulT saParT saLabT) = true := by quickRfl
theorem kSortM : allN 8192 (saSortAt saCodes saSPM saSPIM) = true := by quickRfl

theorem kGensM : allN 6 (fun l => bAnd(Nat.blt (ix13 saGenT l) 8192,
    actsMK NSM NIM (AM.S (sylowIdx.getD l 0)) (saAtK saCodes (ix13 saGenT l)))) = true := by
  quickRfl

theorem kRepsM : allN 36 (fun j => bAnd(Nat.blt (ix13 yIdxT j) 8192,
    bAnd(lettersK 9 (repWords.getD j []), bAnd(cnM (wSM (repWords.getD j [])),
    actsMK NSM NIM (wSM (repWords.getD j [])) (saAtK saCodes (ix13 yIdxT j)))))) = true := by
  quickRfl

theorem kPidM : bAnd(cnM pidM, CFSG.KS.Prim.idK 136 8 (mask 8)) = true := by quickRfl

theorem kStrCM : bAnd(allN 11 (fun j => cnM (AM.S j)), bAnd(pmM (AM.S 10), cnM (pinvM (AM.S 10)))) =
    true := by quickRfl

theorem kStrM : allN 10 (fun i => bAnd(Nat.blt (rvPerm.getD i 0) 10,
    Nat.beq (cjM (AM.S 10) (AM.S i)) (AM.S (rvPerm.getD i 0)))) = true := by quickRfl

theorem kStabM1 : List.all stabIdx (fun j => bAnd(Nat.blt j 18, Nat.beq (at8 (OmM.S j) 0) 0)) =
    true := by quickRfl

theorem kStabM2 : allN 135 (fun p => List.any stabIdx fun j =>
    bIf(Nat.beq (at8 (OmM.S j) (Nat.succ p)) (Nat.succ p), false, true)) = true := by quickRfl

theorem kTreeGM : allN 135 (fun i => Nat.beq (at8 (AM.S (treeLit.2.1[Nat.succ i]!)) (treeLit.1[Nat.succ i]!))
    (Nat.succ i)) = true := by quickRfl

theorem kMainM : allN 5 (fun i => bAnd(lettersK 9 (mainWords.getD i []), bAnd(cnM (mainKM i),
    pmM (mainKM i)))) = true := by quickRfl

theorem kSylowRepsM : allN 36 (fun j => bAnd(cnM (wSM (repWords.getD j [])),
    bAnd(pmM (wSM (repWords.getD j [])),
    bAnd(Nat.beq (pcM (wSM (repWords.getD j [])) (wSM (repWords.getD j []))) pidM,
    bAnd(bIf(Nat.beq (wSM (repWords.getD j [])) pidM, false, true),
    bAnd(bIf(siftK 136 8 (mask 8) (136 * 8) (pidn 136 8) OmM.LR OmM.TRI OmM.BP 7 0 (wSM (repWords.getD j [])),
      Nat.blt (repTypes.getD j 0) 3, bIf(Nat.blt (repTypes.getD j 0) 3, false, true)),
    bAnd(Nat.blt (repTypes.getD j 0) 5,
      Nat.beq (cjM (wAM (conjWords.getD j [])) (mainKM (repTypes.getD j 0))) (wSM (repWords.getD j []))))))))) =
    true := by quickRfl

theorem kCentM : allN 5 (fun i => List.all (cent0Words.getD i []) fun wd => bAnd(lettersK 18 wd,
    bAnd(cnM (wOM wd), bAnd(pmM (wOM wd), Nat.beq (pcM (wOM wd) (mainKM i)) (pcM (mainKM i) (wOM wd)))))) =
    true := by quickRfl

theorem kFgM : allN 2 (fun i => bAnd(lettersK 18 (fgWords.getD i []), bAnd(cnM (wOM (fgWords.getD i [])),
    bAnd(cnM (pinvM (wOM (fgWords.getD i []))), bAnd(pmM (wOM (fgWords.getD i [])),
    strictB (pcM (cjM (wOM (fgWords.getD i [])) (mainKM (Nat.add i 3))) (mainKM (Nat.add i 3))) fun v =>
      bAnd(Nat.beq (pcM v v) pidM, bIf(Nat.beq v pidM, false, true))))))) = true := by quickRfl

theorem kOddM : allN 3 (fun i => bAnd(lettersK 18 (oddData.getD i ([], [], 0, 0, 0)).1,
    bAnd(lettersK 18 (oddData.getD i ([], [], 0, 0, 0)).2.1,
    strictB (wOM (oddData.getD i ([], [], 0, 0, 0)).1) fun u =>
    strictB (wOM (oddData.getD i ([], [], 0, 0, 0)).2.1) fun v =>
      bAnd(cnM u, bAnd(cnM v, bAnd(ordK 136 8 (mask 8) pidM u (oddData.getD i ([], [], 0, 0, 0)).2.2.2.1,
      bAnd(ordK 136 8 (mask 8) pidM v (oddData.getD i ([], [], 0, 0, 0)).2.2.2.2,
      bAnd(Nat.beq (pcM u (mainKM i)) (pcM (mainKM i) u), bAnd(Nat.beq (pcM v (mainKM i)) (pcM (mainKM i) v),
        Nat.beq (ppwM (pcM u v) (oddData.getD i ([], [], 0, 0, 0)).2.2.1) (mainKM i)))))))))) = true := by
  quickRfl

end CertificateChecks.KernelO8

end
