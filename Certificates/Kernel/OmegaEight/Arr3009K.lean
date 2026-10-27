module

public import Certificates.Kernel.OmegaEight.SA3009K
public import Certificates.Data.Kernel.O8.Ord
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.EvenSmallLie.OmegaEight

@[expose] noncomputable def pm (p : Nat) : Bool := permOK 360 9 (mask 9) (360 * 9) p (pinv p)

@[expose] noncomputable def pid : Nat := pidn 360 9

@[expose] noncomputable def ppw (p k : Nat) : Nat := ppow 360 9 (mask 9) pid p k

@[expose] noncomputable def mainK (i : Nat) : Nat := wS (mainWords.getD i [])

@[expose] noncomputable def at9 (P p : Nat) : Nat := pg (nat_lit 9) (nat_lit 511) P p

theorem kPid : bAnd(cn pid, CFSG.KS.Prim.idK 360 9 (mask 9)) = true := by quickRfl

theorem kStrC : bAnd(allN 10 (fun j => cn (AP.S j)), bAnd(pm (AP.S 8), bAnd(pm (AP.S 9),
    bAnd(cn (pinv (AP.S 8)), cn (pinv (AP.S 9)))))) = true := by quickRfl

theorem kStr : allN 8 (fun i => bAnd(Nat.blt (rhoPerm.getD i 0) 10, bAnd(Nat.blt (tauPerm.getD i 0) 10,
    bAnd(Nat.beq (cj (AP.S 8) (AP.S i)) (AP.S (rhoPerm.getD i 0)),
    bAnd(Nat.beq (cj (AP.S 9) (AP.S i)) (AP.S (tauPerm.getD i 0)),
    allN 360 fun p => bIf(Nat.blt p 120, Nat.blt (at9 (AP.S i) p) 120,
      bIf(Nat.blt (at9 (AP.S i) p) 120, false, true))))))) = true := by quickRfl

theorem kRho : allN 360 (fun p => Nat.beq (at9 (AP.S 8) p) (Nat.mod (Nat.add p 120) 360)) = true := by
  quickRfl

theorem kStab1 : List.all stabIdx (fun j => bAnd(Nat.blt j 17, Nat.beq (at9 (OmP.S j) 0) 0)) = true := by
  quickRfl

theorem kStab2 : allN 359 (fun p => List.any stabIdx fun j =>
    bIf(Nat.beq (at9 (OmP.S j) (Nat.succ p)) (Nat.succ p), false, true)) = true := by quickRfl

theorem kTreeG : allN 119 (fun i => Nat.beq (at9 (AP.S (treeLit.2.1[Nat.succ i]!)) (treeLit.1[Nat.succ i]!))
    (Nat.succ i)) = true := by quickRfl

theorem kMain : allN 5 (fun i => bAnd(lettersK 8 (mainWords.getD i []), bAnd(cn (mainK i),
    pm (mainK i)))) = true := by quickRfl

theorem kSylowReps : allN 38 (fun j => bAnd(cn (wS (repWords.getD j [])),
    bAnd(pm (wS (repWords.getD j [])),
    bAnd(Nat.beq (pc (wS (repWords.getD j [])) (wS (repWords.getD j []))) pid,
    bAnd(bIf(Nat.beq (wS (repWords.getD j [])) pid, false, true),
    bAnd(bIf(siftK 360 9 (mask 9) (360 * 9) (pidn 360 9) OmP.LR OmP.TRI OmP.BP 7 0 (wS (repWords.getD j [])),
      Nat.blt (repTypes.getD j 0) 3, bIf(Nat.blt (repTypes.getD j 0) 3, false, true)),
    bAnd(Nat.blt (repTypes.getD j 0) 5,
      Nat.beq (cj (wA (conjWords.getD j [])) (mainK (repTypes.getD j 0))) (wS (repWords.getD j []))))))))) =
    true := by quickRfl

theorem kCent : allN 5 (fun i => List.all (cent0Words.getD i []) fun wd => bAnd(lettersK 17 wd,
    bAnd(cn (wO wd), bAnd(pm (wO wd), Nat.beq (pc (wO wd) (mainK i)) (pc (mainK i) (wO wd)))))) = true := by
  quickRfl

theorem kFg : allN 2 (fun i => bAnd(lettersK 17 (fgWords.getD i []), bAnd(cn (wO (fgWords.getD i [])),
    bAnd(cn (pinv (wO (fgWords.getD i []))), bAnd(pm (wO (fgWords.getD i [])),
    strictB (pc (cj (wO (fgWords.getD i [])) (mainK (Nat.add i 3))) (mainK (Nat.add i 3))) fun v =>
      bAnd(Nat.beq (pc v v) pid, bIf(Nat.beq v pid, false, true))))))) = true := by quickRfl

theorem kOdd : allN 3 (fun i => bAnd(lettersK 17 (oddData.getD i ([], [], 0, 0, 0)).1,
    bAnd(lettersK 17 (oddData.getD i ([], [], 0, 0, 0)).2.1,
    strictB (wO (oddData.getD i ([], [], 0, 0, 0)).1) fun u =>
    strictB (wO (oddData.getD i ([], [], 0, 0, 0)).2.1) fun v =>
      bAnd(cn u, bAnd(cn v, bAnd(CFSG.KC.O8.ordK 360 9 (mask 9) pid u (oddData.getD i ([], [], 0, 0, 0)).2.2.2.1,
      bAnd(CFSG.KC.O8.ordK 360 9 (mask 9) pid v (oddData.getD i ([], [], 0, 0, 0)).2.2.2.2,
      bAnd(Nat.beq (pc u (mainK i)) (pc (mainK i) u), bAnd(Nat.beq (pc v (mainK i)) (pc (mainK i) v),
        Nat.beq (ppw (pc u v) (oddData.getD i ([], [], 0, 0, 0)).2.2.1) (mainK i)))))))))) = true := by
  quickRfl

end CertificateChecks.KernelO8

end
