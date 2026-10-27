module

public import Certificates.Kernel.OmegaEight.Roots127K
public import Certificates.Kernel.OmegaEight.E4O8NbrK
public import Certificates.Kernel.OmegaEight.E4O8MembersData
public import Certificates.Kernel.OmegaEight.Quat125Data
public import Certificates.Data.Kernel.O8.QuatO8
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.EachTrue

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8.Q125

open CFSG.KC.Enum CFSG.KC.O8 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.EvenSmallLie.OmegaEight
open CertificateChecks.KernelO8

@[expose] noncomputable def q125Ty (k : Nat) : Nat :=
  nIf(Nat.beq k (nat_lit 10), nat_lit 1, strictN (r127Ty k) fun t =>
    nIf(Nat.beq t (nat_lit 1), nat_lit 1, nIf(Nat.beq t (nat_lit 2), nat_lit 1, nat_lit 0)))

@[expose] def q125WW : List (List Int) :=
  [CFSG.ClassicalInvolution.Q3.TL4.E4O8.cw 0 [1, 1], CFSG.ClassicalInvolution.Q3.TL4.E4O8.cw 0 [2]]

@[expose] noncomputable def q125Pairs (lo hi : Nat) : Bool :=
  strictB (ycK saCodes yIdxT) fun YP =>
  strictB (wO (q125WW.getD 0 [])) fun c0 => strictB (wO (q125WW.getD 1 [])) fun c1 =>
  strictB (r127M c0) fun C0 => strictB (r127M (pinv c0)) fun D0 =>
  strictB (r127M c1) fun C1 => strictB (r127M (pinv c1)) fun D1 =>
  strictB (saAtK saCodes wit37) fun C2 => strictB (saAtK saCodes wit37i) fun D2 =>
    allRoots roots (pairsOK saCodes saParT saLabT YP lists C0 D0 C1 D1 C2 D2 roots lo hi)

@[expose] noncomputable def q125MW (j : Nat) : List Int :=
  CFSG.ClassicalInvolution.Q3.TL4.E4O8.toWord (e4MR.getD j ([], (0, 0))).1

@[expose] noncomputable def cjI (c ci x : Nat) : Nat := pc (pc c x) ci

@[expose] noncomputable def q125PL : List (List Nat) :=
  [e4L, (fun w => e4L.map (cjI w (pinv w))) (wO (q125MW 1)),
    (fun w => e4L.map (cjI w (pinv w))) (wO (q125MW 3)),
    (fun w => e4L.map (cjI w (pinv w))) (wO (q125MW 4))]

@[expose] noncomputable def q125At (L : List (List Nat)) (j : Nat) : List Nat := L.getD j []

theorem kRoots125 : strictB (ycK saCodes yIdxT) (fun YP => strictB (tyLK YP q125Ty 1) fun L1 =>
    Nat.beq (roots0K saCodes saParT saLabT L1) (recsJ roots)) = true := by quickRfl

theorem kClass125 : strictB (ycK saCodes yIdxT) (fun YP => strictB (repsJ roots) fun CR =>
    allRoots roots (rootOK saCodes saParT saLabT YP CR)) = true := by quickRfl

theorem kPairs125_0 : q125Pairs 0 2048 = true := by quickRfl
theorem kPairs125_1 : q125Pairs 2048 4096 = true := by quickRfl
theorem kPairs125_2 : q125Pairs 4096 6144 = true := by quickRfl
theorem kPairs125_3 : q125Pairs 6144 8192 = true := by quickRfl

theorem kWit125 : bAnd(List.all q125WW (fun w => bAnd(lettersK 17 w, strictB (wO w) fun c =>
    strictB (pinv c) fun ci => bAnd(cn c, bAnd(pm c, bAnd(cn ci,
    bAnd(Nat.beq (pc c (mainK 0)) (pc (mainK 0) c),
    bAnd(actsK NSP NIP c (r127M c), bAnd(actsK NSP NIP ci (r127M ci),
      Nat.beq (matMulK (r127M c) (r127M ci)) idK)))))))),
    bAnd(Nat.blt wit37 8192, bAnd(Nat.blt wit37i 8192,
    bAnd(Nat.beq (parK saParT saLabT wit37) 0,
    bAnd(Nat.beq (matMulK (saAtK saCodes wit37) (saAtK saCodes wit37i)) idK,
      strictB (saAtK saCodes (ix13 yIdxT 37)) fun y =>
        Nat.beq (matMulK (saAtK saCodes wit37) y) (matMulK y (saAtK saCodes wit37))))))) = true := by
  quickRfl

theorem kLists125 : bAnd(Nat.beq lists.length 4, bAnd(Nat.beq g0perm.length 3,
    bAnd(allN 4 (fun j => bAnd(Nat.beq (q125At lists j).length 8,
      allN 8 fun e => strictB ((q125At lists j).getD e 0) fun i => bAnd(Nat.blt i 8192,
        actsK NSP NIP ((q125At q125PL j).getD e 0) (saAtK saCodes i)))),
    allN 3 (fun l => strictB (wO (CFSG.ClassicalInvolution.Q3.TL4.E4O8.cw 0 [Int.ofNat (l + 1)]))
      fun g => strictB (pinv g) fun gi => allN 4 fun j =>
        strictB ((g0perm.getD l []).getD j 0) fun j' => bAnd(Nat.blt j' 4,
          (q125At q125PL j).all fun x => e4Mem (q125At q125PL j') (cjI g gi x)))))) = true := by
  quickRfl

theorem kSwap125 : swTie (fun r => AP.S r) swaps = true := by quickRfl

theorem kWTie125 : wTieK RT e4MR = true := by quickRfl

theorem kConn125 : allN 8 (fun r => bIf(Nat.beq r 2, e4Norms e4L e4U om0V (AP.S 2),
    e4Norms e4L e4U om0V (cj (AP.S r) om0V))) = true := by quickRfl

theorem kWalk125 : strictB e4U (fun U => strictB om0V fun V => strictB (fixMK U V 360) fun F =>
    strictB (gtK (fun l => AP.S l) 8) fun GT => allN 6300 (walkOK RT GT F U V)) = true := by
  quickRfl

@[expose] noncomputable def q125Mem (s : Nat) : Bool :=
  strictB (mainK 0) fun X0 =>
    allBlk (Nat.mul (nat_lit 512) s) (fun k => bIf(Nat.blt k (nat_lit 6300),
      bAnd(memRowK RT MT swaps (fixMK e4U om0V (nat_lit 240)) X0 k, sortAt RT MT k), true))
      (nat_lit 512)

#kc_each CertificateChecks.KernelO8.Q125 ch125m q125Mem 0 13

end CertificateChecks.KernelO8.Q125

end
