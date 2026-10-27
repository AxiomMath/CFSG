module

public import Certificates.Data.Kernel.O8.SA
public import Certificates.Data.Kernel.Spor.Prim
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeData
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeSylowData
public import Certificates.Kernel.OmegaEight.SA3009Data
public import Certificates.Kernel.OmegaEight.Chains3009
public import Certificates.Kernel.OmegaEight.AutChainAP
public import Certificates.Kernel.OmegaEight.AutChainOmP
public import Certificates.Kernel.OmegaEight.NatData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8

open CFSG.KC.Enum CFSG.KC.O8 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.EvenSmallLie.OmegaEight

@[expose] def cw : List (List Nat) :=
  [[]] ++ (List.range 5).map (fun a => [a]) ++
    (List.range 5).flatMap (fun a => (List.range 5).map fun b => [a, b]) ++
    (List.range 5).flatMap (fun a => (List.range 5).flatMap fun b =>
      (List.range 5).map fun c => [a, b, c])

@[expose] noncomputable def pc (p q : Nat) : Nat := pcomp 360 9 (mask 9) p q

@[expose] noncomputable def pinv (p : Nat) : Nat := pinvS 360 9 (mask 9) p

@[expose] noncomputable def cn (p : Nat) : Bool := canonK 360 9 (mask 9) (360 * 9) p

@[expose] noncomputable def wO (wd : List Int) : Nat := wordK 360 9 (mask 9) (pidn 360 9) OmP.S OmP.SI wd

@[expose] noncomputable def wA (wd : List Int) : Nat := wordK 360 9 (mask 9) (pidn 360 9) AQ.S AQ.SI wd

@[expose] noncomputable def wS (wd : List Int) : Nat := wordK 360 9 (mask 9) (pidn 360 9) SY.S SY.SI wd

@[expose] noncomputable def cj (c x : Nat) : Nat := pc (pc c x) (pinv c)

@[expose] def rgLen (j : Nat) : Nat := (cent0Words.getD (repTypes.getD j 0) []).length

@[expose] noncomputable def rgK (j l : Nat) : Nat :=
  nIf(Nat.blt l (rgLen j),
    cj (wA (conjWords.getD j [])) (wO ((cent0Words.getD (repTypes.getD j 0) []).getD l [])),
    wS (repWords.getD j []))

@[expose] noncomputable def rgOK (j l : Nat) : Bool :=
  bAnd(lettersK (nat_lit 18) (conjWords.getD j []),
  bAnd(lettersK (nat_lit 17) ((cent0Words.getD (repTypes.getD j 0) []).getD l []),
  bAnd(cn (wA (conjWords.getD j [])),
  bAnd(cn (pinv (wA (conjWords.getD j []))),
  bAnd(permOK 360 9 (mask 9) (360 * 9) (wA (conjWords.getD j [])) (pinv (wA (conjWords.getD j []))),
  bAnd(cn (wO ((cent0Words.getD (repTypes.getD j 0) []).getD l [])),
  bAnd(cn (wS (repWords.getD j [])),
  bAnd(permOK 360 9 (mask 9) (360 * 9) (rgK j l) (pinv (rgK j l)),
  bAnd(actsK NSP NIP (rgK j l) (saAtK rgT (Nat.add (Nat.mul (nat_lit 5) j) l)),
    actsK NSP NIP (pinv (rgK j l)) (saAtK rgInvT (Nat.add (Nat.mul (nat_lit 5) j) l)))))))))))

@[expose] noncomputable def rgJ (j : Nat) : Bool :=
  allN (nat_lit 5) fun l => bIf(Nat.ble l (rgLen j), rgOK j l, true)

@[expose] noncomputable def fiveJ (j : Nat) : Bool := allN (nat_lit 8192) (fiveAt saCodes yIdxT rgT rgInvT cw j)

theorem kGenSY : allN 5 (fun j => Nat.beq (SY.S j) (AP.S (sylowIdx.getD j 0))) = true := by quickRfl
theorem kGenAQ : allN 10 (fun j => Nat.beq (AQ.S j) (AP.S j)) = true := by quickRfl

theorem kId :Nat.beq (saAtK saCodes 0) idK = true := by quickRfl
theorem kTree : allN 8192 (saTreeAt saMulT saParT saLabT) = true := by quickRfl
theorem kSortSA : allN 8192 (saSortAt saCodes saSP saSPI) = true := by quickRfl

theorem kClosed0 : allBlk 0 (saClosedAt saCodes saMulT saGenT) 1024 = true := by quickRfl
theorem kClosed1 : allBlk 1024 (saClosedAt saCodes saMulT saGenT) 1024 = true := by quickRfl
theorem kClosed2 : allBlk 2048 (saClosedAt saCodes saMulT saGenT) 1024 = true := by quickRfl
theorem kClosed3 : allBlk 3072 (saClosedAt saCodes saMulT saGenT) 1024 = true := by quickRfl
theorem kClosed4 : allBlk 4096 (saClosedAt saCodes saMulT saGenT) 1024 = true := by quickRfl
theorem kClosed5 : allBlk 5120 (saClosedAt saCodes saMulT saGenT) 1024 = true := by quickRfl
theorem kClosed6 : allBlk 6144 (saClosedAt saCodes saMulT saGenT) 1024 = true := by quickRfl
theorem kClosed7 : allBlk 7168 (saClosedAt saCodes saMulT saGenT) 1024 = true := by quickRfl

theorem kInvol0 : allBlk 0 (involAt saCodes yIdxT invWT) 2048 = true := by quickRfl
theorem kInvol1 : allBlk 2048 (involAt saCodes yIdxT invWT) 2048 = true := by quickRfl
theorem kInvol2 : allBlk 4096 (involAt saCodes yIdxT invWT) 2048 = true := by quickRfl
theorem kInvol3 : allBlk 6144 (involAt saCodes yIdxT invWT) 2048 = true := by quickRfl

theorem kFive0 : allBlk 0 fiveJ 4 = true := by quickRfl
theorem kFive1 : allBlk 4 fiveJ 4 = true := by quickRfl
theorem kFive2 : allBlk 8 fiveJ 4 = true := by quickRfl
theorem kFive3 : allBlk 12 fiveJ 4 = true := by quickRfl
theorem kFive4 : allBlk 16 fiveJ 4 = true := by quickRfl
theorem kFive5 : allBlk 20 fiveJ 4 = true := by quickRfl
theorem kFive6 : allBlk 24 fiveJ 4 = true := by quickRfl
theorem kFive7 : allBlk 28 fiveJ 4 = true := by quickRfl
theorem kFive8 : allBlk 32 fiveJ 4 = true := by quickRfl
theorem kFive9 : allBlk 36 fiveJ 2 = true := by quickRfl

theorem kGens : allN 5 (fun l => bAnd(Nat.blt (ix13 saGenT l) 8192,
    actsK NSP NIP (AP.S (sylowIdx.getD l 0)) (saAtK saCodes (ix13 saGenT l)))) = true := by
  quickRfl

theorem kReps : allN 38 (fun j => bAnd(Nat.blt (ix13 yIdxT j) 8192,
    bAnd(lettersK 8 (repWords.getD j []), bAnd(cn (wS (repWords.getD j [])),
    actsK NSP NIP (wS (repWords.getD j [])) (saAtK saCodes (ix13 yIdxT j)))))) = true := by
  quickRfl

theorem kRg0 : allBlk 0 rgJ 8 = true := by quickRfl
theorem kRg1 : allBlk 8 rgJ 8 = true := by quickRfl
theorem kRg2 : allBlk 16 rgJ 8 = true := by quickRfl
theorem kRg3 : allBlk 24 rgJ 8 = true := by quickRfl
theorem kRg4 : allBlk 32 rgJ 6 = true := by quickRfl

end CertificateChecks.KernelO8

end
