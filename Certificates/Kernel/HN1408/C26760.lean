module

public import Certificates.Kernel.HN1408.Words
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408

open CFSG.KC.Enum CFSG.KS CFSG.KS.MulH CFSG.EvenSporadicStandard.HNRecog
open CFSG.EvenSporadicStandard.TwoHS CFSG.Sporadic.Recognition.HSMultiplier

@[expose] noncomputable def X8 (i : Fin 6) : Nat := H8.F i.val

@[expose] noncomputable def EV8 (wd : List (Fin 6 × Bool)) : Nat :=
  wd.foldl (fun acc l => pc acc (cond l.2 (X8 l.1) (X8 l.1))) idK

@[expose] noncomputable def V8 : Nat := H8.F 6

theorem rel26760 : hsRels.all (fun r => (List.finRange 6).all fun i => commP (X8 i) (EV8 r)) =
    true := by
  quickRfl

theorem comm26760 : (List.finRange 6).all (fun i => Nat.beq (EV8 (hsCommWord i)) (X8 i)) = true := by
  quickRfl

theorem sigma26760 : (List.finRange 6).all (fun i =>
    Nat.beq (pc (pc V8 (X8 i)) V8) (WK (sigWords.getD i.val []))) = true := by
  quickRfl

theorem central26760 : bAnd(involK (EV8 h1408R25),
    allN 1408 (fun p => (Nat.beq (pt (EV8 h1408R25) p) p).not)) = true := by
  quickRfl

theorem block26760 : bAnd(allN 6 (fun j => halvesK (H8.F j)),
    bAnd(allN 704 (fun k => bAnd(Nat.beq (pt V8 k) (704 + k), Nat.beq (pt V8 (704 + k)) k)),
      Nat.beq (pc V8 V8) idK)) = true := by
  quickRfl

theorem neg26760 : bAnd((commP (X8 0) (X8 1)).not,
    bAnd((Nat.beq (EV8 (hsCommWord 0)) (X8 1)).not,
    bAnd((Nat.beq (pc (pc V8 (X8 0)) V8) (WK (sigWords.getD 1 []))).not,
    bAnd((halvesK V8).not, (allN 1408 (fun p => (Nat.beq (pt (X8 0) p) p).not)).not)))) = true := by
  quickRfl

end CFSG.KD.HN1408

end
