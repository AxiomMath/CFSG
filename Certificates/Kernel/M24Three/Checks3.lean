module

public import Certificates.Kernel.M24Three.Checks2
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThreeCore.M24Check
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CFSG.KD.M24Three

open CFSG.KC.Enum CFSG.KS CFSG.AGLEmbeddingD2.Wilson.ThreeCore.M24

@[expose] def codeZ (l : ℤ) : Nat :=
  if l = 1 then 0 else if l = 2 then 1 else if l = -1 then 2 else 3

@[expose] def codeN (w : List ℤ) : Nat :=
  @List.rec ℤ (fun _ => Nat) 0 (fun l _ acc => Nat.add (codeZ l) (Nat.mul 4 acc)) w

@[expose] def lenN (w : List ℤ) : Nat :=
  @List.rec ℤ (fun _ => Nat) 0 (fun _ _ acc => Nat.succ acc) w

@[expose] noncomputable def wdK (j : Nat) (w : List ℤ) : Bool :=
  bAnd(Nat.beq (WL j) (codeN w), Nat.beq (LN j) (lenN w))

theorem ch12613_wd : bAnd(wdK 0 xW, bAnd(wdK 1 x2W, bAnd(wdK 12 ra0W, bAnd(wdK 13 ra1W,
    bAnd(wdK 14 ra2W, bAnd(wdK 15 ha0W, bAnd(wdK 16 ha1W, bAnd(wdK 17 ha2W, bAnd(wdK 18 rb0W,
    bAnd(wdK 19 rb1W, bAnd(wdK 20 rb2W, bAnd(wdK 21 hb0W, bAnd(wdK 22 hb1W,
    wdK 23 hb2W))))))))))))) = true := by
  quickRfl

theorem ch12613_wd2 : bAnd(wdK 2 s1W, bAnd(wdK 3 s2W, bAnd(wdK 4 ca1W, bAnd(wdK 5 ca2W,
    bAnd(wdK 6 cb1W, wdK 7 cb2W))))) = true := by
  quickRfl

@[expose] noncomputable def pw5 (z : Nat) : Nat := pc z (pc z (pc z (pc z z)))

@[expose] noncomputable def ord3K (y : Nat) : Bool :=
  bIf(Nat.beq y idK, false, Nat.beq (pc y (pc y y)) idK)

@[expose] noncomputable def wit3K (r h e : Nat) : Bool :=
  strictB (pc (EL r) (pc (EL h) (pc (EL r) (EI h)))) fun z =>
    bIf(Nat.beq e 0, ord3K z, ord3K (pw5 z))

theorem ch12613_wit3 : bAnd(wit3K 12 15 0, bAnd(wit3K 13 16 0, bAnd(wit3K 14 17 1,
    bAnd(wit3K 18 21 0, bAnd(wit3K 19 22 0, wit3K 20 23 0))))) = true := by
  quickRfl

end CFSG.KD.M24Three

end
