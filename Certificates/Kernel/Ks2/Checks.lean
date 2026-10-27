module

public import Certificates.Kernel.CU43Aut.Small
public import Certificates.Kernel.Ks2.Data
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RUKs2Data
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RUKsData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelKs2

open CFSG.EvenSporadicStandard.Fin76b.U16
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim
open CertificateChecks.KernelU43B CertificateChecks.KernelCU43Aut

@[expose] noncomputable def commK (a b : Nat) : Bool := Nat.beq (pc a b) (pc b a)

@[expose] noncomputable def blkS (i : Nat) : Nat := nIf(Nat.beq i 0, 0, nIf(Nat.beq i 1, 4, 20))

@[expose] noncomputable def blkE (i : Nat) : Nat := nIf(Nat.beq i 0, 4, nIf(Nat.beq i 1, 20, 68))

@[expose] noncomputable def xS (i : Nat) : Nat := nIf(Nat.beq i 0, 0, nIf(Nat.beq i 1, 4, 12))

@[expose] noncomputable def xE (i : Nat) : Nat := nIf(Nat.beq i 0, 4, nIf(Nat.beq i 1, 12, 24))

@[expose] noncomputable def pairOf (r : Nat) : Nat := nIf(Nat.blt r 4, 0, nIf(Nat.blt r 12, 1, 2))

@[expose] noncomputable def isV (k : Nat) : Bool :=
  bIf(Nat.beq k 0, true, bIf(Nat.beq k 2, true, bIf(Nat.beq k 5, true, Nat.beq k 7)))

@[expose] noncomputable def wK (i k : Nat) : Nat :=
  nIf(Nat.beq k 2, G2 i, nIf(Nat.beq k 5, G5 i, nIf(Nat.beq k 7, V i, pidn 820 10)))

@[expose] noncomputable def listK (i q : Nat) : Bool :=
  strictB (C q) (fun c => bAnd(cK c, bAnd(inPK c, bAnd(commK c (V i),
    bIf(Nat.blt (Nat.succ q) (blkE i), Nat.blt c (C (Nat.succ q)), true)))))

@[expose] noncomputable def witK (w r k : Nat) : Bool :=
  bAnd(cK w, bAnd(inPK (pc w (TKI k)), commK w r))

@[expose] noncomputable def invT (i q : Nat) : Bool :=
  strictB (pc (C q) (XI i)) (fun y => Nat.beq (pc y y) (pidn 820 10))

@[expose] noncomputable def xCnt (i : Nat) : Nat :=
  foldUp (Nat.sub (blkE i) (blkS i))
    (fun d acc => nIf(invT i (Nat.add (blkS i) d), Nat.succ acc, acc)) 0

@[expose] noncomputable def xK (i n : Nat) : Bool :=
  bAnd(Nat.beq (xCnt i) n, allN (Nat.sub (xE i) (xS i)) (fun d => strictB (Nat.add (xS i) d)
    (fun r => strictB (XL r) (fun q => bAnd(Nat.ble (blkS i) q, bAnd(Nat.blt q (blkE i),
      bAnd(invT i q, bIf(Nat.blt (Nat.succ r) (xE i), Nat.blt q (XL (Nat.succ r)), true))))))))

@[expose] noncomputable def orbW (i q k x : Nat) : Bool :=
  strictB (pc (C q) (wK i k)) (fun h => strictB (XI i) (fun xi =>
    bAnd(Nat.ble (blkS i) q, bAnd(Nat.blt q (blkE i), bAnd(isV k,
      Nat.beq (pc h xi) (pc (pc (C x) xi) h))))))

@[expose] noncomputable def orbK (r : Nat) : Bool := orbW (pairOf r) (OQ r) (OK r) (XL r)

@[expose] noncomputable def xiK (i : Nat) : Bool :=
  strictB (XI i) (fun x => strictB (V i) (fun v => bAnd(cK x, bAnd(Nat.beq (pc x x) (pidn 820 10),
    bAnd(inPK (pc x (TKI 7)), Nat.beq (pc v (pc x v)) x)))))

@[expose] noncomputable def ord8K (y : Nat) : Bool :=
  strictB (pc y y) (fun y2 => strictB (pc y2 y2) (fun y4 =>
    bAnd(Nat.beq (pc y4 y4) (pidn 820 10), bIf(Nat.beq y4 (pidn 820 10), false, true))))

theorem ks2Bind : bindListK 820 10 (Y8 0) y8Arr.toList = true ∧
    bindListK 820 10 (XI 0) (xiArrs[0]!).toList = true ∧
    bindListK 820 10 (XI 1) (xiArrs[1]!).toList = true ∧
    bindListK 820 10 (XI 2) (xiArrs[2]!).toList = true ∧
    bindListK 820 10 (V 0) (ks8Reps[5]!).toList = true ∧
    bindListK 820 10 (V 1) (ks8Reps[6]!).toList = true ∧
    bindListK 820 10 (V 2) (ks8Reps[7]!).toList = true ∧
    bindListK 820 10 (DA 0) d16A.toList = true ∧
    bindListK 820 10 (DB 0) d16B.toList = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> quickRfl

theorem ks2L0 : allN 4 (fun d => listK 0 d) = true := by quickRfl
theorem ks2L1 : allN 16 (fun d => listK 1 (Nat.add 4 d)) = true := by quickRfl
theorem ks2L2 : allN 16 (fun d => listK 2 (Nat.add 20 d)) = true := by quickRfl
theorem ks2L3 : allN 16 (fun d => listK 2 (Nat.add 36 d)) = true := by quickRfl
theorem ks2L4 : allN 16 (fun d => listK 2 (Nat.add 52 d)) = true := by quickRfl

theorem ks2Cos : allN 3 (fun i => strictB (V i) (fun v =>
    bAnd(witK v v 7, bAnd(witK (G2 i) v 2, witK (G5 i) v 5)))) = true := by
  quickRfl

theorem ks2CosU : bAnd(witK (U2 0) (CU43T 6) 2, witK (U5 0) (CU43T 6) 5) = true := by quickRfl

theorem ks2Xi : allN 3 xiK = true := by quickRfl

theorem ks2X : allN 3 (fun i => xK i (Nat.sub (xE i) (xS i))) = true := by quickRfl

theorem ks2Orb : allN 24 orbK = true := by quickRfl

theorem ks2U7 : strictB (Y8 0) (fun y => bAnd(cK y, bAnd(inPK y, bAnd(ord8K y, commK y (CU43T 6))))) =
    true := by
  quickRfl

@[expose] noncomputable def d16K (a b : Nat) : Bool :=
  bAnd(cK a, bAnd(cK b, bAnd(inPK (pc a (TKI 5)), bAnd(inPK (pc b (TKI 5)), bAnd(ord8K a,
    bAnd(Nat.beq (pc b b) (pidn 820 10), bAnd(Nat.beq (pc a (pc b a)) b,
      allN 8 (fun j => bIf(Nat.beq b (KernelCU43Aut.ppow a j), false, true)))))))))

@[expose] noncomputable def comm4K (a b v x : Nat) : Bool :=
  bAnd(commK a v, bAnd(commK b v, bAnd(commK a x, commK b x)))

theorem ks2D16 : strictB (DA 0) (fun a => strictB (DB 0) (fun b =>
    bAnd(d16K a b, comm4K a b (V 2) (XI 2)))) = true := by
  quickRfl

end CertificateChecks.KernelKs2

end
