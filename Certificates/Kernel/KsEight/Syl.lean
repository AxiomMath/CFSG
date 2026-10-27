module

public import Certificates.Kernel.CU43Aut.Syl
public import Certificates.Kernel.KsEight.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelKsEight

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum
open CertificateChecks.KernelU43B CertificateChecks.KernelCU43Aut

@[expose] noncomputable def mulD8 (a b : Nat) : Nat :=
  Nat.add (Nat.mul 4 (Nat.mod (Nat.add (Nat.div a 4) (Nat.div b 4)) 2))
    (Nat.mod (Nat.add (nIf(Nat.beq (Nat.div b 4) 1, Nat.sub 4 (Nat.mod a 4), Nat.mod a 4))
      (Nat.mod b 4)) 4)

@[expose] noncomputable def genLab (l : Nat) : Nat := nIf(Nat.beq l 5, 1, nIf(Nat.beq l 6, 4, 0))

@[expose] noncomputable def inV (k : Nat) : Bool :=
  bIf(Nat.beq k 0, true, bIf(Nat.beq k 2, true, bIf(Nat.beq k 5, true, Nat.beq k 7)))

@[expose] noncomputable def fourK (i : Nat) : Bool :=
  bIf(inV (LB i), bIf(hasBit (LM 0) i, true,
    strictB (pc (TS.T i) (TS.T i)) (fun y => Nat.beq (pc y y) (pidn 820 10))), true)

@[expose] noncomputable def swK (q : Nat) : Bool :=
  strictB (SWI q) (fun t => strictB (SCL q) (fun c => strictB (TS.T t) (fun u =>
    bAnd(Nat.blt t 1024, bAnd(inV (LB t), bAnd(Nat.blt c 14,
      Nat.beq (pc u (TS.T (LS (CRQ c)))) (pc (TS.T (LS q)) u)))))))

@[expose] noncomputable def pwK (c : Nat) : Bool :=
  strictB (CRQ c) (fun q => strictB (CJP c) (fun j => strictB (GW c) (fun g =>
    bAnd(Nat.blt q 224, bAnd(Nat.blt j 8, bAnd(cK g, bAnd(inPK g,
      Nat.beq (pc g (RK j)) (pc (TS.T (LS q)) g))))))))

theorem ksLab : bAnd(Nat.beq (LB 0) 0, allN 1023 (fun d => strictB (Nat.succ d) (fun i =>
    Nat.beq (LB i) (mulD8 (LB (parOf TS.PL i)) (genLab (labOf TS.PL i)))))) = true := by
  quickRfl

theorem ksCnt : Nat.beq (foldUp 1024 (fun i acc => nIf(inV (LB i), Nat.succ acc, acc)) 0) 512 = true := by
  quickRfl

theorem ksLS : allN 224 (fun q => strictB (LS q) (fun i => bAnd(Nat.blt i 1024, bAnd(inV (LB i),
    bIf(Nat.blt q 223, Nat.blt i (LS (Nat.succ q)), true))))) = true := by
  quickRfl

theorem ksLM : Nat.beq (foldUp 224 (fun q M => Nat.lor M (Nat.shiftLeft 1 (LS q))) 0) (LM 0) = true := by
  quickRfl

theorem ksF0 : allN 128 fourK = true := by quickRfl
theorem ksF1 : allN 128 (fun d => fourK (Nat.add 128 d)) = true := by quickRfl
theorem ksF2 : allN 128 (fun d => fourK (Nat.add 256 d)) = true := by quickRfl
theorem ksF3 : allN 128 (fun d => fourK (Nat.add 384 d)) = true := by quickRfl
theorem ksF4 : allN 128 (fun d => fourK (Nat.add 512 d)) = true := by quickRfl
theorem ksF5 : allN 128 (fun d => fourK (Nat.add 640 d)) = true := by quickRfl
theorem ksF6 : allN 128 (fun d => fourK (Nat.add 768 d)) = true := by quickRfl
theorem ksF7 : allN 128 (fun d => fourK (Nat.add 896 d)) = true := by quickRfl

theorem ksSW0 : allN 32 swK = true := by quickRfl
theorem ksSW1 : allN 32 (fun d => swK (Nat.add 32 d)) = true := by quickRfl
theorem ksSW2 : allN 32 (fun d => swK (Nat.add 64 d)) = true := by quickRfl
theorem ksSW3 : allN 32 (fun d => swK (Nat.add 96 d)) = true := by quickRfl
theorem ksSW4 : allN 32 (fun d => swK (Nat.add 128 d)) = true := by quickRfl
theorem ksSW5 : allN 32 (fun d => swK (Nat.add 160 d)) = true := by quickRfl
theorem ksSW6 : allN 32 (fun d => swK (Nat.add 192 d)) = true := by quickRfl

theorem ksPW : allN 14 pwK = true := by quickRfl

theorem ksC2 : bAnd(Nat.beq (foldUp 14 (fun c acc => nIf(Nat.beq (CJP c) 2, Nat.succ acc, acc)) 0) 1,
    Nat.beq (foldUp 224 (fun q acc => nIf(Nat.beq (CJP (SCL q)) 2, Nat.succ acc, acc)) 0) 32) = true := by
  quickRfl

end CertificateChecks.KernelKsEight

end
