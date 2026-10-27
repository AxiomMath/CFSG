module

public import Certificates.Kernel.Sporadic.Fi22.Q450106K
public import Certificates.Kernel.Sporadic.Fi22.Perf450108
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Fi22TwoBBlocksCheck
public meta import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Fi22TwoBBlocksCheck
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.B450107

meta def labM : Array (Array Nat) :=
  #[CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Fi22TwoB.labelArr ()]

end CertificateChecks.KernelSpor.B450107

#kmisc_packarrs CertificateChecks.KernelSpor.B450107.LABT CertificateChecks.KernelSpor.B450107.labM 6

namespace CertificateChecks.KernelSpor.B450107

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin
open CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Fi22TwoB
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.Perf450108
open CertificateChecks.KernelSpor.Q450106

@[expose] noncomputable def LAB : Nat := LABT 0

@[expose] noncomputable def labCk (c : Nat) : Bool :=
  strictB LAB (fun lab => allN 351 (fun r => strictB (Nat.add (Nat.mul 351 c) r) (fun p =>
    Nat.beq (labelOf p) (pg 6 (mask 6) lab p))))

@[expose] noncomputable def tauK : Bool :=
  allN 10 (fun k => bAnd(permOK 45 6 (mask 6) (45 * 6) (TK k) (inv45 (TK k)),
    bAnd(cn45 (TK k), lettersK 3 (tauWords.getD k [])))) &&
  allN 3 (fun j => bAnd(cn45 (XY45 j), lettersK 10 (genWords.getD j []))) &&
  allN 3 (fun j => Nat.beq (wordK 45 6 (mask 6) (pidn 45 6) TK (fun k => inv45 (TK k))
    (genWords.getD j [])) (XY45 j))

@[expose] def hd (i : Nat) : Nat := (blocks45.getD i []).headD 0

@[expose] noncomputable def headK : Bool :=
  strictB LAB (fun lab => allN 45 (fun i => bAnd(Nat.blt (hd i) 3510,
    Nat.beq (pg 6 (mask 6) lab (hd i)) i)))

@[expose] noncomputable def extK (τ m : Nat) : Nat :=
  nIf(Nat.blt m (nat_lit 45), pg 6 (mask 6) τ m, nat_lit 45)

@[expose] noncomputable def labK (lab g τ : Nat) : Bool :=
  allN 3510 (fun p => Nat.beq (pg 6 (mask 6) lab (pg 12 (mask 12) g p))
    (extK τ (pg 6 (mask 6) lab p)))

@[expose] noncomputable def fixK (lab g : Nat) : Bool :=
  allN 3510 (fun p => Nat.beq (pg 6 (mask 6) lab (pg 12 (mask 12) g p)) (pg 6 (mask 6) lab p))

@[expose] noncomputable def genK (k : Nat) : Bool :=
  strictB LAB (fun lab => strictB (Q450106.CG k) (fun g => strictB (TK k) (fun τ => labK lab g τ)))

@[expose] noncomputable def qFixK (j : Nat) : Bool :=
  strictB LAB (fun lab => strictB (QD j) (fun g => fixK lab g))

@[expose] noncomputable def tFixK : Bool := strictB LAB (fun lab => strictB T (fun g => fixK lab g))

theorem lab0 : labCk 0 = true := by quickRfl
theorem lab1 : labCk 1 = true := by quickRfl
theorem lab2 : labCk 2 = true := by quickRfl
theorem lab3 : labCk 3 = true := by quickRfl
theorem lab4 : labCk 4 = true := by quickRfl
theorem lab5 : labCk 5 = true := by quickRfl
theorem lab6 : labCk 6 = true := by quickRfl
theorem lab7 : labCk 7 = true := by quickRfl
theorem lab8 : labCk 8 = true := by quickRfl
theorem lab9 : labCk 9 = true := by quickRfl
theorem tau_ok : tauK = true := by quickRfl
theorem head_ok : headK = true := by quickRfl
theorem gen0 : genK 0 = true := by quickRfl
theorem gen1 : genK 1 = true := by quickRfl
theorem gen2 : genK 2 = true := by quickRfl
theorem gen3 : genK 3 = true := by quickRfl
theorem gen4 : genK 4 = true := by quickRfl
theorem gen5 : genK 5 = true := by quickRfl
theorem gen6 : genK 6 = true := by quickRfl
theorem gen7 : genK 7 = true := by quickRfl
theorem gen8 : genK 8 = true := by quickRfl
theorem gen9 : genK 9 = true := by quickRfl
theorem qfix0 : qFixK 0 = true := by quickRfl
theorem qfix1 : qFixK 1 = true := by quickRfl
theorem qfix2 : qFixK 2 = true := by quickRfl
theorem qfix3 : qFixK 3 = true := by quickRfl
theorem qfix4 : qFixK 4 = true := by quickRfl
theorem qfix5 : qFixK 5 = true := by quickRfl
theorem qfix6 : qFixK 6 = true := by quickRfl
theorem qfix7 : qFixK 7 = true := by quickRfl
theorem qfix8 : qFixK 8 = true := by quickRfl
theorem qfix9 : qFixK 9 = true := by quickRfl
theorem tfix : tFixK = true := by quickRfl

end CertificateChecks.KernelSpor.B450107

end
