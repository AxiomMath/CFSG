module

public import Certificates.Kernel.Sporadic.OddCore.SuzBtTD
public import Certificates.Kernel.Sporadic.OddCore.SuzBtZD
public import Certificates.Kernel.Sporadic.OddCore.SuzBtFD
public import Certificates.Data.Kernel.Spor.BTupI
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzBtFF

open CFSG.KC.Enum CFSG.KS CFSG.KS.BTup CertificateChecks.KernelSpor

@[expose] noncomputable def mulT (a q : Nat) : Nat := btMul 4 SuzBtT0.R SuzBtT0Z.RT a q

@[expose] noncomputable def czT (i : Nat) : Bool :=
  allN 4 (fun j => Nat.beq (btPos SuzBtT0.POS 4 i j) (btPos SuzBtT0Z.RT 4 i j))

@[expose] noncomputable def inKT (cnt : Nat) (KL : Nat → Nat) (i : Nat) : Bool :=
  strictB (btKey 33 (mask 33) SuzBtT0.K i) (fun x =>
    Bool.not (allN cnt (fun p => Bool.not (Nat.beq x (btKey 33 (mask 33) KL p)))))

@[expose] noncomputable def inLT (i : Nat) : Bool := inKT SuzBtL1.cnt SuzBtL1.K i

@[expose] noncomputable def inMT (i : Nat) : Bool := inKT SuzBtM21.cnt SuzBtM21.K i

@[expose] noncomputable def ncT (i : Nat) : Bool := bAnd(bIf(inLT i, true, inMT i), Bool.not (czT i))

@[expose] noncomputable def cenT (i : Nat) : Nat :=
  btCntN 64 (fun j => Nat.beq (mulT i j) (mulT j i))

theorem kM21Hd : btHdK SuzBtM21.cnt = true := by quickRfl

theorem kM21Cnt : SuzBtM21.cnt = 16 := by decide

theorem kM21Sl : btSlK 1782 11 (mask 11) 3 33 (mask 33) 4 SuzBtM21.cnt SuzBtM21.B SuzBtM21.G
    SuzBtM21.K SuzBtM21.R SuzBtM21.POS 0 16 = true := by quickRfl

theorem kKHd : btHdK SuzBtK.cnt = true := by quickRfl

theorem kKCnt : SuzBtK.cnt = 4 := by decide

theorem kKSl : btSlK 1782 11 (mask 11) 3 33 (mask 33) 2 SuzBtK.cnt SuzBtK.B SuzBtK.G
    SuzBtK.K SuzBtK.R SuzBtK.POS 0 4 = true := by quickRfl

theorem kKL : allN SuzBtK.cnt (fun s => bIf(Nat.beq (btDep (btRec SuzBtK.R s)) 0, true,
    allN SuzBtL1.cnt (fun p => Bool.not (Nat.beq (btKey 33 (mask 33) SuzBtK.K s)
      (btKey 33 (mask 33) SuzBtL1.K p))))) = true := by quickRfl

theorem kZ : Nat.beq (btCntN 64 czT) 4 = true := by quickRfl

theorem kLM : allN 64 (fun i => bIf(czT i, bAnd(inLT i, inMT i),
    Bool.not (bAnd(inLT i, inMT i)))) = true := by quickRfl

theorem kInv : allN 64 (fun i => bIf(bAnd(Bool.not (Nat.beq (btDep (btRec SuzBtT0.R i)) 0),
    Nat.beq (btDep (btRec SuzBtT0.R (mulT i i))) 0), bIf(inLT i, true, inMT i), true)) = true := by
  quickRfl

theorem kNC : allN 64 (fun i => bIf(bAnd(inLT i, Bool.not (czT i)),
    allN 64 (fun j => bIf(bAnd(inMT j, Bool.not (czT j)),
      Bool.not (Nat.beq (mulT i j) (mulT j i)), true)), true)) = true := by quickRfl

theorem kCen : allN 64 (fun i => bIf(ncT i, Nat.beq (cenT i) 16, true)) = true := by quickRfl

theorem kSq : allN 64 (fun i => czT (mulT i i)) = true := by quickRfl

theorem kLT : allN 4 (fun j => Bool.not (allN 64 (fun q => Bool.not (btMov 11 (mask 11) 3
    (SuzBtL1.G j) SuzBtT0.B (btKey 33 (mask 33) SuzBtT0.K q))))) = true := by quickRfl

theorem kMT : allN 4 (fun j => Bool.not (allN 64 (fun q => Bool.not (btMov 11 (mask 11) 3
    (SuzBtM21.G j) SuzBtT0.B (btKey 33 (mask 33) SuzBtT0.K q))))) = true := by quickRfl

end CertificateChecks.KernelSpor.SuzBtFF

end
