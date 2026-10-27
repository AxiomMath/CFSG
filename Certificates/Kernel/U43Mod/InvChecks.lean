module

public import Certificates.Data.Kernel.U43Mod.InvDefs
public import Certificates.Kernel.U43Mod.InvData
public import Certificates.Kernel.U43Mod.Checks
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43InvData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU43Inv

open CFSG.KC.Enum CFSG.KC.U43Inv CertificateChecks.KernelU43Mod
open CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43Inv

@[expose] noncomputable def LP (l q : Nat) : Nat :=
  nIf(Nat.beq l (nat_lit 0), GA (nat_lit 0) q, nIf(Nat.beq l (nat_lit 1), GA (nat_lit 1) q,
    nIf(Nat.beq l (nat_lit 2), GAi (nat_lit 0) q, GAi (nat_lit 1) q)))

@[expose] noncomputable def GkH (l q : Nat) : Nat := pg (nat_lit 10) (nat_lit 1023) (LT l) q

@[expose] noncomputable def GrH (l q : Nat) : Nat :=
  pg (nat_lit 10) (nat_lit 1023) (LT (Nat.xor l (nat_lit 1))) q

@[expose] noncomputable def EH (k q : Nat) : Nat := eW HR GrH (nat_lit 32) k q

@[expose] noncomputable def EHi (k q : Nat) : Nat := eWi HR GkH (nat_lit 32) k q

@[expose] noncomputable def pIdx (j : Nat) : Nat := pGenIdx.getD j (nat_lit 0)

@[expose] noncomputable def GkP (l q : Nat) : Nat :=
  nIf(Nat.beq (Nat.land l (nat_lit 1)) (nat_lit 0), EHi (pIdx (Nat.shiftRight l (nat_lit 1))) q,
    EH (pIdx (Nat.shiftRight l (nat_lit 1))) q)

@[expose] noncomputable def GrP (l q : Nat) : Nat :=
  nIf(Nat.beq (Nat.land l (nat_lit 1)) (nat_lit 0), EH (pIdx (Nat.shiftRight l (nat_lit 1))) q,
    EHi (pIdx (Nat.shiftRight l (nat_lit 1))) q)

@[expose] noncomputable def gensRec (_ : Nat) (w : List Nat) : Bool :=
  base3 (fun q => mwv LP w (GA (nat_lit 0) q)) (fun q => GA (nat_lit 0) (mwv LP w q))

@[expose] noncomputable def lRec (j : Nat) (w : List Nat) : Bool :=
  allN (nat_lit 820) fun q =>
    strictB (pg (nat_lit 10) (nat_lit 1023) (LT (Nat.succ (Nat.shiftLeft j (nat_lit 1)))) q) fun y =>
      bAnd(Nat.beq y (mwv LP w q),
        Nat.beq (pg (nat_lit 10) (nat_lit 1023) (LT (Nat.shiftLeft j (nat_lit 1))) y) q)

theorem kGens : lwalk gensRec (nat_lit 6) hGenWords (nat_lit 0) = true := by quickRfl

theorem kL : lwalk lRec (nat_lit 6) hGenWords (nat_lit 0) = true := by quickRfl

theorem kHpar : fldsAre HR kpar (nat_lit 1152) hPar.toList = true := by quickRfl

theorem kHlab : fldsAre HR klab (nat_lit 1152) hLab.toList = true := by quickRfl

theorem kHtree : kTree HR (nat_lit 1152) (nat_lit 12) GkH = true := by quickRfl

theorem kHclos : kClos HR (nat_lit 1152) (nat_lit 12) GkH hTbl.toList = true := by quickRfl

theorem kHord : kOrd HR (nat_lit 1152) HO = true := by quickRfl

theorem kPpar : fldsAre PR kpar (nat_lit 128) pPar.toList = true := by quickRfl

theorem kPlab : fldsAre PR klab (nat_lit 128) pLab.toList = true := by quickRfl

theorem kPtree : kTree PR (nat_lit 128) (nat_lit 6) GkP = true := by quickRfl

theorem kPclos : kClos PR (nat_lit 128) (nat_lit 6) GkP pTbl.toList = true := by quickRfl

theorem kPord : kOrd PR (nat_lit 128) PO = true := by quickRfl

theorem kCpar : fldsAre CR cpar (nat_lit 2835) cPar.toList = true := by quickRfl

theorem kClab : fldsAre CR clab (nat_lit 2835) cLab.toList = true := by quickRfl

theorem kCtree : cTree CR (nat_lit 2835) LP = true := by quickRfl

theorem kCfix : cFix CR (GA (nat_lit 0)) = true := by quickRfl

theorem kCord : cOrd CR (nat_lit 2835) CO = true := by quickRfl

theorem kF2 : f2All EH EHi (GA (nat_lit 0)) FR (nat_lit 1152) f2Wit.toList = true := by quickRfl

theorem kG0 : g0Chk LP (GA (nat_lit 0)) g0Word (MR (nat_lit 0)) = true := by quickRfl

end CertificateChecks.KernelU43Inv

end
