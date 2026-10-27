module

public import Certificates.Kernel.Fi22Syl.ChainData
public import Certificates.Data.Kernel.Fi22.Syl
public import Certificates.Data.Kernel.Fi22.Cent
public import Certificates.Data.Kernel.Spor.PChain

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi22S

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KS.TBfs CFSG.KS.PC CFSG.KS.Fi22S CFSG.KS.Fi22Cent

@[expose] noncomputable def BS (i : Nat) : Nat := List.getD [0, 3] i (nat_lit 0)

@[expose] noncomputable def lvSel (fs : List (Nat → Nat)) (i : Nat) : Nat → Nat :=
  List.getD fs i fun _ => nat_lit 0
@[expose] noncomputable def PTSS : Nat → Nat → Nat := lvSel [ST0.PTS, ST1.PTS]
@[expose] noncomputable def POSS : Nat → Nat → Nat := lvSel [ST0.POS, ST1.POS]
@[expose] noncomputable def PARS : Nat → Nat → Nat := lvSel [ST0.PAR, ST1.PAR]
@[expose] noncomputable def LABS : Nat → Nat → Nat := lvSel [ST0.LAB, ST1.LAB]
@[expose] noncomputable def TIS : Nat → Nat → Nat := lvSel [ST0.TI, ST1.TI]
@[expose] noncomputable def CNTS (i : Nat) : Nat := List.getD [ST0.cnt, ST1.cnt] i (nat_lit 0)

@[expose] noncomputable def QL : List Nat := [0, 1, 3, 6, 11, 17, 28, 44, 66, 103, 155, 238, 362]

@[expose] noncomputable def QB (i : Nat) : Nat := List.getD [0, 2] i (nat_lit 0)

@[expose] noncomputable def swL : List (List Nat) := [
  [18, 24, 10, 28, 12],
  [8, 6, 24, 7, 25, 9, 11, 18, 30, 12, 26, 22],
  [6, 11, 12, 6, 11, 25, 16, 8, 19, 30, 12, 22],
  [20, 18, 3, 30, 18, 6, 11, 12, 25, 8, 14, 22, 16],
  [20, 18, 3, 27, 7, 20, 11, 7, 12, 8, 30, 9, 25, 31, 12, 27, 16],
  [20, 18, 3, 7, 0, 26, 8, 28, 19, 26, 22, 16],
  [20, 18, 3, 7, 0, 11, 31, 8, 10, 25, 28, 19, 31, 23],
  [14, 2, 2, 19, 28, 7, 0, 12, 8, 30, 8, 25, 28, 19, 30, 23, 16],
  [16, 7, 22, 2, 2, 19, 7, 12, 6, 10, 19, 30, 9, 28, 24, 14, 26, 22, 16],
  [23, 16, 2, 8, 3, 26, 7, 20, 6, 0, 18, 28, 9, 16, 28, 30, 26, 23],
  [12, 24, 3, 14, 10, 6, 6, 10, 18, 24, 10, 24, 28, 18, 22, 16]]

@[expose] noncomputable def swS (j : Nat) : Bool := swChk j (List.getD swL j [])

@[expose] noncomputable def invSK : Bool := invK LSK (nat_lit 3510) (nat_lit 22)

@[expose] noncomputable def hdK : Bool :=
  allN (nat_lit 2) fun i => tbfsHdK (nat_lit 3510) (BS i) (CNTS i) (PTSS i) (POSS i) (PARS i) (LABS i)

@[expose] noncomputable def ptSl (i c : Nat) : Bool :=
  tbfsSlK (nat_lit 3510) (CNTS i) (lvK LSK BS (nat_lit 22) i).length LSK (lvAt LSK BS (nat_lit 22) i)
    (PTSS i) (POSS i) (PARS i) (LABS i) (TIS i) (Nat.mul c (nat_lit 64)) (nat_lit 64)

@[expose] noncomputable def t0Sl (c : Nat) : Bool := ptSl (nat_lit 0) c
@[expose] noncomputable def t1K : Bool := bAnd(ptSl (nat_lit 1) (nat_lit 0), ptSl (nat_lit 1) (nat_lit 1))

@[expose] noncomputable def sizesK : Bool :=
  bAnd(Nat.beq ST0.cnt (nat_lit 1024), Nat.beq ST1.cnt (nat_lit 128))

@[expose] noncomputable def sch0Sl (c : Nat) : Bool :=
  schSlK LSK BS (nat_lit 22) PTSS POSS PARS LABS CNTS QB QL (nat_lit 2) (nat_lit 0)
    (Nat.mul c (nat_lit 16)) (nat_lit 16)

@[expose] noncomputable def sch1K : Bool :=
  schSlK LSK BS (nat_lit 22) PTSS POSS PARS LABS CNTS QB QL (nat_lit 2) (nat_lit 1) (nat_lit 0)
    (nat_lit 128)

@[expose] noncomputable def termSK : Bool := termK LSK BS (nat_lit 22) (nat_lit 2) QL

@[expose] noncomputable def wPF (i f : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ x => x)
    (fun _ ih k x => Bool.rec (motive := fun _ => Nat) x
      (strictN (ih (r32 (PARS i) k) x) (LSK (r32 (LABS i) k)))
      (bAnd(Nat.blt (nat_lit 0) k, Nat.blt (r32 (PARS i) k) k))) f

@[expose] noncomputable def wP (i k x : Nat) : Nat := wPF i k k x

@[expose] noncomputable def gK (k j x : Nat) : Nat := strictN (wP (nat_lit 1) j x) (wP (nat_lit 0) k)

@[expose] noncomputable def anyMv (F : Nat → Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun q _ ih => bIf(Nat.beq (F q) q, ih, true)) QL

@[expose] noncomputable def allFix (F : Nat → Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun q _ ih => bAnd(Nat.beq (F q) q, ih)) QL

@[expose] noncomputable def wF (w x : Nat) : Nat :=
  nIf(Nat.beq w (nat_lit 0), gB x, strictN (gB x) fun y => strictN (gA y) fun z => strictN (gB z) gA)

@[expose] noncomputable def wI (w x : Nat) : Nat :=
  nIf(Nat.beq w (nat_lit 0), gBi x, strictN (gA x) fun y => strictN (gBi y) fun z => strictN (gA z) gBi)

@[expose] noncomputable def sq (F : Nat → Nat) (x : Nat) : Nat := strictN (F x) F

@[expose] noncomputable def cb (F : Nat → Nat) (x : Nat) : Nat := strictN (F x) fun y => strictN (F y) F

@[expose] noncomputable def rK (G : Nat → Nat) (w x : Nat) : Nat :=
  strictN (wI w x) fun y => strictN (G y) fun z => strictN (wF w z) G

@[expose] noncomputable def conjK (G : Nat → Nat) (w : Nat) : Bool :=
  bAnd(anyMv (rK G w), bAnd(anyMv (sq (rK G w)), anyMv (cb (rK G w))))

@[expose] noncomputable def leafF (G : Nat → Nat) : Bool :=
  bIf(anyMv (sq G), true, bIf(allFix G, true,
    bIf(allFix (cb fun x => strictN (gA x) G), true,
      bIf(conjK G (nat_lit 0), true, conjK G (nat_lit 1)))))

@[expose] noncomputable def leafK (k j : Nat) : Bool := leafF (gK k j)

@[expose] noncomputable def leafSl (c : Nat) : Bool :=
  allN (nat_lit 8) fun d => strictB (Nat.add (Nat.mul c (nat_lit 8)) d) fun k =>
    allN (nat_lit 128) fun j => leafK k j

end CertificateChecks.KernelFi22S

end
