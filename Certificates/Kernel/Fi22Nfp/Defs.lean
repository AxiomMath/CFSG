module

public import Certificates.Kernel.Fi22Nfp.Trees
public import Certificates.Kernel.Fi22Syl.ChainDefs
public import Certificates.Data.Kernel.Fi22.NfpK

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi22N

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KS.TBfs CFSG.KS.PC CFSG.KS.Fi22S CFSG.KS.Fi22Cent
  CFSG.KS.Fi22N CertificateChecks.KernelFi22S

@[expose] noncomputable def NB (l : Nat) : Nat := List.getD [641, 911, 738, 265, 399, 1042] l (nat_lit 0)
@[expose] noncomputable def UI (l : Nat) : Nat := List.getD [889, 2372, 2865, 400, 52, 886] l (nat_lit 0)

@[expose] noncomputable def LC (l x : Nat) : Nat := cK (NB l) x

@[expose] noncomputable def PTSN : Nat → Nat → Nat :=
  lvSel [NT1.PTS, NT1.PTS, NT2.PTS, NT3.PTS, NT4.PTS, NT5.PTS, NT6.PTS]
@[expose] noncomputable def POSN : Nat → Nat → Nat :=
  lvSel [NT1.POS, NT1.POS, NT2.POS, NT3.POS, NT4.POS, NT5.POS, NT6.POS]
@[expose] noncomputable def PARN : Nat → Nat → Nat :=
  lvSel [NT1.PAR, NT1.PAR, NT2.PAR, NT3.PAR, NT4.PAR, NT5.PAR, NT6.PAR]
@[expose] noncomputable def LABN : Nat → Nat → Nat :=
  lvSel [NT1.LAB, NT1.LAB, NT2.LAB, NT3.LAB, NT4.LAB, NT5.LAB, NT6.LAB]
@[expose] noncomputable def TIN : Nat → Nat → Nat :=
  lvSel [NT1.TI, NT1.TI, NT2.TI, NT3.TI, NT4.TI, NT5.TI, NT6.TI]
@[expose] noncomputable def CNTN (i : Nat) : Nat :=
  List.getD [NT1.cnt, NT1.cnt, NT2.cnt, NT3.cnt, NT4.cnt, NT5.cnt, NT6.cnt] i (nat_lit 0)

@[expose] noncomputable def hdN : Bool :=
  allN (nat_lit 6) fun i => tbfsHdK (nat_lit 3510) (nat_lit 641) (CNTN (Nat.succ i)) (PTSN (Nat.succ i))
    (POSN (Nat.succ i)) (PARN (Nat.succ i)) (LABN (Nat.succ i))

@[expose] noncomputable def ptN (i lo len : Nat) : Bool :=
  tbfsSlK (nat_lit 3510) (CNTN i) i LC (fun t => t) (PTSN i) (POSN i) (PARN i) (LABN i) (TIN i) lo len

@[expose] noncomputable def smallK : Bool :=
  bAnd(ptN (nat_lit 1) (nat_lit 0) (nat_lit 256), bAnd(ptN (nat_lit 2) (nat_lit 0) (nat_lit 256),
  bAnd(ptN (nat_lit 3) (nat_lit 0) (nat_lit 256), bAnd(ptN (nat_lit 4) (nat_lit 0) (nat_lit 256),
    ptN (nat_lit 5) (nat_lit 0) (nat_lit 256)))))

@[expose] noncomputable def t6Sl (c : Nat) : Bool :=
  ptN (nat_lit 6) (Nat.mul c (nat_lit 256)) (nat_lit 256)

@[expose] noncomputable def sizesN : Bool :=
  bAnd(Nat.beq NT1.cnt (nat_lit 1), bAnd(Nat.beq NT2.cnt (nat_lit 3), bAnd(Nat.beq NT3.cnt (nat_lit 6),
  bAnd(Nat.beq NT4.cnt (nat_lit 36), bAnd(Nat.beq NT5.cnt (nat_lit 165), Nat.beq NT6.cnt (nat_lit 3510))))))

@[expose] noncomputable def relK (c v : Nat) : Nat :=
  nIf(Nat.beq v c, nat_lit 2, nIf(Nat.beq (cK c v) v, nat_lit 1, nat_lit 0))

@[expose] noncomputable def candK (i v : Nat) : Bool :=
  allN (CNTN i) fun k => strictB (r32 (PTSN i) k) fun c => Nat.beq (relK c v) (relK c (NB i))

@[expose] noncomputable def cntC (i : Nat) : Nat :=
  foldN (nat_lit 3510) (fun v s => nIf(candK i v, Nat.succ s, s)) (nat_lit 0)

@[expose] noncomputable def candN (i : Nat) : Bool :=
  Nat.beq (cntC i) (List.getD [3510, 2816, 567, 720, 16, 2] i (nat_lit 0))

@[expose] noncomputable def uInvK : Bool :=
  allN (nat_lit 3510) fun x => strictB (UK x) fun y => bAnd(Nat.blt y (nat_lit 3510), Nat.beq (UK y) x)

@[expose] noncomputable def uBaseK : Bool :=
  allN (nat_lit 6) fun j => Nat.beq (UK (NB j)) (UI j)

@[expose] noncomputable def uConj (j : Nat) : Bool :=
  allN (nat_lit 3510) fun x => Nat.beq (UK (cK (NB j) (UK x))) (cK (UI j) x)

@[expose] noncomputable def uRecSl (c : Nat) : Bool :=
  bAnd(Nat.beq (UK (r32 (PTSN (nat_lit 6)) (nat_lit 0))) (UI (nat_lit 0)),
    allN (nat_lit 256) fun d => strictB (Nat.add (Nat.mul c (nat_lit 256)) d) fun k =>
      bIf(bAnd(Nat.blt (nat_lit 0) k, Nat.blt k (nat_lit 3510)),
        Nat.beq (UK (r32 (PTSN (nat_lit 6)) k))
          (cK (UI (r32 (LABN (nat_lit 6)) k)) (UK (r32 (PTSN (nat_lit 6)) (r32 (PARN (nat_lit 6)) k)))),
        true))

@[expose] noncomputable def uSiftK : Bool :=
  allN (nat_lit 11) fun j => siftK LSK POSS PARS LABS CNTS QB QL (nat_lit 2) (nat_lit 0)
    (mapK (fun q => UK (LSK (Nat.mul (nat_lit 2) j) (UK q))) QL)

@[expose] noncomputable def hasFix (F : Nat → Nat) : Bool :=
  bIf(allN (nat_lit 3510) (fun x => bIf(Nat.beq (F x) x, false, true)), false, true)

@[expose] noncomputable def invFixK (F : Nat → Nat) : Bool := bIf(anyMv (sq F), true, hasFix F)

@[expose] noncomputable def gU (k j x : Nat) : Nat := strictN (UK x) (gK k j)

@[expose] noncomputable def nfpLeafK (k j : Nat) : Bool :=
  bAnd(invFixK (gK k j), bAnd(anyMv (gU k j), invFixK (gU k j)))

@[expose] noncomputable def nfpSl (c : Nat) : Bool :=
  allN (nat_lit 8) fun d => strictB (Nat.add (Nat.mul c (nat_lit 8)) d) fun k =>
    allN (nat_lit 128) fun j => nfpLeafK k j

end CertificateChecks.KernelFi22N

end
