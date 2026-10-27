module

public import Certificates.Kernel.HN1408.Cz1TData
public import Certificates.Kernel.HN1408.Tr2Defs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.WordData

public section

namespace CFSG.KD.HN1408.W441875

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.EvenSporadicStandard.HNRecog CFSG.KD.HN1408.Tr2

@[expose] noncomputable def ev (k p : Nat) : Nat :=
  pt (Cz1T.T0 (Nat.div k 24)) (pt (Cz1T.T1 (Nat.mod k 24)) p)

@[expose] noncomputable def elK (k : Nat) : Nat :=
  pc (Cz1T.T0 (Nat.div k 24)) (Cz1T.T1 (Nat.mod k 24))

@[expose] noncomputable def base2 (f : Nat → Bool) : Bool := bAnd(f 0, f 1)

@[expose] noncomputable def invK (k : Nat) : Bool :=
  bAnd(bIf(Nat.beq k 0, false, true), base2 fun p => Nat.beq (ev k (ev k p)) p)

@[expose] noncomputable def rowK (R RK : Nat → Nat) (k : Nat) : Bool :=
  strictB (R k) fun v =>
    bIf(Nat.beq v 0, bIf(invK k, false, true),
      strictB (Nat.mod (Nat.sub v 1) 16) fun c => strictB (Nat.div (Nat.sub v 1) 16) fun c' =>
        bAnd(invK k, bAnd(Nat.blt c 15, bAnd(Nat.blt c' 3840,
          base2 fun p => Nat.beq (ev c' (ev (RK c) p)) (ev k (ev c' p))))))

@[expose] noncomputable def tgtK (t : Nat) : Nat :=
  nIf(Nat.beq t 0, WK wordA, nIf(Nat.beq t 1, WK wordZ, nIf(Nat.beq t 2, pc (WK wordA) (WK wordZ),
    nIf(Nat.beq t 3, WK wordB, WK wordZ₁))))

@[expose] noncomputable def invX (X : Nat) : Bool :=
  bAnd(Nat.beq (pc X X) idK, bIf(Nat.beq (pt X 0) 0, false, true))

@[expose] noncomputable def tgtInvK (t : Nat) : Bool := strictB (tgtK t) invX

@[expose] noncomputable def repK (RK RT : Nat → Nat) (RW : List (List Nat)) (c : Nat) : Bool :=
  strictB (RK c) fun k => strictB (RT c) fun t =>
    bAnd(Nat.blt k 3840, bAnd(Nat.blt t 5, bAnd(lettersOK (RW.getD c []),
      Nat.beq (pc (WK (RW.getD c [])) (tgtK t)) (pc (elK k) (WK (RW.getD c []))))))

@[expose] noncomputable def in2AK (t : Nat) : Bool :=
  bIf(Nat.beq t 0, true, bIf(Nat.beq t 2, true, Nat.beq t 3))

@[expose] noncomputable def rowIn2A (R RT : Nat → Nat) (y : Nat) : Bool :=
  strictB (R y) fun v => bAnd(bIf(Nat.beq v 0, false, true), in2AK (RT (Nat.mod (Nat.sub v 1) 16)))

@[expose] noncomputable def evW (Yc : Nat) (w : List Nat) (p : Nat) : Nat :=
  w.foldr (fun i q => ev (fd Yc i) q) p

@[expose] noncomputable def evPow2 (g h n p : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) p (fun _ q => ev g (ev h q)) n

@[expose] noncomputable def vertK (R RT : Nat → Nat) (r Yc Pc i : Nat) : Bool :=
  strictB (fd Yc i) fun y => strictB (fd Pc i) fun p =>
    bAnd(Nat.blt y 3840, bAnd(rowIn2A R RT y, bAnd(Nat.blt p 1408,
      bIf(Nat.beq (evPow2 r y 5 p) p, false, true))))

@[expose] noncomputable def genWK (CW : List (List Nat)) (Yc c l : Nat) : Bool :=
  bAnd((CW.getD (Nat.add (Nat.mul 2 c) l) []).all (fun i => Nat.blt i 4),
    base2 fun p => Nat.beq (evW Yc (CW.getD (Nat.add (Nat.mul 2 c) l) []) p) (pt (Cz1T.G l) p))

@[expose] noncomputable def rowYK (R RK RT Y YP : Nat → Nat) (CW : List (List Nat)) (c : Nat) :
    Bool :=
  bIf(in2AK (RT c),
    strictB (RK c) fun r => strictB (Y c) fun Yc => strictB (YP c) fun Pc =>
      bAnd(allN 4 (vertK R RT r Yc Pc), allN 2 (genWK CW Yc c)), true)

end CFSG.KD.HN1408.W441875

end
