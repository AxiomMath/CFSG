module

public import Certificates.Kernel.HN1408.SylS
public import Certificates.Kernel.HN1408.SylTData

public section

namespace CFSG.KD.HN1408.SylT

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KS.BaseMask CFSG.KD.HN1408
  CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.HaradaModel

@[expose] noncomputable def mk (i j q : Nat) : Bool := mulKeyK 11 (mask 11) 2 0 SylS.T i j q

@[expose] noncomputable def halfB (i : Nat) : Bool := Nat.blt (pt (SylS.T i) 0) 704

@[expose] noncomputable def genIdxK : Bool :=
  allN 5 fun j => Nat.beq (SylS.T (Nat.succ j)) (SylS.G j)

@[expose] noncomputable def commRowK (i j : Nat) : Bool :=
  strictB (Nat.add (Nat.mul 5 i) j) fun r => strictB (r32 PI r) fun p => strictB (r32 CI r) fun c =>
    bAnd(Nat.blt p 2048, bAnd(Nat.blt c 2048, bAnd(mk (Nat.succ i) (Nat.succ j) p,
      bAnd(mk c (r32 PI (Nat.add (Nat.mul 5 j) i)) p,
        bAnd(Nat.blt (r32 CP r) 128, Nat.beq (r32 E1 (r32 CP r)) c)))))

@[expose] noncomputable def commK : Bool := allN 5 fun i => allN 5 fun j => commRowK i j

@[expose] noncomputable def parF (PL : Nat → Nat) (e : Nat) : Nat := Nat.shiftRight (r32 PL e) 4

@[expose] noncomputable def labF (PL : Nat → Nat) (e : Nat) : Nat := Nat.land (r32 PL e) 15

@[expose] noncomputable def subK (E PL C G : Nat → Nat) (ng cnt : Nat) : Bool :=
  bAnd(Nat.beq (r32 E 0) 0, bAnd(distinctK 2048 E 0 cnt,
    bAnd(allN ng (fun t => Nat.blt (r32 G t) 2048),
      allN cnt fun e => strictB (r32 E e) fun x =>
        bAnd(bIf(Nat.beq e 0, true,
            bAnd(Nat.blt (parF PL e) e, bAnd(Nat.blt (labF PL e) ng,
              mk (r32 E (parF PL e)) (r32 G (labF PL e)) x))),
          allN ng fun t => strictB (r32 C (Nat.add (Nat.mul ng e) t)) fun q =>
            bAnd(Nat.blt q cnt, mk x (r32 G t) (r32 E q))))))

@[expose] noncomputable def g1K : Bool :=
  bAnd(Nat.beq (r32 G1 0) (r32 CI 1), bAnd(Nat.beq (r32 G1 1) (r32 CI 4),
    bAnd(Nat.beq (r32 G1 2) (r32 CI 7), bAnd(Nat.beq (r32 G1 3) (r32 CI 13),
      bAnd(Nat.beq (r32 G1 4) (r32 CI 14), bAnd(Nat.beq (r32 G1 5) (r32 CI 19),
        allN 6 fun t => Nat.beq (SylS.T (r32 G1 t)) (WK (tpWords.getD t []))))))))

@[expose] noncomputable def g2K : Bool :=
  bAnd(allN 6 (fun t => Nat.beq (r32 G2 t) (r32 G1 t)),
    allN 2 fun k => strictB (r32 G2 (Nat.add 6 k)) fun s =>
      bAnd(Nat.blt s 2048, bAnd(Nat.beq (SylS.T s) (WK (w0Extra.getD k [])),
        bAnd(halfB s, mk s s 0))))

@[expose] noncomputable def normK : Bool :=
  allN 5 fun j => allN 6 fun t => strictB (r32 NC (Nat.add (Nat.mul 6 j) t)) fun d =>
    bAnd(Nat.blt d 128, conjKeyK 11 (mask 11) 2 0 SylS.T (Nat.succ j) (r32 G1 t) (r32 E1 d))

@[expose] noncomputable def invW0K : Bool :=
  strictB (maskK E2 0 512) fun MW =>
    allN 2048 fun i => bIf(bAnd(hasBit ivMask i, halfB i), hasBit MW i, true)

@[expose] noncomputable def blkGenK (G : Nat) : Bool :=
  bIf(allN 1408 (fun p => strictB (pt G p) fun y => bIf(Nat.blt y 704, Nat.blt p 704,
      bIf(Nat.blt p 704, false, true))), true,
    allN 1408 (fun p => strictB (pt G p) fun y => bIf(Nat.blt y 704,
      bIf(Nat.blt p 704, false, true), Nat.blt p 704)))

@[expose] noncomputable def genBlkK : Bool := allN 5 fun j => blkGenK (SylS.G j)

@[expose] noncomputable def tgK : Bool :=
  bAnd(allN 3 (fun l => strictB (r32 TG l) fun s => bAnd(Nat.blt s 2048,
      bAnd(Nat.beq (SylS.T s) (WK (tGens.getD l [])), halfB s))),
    bAnd(halfB (r32 SylS.FM 1), halfB (r32 SylS.FM 2)))

@[expose] noncomputable def centRowK (z a c t0 t1 t2 i : Nat) : Bool :=
  bIf(halfB i, bAnd(commKeyK 11 (mask 11) 2 0 SylS.T i z,
    bIf(bAnd(commKeyK 11 (mask 11) 2 0 SylS.T i t0, bAnd(commKeyK 11 (mask 11) 2 0 SylS.T i t1,
        commKeyK 11 (mask 11) 2 0 SylS.T i t2)),
      bIf(Nat.beq i 0, true, bIf(Nat.beq i a, true, bIf(Nat.beq i z, true, Nat.beq i c))), true)),
    true)

@[expose] noncomputable def centK : Bool :=
  strictB (r32 SylS.FM 1) fun a => strictB (r32 SylS.FM 2) fun z => strictB (r32 SylS.FM 3) fun c =>
    strictB (r32 TG 0) fun t0 => strictB (r32 TG 1) fun t1 => strictB (r32 TG 2) fun t2 =>
      allN 2048 (centRowK z a c t0 t1 t2)

@[expose] noncomputable def cntN (n : Nat) (f : Nat → Bool) : Nat :=
  foldN n (fun i s => nIf(f i, Nat.succ s, s)) 0

@[expose] noncomputable def cntS (y : Nat) : Nat :=
  cntN 2048 fun i => bAnd(halfB i, mk i i y)

@[expose] noncomputable def cntE (E : Nat → Nat) (cnt y : Nat) : Nat :=
  cntN cnt fun e => strictB (r32 E e) fun x => mk x x y

@[expose] noncomputable def countsK : Bool :=
  strictB (r32 SylS.FM 1) fun a => strictB (r32 SylS.FM 2) fun z => strictB (r32 SylS.FM 3) fun c =>
    bAnd(Nat.beq (cntS a) 80, bAnd(Nat.beq (cntS c) 48,
      bAnd(Nat.beq (cntE E1 128 a) 16, bAnd(Nat.beq (cntE E1 128 z) 32,
        bAnd(Nat.beq (cntE E1 128 c) 16, bAnd(Nat.beq (cntE E2 512 a) 48,
          Nat.beq (cntE E2 512 c) 16))))))

end CFSG.KD.HN1408.SylT

end
