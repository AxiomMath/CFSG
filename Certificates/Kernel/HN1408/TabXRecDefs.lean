module

public import Certificates.Kernel.HN1408.TabXRecData
public import Certificates.Kernel.HN1408.TableIData
public import Certificates.Data.Kernel.Spor.BaseEq
public import Certificates.Kernel.HN1408.CzTDefs

public section

namespace CFSG.KD.HN1408.TabX

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.BaseEq CFSG.KD.HN1408.CzT
open CFSG.EvenSporadicStandard.HNRecog

@[expose] noncomputable def ev (c x : Nat) : Nat := pt (T0 (Nat.div c 24)) (pt (T1 (Nat.mod c 24)) x)

@[expose] noncomputable def eqB (f g : Nat → Nat) : Bool :=
  bAnd(Nat.beq (f 0) (g 0), Nat.beq (f 1) (g 1))

@[expose] noncomputable def commC (c h : Nat) : Bool :=
  eqB (fun x => ev c (ev h x)) (fun x => ev h (ev c x))

@[expose] noncomputable def nm (k : Nat) : Nat := fd (NM 0) k

@[expose] noncomputable def cdOf (Rw : Nat → Nat) (r : Nat) : Nat := fd (Rw r) 0

@[expose] noncomputable def recRow (Rw : Nat → Nat) (n k : Nat) (gc : Nat → Nat) (r : Nat) : Bool :=
  strictB (Rw r) fun w => strictB (fd w 0) fun c =>
    bAnd(Nat.blt c 30720,
    bAnd(bIf(Nat.blt (Nat.succ r) n, Nat.blt c (cdOf Rw (Nat.succ r)), true),
    bAnd(bIf(Nat.beq r 0, bAnd(Nat.beq c 0, Nat.beq (fd w 3) 0),
      strictB (fd w 1) fun p => strictB (fd w 2) fun l =>
        bAnd(Nat.blt p n, bAnd(Nat.blt l k, bAnd(Nat.beq (fd w 3) (Nat.succ (fd (Rw p) 3)),
          eqB (fun x => ev c x) (fun x => ev (cdOf Rw p) (ev (gc l) x)))))),
      allN k fun l => strictB (fd w (Nat.add 4 l)) fun q =>
        bAnd(Nat.blt q n, eqB (fun x => ev (cdOf Rw q) x) (fun x => ev c (ev (gc l) x))))))

@[expose] noncomputable def dGen (l : Nat) : Nat := nm l

@[expose] noncomputable def rGen (l : Nat) : Nat := nm (Nat.add 29 l)

@[expose] noncomputable def dSl (s : Nat) : Bool :=
  allN 256 fun d => recRow DR 7680 3 dGen (Nat.add (Nat.mul 256 s) d)

@[expose] noncomputable def gapK (Cd : Nat → Nat) (n c p : Nat) : Bool :=
  bAnd(Nat.ble 1 p, bAnd(Nat.ble p n, bAnd(Nat.blt (Cd (Nat.pred p)) c,
    bIf(Nat.beq p n, true, Nat.blt c (Cd p)))))

@[expose] noncomputable def atK (Rw : Nat → Nat) (n c p : Nat) : Bool :=
  bAnd(Nat.blt p n, Nat.beq (cdOf Rw p) c)

@[expose] noncomputable def inD (r : Nat) : Bool :=
  strictB (RR r) fun w => atK DR 7680 (fd w 0) (fd w 11)

@[expose] noncomputable def posK (r : Nat) : Bool :=
  strictB (RR r) fun w =>
    bIf(atK DR 7680 (fd w 0) (fd w 11), true, gapK (cdOf DR) 7680 (fd w 0) (fd w 11))

@[expose] noncomputable def rAll : Bool :=
  allN 256 fun r => bAnd(recRow RR 256 7 rGen r, posK r)

@[expose] noncomputable def dGensK : Bool :=
  allN 3 fun m => strictB (dGen m) fun d => strictB (nm (Nat.add 3 (Nat.mul 2 m))) fun x =>
    strictB (nm (Nat.add 4 (Nat.mul 2 m))) fun y =>
      bAnd(Nat.blt d 30720, bAnd(Nat.blt x 30720, bAnd(Nat.blt y 30720,
        eqB (fun p => ev d (ev y (ev x p))) (fun p => ev x (ev y p)))))

@[expose] noncomputable def normK : Bool :=
  allN 2 fun l => strictB (G l) fun U => allN 3 fun m => strictB (dGen m) fun d =>
    strictB (Nat.add 9 (Nat.add (Nat.mul 6 l) (Nat.mul 2 m))) fun k =>
      strictB (nm k) fun e => strictB (nm (Nat.succ k)) fun e' =>
        bAnd(Nat.blt e 7680, bAnd(Nat.blt e' 7680,
          bAnd(eqB (fun x => pt U (ev d x)) (fun x => ev (cdOf DR e) (pt U x)),
            eqB (fun x => ev d (pt U x)) (fun x => pt U (ev (cdOf DR e') x)))))

@[expose] noncomputable def quotK : Bool :=
  strictB (G 0) fun U₁ => strictB (G 1) fun U₂ =>
    strictB (nm 21) fun c₁ => strictB (nm 22) fun c₂ => strictB (nm 25) fun v =>
      bAnd(Nat.blt c₁ 30720, bAnd(Nat.blt c₂ 30720, bAnd(Nat.blt v 30720,
      bAnd(eqB (fun x => ev c₁ x) (fun x => pt U₁ x), bAnd(eqB (fun x => ev c₂ x) (fun x => pt U₂ x),
      bAnd(Nat.blt (nm 23) 7680, bAnd(Nat.blt (nm 24) 7680,
      bAnd(eqB (fun x => ev (cdOf DR (nm 23)) x) (fun x => pt U₁ (pt U₁ x)),
      bAnd(eqB (fun x => ev (cdOf DR (nm 24)) x) (fun x => pt U₂ (pt U₂ x)),
      bAnd(eqB (fun x => ev v (pt U₂ x)) (fun x => pt U₁ x),
      bAnd(gapK (cdOf DR) 7680 c₁ (nm 26), bAnd(gapK (cdOf DR) 7680 c₂ (nm 27),
        gapK (cdOf DR) 7680 v (nm 28)))))))))))))

@[expose] noncomputable def rGensK : Bool :=
  allN 7 fun l => strictB (rGen l) fun c => strictB (TI1.GI l) fun X =>
    bAnd(Nat.blt c 30720, eqB (fun x => ev c x) (fun x => pt X x))

@[expose] noncomputable def namedK : Bool :=
  strictB (nm 62) fun c₀ => strictB (nm 63) fun c₁ => strictB (WK wordB) fun Bt =>
    strictB (cdOf DR (nm 38)) fun m₁ => strictB (cdOf DR (nm 39)) fun m₂ => strictB (nm 40) fun e =>
      bAnd(Nat.blt c₀ 30720, bAnd(Nat.beq c₁ 19608, bAnd(Nat.blt e 30720,
      bAnd(eqB (fun x => ev c₀ x) (fun x => pt Bt x), bAnd(atK RR 256 c₀ (nm 36),
      bAnd(gapK (cdOf RR) 256 c₁ (nm 37),
      bAnd(Nat.blt (nm 38) 7680, bAnd(Nat.blt (nm 39) 7680,
      bAnd(commC m₁ c₁, bAnd(commC m₂ c₁,
      bAnd(eqB (fun x => ev e (ev m₂ (ev m₁ x))) (fun x => ev m₁ (ev m₂ x)),
        gapK (cdOf RR) 256 e (nm 41))))))))))))

@[expose] noncomputable def zc (k : Nat) : Nat := cdOf DR (nm (Nat.add 42 k))

@[expose] noncomputable def zK : Bool :=
  strictB (nm 62) fun c₀ =>
    bAnd(allN 4 (fun k => strictB (fd (ZG 0) k) fun r => bAnd(Nat.blt r 256, inD r)),
    bAnd(allN 8 (fun k => strictB (nm (Nat.add 42 k)) fun p => strictB (zc k) fun z =>
      bAnd(Nat.blt p 7680, bAnd(bIf(Nat.blt k 7, Nat.blt p (nm (Nat.add 43 k)), true),
      bAnd(allN 3 (fun m => commC z (dGen m)), bAnd(atK RR 256 z (nm (Nat.add 50 k)),
        bIf(Nat.beq z c₀, false, true)))))),
    bAnd(Nat.blt (nm 58) 8, bAnd(Nat.blt (nm 59) 8,
      strictB (zc (nm 58)) fun x₄ => strictB (zc (nm 59)) fun x₂ =>
        bAnd(bIf(eqB (fun x => ev x₄ (ev x₄ x)) (fun x => x), false, true),
        bAnd(eqB (fun x => ev x₄ (ev x₄ (ev x₄ (ev x₄ x)))) (fun x => x),
        bAnd(bIf(Nat.beq x₂ 0, false, true), bAnd(eqB (fun x => ev x₂ (ev x₂ x)) (fun x => x),
          bIf(eqB (fun x => ev x₂ x) (fun x => ev x₄ (ev x₄ x)), false, true)))))))))

@[expose] noncomputable def sigK : Bool :=
  strictB (nm 60) fun s => strictB (nm 61) fun t => strictB (nm 62) fun c₀ =>
    bAnd(Nat.blt s 30720, bAnd(Nat.blt t 30720, bAnd(bIf(Nat.beq s 0, false, true),
    bAnd(eqB (fun x => ev s (ev s (ev s x))) (fun x => x),
    bAnd(eqB (fun x => ev s (ev t (ev s x))) (fun x => ev t x),
    bAnd(commC c₀ s, bAnd(eqB (fun x => ev c₀ (ev c₀ x)) (fun x => x),
      allN 8 fun k => commC (zc k) s)))))))

@[expose] noncomputable def cntR (F : Nat → Nat → Bool) : Nat :=
  cntN 256 fun r => F r (cdOf RR r)

@[expose] noncomputable def cntD (F : Nat → Bool) : Nat :=
  cntN 7680 fun r => F (cdOf DR r)

@[expose] noncomputable def zgF (n r c : Nat) : Bool :=
  bAnd(inD r, allN n fun k => commC c (cdOf RR (fd (ZG 0) k)))

@[expose] noncomputable def cntK (i : Nat) : Nat :=
  nIf(Nat.beq i 0, cntR fun _ c => commC c (nm 62),
  nIf(Nat.beq i 1, cntR fun r c => bAnd(inD r, commC c (nm 62)),
  nIf(Nat.beq i 2, cntD fun c => commC c (nm 62),
  nIf(Nat.beq i 3, cntR fun _ c => commC c (nm 63),
  nIf(Nat.beq i 4, cntR fun r c => bAnd(inD r, commC c (nm 63)),
  nIf(Nat.beq i 5, cntD fun c => commC c (nm 63),
  nIf(Nat.beq i 6, cntR fun r _ => inD r,
  nIf(Nat.beq i 7, cntD fun c => allN 3 fun m => commC c (dGen m),
  nIf(Nat.beq i 8, cntR fun _ c => commC c (nm 60),
  nIf(Nat.beq i 9, cntR fun r c => bAnd(inD r, commC c (nm 60)),
    cntR (zgF 4)))))))))))

@[expose] noncomputable def cntV (i : Nat) : Nat :=
  nIf(Nat.beq i 0, 128, nIf(Nat.beq i 1, 64, nIf(Nat.beq i 2, 192, nIf(Nat.beq i 3, 32,
  nIf(Nat.beq i 4, 16, nIf(Nat.beq i 5, 96, nIf(Nat.beq i 6, 128, nIf(Nat.beq i 7, 8,
  nIf(Nat.beq i 8, 16, 8)))))))))

@[expose] noncomputable def cntOK (i : Nat) : Bool := Nat.beq (cntK i) (cntV i)

@[expose] noncomputable def sqK : Bool :=
  allN 256 fun r => strictB (cdOf RR r) fun c =>
    bIf(commC c (nm 63), eqB (fun x => ev c (ev c x)) (fun x => x), true)

end CFSG.KD.HN1408.TabX

end
