module

public import Certificates.Data.Kernel.Fi23S.Defs
public import Certificates.Data.Kernel.Fi23R.Defs
public import Certificates.Data.Kernel.Spor.PChain
public import Certificates.Kernel.Fi23K.Tabs
public import Certificates.Kernel.Fi23S.Tabs
public import Certificates.Kernel.Fi23S.Trees
public import Certificates.Kernel.Fi23S.Codes

public section

namespace CFSG.KD.Fi23S

open CFSG.KC.Enum CFSG.KC.Fi23K CFSG.KC.Fi23R CFSG.KC.Fi23S CFSG.KS.TBfs CFSG.KS.PC CFSG.KS.PEnum
  CFSG.KD.Fi23K

@[expose] noncomputable def LS (l x : Nat) : Nat := tb H l x

@[expose] noncomputable def BS (i : Nat) : Nat := nIf(Nat.beq i (nat_lit 0), nat_lit 0, nat_lit 2)

@[expose] noncomputable def offS (i t : Nat) : Nat :=
  List.getD (List.getD [[0, 16, 1006, 1022, 1038], [1054, 1070, 2060, 2076, 2092]] i []) t
    (nat_lit 0)

@[expose] noncomputable def TTS (i t : Nat) (r : Nat) : Nat := TS (Nat.add (offS i t) r)

@[expose] noncomputable def CNTS (_ : Nat) : Nat := nat_lit 512

@[expose] def QS : List Nat := [0, 1, 2, 3, 4, 5]

@[expose] def SW : List (List Nat) := [[62, 57, 58, 56, 66, 64, 61, 64, 60, 66, 71, 65, 71, 69, 72,
  68, 68, 74, 72], [59, 74, 57, 57, 74, 64, 62, 68, 61, 72, 69, 66, 68, 72, 71, 74, 69, 74, 72], [59,
  61, 67, 56, 67, 70, 62, 60, 60, 70, 67, 65, 66, 64, 74, 72, 70, 72, 68, 68, 72], [61, 70, 58, 58, 63,
  60, 64, 61, 61, 72, 66, 68, 74, 70, 68, 72], [69, 56, 69, 56, 66, 68, 64, 62, 65, 72, 67, 67, 69, 72,
  68, 70, 69, 74], [52, 67, 54, 69, 54, 66, 57, 63, 56, 62, 65, 65, 60, 72, 64, 68, 64, 70, 68, 72, 68,
  72], [61, 70, 64, 54, 54, 58, 56, 71, 56, 70, 61, 71, 66, 60, 71, 67, 65, 72, 70, 72, 70, 68, 72],
  [68, 58, 54, 67, 54, 57, 64, 58, 68, 72, 68, 60, 67, 74, 72, 68, 70, 74, 68, 72], [61, 66, 57, 52,
  65, 66, 58, 56, 66, 69, 67, 64, 61, 74, 69, 65, 72, 70, 69, 69, 74, 72], [66, 61, 57, 55, 52, 56, 61,
  63, 56, 64, 64, 60, 63, 61, 66, 69, 66, 65, 71, 69, 69, 71], [57, 54, 64, 62, 54, 56, 74, 56, 56, 70,
  65, 69, 63, 69, 64, 67, 64, 68, 70, 68, 72, 68, 74, 72], [57, 54, 64, 62, 54, 71, 67, 65, 56, 72, 63,
  66, 69, 60, 72, 65, 69, 64, 70, 70, 70, 69, 70], [68, 67, 54, 56, 67, 58, 57, 74, 62, 74, 60, 60, 64,
  70, 64, 74, 68, 70, 68, 71, 69, 74], [56, 54, 69, 55, 52, 58, 57, 71, 63, 74, 60, 67, 70, 65, 72, 69,
  71, 69, 70, 74, 72], [66, 64, 55, 59, 52, 64, 57, 68, 57, 67, 64, 71, 65, 60, 69, 72, 64, 69, 74, 72,
  70, 70], [70, 62, 69, 54, 54, 68, 72, 64, 56, 68, 63, 60, 74, 61, 66, 68, 64, 68, 71, 74, 71, 68, 72],
  [58, 74, 52, 54, 58, 74, 62, 56, 74, 61, 68, 68, 60, 68, 66, 65, 70, 74, 68, 68, 68], [58, 61, 57, 52,
  61, 57, 58, 68, 62, 70, 62, 60, 64, 64, 68, 64, 72, 69, 74, 72, 69, 74], [63, 60, 58, 54, 54, 62, 65,
  58, 56, 65, 70, 69, 60, 67, 67, 67, 74, 72, 68, 72, 70, 74, 72], [55, 57, 57, 54, 58, 66, 58, 70, 62,
  72, 63, 68, 67, 64, 74, 68, 70, 70, 68], [61, 58, 55, 60, 60, 56, 70, 63, 70, 67, 60, 67, 68, 66, 65,
  70, 72, 68, 71, 68, 74, 72]]

@[expose] noncomputable def sylJW (W : List (List Nat)) (x j : Nat) : Bool :=
  strictB (tb H (Nat.mul (nat_lit 2) j) x) fun y =>
    bAnd(Nat.beq y (wv G (List.getD W j []) x), bAnd(Nat.blt y (nat_lit 31671),
      strictB (Nat.succ (Nat.mul (nat_lit 2) j)) fun l =>
        bAnd(Nat.blt (tb H l x) (nat_lit 31671), Nat.beq (tb H l y) x)))

@[expose] noncomputable def sylJ (x j : Nat) : Bool := sylJW SW x j

@[expose] noncomputable def sylAt (x : Nat) : Bool :=
  bAnd(allN (nat_lit 21) (sylJ x),
    bAnd(Nat.beq (tb H (nat_lit 42) x) (tb G (nat_lit 43) (tA G (nat_lit 1) x)),
      Nat.beq (tb H (nat_lit 43) x) (tb H (nat_lit 42) (tA G (nat_lit 39) x))))

@[expose] noncomputable def sylSl (lo len : Nat) : Bool :=
  allN len fun d => strictB (Nat.add lo d) fun x => bIf(Nat.blt x (nat_lit 31671), sylAt x, true)

@[expose] noncomputable def sylF (s : Nat) : Bool := sylSl (Nat.mul s (nat_lit 2048)) (nat_lit 2048)

@[expose] noncomputable def lvS (i : Nat) : List Nat := lvK LS BS (nat_lit 42) i

@[expose] noncomputable def hdS (i : Nat) : Bool :=
  tbfsHdK (nat_lit 31671) (BS i) (nat_lit 512) (TTS i (nat_lit 0)) (TTS i (nat_lit 1))
    (TTS i (nat_lit 2)) (TTS i (nat_lit 3))

@[expose] noncomputable def trS (i lo len : Nat) : Bool :=
  tbfsSlK (nat_lit 31671) (nat_lit 512) (List.length (lvS i)) LS (lvAt LS BS (nat_lit 42) i)
    (TTS i (nat_lit 0)) (TTS i (nat_lit 1)) (TTS i (nat_lit 2)) (TTS i (nat_lit 3))
    (TTS i (nat_lit 4)) lo len

@[expose] noncomputable def schS (i lo len : Nat) : Bool :=
  schSlK LS BS (nat_lit 42) (fun i => TTS i (nat_lit 0)) (fun i => TTS i (nat_lit 1))
    (fun i => TTS i (nat_lit 2)) (fun i => TTS i (nat_lit 3)) CNTS BS QS (nat_lit 2) i lo len

@[expose] noncomputable def termS : Bool := termK LS BS (nat_lit 42) (nat_lit 2) QS

@[expose] noncomputable def wS (i k x : Nat) : Nat :=
  wF LS (TTS i (nat_lit 2)) (TTS i (nat_lit 3)) k k x

@[expose] noncomputable def gK (k j x : Nat) : Nat := wS (nat_lit 0) k (wS (nat_lit 1) j x)

@[expose] noncomputable def code (k j : Nat) : Nat :=
  r32 CW (Nat.add (Nat.mul k (nat_lit 512)) j)

@[expose] noncomputable def movB (f : Nat → Nat) : Bool :=
  Bool.not (allN (nat_lit 6) fun b => Nat.beq (f b) b)

@[expose] noncomputable def fixB (f : Nat → Nat) : Bool := allN (nat_lit 6) fun b => Nat.beq (f b) b

@[expose] def U13 : List (List Nat) := [[40], [40, 39]]
@[expose] def U13i : List (List Nat) := [[41], [39, 41]]

@[expose] noncomputable def cw (t y : Nat) : Nat :=
  wa G (List.getD U13 t []) (tb G (nat_lit 43) (wa G (List.getD U13i t []) y))

@[expose] noncomputable def rw13 (k j t y : Nat) : Nat :=
  gK k j (wa G (List.getD U13 t []) (gK k j (wa G (List.getD U13i t []) y)))

@[expose] noncomputable def lf13c (c k j : Nat) : Bool :=
    bIf(Nat.beq c (nat_lit 0), movB fun b => gK k j (gK k j b),
    bIf(Nat.beq c (nat_lit 1), fixB (gK k j),
    strictB (Nat.land (Nat.sub c (nat_lit 2)) (nat_lit 3)) fun t =>
      bIf(Nat.blt t (nat_lit 2),
        fixB fun b => strictN (gK k j (cw t b)) fun y => strictN (gK k j (cw t y)) fun z =>
          gK k j (cw t z),
        strictB (Nat.sub t (nat_lit 2)) fun u =>
          bAnd(movB (rw13 k j u), bAnd(movB fun b => rw13 k j u (rw13 k j u b),
            movB fun b => rw13 k j u (rw13 k j u (rw13 k j u b)))))))

@[expose] noncomputable def lf13 (k j : Nat) : Bool := strictB (code k j) fun c => lf13c c k j

@[expose] def UR : List (List Nat) := [[40, 39, 40, 39, 40, 39, 41], [39, 40, 39, 41, 39, 40, 39,
  40, 39, 41], [39, 40, 39, 41, 39, 41, 39, 41], [39, 41, 39, 41, 39, 40, 39, 40], [40, 39, 40, 39, 40,
  39, 41, 39], [40, 39, 40, 39, 41, 39, 40, 39], [41, 39, 40, 39], [40, 39, 41, 39, 40, 39, 40, 39, 40,
  39], [41, 39, 41, 39], [39, 41, 39, 40, 39, 41, 39, 41, 39, 40], [41, 39, 40, 39, 41, 39, 40, 39], [41,
  39, 40, 39, 40, 39, 41, 39, 40, 39], [41, 39, 40, 39, 41, 39, 40, 39, 41, 39], [39, 41, 39], [41, 39,
  40, 39, 40, 39, 40, 39], [41, 39], [40, 39, 40, 39], [41, 39, 40, 39, 40, 39], [40, 39, 40], [41, 39,
  41, 39, 40, 39, 40, 39], [40, 39, 41, 39, 40], [40, 39, 41, 39, 40, 39, 40], [41, 39, 40, 39, 40, 39,
  41], [40, 39, 41, 39, 41, 39, 40], [40, 39, 40, 39, 40, 39], [40, 39, 41, 39, 40, 39], [40, 39, 40, 39,
  40, 39, 40, 39], [39], [40, 39]]
@[expose] def URi : List (List Nat) := [[40, 39, 41, 39, 41, 39, 41], [40, 39, 41, 39, 41, 39, 40,
  39, 41, 39], [40, 39, 40, 39, 40, 39, 41, 39], [41, 39, 41, 39, 40, 39, 40, 39], [39, 40, 39, 41, 39,
  41, 39, 41], [39, 41, 39, 40, 39, 41, 39, 41], [39, 41, 39, 40], [39, 41, 39, 41, 39, 41, 39, 40, 39,
  41], [39, 40, 39, 40], [41, 39, 40, 39, 40, 39, 41, 39, 40, 39], [39, 41, 39, 40, 39, 41, 39, 40], [39,
  41, 39, 40, 39, 41, 39, 41, 39, 40], [39, 40, 39, 41, 39, 40, 39, 41, 39, 40], [39, 40, 39], [39, 41,
  39, 41, 39, 41, 39, 40], [39, 40], [39, 41, 39, 41], [39, 41, 39, 41, 39, 40], [41, 39, 41], [39, 41,
  39, 41, 39, 40, 39, 40], [41, 39, 40, 39, 41], [41, 39, 41, 39, 40, 39, 41], [40, 39, 41, 39, 41, 39,
  40], [41, 39, 40, 39, 40, 39, 41], [39, 41, 39, 41, 39, 41], [39, 41, 39, 40, 39, 41], [39, 41, 39, 41,
  39, 41, 39, 41], [39], [39, 41]]

@[expose] noncomputable def xEv (r y : Nat) : Nat :=
  nIf(Nat.blt r (nat_lit 17), tb H (nat_lit 43) y,
    nIf(Nat.blt r (nat_lit 27), tb H (nat_lit 42) y, tb G (nat_lit 43) y))

@[expose] noncomputable def rEv (r y : Nat) : Nat :=
  wa G (List.getD UR r []) (xEv r (wa G (List.getD URi r []) y))

@[expose] noncomputable def hK (k j r y : Nat) : Nat := gK k j (rEv r y)

@[expose] noncomputable def lf14c (c k j : Nat) : Bool :=
  bIf(Nat.blt c (nat_lit 2), true,
    strictB (Nat.shiftRight (Nat.sub c (nat_lit 2)) (nat_lit 2)) fun r =>
      bAnd(Nat.blt r (nat_lit 29), allN (nat_lit 6) fun q =>
        strictB (cyK (hK k j r) q (nat_lit 119) (nat_lit 1) (hK k j r q)) fun l =>
          Nat.beq (Nat.land l (nat_lit 1)) (nat_lit 1)))

@[expose] noncomputable def lf14 (k j : Nat) : Bool := strictB (code k j) fun c => lf14c c k j

@[expose] noncomputable def l13Sl (k0 nk : Nat) : Bool :=
  allN nk fun d => strictB (Nat.add k0 d) fun k => allN (nat_lit 512) (lf13 k)

@[expose] noncomputable def l14Sl (k0 nk : Nat) : Bool :=
  allN nk fun d => strictB (Nat.add k0 d) fun k => allN (nat_lit 512) (lf14 k)

@[expose] noncomputable def l13F (s : Nat) : Bool := l13Sl (Nat.mul s (nat_lit 64)) (nat_lit 64)

@[expose] def l14B : List Nat := [0, 13, 33, 64, 130, 158, 217, 256, 304, 372, 463, 512]

@[expose] noncomputable def l14F (s : Nat) : Bool :=
  strictB (List.getD l14B s (nat_lit 0)) fun a =>
    l14Sl a (Nat.sub (List.getD l14B (Nat.succ s) (nat_lit 0)) a)

@[expose] noncomputable def schF (s : Nat) : Bool :=
  schS (nat_lit 0) (Nat.mul s (nat_lit 128)) (nat_lit 128)

@[expose] noncomputable def miscS : Bool :=
  bAnd(Nat.beq (tb G (nat_lit 43) (nat_lit 39)) (nat_lit 39),
  bAnd(Nat.beq (tA G (nat_lit 1) (nat_lit 39)) (nat_lit 39),
  bAnd(Nat.beq (cntS (fxW G [43]) (nat_lit 0) (nat_lit 31671)) (nat_lit 3511),
  bAnd(Nat.beq (cntS (fun x => Nat.beq (tb H (nat_lit 42) x) x) (nat_lit 0) (nat_lit 31671))
    (nat_lit 695),
  bAnd(Nat.beq (cntS (fun x => Nat.beq (tb H (nat_lit 43) x) x) (nat_lit 0) (nat_lit 31671))
    (nat_lit 183),
    Bool.not (Nat.beq (tb H (nat_lit 43) (nat_lit 2)) (nat_lit 2)))))))

end CFSG.KD.Fi23S

end
