module

public import Certificates.Kernel.HN1408.Y442202Rec

public section

namespace CFSG.KD.HN1408.Y442202

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KD.HN1408
  CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Simple2S5

@[expose] noncomputable def recOK (G GI : Nat → Nat) (k cnt : Nat) (T PL POS SRT SRI : Nat → Nat) :
    Bool :=
  bAnd(penumHdK idK cnt (nat_lit 4096) T PL,
    penumSlK (nat_lit 1408) (nat_lit 11) (mask (nat_lit 11)) (Nat.mul (nat_lit 1408) (nat_lit 11))
      false G GI k cnt T PL POS SRT SRI (nat_lit 0) cnt)

@[expose] noncomputable def recOZ : Bool :=
  recOK OZ.G OZ.GI OZ.k OZ.cnt OZ.T OZ.PL OZ.POS OZ.SRT OZ.SRI

@[expose] noncomputable def recOAZ : Bool :=
  recOK OAZ.G OAZ.GI OAZ.k OAZ.cnt OAZ.T OAZ.PL OAZ.POS OAZ.SRT OAZ.SRI

@[expose] noncomputable def recY0 : Bool :=
  recOK Y0.G Y0.GI Y0.k Y0.cnt Y0.T Y0.PL Y0.POS Y0.SRT Y0.SRI

@[expose] noncomputable def recY1 : Bool :=
  recOK Y1.G Y1.GI Y1.k Y1.cnt Y1.T Y1.PL Y1.POS Y1.SRT Y1.SRI

@[expose] noncomputable def gensK (G : Nat → Nat) (ws : List (List Nat)) (k : Nat) : Bool :=
  allN k (fun j => Nat.beq (G j) (WK (ws.getD j [])))

@[expose] noncomputable def gensOK : Bool :=
  bAnd(gensK OZ.G oGensZ (nat_lit 6), bAnd(gensK OAZ.G oGensAZ (nat_lit 6),
    bAnd(gensK Y0.G (ykWords.getD (nat_lit 0) []) (nat_lit 2),
      gensK Y1.G (ykWords.getD (nat_lit 1) []) (nat_lit 2))))

@[expose] noncomputable def wdK (lo len : Nat) : Bool :=
  allN len (fun d => strictB (Nat.add lo d) (fun j => Nat.beq (W j) (WK (wList.getD j []))))

@[expose] noncomputable def centZ : Bool :=
  centK OZ.G OZ.T (r32 CIz) (W (nat_lit 2)) (W (nat_lit 0)) (W (nat_lit 1))
    (fun c => W (Nat.add (nat_lit 4) c)) (nat_lit 2) (nat_lit 6) (nat_lit 128) (W (nat_lit 5))

@[expose] noncomputable def centAZ : Bool :=
  centK OAZ.G OAZ.T (r32 CIaz) (W (nat_lit 3)) (W (nat_lit 0)) (W (nat_lit 1))
    (fun c => W (Nat.add (nat_lit 6) c)) (nat_lit 2) (nat_lit 6) (nat_lit 128) (W (nat_lit 6))

@[expose] noncomputable def candComm : Bool :=
  allN (nat_lit 64) (fun c => commP (W (Nat.add (nat_lit 8) c)) (W (nat_lit 3)))

@[expose] noncomputable def fltZ : Bool :=
  fltK OZ.T (nat_lit 128) (W (nat_lit 0)) (W (nat_lit 1)) (W (nat_lit 2)) (nat_lit 16)
    (nat_lit 32) YAz YBz (r32 FAz) (r32 FBz)

@[expose] noncomputable def fltAZ : Bool :=
  fltK OAZ.T (nat_lit 128) (W (nat_lit 0)) (W (nat_lit 1)) (W (nat_lit 3)) (nat_lit 16)
    (nat_lit 32) YAaz YBaz (r32 FAaz) (r32 FBaz)

@[expose] noncomputable def badZ : Bool :=
  strictB (r32 CIz (nat_lit 0)) (fun kt =>
    badAllK OZ.T (nat_lit 128) kt (nat_lit 16) (nat_lit 32) YAz YBz (r32 Cz))

@[expose] noncomputable def badAZ : Bool :=
  strictB (r32 CIaz (nat_lit 0)) (fun kt =>
    badSomeK OAZ.T (nat_lit 128) kt (nat_lit 16) (nat_lit 32) YAaz YBaz (r32 Caz))

@[expose] noncomputable def YT (k j : Nat) : Nat := nIf(Nat.beq k (nat_lit 0), Y0.T j, Y1.T j)

@[expose] noncomputable def goodRow (g y₁ y₂ : Nat) : Bool :=
  strictB (r32 GC g) (fun c => strictB (r32 GK g) (fun k =>
  bAnd(Nat.blt c (nat_lit 64), bAnd(Nat.blt k (nat_lit 2),
  bAnd(goodK (YT k) (nat_lit 240) (W (Nat.add (nat_lit 8) c)) y₁ y₂
      (r32 GJ (Nat.mul (nat_lit 2) g)) (r32 GJ (Nat.add (Nat.mul (nat_lit 2) g) (nat_lit 1))),
    orbK y₁ y₂ (nat_lit 240) (fun i => r32 OE (Nat.add (Nat.mul (nat_lit 240) g) i))
      (fun i => r32 OPA (Nat.add (Nat.mul (nat_lit 240) g) i))
      (fun i => r32 OSG (Nat.add (Nat.mul (nat_lit 240) g) i))
      (fun i => r32 OCT (Nat.add (Nat.mul (nat_lit 480) g) i)))))))

@[expose] noncomputable def goodAZ : Bool :=
  allN (nat_lit 16) (fun a => strictB (YAaz a) (fun y₁ => allN (nat_lit 32) (fun b =>
    strictB (r32 Caz (Nat.add (Nat.mul a (nat_lit 32)) b)) (fun k =>
      bIf(Nat.blt k (nat_lit 1000), true, goodRow (Nat.sub k (nat_lit 1000)) y₁ (YBaz b))))))

end CFSG.KD.HN1408.Y442202

end
