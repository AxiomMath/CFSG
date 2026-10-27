module

public import Certificates.Kernel.HN1408.XCentDefs
public import Certificates.Kernel.HN1408.TabXRecDefs

public section

namespace CFSG.KD.HN1408.XInner

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.EvenSporadicStandard.HNRecog CFSG.KD.HN1408.CzT
open CFSG.KD.HN1408.TabX CFSG.KD.HN1408.XCent

@[expose] noncomputable def relF (X Xi Y Yi : Nat → Nat) (p : Nat) : Nat :=
  X (X (Y (Xi (Yi (X (Y (Xi (Xi (Y (Xi (Y (Xi (Yi p)))))))))))))

@[expose] noncomputable def pw4 (X : Nat → Nat) (p : Nat) : Nat := X (X (X (X p)))

@[expose] noncomputable def pw2 (Y : Nat → Nat) (p : Nat) : Nat := Y (Y p)

@[expose] noncomputable def cds (k : Nat) : Nat :=
  nIf(Nat.beq k 0, 8448, nIf(Nat.beq k 1, 17531, nIf(Nat.beq k 2, 26568,
    nIf(Nat.beq k 3, 29919, 49))))

@[expose] noncomputable def dcs (k : Nat) : Nat :=
  nIf(Nat.beq k 0, 5703, nIf(Nat.beq k 1, 15916, nIf(Nat.beq k 2, 17115, nIf(Nat.beq k 3, 4859,
  nIf(Nat.beq k 4, 0, nIf(Nat.beq k 5, 1181, nIf(Nat.beq k 6, 2720, nIf(Nat.beq k 7, 20798,
    nIf(Nat.beq k 8, 19647, 17826)))))))))

@[expose] noncomputable def wCom : Nat := 430348633

@[expose] noncomputable def xiHeadG (C₁ C₂ Ha U₁ U₂ Ec : Nat) (Cd Dc : Nat → Nat) : Bool :=
  bAnd(allN 5 (fun k => Nat.blt (Cd k) 30720),
  bAnd(allN 10 (fun k => Nat.blt (Dc k) 30720),
  bAnd(eqB (fun x => pt Ha (pt U₁ x)) (fun x => pt U₁ (pt Ha x)),
  bAnd(eqB (fun x => pt Ha (pt U₂ x)) (fun x => pt U₂ (pt Ha x)),
  bAnd(eqB (fun x => pt C₁ (ev (Cd 1) (ev (Cd 0) x))) (fun x => ev (Cd 0) (ev (Cd 1) x)),
  bAnd(eqB (fun x => pt C₂ (ev (Cd 3) (ev (Cd 2) x))) (fun x => ev (Cd 2) (ev (Cd 3) x)),
  bAnd(eqB (fun x => pt C₁ (pt C₁ (pt C₁ (pt C₁ (pt C₁ x))))) (fun x => x),
  bAnd(bIf(Nat.beq (pt C₁ 0) 0, false, true),
  bAnd(eqB (fun x => pt C₂ (pt C₂ (pt C₂ x))) (fun x => x),
  bAnd(eqB (fun x => relF (pt C₁) (pw4 (pt C₁)) (pt C₂) (pw2 (pt C₂)) x) (fun x => pt Ha x),
  bAnd(eqB (fun x => ev (Cd 4) (pt C₁ x)) (fun x => pt C₁ (pt C₁ (ev (Cd 4) x))),
  bAnd(eqB (fun x => pt Ec (pt U₂ (pt U₁ x))) (fun x => pt U₁ (pt U₂ x)),
    allN 10 fun k => eqB (fun x => ev (Dc k) (pt C₁ x)) (fun x => pt C₁ (ev (Dc k) x))))))))))))))

@[expose] noncomputable def xiHead (Cd Dc : Nat → Nat) (W : Nat) : Bool :=
  strictB (CT 0) fun C₁ => strictB (CT 1) fun C₂ => strictB (WK wordA) fun Ha =>
    strictB (G 0) fun U₁ => strictB (G 1) fun U₂ => strictB (pwK C₁ C₂ W) fun Ec =>
      xiHeadG C₁ C₂ Ha U₁ U₂ Ec Cd Dc

@[expose] noncomputable def inF2 (Dc : Nat → Nat) (C₂ A B : Nat) : Bool :=
  !(allN 10 fun k =>
    !(eqB (fun x => pt A (pt B (ev (Dc k) x))) (fun x => ev (Dc k) (pt C₂ x))))

@[expose] noncomputable def f2Row (Dc : Nat → Nat) (C₁ C₂ a0 a1 A B : Nat) : Bool :=
  bIf(eqB (fun x => pt A (pt B (pt A (pt B (pt A (pt B x)))))) (fun x => x),
    bIf(bAnd(Nat.beq (relF (pt C₁) (pw4 (pt C₁)) (fun p => pt A (pt B p))
        (pw2 (fun p => pt A (pt B p))) 0) a0,
      Nat.beq (relF (pt C₁) (pw4 (pt C₁)) (fun p => pt A (pt B p))
        (pw2 (fun p => pt A (pt B p))) 1) a1),
      inF2 Dc C₂ A B, true),
    true)

@[expose] noncomputable def xiScan (Dc : Nat → Nat) : Bool :=
  strictB (CT 0) fun C₁ => strictB (CT 1) fun C₂ => strictB (WK wordA) fun Ha =>
    strictB (pt Ha 0) fun a0 => strictB (pt Ha 1) fun a1 => czScan T0 T1 (f2Row Dc C₁ C₂ a0 a1)

end CFSG.KD.HN1408.XInner

end
