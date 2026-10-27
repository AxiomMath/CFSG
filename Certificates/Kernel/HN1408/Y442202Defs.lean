module

public import Certificates.Kernel.HN1408.Words
public import Certificates.Data.Kernel.Misc.PermClos

public section

namespace CFSG.KD.HN1408.Y442202

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KC.Misc.Clos CFSG.KD.HN1408

@[expose] noncomputable def oneOr (t q : Nat) : Bool := bIf(Nat.beq q idK, true, Nat.beq q t)

@[expose] noncomputable def conjInK (c y z : Nat) : Bool := Nat.beq (pc c y) (pc z c)

@[expose] noncomputable def fltSq (s t x nA : Nat) (YA : Nat → Nat) (a : Nat) : Bool :=
  strictB (pc s x) (fun y => bIf(oneOr t (pc y y), bAnd(Nat.blt a nA, Nat.beq (YA a) y), true))

@[expose] noncomputable def fltQu (s t x nB : Nat) (YB : Nat → Nat) (b : Nat) : Bool :=
  strictB (pc s x) (fun y => strictB (pc y y) (fun y2 => strictB (pc y2 y2) (fun y4 =>
    bIf(oneOr t (pc y4 y), bAnd(Nat.blt b nB, Nat.beq (YB b) y), true))))

@[expose] noncomputable def fltK (T : Nat → Nat) (cnt s₁ s₂ t nA nB : Nat)
    (YA YB FA FB : Nat → Nat) : Bool :=
  allN cnt (fun i => strictB (T i) (fun x =>
    bAnd(fltSq s₁ t x nA YA (FA i), fltQu s₂ t x nB YB (FB i))))

@[expose] noncomputable def badK (T : Nat → Nat) (cnt kt y₁ y₂ k : Nat) : Bool :=
  strictB (pc y₁ y₂) (fun u => strictB (pc u u) (fun u2 =>
    bAnd(Nat.blt k cnt, bAnd(bIf(Nat.beq k (nat_lit 0), false, true),
      bAnd(bIf(Nat.beq k kt, false, true), Nat.beq (pc u2 u2) (T k))))))

@[expose] noncomputable def badAllK (T : Nat → Nat) (cnt kt nA nB : Nat) (YA YB C : Nat → Nat) :
    Bool :=
  allN nA (fun a => strictB (YA a) (fun y₁ => allN nB (fun b =>
    badK T cnt kt y₁ (YB b) (C (Nat.add (Nat.mul a nB) b)))))

@[expose] noncomputable def badSomeK (T : Nat → Nat) (cnt kt nA nB : Nat) (YA YB C : Nat → Nat) :
    Bool :=
  allN nA (fun a => strictB (YA a) (fun y₁ => allN nB (fun b =>
    strictB (C (Nat.add (Nat.mul a nB) b)) (fun k =>
      bIf(Nat.blt k (nat_lit 1000), badK T cnt kt y₁ (YB b) k, true)))))

@[expose] noncomputable def goodK (Y : Nat → Nat) (cntY c y₁ y₂ j₁ j₂ : Nat) : Bool :=
  bAnd(Nat.blt j₁ cntY, bAnd(Nat.blt j₂ cntY, bAnd(conjInK c y₁ (Y j₁), conjInK c y₂ (Y j₂))))

@[expose] noncomputable def pairAct (e g : Nat) : Nat :=
  Nat.add (Nat.mul (pt g (Nat.div e (nat_lit 1408))) (nat_lit 1408))
    (pt g (Nat.mod e (nat_lit 1408)))

@[expose] noncomputable def gen2 (y₁ y₂ l : Nat) : Nat := nIf(Nat.beq l (nat_lit 0), y₁, y₂)

@[expose] noncomputable def orbK (y₁ y₂ N : Nat) (E PA SG CT : Nat → Nat) : Bool :=
  bAnd(Nat.blt (E (nat_lit 0)) (nat_lit 1982464), allN N (fun k =>
    bAnd(treeAt pairAct (E (nat_lit 0)) (gen2 y₁ y₂) (nat_lit 2) E PA k,
      bAnd(sortAt N E SG k, closedAt pairAct (gen2 y₁ y₂) (nat_lit 2) N E CT k))))

@[expose] noncomputable def centK (G T CI : Nat → Nat) (t s₁ s₂ : Nat) (C : Nat → Nat)
    (nC nG cnt cSwap : Nat) : Bool :=
  bAnd(allN nG (fun j => bAnd(halvesK (G j), commP (G j) t)),
  bAnd(Nat.blt (CI (nat_lit 0)) cnt, bAnd(Nat.beq (T (CI (nat_lit 0))) t,
  bAnd(halvesK s₁, bAnd(commP s₁ t, bAnd(halvesK s₂, bAnd(commP s₂ t,
  bAnd(Nat.blt (CI (nat_lit 1)) cnt, bAnd(Nat.beq (pc s₁ s₁) (T (CI (nat_lit 1))),
  bAnd(Nat.blt (CI (nat_lit 2)) cnt,
  bAnd(strictB (pc s₂ s₂) (fun q => Nat.beq (pc (pc q q) s₂) (T (CI (nat_lit 2)))),
  bAnd(allN nC (fun c => allN nG (fun j =>
      strictB (CI (Nat.add (nat_lit 3) (Nat.add (Nat.mul c nG) j))) (fun k =>
        bAnd(Nat.blt k cnt, conjInK (C c) (G j) (T k))))),
    Nat.ble (nat_lit 704) (pt cSwap (nat_lit 0))))))))))))))

end CFSG.KD.HN1408.Y442202

end
