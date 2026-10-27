module

public import Certificates.Kernel.HN1408.CbTData
public import Certificates.Kernel.HN1408.Tr2PDefs

public section

namespace CFSG.KD.HN1408.CbT

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KD.HN1408.Tr2

@[expose] noncomputable def tabK (L D P R : Nat → Nat) (nD n : Nat) : Bool :=
  bAnd(allN 1408 (fun x => bIf(Nat.beq (L x) 0, true,
      bAnd(Nat.blt (P x) nD, Nat.beq (D (P x)) x))),
    bAnd(allN nD (fun d => bAnd(Nat.blt (D d) 1408,
        bAnd(!Nat.beq (L (D d)) 0, Nat.ble (L (D d)) n))),
      allN n (fun k => bAnd(Nat.blt (R k) 1408, Nat.beq (L (R k)) (Nat.succ k)))))

@[expose] noncomputable def blkPt (L R : Nat → Nat) (A B x : Nat) : Bool :=
  strictB (L (pt A (pt B x))) fun l =>
    bAnd(!Nat.beq l 0, Nat.beq l (L (pt A (pt B (R (Nat.sub (L x) 1))))))

@[expose] noncomputable def blkK (L D R : Nat → Nat) (nD A B : Nat) : Bool :=
  allN nD fun d => blkPt L R A B (D d)

@[expose] noncomputable def fixK (L R : Nat → Nat) (n A B : Nat) : Bool :=
  allN n fun k => Nat.beq (L (pt A (pt B (R k)))) (Nat.succ k)

@[expose] noncomputable def scan2 (F : Nat → Nat → Bool) : Bool :=
  allN 672 fun i => strictB (T0 i) fun A => allN 120 fun j => F A (T1 j)

@[expose] noncomputable def shapeK (H : Nat) (L D R : Nat → Nat) (nD : Nat)
    (L' D' R' : Nat → Nat) (nD' : Nat) : Bool :=
  strictB H fun H => scan2 fun A B =>
    bIf(comm2 1401 A B H, bAnd(blkK L D R nD A B, blkK L' D' R' nD' A B), true)

@[expose] noncomputable def kerK (H : Nat) (L R : Nat → Nat) (n : Nat) (L' R' : Nat → Nat) : Bool :=
  strictB H fun H => Nat.beq (cnt2 672 120 T0 T1 fun A B =>
    bAnd(comm2 1401 A B H, bAnd(fixK L R n A B, fixK L' R' 2 A B))) 1

end CFSG.KD.HN1408.CbT

end
