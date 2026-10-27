module

public import Certificates.Kernel.Sporadic.OddCore.SuzBtXF
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzBtXK

open CFSG.KC.Enum CFSG.KS CFSG.KS.BTup CertificateChecks.KernelSpor
  CertificateChecks.KernelSpor.SuzBtXF

local notation "pg4" => pg 4 (mask 4)

@[expose] noncomputable def el (K : Nat → Nat) (s : Nat) : Nat := btKey 64 (mask 64) K s

@[expose] noncomputable def cmpT (f g : Nat) : Nat := pcomp 16 4 (mask 4) f g

@[expose] noncomputable def anyN (n : Nat) (f : Nat → Bool) : Bool :=
  Bool.not (allN n (fun i => Bool.not (f i)))

@[expose] noncomputable def isInvT (t : Nat) : Bool := bAnd(Bool.not (isOne t 1), isOne t 2)

@[expose] noncomputable def vS (VP k j : Nat) : Nat :=
  Nat.land (Nat.shiftRight VP (Nat.mul 6 (Nat.add (Nat.mul 3 k) j))) 63

@[expose] noncomputable def vF (VP m : Nat) : Nat := Nat.land (Nat.shiftRight VP (Nat.mul 6 m)) 63

@[expose] noncomputable def inV (VP k s : Nat) : Bool := anyN 3 (fun j => Nat.beq s (vS VP k j))

@[expose] noncomputable def nrm (K : Nat → Nat) (VP : Nat) (x k : Nat) : Bool :=
  allN 3 (fun j => strictB (cmpT x (el K (vS VP k j))) (fun xv =>
    anyN 3 (fun j' => Nat.beq xv (cmpT (el K (vS VP k j')) x))))

@[expose] noncomputable def cnj (K : Nat → Nat) (VP : Nat) (y k l : Nat) : Bool :=
  allN 3 (fun j => strictB (cmpT y (el K (vS VP k j))) (fun yv =>
    anyN 3 (fun j' => Nat.beq yv (cmpT (el K (vS VP l j')) y))))

@[expose] noncomputable def invK (K : Nat → Nat) (c : Nat) : Bool :=
  Nat.beq (btCntN 60 (fun s => isInvT (el K s))) c

@[expose] noncomputable def vK (K : Nat → Nat) (VP : Nat) : Bool :=
  bAnd(allN 15 (fun m => bAnd(Nat.blt (vF VP m) 60, bAnd(isInvT (el K (vF VP m)),
    allN 15 (fun m' => bIf(Nat.beq m m', true, Bool.not (Nat.beq (vF VP m) (vF VP m'))))))),
  allN 5 (fun k => allN 3 (fun j => allN 3 (fun j' => bIf(Nat.beq j j', true,
    Nat.beq (cmpT (el K (vS VP k j)) (el K (vS VP k j')))
      (el K (vS VP k (Nat.sub 3 (Nat.add j j')))))))))

@[expose] noncomputable def cvK (K : Nat → Nat) (VP : Nat) : Bool :=
  allN 60 (fun s => strictB (el K s) (fun S =>
    bAnd(bIf(isInvT S, anyN 5 (fun k => inV VP k s), true),
      allN 5 (fun k => allN 3 (fun j => strictB (el K (vS VP k j)) (fun U =>
        Bool.rec (motive := fun _ => Bool) (Bool.not (inV VP k s)) (inV VP k s)
          (bAnd(isInvT S, Nat.beq (cmpT S U) (cmpT U S)))))))))

@[expose] noncomputable def o5K (K : Nat → Nat) (c : Nat) : Bool :=
  allN 60 (fun s => strictB (el K s) (fun X =>
    bIf(bAnd(Bool.not (isOne X 1), isOne X 5),
      strictB (cmpT X X) (fun X2 => strictB (cmpT X X2) (fun X3 => strictB (cmpT X X3) (fun X4 =>
        Nat.beq (btCntN 60 (fun t => strictB (el K t) (fun Y => strictB (cmpT Y X) (fun YX =>
          bIf(Nat.beq YX (cmpT X Y), true, bIf(Nat.beq YX (cmpT X2 Y), true,
            bIf(Nat.beq YX (cmpT X3 Y), true, Nat.beq YX (cmpT X4 Y)))))))) c))), true)))

@[expose] noncomputable def o3K (K : Nat → Nat) (VP WP : Nat) : Bool :=
  allN 60 (fun s => strictB (el K s) (fun X =>
    bIf(bAnd(Bool.not (isOne X 1), isOne X 3),
      bAnd(Nat.beq (btCntN 5 (fun k => nrm K VP X k)) 2,
        strictB (Nat.land (Nat.shiftRight WP (Nat.mul 12 s)) 63) (fun y => strictB (Nat.land (Nat.shiftRight WP
          (Nat.add (Nat.mul 12 s) 6)) 7) (fun k => strictB (Nat.land (Nat.shiftRight WP
            (Nat.add (Nat.mul 12 s) 9)) 7) (fun l => strictB (el K y) (fun Y =>
          bAnd(Nat.blt y 60, bAnd(isInvT Y, bAnd(strictB (cmpT Y X) (fun YX =>
            bIf(Nat.beq YX (cmpT X Y), true, Nat.beq YX (cmpT (cmpT X X) Y))),
          bAnd(Nat.blt k 5, bAnd(Nat.blt l 5, bAnd(Bool.not (Nat.beq k l),
          bAnd(nrm K VP X k, bAnd(nrm K VP X l, cnj K VP Y k l))))))))))))), true)))

@[expose] noncomputable def nK (K : Nat → Nat) (VP c : Nat) : Bool :=
  allN 5 (fun k => Nat.beq (btCntN 60 (fun t => nrm K VP (el K t) k)) c)

@[expose] noncomputable def VP (i : Nat) : Nat :=
  nIf(Nat.beq i 0, 1139378904092278866813826242, nIf(Nat.beq i 1, 1139378904092010724407046594,
    nIf(Nat.beq i 2, 1139378904091148848017601474, 1139378904090888951979520706)))

@[expose] noncomputable def WP0 : Nat := 75882884098385925684813348129271658218327732617816267124826321226925869573907152154506931243651417549034048526252439778075975118438491747883716778974439754123852906462975003475841116935290880

@[expose] noncomputable def WP1 : Nat := 75910190944125043335099165198220749826770534301522364770094143415154592993466031608889230744713153958663544875272461260021623034824193820049306015360757659528891445414980596112955714274590720

@[expose] noncomputable def WP2 : Nat := 75920992736985899224522849958772643214748670789111636769357622994744319992823551590536406026774686257336949769108354463295231569442384445229667225588587826792310471982645158422498771229212672

@[expose] noncomputable def WP3 : Nat := 75882884637822949601208348032510823238701734797280484924151806929813899162452473823831859910616531483641278448406627283720955779629044090212902576789521896935426693247393042022456326281494528

theorem kX0I : invK SuzBtX0.K 15 = true := by quickRfl
theorem kX0V : vK SuzBtX0.K (VP 0) = true := by quickRfl
theorem kX0C : cvK SuzBtX0.K (VP 0) = true := by quickRfl
theorem kX05 : o5K SuzBtX0.K 10 = true := by quickRfl
theorem kX03 : o3K SuzBtX0.K (VP 0) WP0 = true := by quickRfl
theorem kX0N : nK SuzBtX0.K (VP 0) 12 = true := by quickRfl

theorem kX1I : invK SuzBtX1.K 15 = true := by quickRfl
theorem kX1V : vK SuzBtX1.K (VP 1) = true := by quickRfl
theorem kX1C : cvK SuzBtX1.K (VP 1) = true := by quickRfl
theorem kX15 : o5K SuzBtX1.K 10 = true := by quickRfl
theorem kX13 : o3K SuzBtX1.K (VP 1) WP1 = true := by quickRfl
theorem kX1N : nK SuzBtX1.K (VP 1) 12 = true := by quickRfl

theorem kX2I : invK SuzBtX2.K 15 = true := by quickRfl
theorem kX2V : vK SuzBtX2.K (VP 2) = true := by quickRfl
theorem kX2C : cvK SuzBtX2.K (VP 2) = true := by quickRfl
theorem kX25 : o5K SuzBtX2.K 10 = true := by quickRfl
theorem kX23 : o3K SuzBtX2.K (VP 2) WP2 = true := by quickRfl
theorem kX2N : nK SuzBtX2.K (VP 2) 12 = true := by quickRfl

theorem kX3I : invK SuzBtX3.K 15 = true := by quickRfl
theorem kX3V : vK SuzBtX3.K (VP 3) = true := by quickRfl
theorem kX3C : cvK SuzBtX3.K (VP 3) = true := by quickRfl
theorem kX35 : o5K SuzBtX3.K 10 = true := by quickRfl
theorem kX33 : o3K SuzBtX3.K (VP 3) WP3 = true := by quickRfl
theorem kX3N : nK SuzBtX3.K (VP 3) 12 = true := by quickRfl

end CertificateChecks.KernelSpor.SuzBtXK

end
