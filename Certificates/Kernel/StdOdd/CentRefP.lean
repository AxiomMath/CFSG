module

public import Certificates.Kernel.StdOdd.CentRefSeg
public import Certificates.Data.Kernel.StdOdd.ChainP

public section

namespace CFSG.KD.StdOdd.Cent

open CFSG.KC.StdOdd.Orbit CFSG.KC.StdOdd.Chain CFSG.KC.StdOdd.ChainP CFSG.KC.Misc.E6Std

namespace CentData

variable (D : CentData)

@[expose] noncomputable def rchP (A B RK K ri : ℕ) (O : List ℕ) (Sr : List (List (List ℕ)))
    (l k : ℕ) : Bool :=
  forceLB (D.rkP RK K ri O (Nat.add (Nat.mul l K) k)) fun U =>
  andB (bdB U) (forceB c0P fun c0 =>
  walkP c0 (D.refLet A B l) (spreadS (sliceL (Nat.mul 20 k) 20 (Sr.getD l [])) 1 (lenN D.eL))
      (packP U) fun P => forceLB (unpackP P) fun T =>
    andB (Nat.beq (neqMask T (D.rkP RK K ri O (Nat.succ (Nat.add (Nat.mul l K) k)))) 0)
      (Bool.rec (motive := fun _ => Bool) true
        (Nat.beq (Nat.land (neqV T (nthN D.βs l) (Nat.succ l)) (Nat.shiftLeft 1 l)) 0)
        (Nat.beq (Nat.succ k) K)))

end CentData

end CFSG.KD.StdOdd.Cent

end
