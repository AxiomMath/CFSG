module

public import Certificates.Data.Kernel.HNLocalK

public section

namespace CFSG.KC.HNLocal

open CFSG.KC.Loop

theorem treeSum_add (XC TD MSF : Nat → Nat) (N M L H CM3 RM GA GB GFC lo a : Nat) : ∀ b,
    treeSum XC TD MSF N M L H CM3 RM GA GB GFC lo (a + b) =
      treeSum XC TD MSF N M L H CM3 RM GA GB GFC lo a +
        treeSum XC TD MSF N M L H CM3 RM GA GB GFC (lo + a) b
  | 0 => (Nat.add_zero _).symm
  | b + 1 => by
    have e : ∀ (y : Nat) (k : Nat → Nat), strictN y k = k y := fun y k => by cases y <;> rfl
    change strictN (treeSum XC TD MSF N M L H CM3 RM GA GB GFC lo (a + b))
        (fun x => x + treeLeaf XC TD MSF N M L H CM3 RM GA GB GFC (lo + (a + b))) =
      treeSum XC TD MSF N M L H CM3 RM GA GB GFC lo a +
        strictN (treeSum XC TD MSF N M L H CM3 RM GA GB GFC (lo + a) b)
          (fun x => x + treeLeaf XC TD MSF N M L H CM3 RM GA GB GFC (lo + a + b))
    rw [e, e, treeSum_add XC TD MSF N M L H CM3 RM GA GB GFC lo a b, Nat.add_assoc lo a b,
      Nat.add_assoc]

theorem treeSum_join {XC TD MSF : Nat → Nat} {N M L H CM3 RM GA GB GFC lo n1 lo2 n2 n v1 v2 v : Nat}
    (h1 : Nat.beq (treeSum XC TD MSF N M L H CM3 RM GA GB GFC lo n1) v1 = true)
    (h2 : Nat.beq (treeSum XC TD MSF N M L H CM3 RM GA GB GFC lo2 n2) v2 = true)
    (e1 : lo2 = lo + n1) (e2 : n = n1 + n2) (e3 : v = v1 + v2) :
    Nat.beq (treeSum XC TD MSF N M L H CM3 RM GA GB GFC lo n) v = true := by
  subst e1 e2 e3
  rw [treeSum_add, Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2]
  exact Nat.beq_refl _

end CFSG.KC.HNLocal

end
