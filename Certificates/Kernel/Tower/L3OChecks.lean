module

public import Certificates.Data.Kernel.Tower.Out
public import Certificates.Kernel.Tower.L3WChecks
public import Certificates.Kernel.Tower.L3OData
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.EachBy
import CFSG.Certificates.Kernel.Common.ForallTree

public section

namespace Certificates.KernelTower

open Certificates.KernelTower

@[expose] noncomputable def l3bc (f j k : Nat) : Nat :=
  Nat.xor
    (Bool.rec (motive := fun _ => Nat) (l16 (wrL3 (Nat.add (Nat.mul 34 f) 1)) (Nat.shiftRight k 1))
      (l3M f (l16 (wrL3 (Nat.add (Nat.mul 34 f) 1)) (Nat.shiftRight k 1)) (l16 (l3P f) 2))
      (Nat.beq (Nat.land k 1) 1))
    (Nat.mul 2 (xbit (l3X f j) k))

@[expose] noncomputable def l3o (f j : Nat) : Bool :=
  outB (l3M f) (l3bc f j) (l3G f) (l3Im f j) (l3S f j)
    (wrL3O (Nat.add (Nat.mul 6 (Nat.add (Nat.mul 16 f) j)) 1))
    (wrL3O (Nat.mul 6 (Nat.add (Nat.mul 16 f) j)))
    (wrL3O (Nat.add (Nat.mul 6 (Nat.add (Nat.mul 16 f) j)) 2))
    (fun m => wrL3O (Nat.add (Nat.mul 6 (Nat.add (Nat.mul 16 f) j)) (Nat.add 3 m)))

@[expose] noncomputable def ch36408_l3o (t : Nat) : Bool := l3o (Nat.div t 16) (Nat.mod t 16)

@[expose] noncomputable def l3oK (f j k : Nat) : Bool :=
  allB (l16 (wrL3O (Nat.add (Nat.mul 6 (Nat.add (Nat.mul 16 f) j)) 1)) 4) fun l =>
    !Nat.beq (Nat.mod l 4) k ||
      oLab (l3M f) (l3G f) (wrL3O (Nat.add (Nat.mul 6 (Nat.add (Nat.mul 16 f) j)) 1))
        (wrL3O (Nat.mul 6 (Nat.add (Nat.mul 16 f) j)))
        (wrL3O (Nat.add (Nat.mul 6 (Nat.add (Nat.mul 16 f) j)) 2)) l

@[expose] noncomputable def l3oH (f j : Nat) : Bool :=
  (allB 4 (fun i => Nat.blt (l16 (wrL3O (Nat.add (Nat.mul 6 (Nat.add (Nat.mul 16 f) j)) 1)) i) 16384 &&
      Nat.beq (l3M f (l16 (l3Im f j) i) (l16 (wrL3O (Nat.add (Nat.mul 6 (Nat.add (Nat.mul 16 f) j)) 1)) i))
        0) &&
    Nat.beq (oMaskAll (wrL3O (Nat.add (Nat.mul 6 (Nat.add (Nat.mul 16 f) j)) 1))
      (wrL3O (Nat.add (Nat.mul 6 (Nat.add (Nat.mul 16 f) j)) 2))
      (l16 (wrL3O (Nat.add (Nat.mul 6 (Nat.add (Nat.mul 16 f) j)) 1)) 4)) (l3S f j)) &&
    allB 3 fun m => !Nat.blt (l16 (wrL3O (Nat.add (Nat.mul 6 (Nat.add (Nat.mul 16 f) j)) 1))
        (Nat.add 5 m)) (l16 (wrL3O (Nat.add (Nat.mul 6 (Nat.add (Nat.mul 16 f) j)) 1)) 4) ||
      oRep (l3M f) (l3bc f j) (l3S f j)
        (l16 (wrL3O (Nat.add (Nat.mul 6 (Nat.add (Nat.mul 16 f) j)) 2))
          (oSt (wrL3O (Nat.add (Nat.mul 6 (Nat.add (Nat.mul 16 f) j)) 1))
            (l16 (wrL3O (Nat.add (Nat.mul 6 (Nat.add (Nat.mul 16 f) j)) 1)) (Nat.add 5 m))))
        (wrL3O (Nat.add (Nat.mul 6 (Nat.add (Nat.mul 16 f) j)) (Nat.add 3 m)))

@[expose] noncomputable def ch36408_l3oC (q : Nat) : Bool :=
  l3oK (Nat.div (Nat.div q 4) 16) (Nat.mod (Nat.div q 4) 16) (Nat.mod q 4)

@[expose] noncomputable def ch36408_l3oH (t : Nat) : Bool := l3oH (Nat.div t 16) (Nat.mod t 16)

#kc_each ch36408_l3oC 0 1792
#kc_each ch36408_l3oH 0 448

#kc_forall_tree ch36408_l3oC_all (fun q => ch36408_l3oC q = true) 1792
  Certificates.KernelTower.ch36408_l3oC
#kc_forall_tree ch36408_l3oH_all (fun t => ch36408_l3oH t = true) 448
  Certificates.KernelTower.ch36408_l3oH

theorem l3o_of_parts {f j : Nat} (hH : l3oH f j = true) (hK : ∀ k < 4, l3oK f j k = true) :
    l3o f j = true := by
  simp only [l3oH, Bool.and_eq_true] at hH
  simp only [l3o, outB, Bool.and_eq_true]
  refine ⟨⟨hH.1, ?_⟩, hH.2⟩
  rw [allB_true_iff]
  intro l hl
  have h := allB_true_iff.1 (hK (l % 4) (Nat.mod_lt _ (by decide))) l hl
  have e : Nat.beq (Nat.mod l 4) (l % 4) = true := Nat.beq_refl _
  rw [e] at h
  exact h

theorem ch36408_l3o_lt (t : Nat) (ht : t < 448) : ch36408_l3o t = true := by
  have hK : ∀ k < 4, l3oK (Nat.div t 16) (Nat.mod t 16) k = true := by
    intro k hk
    have hlt : 4 * t + k < 1792 := by omega
    have h := ch36408_l3oC_all (4 * t + k) hlt
    have e1 : Nat.div (4 * t + k) 4 = t := by
      change (4 * t + k) / 4 = t
      omega
    have e2 : Nat.mod (4 * t + k) 4 = k := by
      change (4 * t + k) % 4 = k
      omega
    rw [ch36408_l3oC, e1, e2] at h
    exact h
  rw [ch36408_l3o]
  exact l3o_of_parts (ch36408_l3oH_all t ht) hK

#kc_each_by ch36408_l3o 0 448 ch36408_l3o_lt

theorem ch36408_l3o_neg :
    (!outB (l3M 0) (l3bc 0 0) (l3G 0) (l3Im 0 0) (l3S 0 0) (wrL3O 1) (Nat.xor (wrL3O 0) 1)
      (wrL3O 2) (fun m => wrL3O (Nat.add 3 m))) = true := by
  decide +kernel

theorem ch36408_l3o_neg2 :
    (!outB (l3M 0) (l3bc 0 3) (l3G 0) (l3Im 0 3) (l3S 0 3) (wrL3O 19) (wrL3O 18) (wrL3O 20)
      (fun m => Nat.xor (wrL3O (Nat.add 21 m)) (Nat.shiftLeft 1 16))) = true := by
  decide +kernel

end Certificates.KernelTower
