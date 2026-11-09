module

public import Certificates.Data.Kernel.LceJson

public section

namespace CertificateChecks.KernelFi22F

open CFSG.KC CFSG.KC.LceJson CFSG.Certificates.LCE

theorem recAll {g : Nat → Bool} (hg : ∀ h, g h = true) :
    ∀ n, Nat.rec (motive := fun _ => Bool) true (fun h ih => andB (g h) ih) n = true
  | 0 => rfl
  | n + 1 => by
    show andB (g n) (Nat.rec (motive := fun _ => Bool) true (fun h ih => andB (g h) ih) n) = true
    rw [hg n, recAll hg n]
    rfl

theorem selW_mod (WT : List (List Nat)) (m k : Nat) :
    Nat.beq (selW WT m k) (selW WT m (Nat.mod k m)) = true := by
  have e : Nat.mod (Nat.mod k m) m = Nat.mod k m := Nat.mod_mod k m
  unfold selW
  rw [e]
  exact Nat.beq_refl _

theorem wtPer_selW (WT : List (List Nat)) (m : Nat) : wtPer (selW WT m) m = true := by
  unfold wtPer
  exact recAll (g := fun h => Nat.rec (motive := fun _ => Bool) true (fun l ih2 => andB
      ((fun k => Nat.beq (selW WT m k) (selW WT m (Nat.mod k m))) (Nat.add (Nat.shiftLeft h (nat_lit 8)) l)) ih2)
      (nat_lit 256))
    (fun h => recAll
      (g := fun l => (fun k => Nat.beq (selW WT m k) (selW WT m (Nat.mod k m)))
        (Nat.add (Nat.shiftLeft h (nat_lit 8)) l))
      (fun l => selW_mod WT m (Nat.add (Nat.shiftLeft h (nat_lit 8)) l)) (nat_lit 256)) (nat_lit 256)

end CertificateChecks.KernelFi22F

end
