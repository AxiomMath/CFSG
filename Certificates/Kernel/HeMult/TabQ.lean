module

public import Certificates.Kernel.HeMult.TabFam
import CFSG.Certificates.Kernel.Spor.PackFld
import CFSG.Certificates.Kernel.Spor.Loops

public section

namespace CFSG.KD.HeMult

open CFSG.KC.Enum CFSG.KS.PEnum CFSG.KC.HeMult CFSG.KD.HeOrb CFSG.KD.HeTab
  CFSG.Sporadic.Recognition.HeMultiplier

@[expose] noncomputable def sliceQ (p : Nat → Bool) (m : Nat) : Bool :=
  allN (nat_lit 250) fun d => strictB (Nat.add (Nat.mul (nat_lit 250) m) d) fun x =>
    bIf(Nat.blt x (nat_lit 8330), p x, true)

theorem slice_of_quarters {p : Nat → Bool} {c : Nat} (h : ∀ q < 4, sliceQ p (4 * c + q) = true) :
    slice p c = true := by
  unfold slice
  refine CFSG.KS.PackFld.allN_of_forall fun d hd => ?_
  have hd1 : d < 1000 := hd
  have h1 := CFSG.KS.allN_spec (h (d / 250) (by omega)) (d % 250) (Nat.mod_lt _ (by decide))
  have e : Nat.add (Nat.mul (nat_lit 250) (4 * c + d / 250)) (d % 250) =
      Nat.add (Nat.mul (nat_lit 1000) c) d := by
    show 250 * (4 * c + d / 250) + d % 250 = 1000 * c + d
    omega
  simp only [e] at h1
  exact h1

@[expose] noncomputable def famRQ (m : Nat) : Bool :=
  sliceQ (relK AL BE U V S T Ui Vi Si Ti heTabRels heSurjA heSurjB) m

@[expose] noncomputable def famRQ0 (m : Nat) : Bool := famRQ m
@[expose] noncomputable def famRQ1 (m : Nat) : Bool := famRQ (Nat.add m (nat_lit 12))
@[expose] noncomputable def famRQ2 (m : Nat) : Bool := famRQ (Nat.add m (nat_lit 24))

theorem famR_of_quarters {c : Nat} (h : ∀ q < 4, famRQ (4 * c + q) = true) : famR c = true :=
  slice_of_quarters h

end CFSG.KD.HeMult

end
