module

public import Certificates.Kernel.J4Q.QTBase

public section

namespace CertificateChecks.KernelJ4Q

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.Sporadic.J4.Native

theorem mkStrictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem mkId : WfA (idRows ()) ∧ encR (idRows ()) = one := ⟨wf_idRows, enc_idRows hK⟩

theorem mkMul {X Y : Array V2} {x y : Nat} (hX : WfA X ∧ encR X = x) (hY : WfA Y ∧ encR Y = y) :
    WfA (mulRows X Y) ∧ encR (mulRows X Y) = mulJ c rm x y :=
  ⟨wf_mulRows hX.1 hY.1, by rw [enc_mulRows hK hX.1 hY.1, hX.2, hY.2]⟩

theorem mkPow {X : Array V2} {x : Nat} (hX : WfA X ∧ encR X = x) (e : Nat) :
    WfA (powRows X e) ∧ encR (powRows X e) = powJ c rm one x e :=
  ⟨wf_powRows hX.1 e, by rw [enc_powRows hK hX.1, hX.2]⟩

theorem mkEq {X Y : Array V2} {x y : Nat} (hX : WfA X ∧ encR X = x) (hY : WfA Y ∧ encR Y = y) :
    eqRows X Y = Nat.beq x y := by
  rw [eqRows_eq hX.1 hY.1, hX.2, hY.2]

theorem mkRange_congr {f g : Nat → Bool} : ∀ {n : Nat}, (∀ i < n, f i = g i) →
    (List.range n).all f = (List.range n).all g
  | 0, _ => rfl
  | n + 1, h => by
    rw [List.range_succ, List.all_append, List.all_append,
      mkRange_congr fun i hi => h i (Nat.lt_succ_of_lt hi), List.all_cons, List.all_cons,
      h n (Nat.lt_succ_self n), List.all_nil, List.all_nil]

theorem mkAll_congr {α : Type} {f g : α → Bool} : ∀ {l : List α}, (∀ x ∈ l, f x = g x) →
    l.all f = l.all g
  | [], _ => rfl
  | x :: l, h => by
    rw [List.all_cons, List.all_cons, h x List.mem_cons_self,
      mkAll_congr fun y hy => h y (List.mem_cons_of_mem _ hy)]

end CertificateChecks.KernelJ4Q

end
