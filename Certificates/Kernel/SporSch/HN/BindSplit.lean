module

public import Certificates.Data.Kernel.SporSch.HNXBind

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.Sporadic.HNSchreier.Native

@[expose] def otL : OrbitNats → OrbitNats
  | .leaf w c b => .leaf w c b
  | .branch _ a _ => a

@[expose] def otR : OrbitNats → OrbitNats
  | .leaf w c b => .leaf w c b
  | .branch _ _ b => b

@[expose] def otS : OrbitNats → Nat
  | .leaf _ _ _ => 0
  | .branch ls _ _ => ls

@[expose] def otBr : OrbitNats → Bool
  | .leaf _ _ _ => false
  | .branch _ _ _ => true

theorem walkOK_of_br {f : Nat → Nat → Bool} {t : OrbitNats} {o : Nat} (hb : otBr t = true)
    (h1 : walkOK f (otL t) o = true) (h2 : walkOK f (otR t) (Nat.add o (otS t)) = true) :
    walkOK f t o = true := by
  cases t with
  | leaf w c b => exact absurd hb Bool.false_ne_true
  | branch ls a b =>
    have h1' : walkOK f a o = true := h1
    have h2' : walkOK f b (Nat.add o ls) = true := h2
    have e : strictB (Nat.add o ls) (walkOK f b) = walkOK f b (Nat.add o ls) := by
      unfold strictB
      cases Nat.add o ls <;> rfl
    show bAnd(walkOK f a o, strictB (Nat.add o ls) (walkOK f b)) = true
    rw [e, h1', h2']

end CFSG.KS.SporSch

end
