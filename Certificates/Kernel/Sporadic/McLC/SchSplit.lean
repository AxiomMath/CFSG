module

public import Certificates.Data.Kernel.Spor.PChain
public import CFSG.Certificates.Kernel.Spor.Loops
public import CFSG.Certificates.Kernel.BfsPinBaseSound

public section

namespace CFSG.KS.PC

open CFSG.KC.Enum

theorem strictB_eqPC (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem schSlK_split {L : Nat → Nat → Nat} {B : Nat → Nat} {NL : Nat}
    {PTS POS PAR LAB : Nat → Nat → Nat} {CNT QB : Nat → Nat} {Q : List Nat} {m i : Nat}
    (lo a b lo' : Nat) (hlo : lo + a = lo')
    (h1 : schSlK L B NL PTS POS PAR LAB CNT QB Q m i lo a = true)
    (h2 : schSlK L B NL PTS POS PAR LAB CNT QB Q m i lo' b = true) :
    schSlK L B NL PTS POS PAR LAB CNT QB Q m i lo (a + b) = true := by
  unfold schSlK at h1 h2 ⊢
  rw [strictB_eqPC] at h1 h2 ⊢
  refine CFSG.KC.BfsPin.allN_intro fun d hd => ?_
  by_cases hda : d < a
  · exact CFSG.KS.allN_spec h1 d hda
  · have h := CFSG.KS.allN_spec h2 (d - a) (by omega)
    have e : Nat.add lo' (d - a) = Nat.add lo d := by
      subst hlo
      change lo + a + (d - a) = lo + d
      omega
    rw [e] at h
    exact h

end CFSG.KS.PC

end
