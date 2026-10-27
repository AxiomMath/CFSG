module

public import Certificates.Data.Kernel.Multipliers.BindList
public import CFSG.Certificates.Kernel.Spor.Loops
public import CFSG.Certificates.Kernel.Spor.RawDefs

public section

namespace CFSG.KC.BindList

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem bindListK_get {w m P : Nat} :
    ∀ (l : List Nat) (k : Nat), bindListK w m P l k = true → ∀ i (hi : i < l.length),
      l[i] = pg w m P (k + i)
  | [], _, _, i, hi => absurd hi (by simp)
  | x :: l, k, h, i, hi => by
    change Bool.rec (motive := fun _ => Bool) false
      (strictB (Nat.succ k) (bindListK w m P l)) (Nat.beq x (pg w m P k)) = true at h
    rw [bAnd_iff, strictB_eq] at h
    obtain ⟨h1, h2⟩ := h
    rcases i with _ | i
    · simpa using Nat.eq_of_beq_eq_true h1
    · rw [List.getElem_cons_succ, bindListK_get l (k + 1) h2 i (by simpa using hi)]
      congr 1
      omega

theorem toArray_eq_unpack {n w P : Nat} {l : List Nat} (hn : l.length = n)
    (h : bindListK w (mask w) P l 0 = true) : l.toArray = unpack n w P := by
  unfold unpack
  refine Array.ext (by simp [hn]) fun i hi _ => ?_
  simp only [List.getElem_toArray, Array.getElem_ofFn]
  rw [bindListK_get l 0 h i (by simpa using hi), Nat.zero_add]

theorem permOK_inv {n w m nw p q : Nat} (h : permOK n w m nw p q = true) :
    ∀ i < n, pg w m p i < n ∧ pg w m q (pg w m p i) = i := by
  unfold permOK at h
  rw [bAnd_iff, bAnd_iff] at h
  intro i hi
  have := allN_spec h.2.2 i hi
  rw [strictB_eq, bAnd_iff] at this
  exact ⟨Nat.blt_eq.mp this.1, Nat.eq_of_beq_eq_true this.2⟩

end CFSG.KC.BindList

end
