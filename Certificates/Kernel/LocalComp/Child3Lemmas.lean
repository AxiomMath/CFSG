module

public import CFSG.Certificates.Kernel.Child3Sound
public import CFSG.Certificates.Kernel.Spor.PrimSound

public section

namespace CFSG.KC.Child3

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.Monster.B.Co2.Native
open CFSG.EvenSmallLie.Child3

abbrev CnN (n w X : Nat) : Prop := canonK n w (mask w) (n * w) X = true

theorem compA_unpackN {n w p q : Nat} (hp : CnN n w p) (hq : CnN n w q) :
    compA n (unpack n w p) (unpack n w q) = unpack n w (pcomp n w (mask w) p q) := by
  apply compEqK_sound
  unfold compEqK
  rw [hp, hq]
  exact Nat.beq_refl _

@[expose] noncomputable def ppowN (n w P : Nat) : Nat → Nat
  | 0 => pidn n w
  | k + 1 => pcomp n w (mask w) P (ppowN n w P k)

theorem powN_unpack {n w P : Nat} (hP : CnN n w P) (hid : unpack n w (pidn n w) = idA n)
    (hidc : CnN n w (pidn n w)) :
    ∀ k, powN n (unpack n w P) k = unpack n w (ppowN n w P k) ∧ CnN n w (ppowN n w P k)
  | 0 => ⟨hid.symm, hidc⟩
  | k + 1 => by
    obtain ⟨e, c⟩ := powN_unpack hP hid hidc k
    refine ⟨?_, canon_pcN hP c⟩
    unfold powN ppowN
    rw [e, compA_unpackN hP c]

theorem getElem!_map' {α β : Type} [Inhabited α] [Inhabited β] {a : Array α} {f : α → β}
    {l : Nat} (hl : l < a.size) : (a.map f)[l]! = f a[l]! := by
  rw [getElem!_pos (a.map f) l (by simpa using hl), getElem!_pos a l hl, Array.getElem_map]

end CFSG.KC.Child3

end
