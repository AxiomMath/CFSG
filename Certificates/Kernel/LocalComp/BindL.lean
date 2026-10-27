module

public import CFSG.Certificates.Kernel.LocalCompUnpackList

public section

namespace CertificateChecks.KernelLC.BindL

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

@[expose] noncomputable def gensP (n w g : Nat) (G : Nat → Nat) : Bool :=
  allN g fun k => permOK n w (mask w) (n * w) (G k) (pinvS n w (mask w) (G k))

@[expose] noncomputable def bindL (gs : List (Array Nat)) (n w g : Nat) (G : Nat → Nat) : Bool :=
  Nat.beq gs.toArray.size g && allN g fun k =>
    Nat.beq gs.toArray[k]!.size n && bindListFromK gs.toArray[k]!.toList w (G k) 0

theorem bindA_eq {A : Array Nat} {n w P : Nat}
    (h : (Nat.beq A.size n && bindListFromK A.toList w P 0) = true) : A = unpack n w P := by
  rw [Bool.and_eq_true] at h
  have e := toArray_eq_of_bindListFromK h.2
  rw [Array.toArray_toList, Array.length_toList, Nat.eq_of_beq_eq_true h.1] at e
  exact e

theorem bindL_get {gs : List (Array Nat)} {n w g : Nat} {G : Nat → Nat}
    (h : bindL gs n w g G = true) :
    gs.toArray.size = g ∧ ∀ k < g, gs.toArray[k]! = unpack n w (G k) := by
  unfold bindL at h
  rw [Bool.and_eq_true] at h
  exact ⟨Nat.eq_of_beq_eq_true h.1, fun k hk => bindA_eq (allN_spec h.2 k hk)⟩

end CertificateChecks.KernelLC.BindL

end
