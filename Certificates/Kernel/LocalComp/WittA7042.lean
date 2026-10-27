module

public import Certificates.Kernel.LocalComp.M22Hexads
public import CFSG.Quasithin.Recognition.M22UniqueDataInputs

public section

namespace CertificateChecks.KernelLC.Witt

open Equiv CFSG.ComponentClassification.WittDesign CFSG.Quasithin.Asc94

@[expose] def witWs : List (List Bool) :=
  [[], [], [],
    [],
    [false, true, true, false, true, false, true, false, true, true, false, true, false, true, true,
      true, false, true, false, true, false, true, true, false, true, false],
    [false, true, false, true, false, true, true, true, false, true, true, true, false],
    [true, true, true, false, true, true, false, true, false, true, true, true, false, true, false,
      true, true, true, false, true, false, true, false, true],
    [true, false, true, false, true, false, true, true, false, true, false, true, false, true, true,
      true, false, true, false, true, true, false],
    [true, false, true, false, true, true, false, true, true, true, false, true, true, true],
    [],
    [false, true, true, false, true, false, true, false, true, true, false, true, true, true, false,
      true, true, true, false, true, true, false],
    [true, true, true, false, true, false, true, true, false, true, true, true, false, true, false,
      true, false, true, true, false, true, true, true],
    [true, false, true, false, true, false, true, false, true, true, true, false, true, false, true,
      false],
    [true, false, true, false, true, false, true, false, true, true, false, true, true, false, true,
      false, true, false, true, false],
    [true, true, true, false, true, true, false, true, false, true, true, true, false, true, true,
      false, true],
    [true, false, true, true, false, true, true, true, false, true, true, true, false, true, false,
      true, true, false, true, true, true, false, true],
    [false, true, false, true, false, true, true, false, true, false, true, false, true, false, true,
      false, true, true, false, true, false, true, false, true, false, true],
    [],
    [false, true, true, false, true, false, true, true, true, false, true, false, true, true, false,
      true, false, true, false, true, true],
    [],
    [true, true, true, false, true, true, true, false, true, true, true, false, true, false, true,
      false, true],
    [false, true, true, false, true, true, true, false, true, true, true, false, true, true, false,
      true, false, true, false, true, true, false]]

theorem witWs_ok : ∀ y : Fin 22, y ∉ m22HexadL →
    (KernelLC.wordPerm (witWs.getD y.val []) 0 = 0 ∧
      (∀ p ∈ m22HexadL, KernelLC.wordPerm (witWs.getD y.val []) p ∈ m22HexadL) ∧
      KernelLC.wordPerm (witWs.getD y.val []) 3 = y) := by
  decide +kernel

theorem count_ptHex_trans : ∀ y : Fin 22, y ∉ m22HexadL →
    0 < m22Count (fun σ => σ 0 = 0 ∧ (∀ p ∈ m22HexadL, σ p ∈ m22HexadL) ∧ σ 3 = y) := by
  intro y hy
  rw [← card_m22_subtype]
  have : Nonempty {x : M22 // ((x : Perm (Fin 22)) 0 = 0 ∧
      (∀ p ∈ m22HexadL, (x : Perm (Fin 22)) p ∈ m22HexadL) ∧ (x : Perm (Fin 22)) 3 = y)} :=
    ⟨⟨⟨_, KernelLC.wordPerm_mem (witWs.getD y.val [])⟩, witWs_ok y hy⟩⟩
  exact Nat.card_pos

end CertificateChecks.KernelLC.Witt

end
