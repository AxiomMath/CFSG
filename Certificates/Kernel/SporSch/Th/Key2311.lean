
module

public import Certificates.Kernel.SporSch.Th.Key2311Base

public import Certificates.Kernel.SporSch.Th.Row2322
public import CFSG.Sporadic.ThSchreier.Row
public import CFSG.Sporadic.ThSchreier.LocalOrbitInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.SporSch.ThRowsSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.ThKey

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch CFSG.Sporadic.Th.Native CFSG.Sporadic.ThSchreier
open CertificateChecks.KernelSporSch
open CertificateChecks.KernelSporSch.ThRow (sh1 lt_of ltFC bindFC)

theorem facts : rowKeyOf wKey = wKeyRow := by
  have l0 : v4N wKey.u < 2 ^ 248 := by
    rw [← sh1]
    exact Nat.blt_eq.mp (allN_spec lts 0 (by omega))
  have l1 : v4N wKey.v < 2 ^ 248 := by
    rw [← sh1]
    exact Nat.blt_eq.mp (allN_spec lts 1 (by omega))
  have l2 : colK ThFC (v4N wKey.u) < 2 ^ 248 := by
    rw [← sh1]
    exact Nat.blt_eq.mp (allN_spec lts 2 (by omega))
  have l3 : colK ThFC (v4N wKey.v) < 2 ^ 248 := by
    rw [← sh1]
    exact Nat.blt_eq.mp (allN_spec lts 3 (by omega))
  have l4 : C1 < 2 ^ 248 := by
    rw [← sh1]
    exact Nat.blt_eq.mp (allN_spec lts 4 (by omega))
  have l5 : C2 < 2 ^ 248 := by
    rw [← sh1]
    exact Nat.blt_eq.mp (allN_spec lts 5 (by omega))
  have hu : wKey.u = v4OfNat (v4N wKey.u) := v4N_sound rfl
  have hv : wKey.v = v4OfNat (v4N wKey.v) := v4N_sound rfl
  have hk : wKey = ⟨v4OfNat (v4N wKey.u), v4OfNat (v4N wKey.v)⟩ := by
    rw [← hu, ← hv]
  have hrow : wKeyRow = canon (v4OfNat C1) (v4OfNat C2) := rfl
  rw [rowKeyOf, hk, v4Bind_sound bindFC, imageKey]
  dsimp only
  rw [colK_sound (lt_of ltFC) l0, colK_sound (lt_of ltFC) l1, canonN_sound l2 l3, hrow,
    canonN_sound l4 l5, Nat.eq_of_beq_eq_true key_ok]

end CertificateChecks.KernelSporSch.ThKey

end
