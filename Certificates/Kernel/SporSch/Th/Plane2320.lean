
module

public import Certificates.Kernel.SporSch.Th.Plane2320Base
public import Certificates.Kernel.SporSch.Th.Orb2315

public import CFSG.Sporadic.Th.Max3.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelSporSch.ThPlane

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch CFSG.Sporadic.Th.Native CFSG.Sporadic.ThSchreier
open CertificateChecks.KernelSporSch
open CertificateChecks.KernelSporSch.ThRow (sh1)
open CertificateChecks.KernelSporSch.ThUA (all8 UB ltUB block_eq rowsA_eq un)
open CertificateChecks.KernelSporSch.ThKey (C1 C2)

@[expose] noncomputable def IA : Nat := vmT (unpk ThO.VI) (canonN C1 C2 % 2 ^ 256)
@[expose] noncomputable def IB : Nat := vmT (unpk ThO.VI) (canonN C1 C2 / 2 ^ 256)
@[expose] noncomputable def SU : Nat :=
  canonN (vmT (unpk ThO.VI) (canonN C1 C2 % 2 ^ 256))
    (vmT (unpk ThO.VI) (canonN C1 C2 / 2 ^ 256)) % 2 ^ 256
@[expose] noncomputable def SV : Nat :=
  canonN (vmT (unpk ThO.VI) (canonN C1 C2 % 2 ^ 256))
    (vmT (unpk ThO.VI) (canonN C1 C2 / 2 ^ 256)) / 2 ^ 256

theorem kIA : Nat.blt IA (Nat.shiftLeft 1 248) = true := by quickRfl
theorem kIB : Nat.blt IB (Nat.shiftLeft 1 248) = true := by quickRfl
theorem kSU : Nat.blt SU (Nat.shiftLeft 1 248) = true := by quickRfl
theorem kSV : Nat.blt SV (Nat.shiftLeft 1 248) = true := by quickRfl
theorem uU : Nat.beq (Nat.shiftRight (vmT (UB 1) SU) 120) 0 = true := by quickRfl
theorem uV : Nat.beq (Nat.shiftRight (vmT (UB 1) SV) 120) 0 = true := by quickRfl

theorem facts : inUA starKey.u = true ∧ inUA starKey.v = true := by
  have hrow : wKeyRow = canon (v4OfNat C1) (v4OfNat C2) := rfl
  have hk : starKey = ⟨v4OfNat SU, v4OfNat SV⟩ := by
    rw [starKey, ThOrb.rowsVInv_eq, hrow, canonN_sound (bnd kC1) (bnd kC2), imageKey]
    dsimp only
    have hS0 : ∀ i < 248, unpk ThO.VI i < 2 ^ 248 := fun i _ => unpk_lt ThO.VI i
    rw [frApply_sound (R := unpk ThO.VI) (x := canonN C1 C2 % 2 ^ 256) hS0 (bnd kA),
      frApply_sound (R := unpk ThO.VI) (x := canonN C1 C2 / 2 ^ 256) hS0 (bnd kB),
      canonN_sound (a := vmT (unpk ThO.VI) (canonN C1 C2 % 2 ^ 256))
        (b := vmT (unpk ThO.VI) (canonN C1 C2 / 2 ^ 256)) (bnd kIA) (bnd kIB)]
    rfl
  rw [hk, inUA, inUA, rowsUAQ, block_eq 1 (by omega)]
  exact ⟨inUAT_sound (ltUB 1 (by omega)) (bnd kSU) (Nat.eq_of_beq_eq_true uU),
    inUAT_sound (ltUB 1 (by omega)) (bnd kSV) (Nat.eq_of_beq_eq_true uV)⟩

end CertificateChecks.KernelSporSch.ThPlane

end
