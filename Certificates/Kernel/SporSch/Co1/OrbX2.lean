
module

public import Certificates.Kernel.SporSch.Co1.Stab2148
public import CFSG.Sporadic.Schreier.Co1StabFixBase

public section

namespace CertificateChecks.KernelSporSch.Co1Full2135

open CFSG.Sporadic.Co1Schreier CFSG.Sporadic.SmallF2 Matrix
open CFSG.Sporadic.SmallF2.Native (transposeRows)
open CFSG.KS.Raw CFSG.KS.SporSch.M24 CFSG.KS.SporSch.VOrb
open CertificateChecks.KernelSporSch.Co1Orbs
open CertificateChecks.KernelSporSch.Co1Packed CertificateChecks.KernelSporSch.Co1Stab2148

theorem colsA_eq : CFSG.Sporadic.Co1.Native.co1Data.colsA = transposeRows 24 (unpack 24 24 PA) := by
  have hA : CFSG.Sporadic.Co1.Native.co1Data.colsA =
      transposeRows 24 CFSG.Sporadic.Co1.Native.co1Data.rowsA := rfl
  rw [hA, Co1Rows.rowsA_eq, uA]

theorem colsB_eq : CFSG.Sporadic.Co1.Native.co1Data.colsB = transposeRows 24 (unpack 24 24 PB) := by
  have hB : CFSG.Sporadic.Co1.Native.co1Data.colsB =
      transposeRows 24 CFSG.Sporadic.Co1.Native.co1Data.rowsB := rfl
  rw [hB, Co1Rows.rowsB_eq, uB]

theorem enum2 : Native.enumOK CFSG.Sporadic.Co1.Native.co1Data.colsA
    CFSG.Sporadic.Co1.Native.co1Data.colsB 2 98280 (Native.fullOrb 2) = true := by
  rw [colsA_eq, colsB_eq, full2]
  exact (vorbK_sound F2.hr (by decide) (by decide) (by decide) F2.hc0 F2.hcN F2.hb F2.hp).1

abbrev XS : Set Vec24 := kOrbit GA (toVecD 24 2)

theorem X_eq : XS = enumSet (Native.fullOrb 2) 98280 :=
  kOrbit_eq_enumSet actsBy_A₁ actsBy_A₂ enum2 (by decide)

theorem pts_lt {i : Nat} (hi : i < 98280) : (Native.fullOrb 2).pts[i]! < 2 ^ 24 :=
  ((enumOK_parts enum2).2.1 i hi).1

theorem any_eq (m : Nat) : ((List.range 98280).any fun i => (Native.fullOrb 2).pts[i]! == m) =
    memK F2.T F2.S 98280 m := by
  rw [full2]
  exact qF m

theorem memX {m : Nat} (hm : m < 2 ^ 24) :
    toVecD 24 m ∈ XS ↔ memK F2.T F2.S 98280 m = true := by
  rw [X_eq, ← any_eq, List.any_eq_true]
  constructor
  · rintro ⟨i, hi, he⟩
    exact ⟨i, List.mem_range.mpr hi, beq_iff_eq.mpr (toVecD_injective (pts_lt hi) hm he.symm)⟩
  · rintro ⟨i, hi, he⟩
    have hi' := List.mem_range.mp hi
    exact ⟨i, hi', by rw [beq_iff_eq.mp he]⟩

theorem ncard_X : XS.ncard = 98280 := by
  rw [X_eq, ncard_enumSet enum2]

theorem z_mem : stabVecOf 0 ∈ XS := (memX (by decide)).mpr x0

end CertificateChecks.KernelSporSch.Co1Full2135

end
