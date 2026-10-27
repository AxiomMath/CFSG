
module

public import Certificates.Kernel.SporSch.Co3.OrbitZ
public import CFSG.Certificates.Kernel.SporSch.SetReplayProof

public section

namespace CertificateChecks.KernelSporSch.Co3OrbZP

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch
open CFSG.Sporadic.Schreier.Co3 CFSG.Sporadic.Schreier.Co3.Native CFSG.Certificates.Native
open CertificateChecks.KernelSpor CertificateChecks.KernelSporSch

theorem replay : SetReplayOK 276 9 36 2 170775 170775 134 10 42 32 128 Co3OZ.G Co3OZ.GI
    (rowGet Co3OZ.XT 352) (rowGet Co3OZ.WT 40) (rowGet Co3OZ.ST 20) (rowGet Co3OZ.SIT 20) Co3OZ.C
    co3IzNat :=
  ⟨by norm_num, by norm_num, by norm_num, by norm_num, le_refl _, by norm_num, by norm_num,
    by norm_num, by norm_num, fun k hk => allN_spec Co3OrbZ.perm k hk, Co3OrbZ.start, Co3OZ.helt,
    Co3OZ.hsrt, Nat.eq_of_beq_eq_true Co3OrbZ.c0, Nat.eq_of_beq_eq_true Co3OrbZ.cN, Co3OZ.hrun⟩

theorem facts : translatesOK co3OrigArrs co3IzNat co3OrbitZ.1 co3OrbitZ.2.1 co3OrbitZ.2.2 = true ∧
    keysSortedOK co3OrbitZ.1 = true ∧ co3OrbitZ.1.size = 170775 := by
  have hc : co3ChainArrs.size = 14 := Co3C.binds.2.2.2.1
  refine SRP.setReplay_proved ⟨by simp [co3OrigArrs, hc], fun k hk => ?_⟩ replay
  rw [co3OrigArrs, Co3OrbZ.extract_get hk (by omega), Co3C.binds.2.2.2.2.1 k (by omega),
    Nat.eq_of_beq_eq_true (allN_spec Co3OrbZ.gens k hk)]

end CertificateChecks.KernelSporSch.Co3OrbZP

end
