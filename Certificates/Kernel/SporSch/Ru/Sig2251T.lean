module

public import Certificates.Kernel.SporSch.Ru.Sig2251P
public import CFSG.Certificates.Kernel.SporSch.RuVOrbProved
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.RuSig

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CFSG.KC.VecK CFSG.Sporadic.RuSchreier
  CFSG.Monster.B.Co2.Native CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallF2.Native
  CertificateChecks.KernelSporSch.RuG CertificateChecks.KernelVec.Ru

theorem tables_proved : ∀ i < 4060,
    ap (CFSG.Sporadic.Ru.Native.ruData.orbit ()).alpha i = lk AT 32 i ∧
      ap (CFSG.Sporadic.Ru.Native.ruData.orbit ()).beta i = lk BT 32 i :=
  vOrbit_tables_proved (CFSG.Sporadic.Ru.Native.ruData ()) hA hB seed (by quickRfl) p0 horb hbfs
    hsort

theorem facts_proved : isInvA 4060 ruSigmaA (invCand 4060 ruSigmaA) = true ∧
    (∀ i < 4060, ruSigmaA[ruA0A[i]!]! =
        ap (CFSG.Sporadic.Ru.Native.ruData.orbit ()).alpha ruSigmaA[i]! ∧
      ruSigmaA[ruA1A[i]!]! = ap (CFSG.Sporadic.Ru.Native.ruData.orbit ()).beta ruSigmaA[i]!) := by
  refine ⟨(inv_of sig_eq pSig).2, fun i hi => ?_⟩
  have hs : pg 12 (mask 12) SIG i < 4060 := by simpa [Nat.blt_eq] using allN_spec sigLt i hi
  have h0 : pg 12 (mask 12) A0 i < 4060 := by simpa [Nat.blt_eq] using allN_spec a0Lt i hi
  have h1 : pg 12 (mask 12) A1 i < 4060 := by simpa [Nat.blt_eq] using allN_spec a1Lt i hi
  obtain ⟨tA, tB⟩ := tables_proved _ hs
  rw [sig_eq, a0_eq, a1_eq, get_unpack hi, get_unpack hi, get_unpack hi, get_unpack h0,
    get_unpack h1, tA, tB]
  exact ⟨Nat.eq_of_beq_eq_true (allN_spec eqA0 i hi), Nat.eq_of_beq_eq_true (allN_spec eqA1 i hi)⟩

end CertificateChecks.KernelSporSch.RuSig

end
