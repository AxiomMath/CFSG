module

public import Certificates.Kernel.SporSch.Tits.Common
public import Certificates.Kernel.LocalComp.Tits.Bind
public import CFSG.Sporadic.Schreier.TitsCertCheck
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.TitsIso

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim
open CFSG.Sporadic.Schreier.Tits CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.Tits2264 CertificateChecks.KernelMisc
open CertificateChecks.KernelSporSch.TitsCommon CertificateChecks.KernelLC.Tits
open CFSG.KC.LocalComp.Tits

theorem kPerm : permOK 1755 11 (mask 11) (1755 * 11) (TitsText.F 95)
    (pinvS 1755 11 (mask 11) (TitsText.F 95)) = true := by quickRfl

theorem kHi : Nat.beq (Nat.shiftRight (TitsText.F 95) (1755 * 11)) 0 = true := by quickRfl
theorem kHiG : allN 4 (fun s => Nat.beq (Nat.shiftRight (TitsText.F s) (1755 * 11)) 0) = true := by
  quickRfl
theorem kTG : allN 4 (fun s => allN 1755 (fun i => Nat.blt (pg 11 (mask 11) (TG s) i) 2048)) =
    true := by quickRfl

theorem kInt : allN 4 (fun s => allN 1755 (fun i =>
    Nat.beq (pg 11 (mask 11) (TitsText.F 95) (pg 11 (mask 11) (TG s) i))
      (pg 11 (mask 11) (TitsText.F s) (pg 11 (mask 11) (TitsText.F 95) i)))) = true := by quickRfl

theorem sigma_eq : titsSigmaArr = unpack 1755 11 (TitsText.F 95) := by
  rw [titsSigmaArr]
  exact TitsText.titsArr1755_eq (by norm_num)

theorem ap_eq {s i : Nat} (hs : s < 4) (hi : i < 1755)
    (hb : Nat.blt (pg 11 (mask 11) (TG s) i) 2048 = true) :
    CFSG.Sporadic.Th.Native.ap CFSG.SectionRank.Native.Tits.genTables[s]! i =
      pg 11 (mask 11) (TG s) i := by
  rw [gens_eq, getElem!_pos _ s (by simpa using hs), Array.getElem_ofFn]
  unfold CFSG.Sporadic.Th.Native.ap tabP
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]
  exact UInt32.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le (Nat.blt_eq ▸ hb) (by decide))

theorem facts : isInvA 1755 titsSigmaArr (invCand 1755 titsSigmaArr) = true ∧
    CFSG.SectionRank.Native.Tits.genTables.size = 4 ∧
    (∀ s < 4, ∀ i < 1755, titsSigmaArr[
      CFSG.Sporadic.Th.Native.ap CFSG.SectionRank.Native.Tits.genTables[s]! i]! =
        (titsGenArrs[s]!)[titsSigmaArr[i]!]!) := by
  refine ⟨?_, by rw [gens_eq]; simp, fun s hs i hi => ?_⟩
  · rw [sigma_eq]
    obtain ⟨e1, e2⟩ := invEqK_sound kPerm
    rw [e1]
    exact e2
  · rw [ap_eq hs hi (allN_spec (allN_spec kTG s hs) i hi), sigma_eq, gen_eq hs]
    simp only [unpack_get0 kHi, unpack_get0 (allN_spec kHiG s hs)]
    exact Nat.eq_of_beq_eq_true (allN_spec (allN_spec kInt s hs) i hi)

end CertificateChecks.KernelSporSch.TitsIso

end
