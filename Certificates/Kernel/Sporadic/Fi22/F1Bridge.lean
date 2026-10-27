module

public import Certificates.Kernel.Sporadic.Fi22.F1BridgeK
public import Certificates.Kernel.Sporadic.Fi22.C3039
public import Certificates.Kernel.Sporadic.Fi22.E2067
public import CFSG.Certificates.Kernel.Misc.ArrEnumOps

public section

namespace CertificateChecks.KernelSpor.Fi22F1B

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KC.Misc.ArrEnum
open CFSG.Monster.B.Fischer CFSG.Monster.B.Co2.Native
open CertificateChecks.KernelSpor CertificateChecks.KernelMonB

theorem hw : szOK 3510 12 = true := by decide +kernel

theorem xi_eq : pinXiRaw = unpack 3510 12 XP := by
  have h := CFSG.KC.Misc.HexFlat.hexTable3_sound Fi22PXT.all 0 (by norm_num)
  rw [← Fi22PXT.eq, Nat.mul_zero] at h
  exact h

theorem cand_eq {k : Nat} (hk : k < 13) : indCandidate k = unpack 3510 12 (candP k) := by
  unfold indCandidate candP
  by_cases h2 : k < 2
  · have hb : Nat.blt k 2 = true := by simpa using h2
    rw [if_pos h2, hb]
    have h := CFSG.KC.Misc.HexFlat.hexTable3_sound IG.all k h2
    rw [← IG.eq] at h
    exact h
  · have hb : Nat.blt k 2 = false := Bool.eq_false_iff.2 fun e => h2 (Eq.mp Nat.blt_eq e)
    rw [if_neg h2, hb]
    by_cases h12 : k < 12
    · have hb' : Nat.blt k 12 = true := by simpa using h12
      rw [if_pos h12, hb']
      have hk2 : k - 2 < 10 := by omega
      have h := CFSG.KC.Misc.HexFlat.hexTable3_sound ITr.all (k - 2) hk2
      rw [← ITr.eq] at h
      exact h
    · have hb' : Nat.blt k 12 = false := Bool.eq_false_iff.2 fun e => h12 (Eq.mp Nat.blt_eq e)
      rw [if_neg h12, hb']
      have h := CFSG.KC.Misc.HexFlat.hexTable3_sound ICe.all 0 (by norm_num)
      rw [← ICe.eq, Nat.mul_zero] at h
      exact h

theorem letters : ∀ k < 13, lettersOK 19 (pinWord k) = true := by decide +kernel

theorem facts3040 : isInvA 3510 pinXiRaw (invCand 3510 pinXiRaw) = true ∧
    (∀ k < 13, lettersOK 19 (pinWord k) = true ∧
      eqA 3510 (wordA 3510 fi22StrongArrs fi22StrongInvs (pinWord k))
        (compA 3510 (compA 3510 pinXiRaw (indCandidate k)) (invCand 3510 pinXiRaw)) = true) ∧
    (pinMembership.map fun m => m.strongGeneratorWord.length) =
      [14, 12, 18, 16, 20, 12, 21, 16, 16, 17, 16, 5, 8] ∧
    (pinMembership.map fun m => m.modelGenerator) = List.range 13 := by
  have hX := pp_of_permB hw permX
  have hSp : ∀ h < 19, permB 3510 12 (Fi22ChT.F h) = true := fun h hh => allN_spec permS h hh
  have hS : ∀ h < 19, fi22StrongArrs[h]! = unpack 3510 12 (Fi22ChT.F h) :=
    fun h hh => Fi22X.strong_eq hh
  have hSI : ∀ h < 19, fi22StrongInvs[h]! = unpack 3510 12 (SIP h) := fun h hh => by
    rw [Fi22C3039.invs_eq, Orb.rawInvs_get (by rw [Fi22C3039.size19]; exact hh), Fi22X.strong_eq hh]
    exact invCand_PP (pp_of_permB hw (hSp h hh))
  have hSIp : ∀ h < 19, permB 3510 12 (SIP h) = true := fun h hh => permB_pinvS hw (hSp h hh)
  refine ⟨Fi22E2067.isInv_of xi_eq permX, fun k hk => ⟨letters k hk, ?_⟩, by decide +kernel,
    by decide +kernel⟩
  have hC := pp_of_permB hw (allN_spec permC k hk)
  rw [wordA_eq hw hS hSI hSp hSIp _ (letters k hk), xi_eq, cand_eq hk, invCand_PP hX,
    compA_PP hX hC, compA_PP (hX.mul hC) hX.inv,
    eqA_PP (pp_wordK hw hSp hSIp _ (letters k hk)) ((hX.mul hC).mul hX.inv)]
  exact wordAll k hk

end CertificateChecks.KernelSpor.Fi22F1B

end
