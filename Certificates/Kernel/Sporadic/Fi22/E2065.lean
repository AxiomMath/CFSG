module

public import Certificates.Kernel.Sporadic.Fi22.E2065T
public import Certificates.Kernel.Sporadic.Fi22.E2065I
public import Certificates.Kernel.Sporadic.Fi22.E2067
public import CFSG.Sporadic.FischerOddCore.Fi22CentCheckInputs
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000
set_option Elab.async false

namespace CertificateChecks.KernelSpor.Fi22E2065

open CFSG.KC.Enum CFSG.KS CFSG.KS.Text CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin
open CFSG.Sporadic.FischerOddCore CFSG.Monster.B.Fischer CFSG.Monster.B.Co2.Native

@[expose] noncomputable def permSl (s : Nat) : Bool :=
  allN 20 (fun j => strictB (Nat.add (Nat.mul 20 s) j) (fun L => bIf(Nat.blt L 306,
    permOK 3510 12 (mask 12) (3510 * 12) (Fi22CentT.L L) (CI L), true)))

theorem ps0 : permSl 0 = true := by quickRfl
theorem ps1 : permSl 1 = true := by quickRfl
theorem ps2 : permSl 2 = true := by quickRfl
theorem ps3 : permSl 3 = true := by quickRfl
theorem ps4 : permSl 4 = true := by quickRfl
theorem ps5 : permSl 5 = true := by quickRfl
theorem ps6 : permSl 6 = true := by quickRfl
theorem ps7 : permSl 7 = true := by quickRfl
theorem ps8 : permSl 8 = true := by quickRfl
theorem ps9 : permSl 9 = true := by quickRfl
theorem ps10 : permSl 10 = true := by quickRfl
theorem ps11 : permSl 11 = true := by quickRfl
theorem ps12 : permSl 12 = true := by quickRfl
theorem ps13 : permSl 13 = true := by quickRfl
theorem ps14 : permSl 14 = true := by quickRfl
theorem ps15 : permSl 15 = true := by quickRfl

theorem perm {L : Nat} (hL : L < 306) :
    permOK 3510 12 (mask 12) (3510 * 12) (Fi22CentT.L L) (CI L) = true := by
  have hs : ∀ s < 16, permSl s = true := by
    intro s hs
    interval_cases s
    exacts [ps0, ps1, ps2, ps3, ps4, ps5, ps6, ps7, ps8, ps9, ps10, ps11, ps12, ps13, ps14, ps15]
  have h := allN_spec (hs (L / 20) (by omega)) (L % 20) (Nat.mod_lt _ (by norm_num))
  rw [strictB_eq] at h
  have e : Nat.add (Nat.mul 20 (L / 20)) (L % 20) = L := by
    change 20 * (L / 20) + L % 20 = L
    omega
  rw [e] at h
  have hb : Nat.blt L 306 = true := Eq.mpr Nat.blt_eq hL
  rw [hb] at h
  exact h

theorem cent_eq {L : Nat} : fi22CentArr L = unpack 3510 12 (Fi22CentT.L L) := rfl

theorem dk : allN 5 (fun c => CFSG.KS.SporSch.derivK (fi22CentGenCount.getD c 0)
    (fi22CentStrongCount.getD c 0) (fi22CentDerivations.getD c [])) = true := by quickRfl

theorem facts2065 :
    (∀ L < 306, isInvA 3510 (fi22CentArr L) (invCand 3510 (fi22CentArr L)) = true) ∧
    fi22CentBases = List.replicate 5 [0, 1, 2, 3, 6, 4] ∧
    fi22CentStrongStart = [0, 19, 35, 44, 63] ∧ fi22CentStrongCount = [19, 16, 9, 19, 16] ∧
    fi22CentGenCount = [12, 9, 3, 9, 9] ∧
    (∀ c < 5, wordsOK (fi22CentGenCount.getD c 0) (fi22CentStrongCount.getD c 0)
      (fi22CentDerivations.getD c []) = true) ∧
    fi22CentSylows.length = 11 ∧ fi22CentWitnesses.length = 66 ∧
    fi22SearchNodeDataOK = true ∧ fi22SearchBase.length = 10 ∧
    (∀ x ∈ fi22SearchBase, x < 3510) := by
  refine ⟨fun L hL => Fi22E2067.isInv_of cent_eq (perm hL), by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, fun c hc => ?_, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
  rw [Fi22E2067.words_eq]
  exact CFSG.KS.SporSch.derivK_sound (allN_spec dk c hc)

end CertificateChecks.KernelSpor.Fi22E2065

end
