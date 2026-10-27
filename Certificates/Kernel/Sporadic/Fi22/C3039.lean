
module

public import Certificates.Kernel.Sporadic.Fi22.C3147Base
public import CFSG.Certificates.Kernel.MonsterB.Co2MatSound

public section

namespace CertificateChecks.KernelSpor.Fi22C3039

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Certificates CFSG.Certificates.Native
open CFSG.Monster.B.Fischer CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

theorem size19 : fi22StrongArrs.size = 19 := by simp [fi22StrongArrs]

theorem hd : Orb.Hd 3510 fi22StrongArrs Fi22C3147.B7 2
    (CFSG.Sporadic.Schreier.Co3.Native.wordsArr 2 19 fi22ChainDerivations) :=
  Orb.hd_of_head (by rw [size19]; omega) (rawHeadK_sound Fi22C3147.binds7 Fi22R7.head)

theorem invs_eq : fi22StrongInvs = rawInvs 3510 fi22StrongArrs := rfl

theorem gen_eq {k : Nat} (hk : k < 2) : fi22ChainGen k = fi22StrongArrs[k]! := by
  rw [Fi22G.gen_eq hk, Fi22X.strong_eq (by omega),
    Nat.eq_of_beq_eq_true (allN_spec Fi22C3147.genOK k hk)]

theorem facts3039 :
    (∀ j < 19, isInvA 3510 fi22StrongArrs[j]! fi22StrongInvs[j]! = true) ∧
    (∀ k < 2, isInvA 3510 (fi22ChainGen k) (invCand 3510 (fi22ChainGen k)) = true) ∧
    (∀ k < 2, eqA 3510 fi22StrongArrs[k]! (fi22ChainGen k) = true) ∧
    (∀ j < 19, 2 ≤ j → lettersOK j (fi22Derivation j) = true ∧
      eqA 3510 fi22StrongArrs[j]!
        (wordA 3510 fi22StrongArrs fi22StrongInvs (fi22Derivation j)) = true) ∧
    fi22ChainDerivations.length = 17 := by
  refine ⟨fun j hj => ?_, fun k hk => ?_, fun k hk => ?_, fun j hj hj2 => ?_, rfl⟩
  · rw [invs_eq]
    exact hd.inv j (by rw [size19]; exact hj)
  · have h := hd.inv k (by rw [size19]; omega)
    rw [Orb.rawInvs_get (by rw [size19]; omega)] at h
    rw [gen_eq hk]
    exact h
  · rw [gen_eq hk]
    exact CFSG.KC.Co2Mem.eqA_iff.2 fun _ _ => rfl
  · have h := hd.words j (by rw [size19]; exact hj) hj2
    rw [Orb.wordsArr_get' hj2 hj] at h
    rw [invs_eq]
    exact h

open Certificates in
open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer in
theorem certificate3039_of : (∀ j < 19, isInvA 3510 fi22StrongArrs[j]! fi22StrongInvs[j]! = true) ∧
      (∀ k < 2, isInvA 3510 (fi22ChainGen k) (invCand 3510 (fi22ChainGen k)) = true) ∧
      (∀ k < 2, eqA 3510 fi22StrongArrs[k]! (fi22ChainGen k) = true) ∧
      (∀ j < 19, 2 ≤ j → lettersOK j (fi22Derivation j) = true ∧
        eqA 3510 fi22StrongArrs[j]!
          (wordA 3510 fi22StrongArrs fi22StrongInvs (fi22Derivation j)) = true) ∧
      fi22ChainDerivations.length = 17 := facts3039

end CertificateChecks.KernelSpor.Fi22C3039

end
