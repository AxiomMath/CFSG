module

public import Certificates.Kernel.Sporadic.Co3.C
public import Certificates.Kernel.Sporadic.Co3.T
public import Certificates.Kernel.Sporadic.Co3.Single
public import CFSG.Certificates.Kernel.Spor.PrimSound
public import CFSG.Certificates.Kernel.Spor.SiftRSound
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.Kernel.Spor.RawSlSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Co3Sylow

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim
open CFSG.Sporadic.Schreier.Co3 CFSG.Sporadic.Schreier.Co3.Native
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CertificateChecks.KernelSpor.Co3Single (z_eq)

@[expose] noncomputable def genOK (k : Nat) : Bool :=
  bAnd(Co3C.sift (Co3T.S k), bAnd(Co3Text.hiOK (Co3T.S k),
    commK 276 9 (mask 9) (276 * 9) Co3Z (Co3T.S k)))

theorem gen0 : genOK 0 = true := by quickRfl
theorem gen1 : genOK 1 = true := by quickRfl
theorem gen2 : genOK 2 = true := by quickRfl
theorem gen3 : genOK 3 = true := by quickRfl
theorem gen4 : genOK 4 = true := by quickRfl
theorem gen5 : genOK 5 = true := by quickRfl
theorem gen6 : genOK 6 = true := by quickRfl
theorem gen7 : genOK 7 = true := by quickRfl

theorem zC : Co3C.sift Co3Z = true := by quickRfl
theorem zT : Co3T.sift Co3Z = true := by quickRfl
theorem zhi : Co3Text.hiOK Co3Z = true := by quickRfl
theorem zR : allN 276 (fun i => Nat.blt (pg 9 (mask 9) Co3Z i) 276) = true := by quickRfl
theorem zsq : sqIdK 276 9 (mask 9) (276 * 9) (pidn 276 9) Co3Z = true := by quickRfl
theorem zne : neIdK 276 9 (mask 9) (276 * 9) (pidn 276 9) Co3Z = true := by quickRfl
theorem zcan : canonK 276 9 (mask 9) (276 * 9) Co3Z = true := by quickRfl
theorem center : center3K 276 9 (mask 9) (276 * 9) (pidn 276 9) Co3T.S Co3T.LR Co3T.TR 8 Co3Z =
    true := by quickRfl

theorem gen_ok (k : Nat) (hk : k < 8) : genOK k = true := by
  interval_cases k
  · exact gen0
  · exact gen1
  · exact gen2
  · exact gen3
  · exact gen4
  · exact gen5
  · exact gen6
  · exact gen7

theorem rawChain_T : rawChainOK 276 (co3TArrs.extract 0 co3TGenCount) co3TArrs co3TBaseArr
    (wordsArr co3TGenCount co3TStrongCount co3TDerivations) 4 = true :=
  rawChainK_sound (NS := 18) (CH := 16) Co3T.binds Co3T.head Co3T.hl (by norm_num) Co3T.hs

theorem orbits_T : rawOrbitSizes 276 co3TArrs co3TBaseArr = [128, 4, 2] := by
  rw [rawOrbitSizesK_sound Co3T.binds Co3T.perm Co3T.hl]
  decide

theorem sift_gen (k : Nat) (hk : k < 8) :
    siftA 276 co3ChainLevels co3ChainBaseArr 0 co3TArrs[k]! = true := by
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 (gen_ok k hk)
  obtain ⟨h3, _⟩ := (bAnd_iff _ _).1 h2
  exact siftK_soundR Co3C.binds Co3C.perm Co3C.hl (Co3T.arr_eq k (by omega))
    (Nat.eq_of_beq_eq_true h3) (range_of_permOK (allN_spec Co3T.perm k (by omega))) h1

theorem comm_gen (k : Nat) (hk : k < 8) : commutesA 276 co3ZArr co3TArrs[k]! = true := by
  obtain ⟨_, h2⟩ := (bAnd_iff _ _).1 (gen_ok k hk)
  obtain ⟨_, h4⟩ := (bAnd_iff _ _).1 h2
  rw [z_eq, Co3T.arr_eq k (by omega)]
  exact commK_sound h4

theorem facts : (rawChainOK 276 (co3TArrs.extract 0 co3TGenCount) co3TArrs co3TBaseArr
        (wordsArr co3TGenCount co3TStrongCount co3TDerivations) 4 = true ∧
      rawOrbitSizes 276 co3TArrs co3TBaseArr = [128, 4, 2]
    )
    ∧ ((∀ k < 8, siftA 276 co3ChainLevels co3ChainBaseArr 0 co3TArrs[k]! = true) ∧
      siftA 276 co3ChainLevels co3ChainBaseArr 0 co3ZArr = true ∧
      siftA 276 co3TLevels co3TBaseArr 0 co3ZArr = true ∧
      (∀ k < 8, commutesA 276 co3ZArr co3TArrs[k]! = true) ∧
      eqA 276 (compA 276 co3ZArr co3ZArr) (idA 276) = true ∧ eqA 276 co3ZArr (idA 276) = false ∧
      centerCheck3 276 co3TLevels (co3TArrs.extract 0 8) co3ZArr = true
    ) := by
  refine ⟨⟨rawChain_T, orbits_T⟩, sift_gen, ?_, ?_, comm_gen, ?_, ?_, ?_⟩
  · exact siftK_soundR Co3C.binds Co3C.perm Co3C.hl z_eq (Nat.eq_of_beq_eq_true zhi) zR zC
  · exact siftK_soundR Co3T.binds Co3T.perm Co3T.hl z_eq (Nat.eq_of_beq_eq_true zhi) zR zT
  · rw [z_eq]
    exact sqIdK_sound zsq
  · rw [z_eq]
    exact neIdK_sound zne
  · rw [z_eq]
    exact center3K_sound Co3T.binds Co3T.perm Co3T.hl (by norm_num) zcan center

end CertificateChecks.KernelSpor.Co3Sylow

end
