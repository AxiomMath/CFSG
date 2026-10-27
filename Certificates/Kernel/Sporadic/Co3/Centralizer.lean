
module

public import Certificates.Kernel.Sporadic.Co3.C
public import Certificates.Kernel.Sporadic.Co3.T
public import Certificates.Kernel.Sporadic.Co3.M
public import Certificates.Kernel.Sporadic.Co3.Single
public import CFSG.Certificates.Kernel.Spor.PrimSound
public import CFSG.Sporadic.Schreier.Co3CentralizerCheckBase
public import CFSG.Certificates.Kernel.Spor.SiftRSound
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.Kernel.Spor.RawSlSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Co3Cent

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim
open CFSG.Sporadic.Schreier.Co3 CFSG.Sporadic.Schreier.Co3.Native
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CertificateChecks.KernelSpor.Co3Single (z_eq tt_eq)

@[expose] noncomputable def mOK (k : Nat) : Bool :=
  bAnd(Co3C.sift (Co3M.S k), bAnd(Co3Text.hiOK (Co3M.S k),
    commK 276 9 (mask 9) (276 * 9) (Co3M.S k) Co3Z))

@[expose] noncomputable def m1OK (k : Nat) : Bool :=
  bAnd(Co3C.sift (Co3M1.S k), bAnd(Co3Text.hiOK (Co3M1.S k),
    commK 276 9 (mask 9) (276 * 9) (Co3M1.S k) Co3Tt))

theorem m0 : mOK 0 = true := by quickRfl
theorem m1 : mOK 1 = true := by quickRfl
theorem m2 : mOK 2 = true := by quickRfl
theorem m3 : mOK 3 = true := by quickRfl
theorem m4 : mOK 4 = true := by quickRfl
theorem m5 : mOK 5 = true := by quickRfl
theorem m6 : mOK 6 = true := by quickRfl

theorem n0 : m1OK 0 = true := by quickRfl
theorem n1 : m1OK 1 = true := by quickRfl
theorem n2 : m1OK 2 = true := by quickRfl
theorem n3 : m1OK 3 = true := by quickRfl
theorem n4 : m1OK 4 = true := by quickRfl
theorem n5 : m1OK 5 = true := by quickRfl

theorem tsq : sqIdK 276 9 (mask 9) (276 * 9) (pidn 276 9) Co3Tt = true := by quickRfl
theorem tne : neIdK 276 9 (mask 9) (276 * 9) (pidn 276 9) Co3Tt = true := by quickRfl
theorem thi : Co3Text.hiOK Co3Tt = true := by quickRfl
theorem tR : allN 276 (fun i => Nat.blt (pg 9 (mask 9) Co3Tt i) 276) = true := by quickRfl
theorem tT : Co3T.sift Co3Tt = true := by quickRfl
theorem tM : Co3M.sift Co3Tt = true := by quickRfl
theorem zfix : fixedK 276 9 (mask 9) Co3Z co3IzNat = true := by quickRfl
theorem tfix : fixedK 276 9 (mask 9) Co3Tt co3ItNat = true := by quickRfl

theorem m_ok (k : Nat) (hk : k < 7) : mOK k = true := by
  interval_cases k
  · exact m0
  · exact m1
  · exact m2
  · exact m3
  · exact m4
  · exact m5
  · exact m6

theorem m1_ok (k : Nat) (hk : k < 6) : m1OK k = true := by
  interval_cases k
  · exact n0
  · exact n1
  · exact n2
  · exact n3
  · exact n4
  · exact n5

theorem facts : (rawChainOK 276 (co3MArrs.extract 0 co3MGenCount) co3MArrs co3MBaseArr
        (wordsArr co3MGenCount co3MStrongCount co3MDerivations) 4 = true ∧
      rawOrbitSizes 276 co3MArrs co3MBaseArr = [240, 126, 32, 3]
    )
    ∧ (rawChainOK 276 (co3M1Arrs.extract 0 co3M1GenCount) co3M1Arrs co3M1BaseArr
        (wordsArr co3M1GenCount co3M1StrongCount co3M1Derivations) 4 = true ∧
      rawOrbitSizes 276 co3M1Arrs co3M1BaseArr = [132, 72, 10, 2]
    )
    ∧ ((∀ k < 7, siftA 276 co3ChainLevels co3ChainBaseArr 0 co3MArrs[k]! = true ∧
        commutesA 276 co3MArrs[k]! co3ZArr = true) ∧
      (∀ k < 6, siftA 276 co3ChainLevels co3ChainBaseArr 0 co3M1Arrs[k]! = true ∧
        commutesA 276 co3M1Arrs[k]! co3TtArr = true) ∧
      eqA 276 (compA 276 co3TtArr co3TtArr) (idA 276) = true ∧ eqA 276 co3TtArr (idA 276) = false ∧
      siftA 276 co3TLevels co3TBaseArr 0 co3TtArr = true ∧
      siftA 276 co3MLevels co3MBaseArr 0 co3TtArr = true ∧
      fixedList 276 co3ZArr = co3IzNat ∧ fixedList 276 co3TtArr = co3ItNat
    ) := by
  refine ⟨⟨rawChainK_sound (NS := 18) (CH := 16) Co3M.binds Co3M.head Co3M.hl (by norm_num)
      Co3M.hs, by rw [rawOrbitSizesK_sound Co3M.binds Co3M.perm Co3M.hl]; decide⟩,
    ⟨rawChainK_sound (NS := 18) (CH := 16) Co3M1.binds Co3M1.head Co3M1.hl (by norm_num)
      Co3M1.hs, by rw [rawOrbitSizesK_sound Co3M1.binds Co3M1.perm Co3M1.hl]; decide⟩,
    fun k hk => ?_, fun k hk => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 (m_ok k hk)
    obtain ⟨h3, h4⟩ := (bAnd_iff _ _).1 h2
    refine ⟨siftK_soundR Co3C.binds Co3C.perm Co3C.hl (Co3M.arr_eq k (by omega))
      (Nat.eq_of_beq_eq_true h3) (range_of_permOK (allN_spec Co3M.perm k (by omega))) h1, ?_⟩
    rw [z_eq, Co3M.arr_eq k (by omega)]
    exact commK_sound h4
  · obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 (m1_ok k hk)
    obtain ⟨h3, h4⟩ := (bAnd_iff _ _).1 h2
    refine ⟨siftK_soundR Co3C.binds Co3C.perm Co3C.hl (Co3M1.arr_eq k (by omega))
      (Nat.eq_of_beq_eq_true h3) (range_of_permOK (allN_spec Co3M1.perm k (by omega))) h1, ?_⟩
    rw [tt_eq, Co3M1.arr_eq k (by omega)]
    exact commK_sound h4
  · rw [tt_eq]
    exact sqIdK_sound tsq
  · rw [tt_eq]
    exact neIdK_sound tne
  · exact siftK_soundR Co3T.binds Co3T.perm Co3T.hl tt_eq (Nat.eq_of_beq_eq_true thi) tR tT
  · exact siftK_soundR Co3M.binds Co3M.perm Co3M.hl tt_eq (Nat.eq_of_beq_eq_true thi) tR tM
  · rw [z_eq]
    exact fixedK_sound zfix
  · rw [tt_eq]
    exact fixedK_sound tfix

end CertificateChecks.KernelSpor.Co3Cent

end
