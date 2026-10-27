module

public import Certificates.Kernel.MonsterExist.ShortKey.Sound
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.Monster.AxisCount.DenseIndex
public import CFSG.Monster.B.TwoA.Base.Flags
public import CFSG.Monster.B.TwoA.Base.Par45A
public import CFSG.Monster.B.TwoA.Par3.Main
public import CFSG.Monster.B.TwoA.Par3.MainBase
public import CFSG.Monster.B.TwoA.Unitary.Semilinear
public import CFSG.Open.MonsterY443Defs
public import CFSG.Sporadic.Co1Base
public import CFSG.Sporadic.Th.F2Spec

public section

set_option maxRecDepth 100000

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CertificateChecks.MonsterExist.ShortKey

open CFSG.Monster CFSG.Monster.VisCert CFSG.Monster.Existence

theorem count_ok : countOK = true := by quickRfl

theorem buckets0 : bucketsOK 0 512 = true := by quickRfl
theorem buckets1 : bucketsOK 512 512 = true := by quickRfl
theorem buckets2 : bucketsOK 1024 512 = true := by quickRfl
theorem buckets3 : bucketsOK 1536 512 = true := by quickRfl
theorem buckets4 : bucketsOK 2048 512 = true := by quickRfl
theorem buckets5 : bucketsOK 2560 512 = true := by quickRfl
theorem buckets6 : bucketsOK 3072 512 = true := by quickRfl
theorem buckets7 : bucketsOK 3584 512 = true := by quickRfl

theorem bucket_ok : ∀ a < 4096, bucketOK a = true := by
  intro a ha
  have h : ∀ c < 8, bucketsOK (512 * c) 512 = true := by
    intro c hc
    interval_cases c
    exacts [buckets0, buckets1, buckets2, buckets3, buckets4, buckets5, buckets6, buckets7]
  have := (bucketsOK_iff _ _).1 (h (a / 512) (by omega)) (a % 512) (Nat.mod_lt _ (by norm_num))
  rwa [Nat.div_add_mod] at this

theorem memK_iff {x : ℕ} (hx : x < 2 ^ 24) : memK x = true ↔ vecX x ∈ shortSet :=
  memK_iff_of_checks bucket_ok count_ok hx

theorem memK_eq_isShortX {x : ℕ} (hx : x < 2 ^ 24) :
    memK x = isShortX x :=
  memK_eq_isShortX_of_checks bucket_ok count_ok hx

theorem mem_shortPacked_iff_memK {x : ℕ} :
    x ∈ shortPacked ↔ x < 2 ^ 24 ∧ memK x = true := by
  rw [mem_shortPacked_iff]
  exact and_congr_right fun hx => by rw [memK_eq_isShortX hx]

end CertificateChecks.MonsterExist.ShortKey

end
