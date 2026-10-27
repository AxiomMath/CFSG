module

public import Certificates.Kernel.Sporadic.OddCore.SuzTwK
public import CFSG.Certificates.Kernel.CosetLogSound
public import CFSG.Certificates.Kernel.Spor.RawSlSound
public import CFSG.Certificates.Kernel.Spor.Loops
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelSpor.SuzTwF

open CFSG.KC.Enum CFSG.KS.PEnum CFSG.KC.CLog CFSG.Sporadic.SuzRecog.B0TwistData
open CFSG.Certificates.CosetEnumeration CFSG.KS CFSG.KS.Raw
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.SuzTwK

theorem fact_of {lo len t : Nat}
    (h : factSlK 7 32 (r32 SuzTwN 1) 1365 (r32 SuzTwN 0) SuzTwRL (r32 SuzTwRN) SuzTwFD SuzTwFS
      SuzTwFW SuzTwSD SuzTwDT lo len = true) (h1 : lo ≤ t) (h2 : t < lo + len)
    (h3 : t < r32 SuzTwN 0) :
    factK 7 32 (r32 SuzTwN 1) 1365 SuzTwRL (r32 SuzTwRN) SuzTwFD SuzTwFS SuzTwFW SuzTwSD SuzTwDT t =
      true := by
  have h' := allN_spec h (t - lo) (by omega)
  rw [strictB_eq] at h'
  have e : Nat.add lo (t - lo) = t := by
    change lo + (t - lo) = t
    omega
  rw [e] at h'
  have hb : Nat.blt t (r32 SuzTwN 0) = true := Eq.mpr Nat.blt_eq h3
  rw [hb] at h'
  exact h'

theorem facts : ∀ t < r32 SuzTwN 0,
    factK 7 32 (r32 SuzTwN 1) 1365 SuzTwRL (r32 SuzTwRN) SuzTwFD SuzTwFS SuzTwFW SuzTwSD SuzTwDT t =
      true := by
  intro t ht
  have hn : r32 SuzTwN 0 ≤ 40000 := Nat.le_of_ble_eq_true nf
  have hs : ∀ s < 10, sl s = true := by
    intro s hs
    interval_cases s
    exacts [sl0, sl1, sl2, sl3, sl4, sl5, sl6, sl7, sl8, sl9]
  have h := hs (t / 4000) (by omega)
  unfold sl at h
  exact fact_of h (by change 4000 * (t / 4000) ≤ t; omega)
    (by change t < 4000 * (t / 4000) + 4000; omega) ht

theorem tw_mem (G : Type) [Group G] (gen : ℕ → G) (hinv : ∀ x < 14, gen (invCode x) = (gen x)⁻¹)
    (hrels : ∀ r ∈ twRels, evalWord gen r = 1) :
    gen 12 ∈ Subgroup.closure (gen '' {c | c ∈ [0, 2, 4, 6, 8, 10]}) :=
  clogK_sound hd (fun b hb => allN_spec defs b hb) facts G gen hinv hrels

end CertificateChecks.KernelSpor.SuzTwF

end
