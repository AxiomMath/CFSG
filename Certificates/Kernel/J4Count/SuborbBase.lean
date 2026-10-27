
module

public import Certificates.Kernel.J4Count.FixZBase
public import Certificates.Kernel.J4Count.ChecksQ1
public import Certificates.Kernel.J4Hub.Struct
public import Certificates.Kernel.J4Q.Mat
public import CFSG.Sporadic.J4.QT2LocX0CentMainBase
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.J4CountSound
public import CFSG.Quasithin.H13.J4CentralizerBase
public import CFSG.Sporadic.J4.QT2AGen
public import CFSG.Sporadic.J4.QT2LocScanCheckBase
public import CFSG.Sporadic.J4.QT2LocX0KCheckBase
public import CFSG.Sporadic.J4.QT2LocX0NMainBase
public import CFSG.Sporadic.J4.Struct.FixCount
public import CFSG.Sporadic.Schreier.J4SNoCompCoverBase
public import Certificates.Kernel.J4Count.HOrderBase

@[expose] public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Count

open CFSG.Sporadic.J4 CFSG.Sporadic.J4Schreier CFSG.Sporadic.J4Schreier.NoComp MulAction
open CFSG.Sporadic.SmallF2 CFSG.Sporadic.J4.Struct CertificateChecks.KernelSporSch

section Dvd

variable {G X : Type*} [Group G] [Finite G] [MulAction G X]

theorem dvd_orbit_left (N : Subgroup G) [N.Normal] (x : X) :
    Nat.card N ∣ (orbit G x).ncard * Nat.card (N ⊓ stabilizer G x : Subgroup G) := by
  set S := stabilizer G x
  have h1 : N.relIndex S * Nat.card (N ⊓ S : Subgroup G) = Nat.card S := Subgroup.relIndex_mul_card N S
  have h2 : N.relIndex (S ⊔ N) * Nat.card (N ⊓ (S ⊔ N) : Subgroup G) = Nat.card (S ⊔ N : Subgroup G) :=
    Subgroup.relIndex_mul_card N (S ⊔ N)
  rw [Subgroup.relIndex_sup_right, inf_of_le_left le_sup_right] at h2
  have h3 : Nat.card (S ⊔ N : Subgroup G) ∣ Nat.card G := Subgroup.card_subgroup_dvd_card _
  have h4 : Nat.card S * S.index = Nat.card G := Subgroup.card_mul_index S
  rw [index_stabilizer] at h4
  have hS : 0 < Nat.card S := Nat.card_pos
  obtain ⟨k, hk⟩ := h3
  refine ⟨k, Nat.eq_of_mul_eq_mul_left hS ?_⟩
  calc Nat.card S * ((orbit G x).ncard * Nat.card (N ⊓ S : Subgroup G))
      = Nat.card G * Nat.card (N ⊓ S : Subgroup G) := by rw [← h4]; ring
    _ = Nat.card (S ⊔ N : Subgroup G) * k * Nat.card (N ⊓ S : Subgroup G) := by rw [hk]
    _ = Nat.card S * (Nat.card N * k) := by rw [← h2, ← h1]; ring

theorem dvd_orbit_right (N : Subgroup G) (x : X) :
    (orbit G x).ncard * Nat.card (N ⊓ stabilizer G x : Subgroup G) ∣ Nat.card G := by
  have h4 : Nat.card (stabilizer G x) * (stabilizer G x).index = Nat.card G :=
    Subgroup.card_mul_index _
  rw [index_stabilizer] at h4
  rw [← h4, mul_comm (Nat.card (stabilizer G x))]
  exact Nat.mul_dvd_mul_left _ (Subgroup.card_dvd_of_le inf_le_right)

theorem dvd_orbit_of_le (K : Subgroup G) (x : X) (hK : K ≤ stabilizer G x) :
    (orbit G x).ncard * Nat.card K ∣ Nat.card G := by
  have h4 : Nat.card (stabilizer G x) * (stabilizer G x).index = Nat.card G :=
    Subgroup.card_mul_index _
  rw [index_stabilizer] at h4
  rw [← h4, mul_comm (Nat.card (stabilizer G x))]
  exact Nat.mul_dvd_mul_left _ (Subgroup.card_dvd_of_le hK)

end Dvd

@[expose] def L7 : List ℕ := [1, 15180, 3400320, 32643072, 28336, 54405120, 82575360]

theorem nO_mem : ∀ o : Option (Fin 6), nO KernelJ4Hub.nD o ∈ L7 := by decide

theorem nO_inj : Function.Injective (nO KernelJ4Hub.nD) := by decide

noncomputable abbrev sz (l : ℕ) : ℕ := (orbit H (qv l)).ncard

theorem card_NH_stab (w : Row) :
    Nat.card (N.subgroupOf H ⊓ stabilizer H w : Subgroup H) = fixCard w := by
  have e : N.subgroupOf H ⊓ stabilizer H w = (N ⊓ stabilizer J w).subgroupOf H := by
    ext g
    simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf, mem_stabilizer_iff]
    rfl
  rw [e, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans N_le_H)).toEquiv]
  rfl

theorem L7_nodup : L7.Nodup := by decide

theorem x0Q1_toNat : CFSG.Sporadic.J4.QT2.x0Q1.toNat = Q1N := by decide

theorem q1_toVec : CFSG.Sporadic.J4.QT2.x0Q1.toVec = toVecD 112 Q1N := by
  funext j
  rw [toVecD_apply, Native.V2.toVec_apply, ← Native.V2.testBit_toNat _ (by omega), x0Q1_toNat]

theorem zmod_ite_inj {b b' : Bool} (h : (if b then 1 else 0 : ZMod 2) = if b' then 1 else 0) :
    b = b' := by
  cases b <;> cases b' <;> first | rfl | exact absurd h (by decide)

theorem toVecD_eq_iff (x y : ℕ) : toVecD 112 x = toVecD 112 y ↔ x % 2 ^ 112 = y % 2 ^ 112 := by
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
    by_cases hj : j < 112
    · have e := congrFun h ⟨j, hj⟩
      rw [toVecD_apply, toVecD_apply] at e
      rw [zmod_ite_inj e]
    · simp [hj]
  · intro h
    funext j
    have e := congrArg (fun n => n.testBit j.val) h
    simp only [Nat.testBit_mod_two_pow, j.isLt, decide_true, Bool.true_and] at e
    rw [toVecD_apply, toVecD_apply, e]

set_option synthInstance.maxSize 4096 in
theorem sizes_forced :
    ∀ b ∈ L7, 2048 ∣ b * 1 → b ≠ 32643072 →
    ∀ c ∈ L7, 2048 ∣ c * 1 → c ≠ 32643072 → c ≠ b →
    ∀ d ∈ L7, 2048 ∣ d * 16 → d * 16 ∣ 501397585920 → d ≠ 32643072 → d ≠ b → d ≠ c →
    ∀ e ∈ L7, 2048 ∣ e * 512 → e * 512 ∣ 501397585920 → e ≠ 32643072 → e ≠ b → e ≠ c → e ≠ d →
    ∀ f ∈ L7, 2048 ∣ f * 128 → f * 128 ∣ 501397585920 → f ≠ 32643072 → f ≠ b → f ≠ c →
      f ≠ d → f ≠ e → d = 3400320 ∧ e = 15180 ∧ f = 28336 := by
  decide

end CertificateChecks.KernelJ4Count

end
