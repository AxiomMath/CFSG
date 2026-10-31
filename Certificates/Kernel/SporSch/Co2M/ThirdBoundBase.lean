
module

public import Certificates.Kernel.SporSch.Co2M.ThirdGlueBase
public import CFSG.Certificates.Kernel.SporSch.OrbitBound
public import CFSG.Certificates.Kernel.SporSch.Co2ThirdSound
public import CFSG.Certificates.Kernel.SporSch.OrbitTrSound
public import CFSG.Certificates.Kernel.SporSch.ThirdDfsBase

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CertificateChecks.KernelSporSch.Co2M

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.Co2M CFSG.KS.Co2Third
  CFSG.KS.OrbitBound
open CFSG.Sporadic.Co2Schreier CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Certificates.Native CFSG.Certificates CFSG.Sporadic.Co2Cert CFSG.Monster.B.Mathieu

local notation "cJ " j:max => rcnt (Co2T3.LR j)

local notation "rptJ " j:max k:max => rpt 12 (mask 12) (Co2T3.LR j) k

local notation "rposJ " j:max z:max => rpos 12 (mask 12) (2300 * 12) (Co2T3.LR j) z

local notation "tau " j:max k:max => treeF (stp 2300 S3 thB j)
  (rpar 12 (mask 12) (2300 * 12) (Co2T3.LR j)) (rlab 2300 (2300 * 12) (Co2T3.LR j)) k k

local notation "walkJ " j:max k:max z:max =>
  walkIK 2300 12 (mask 12) (2300 * 12) Co2T3.S Co2T3.SI 30 (t3St j) (Co2T3.LR j) k k z

local notation "mJ " j:max inO:max k:max =>
  mIK 2300 12 (mask 12) (2300 * 12) Co2T3.S Co2T3.SI 30 (t3St j) (Co2T3.LR j) inO fxP 52 k

def toF (z : ℕ) : Fin 2300 := ⟨z % 2300, Nat.mod_lt _ (by norm_num)⟩

theorem toF_val {z : ℕ} (hz : z < 2300) : (toF z : ℕ) = z := Nat.mod_eq_of_lt hz

theorem mul_inv_inv_mul {G : Type*} [Group G] (g t : G) : g * (t⁻¹ * g)⁻¹ = t := by group

theorem fix_iff_of_comm {α : Type*} (u g : Equiv.Perm α) (hc : u * g = g * u) (y : α) :
    u (g y) = g y ↔ u y = y := by
  have e : u (g y) = g (u y) := by
    rw [← Equiv.Perm.mul_apply, hc, Equiv.Perm.mul_apply]
  rw [e, g.injective.eq_iff]

abbrev O1 : Finset (Fin 2300) := Finset.univ.filter fun y => inO1 y = true

abbrev O42 : Finset (Fin 2300) := Finset.univ.filter fun y => inO42 y = true

abbrev FixS : Finset (Fin 2300) := Finset.univ.filter fun y => locU y = y

abbrev fxF (i : ℕ) : Fin 2300 := toF (fxP i)

theorem fxs : (∀ i < 52, fxP i < 2300 ∧ pg 12 (mask 12) (UP 0) (fxP i) = fxP i) ∧
    (∀ i, i + 1 < 52 → fxP i < fxP (i + 1)) ∧
    ((Finset.range 2300).filter fun z => pg 12 (mask 12) (UP 0) z = z).card = 52 :=
  fixList_spec t3fix_ok

theorem fxP_lt {i : ℕ} (hi : i < 52) : fxP i < 2300 := (fxs.1 i hi).1

theorem fxF_val {i : ℕ} (hi : i < 52) : (fxF i : ℕ) = fxP i := toF_val (fxP_lt hi)

theorem fxP_mono : ∀ d i, i + d + 1 < 52 → fxP i < fxP (i + d + 1)
  | 0, i, h => fxs.2.1 i h
  | d + 1, i, h => (fxP_mono d i (by omega)).trans (fxs.2.1 _ (by omega))

theorem fxF_injOn : Set.InjOn fxF (Finset.range 52 : Set ℕ) := by
  intro i hi i' hi' e
  have hi1 : i < 52 := Finset.mem_range.1 hi
  have hi2 : i' < 52 := Finset.mem_range.1 hi'
  have e' := congrArg Fin.val e
  rw [fxF_val hi1, fxF_val hi2] at e'
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have := fxP_mono (i' - i - 1) i (by omega)
    rw [show i + (i' - i - 1) + 1 = i' by omega] at this
    omega
  · have := fxP_mono (i - i' - 1) i' (by omega)
    rw [show i' + (i - i' - 1) + 1 = i by omega] at this
    omega

abbrev Hj (j : ℕ) : Subgroup (Equiv.Perm (Fin 2300)) := locH3 ⊓ stabB j

theorem mem_Hj_succ {j : ℕ} (g : Equiv.Perm (Fin 2300)) :
    g ∈ Hj (j + 1) ↔ g ∈ Hj j ∧ g (bpt j) = bpt j := by
  simp only [Hj, Subgroup.mem_inf, mem_stabB]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, h2, fun i hi => h3 i (by omega)⟩, h3 j (by omega)⟩
  · rintro ⟨⟨h1, h2, h3⟩, h4⟩
    refine ⟨h1, h2, fun i hi => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact h3 i hi
    · exact h4

def cB : List ℕ := [20, 18, 32, 8, 4, 1, 2, 1, 1, 1, 1, 1, 2]

end CertificateChecks.KernelSporSch.Co2M
