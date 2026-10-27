
module

public import Certificates.Kernel.Sporadic.L2C.Defs
public import Certificates.Kernel.Sporadic.L2.G4
public import CFSG.Sporadic.SuzRecog.LevelTwoCoverDefsBase

@[expose] public section

namespace CertificateChecks.KernelSpor.L2CG

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.SuzRecog.LevelTwo
open CFSG.Sporadic.SuzRecog.LevelTwoCover CFSG.Sporadic.SuzRecog.LevelTwoCoverData
open CFSG.Sporadic.SuzRecog CFSG.Sporadic.SuzRecog.ElimCert
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.L2K CertificateChecks.KernelSpor.L2CK
open CertificateChecks.KernelSpor.L2G (sB band bif_true nbeq nblt nble nblt_f nble_f allN_get
  hexE hexTable_at nbr_get nbr_size nbr_high)

local notation "pgv" => pg 12 (mask 12)
local notation "pg2" => pg 2 (mask 2)

attribute [local irreducible] volt shift nbr

theorem anyN_iff {n : Nat} {f : Nat → Bool} : anyN n f = true ↔ ∃ j < n, f j = true := by
  unfold anyN
  constructor
  · intro h
    by_contra hno
    have : allN n (fun j => Bool.not (f j)) = true :=
      CFSG.KS.Raw.allN_of_forall fun j hj => by
        cases e : f j
        · rfl
        · exact absurd ⟨j, hj, e⟩ hno
    rw [this] at h
    exact Bool.false_ne_true h
  · rintro ⟨j, hj, e⟩
    cases ha : allN n (fun j => Bool.not (f j))
    · rfl
    · have := allN_get ha hj
      rw [e] at this
      exact absurd this (by decide)

theorem nbeq_f {a b : Nat} (h : Nat.beq a b = false) : a ≠ b := fun e => by
  rw [e, Nat.beq_refl] at h
  exact absurd h (by decide)

theorem not_true {b : Bool} : Bool.not b = true ↔ b = false := by cases b <;> decide

theorem volt_get {x k : Nat} (hx : x < 2835) (hk : k < 36) : volt[36 * x + k]! = voltK x k := by
  unfold volt
  rw [hexTable_at (by omega), Nat.zero_add]
  exact hexE L2CV.eq L2CV.all hx hk

theorem shift_get {s v : Nat} (hs : s < 2) (hv : v < 2997) : (shift s)[v]! = shK s v := by
  unfold shift
  rw [hexTable_at hv]
  exact hexE L2CS.eq L2CS.all hs hv

theorem nbC_eq (u k : Nat) :
    nbC u k = nbK (u % 2997) k + 2997 * ((u / 2997 + voltK (u % 2997) k) % 3) := rfl

theorem nbrC_low {u : Nat} (hu : u < 8991) (hl : u % 2997 < 2835) {k : Nat} (hk : k < 36) :
    (nbrC[u]!)[k]! = nbC u k := by
  rw [nbrC_get hu hl hk, nbr_get hl hk, volt_get hl hk, nbC_eq]

theorem occB_nbrC {u : Nat} (hu : u < 8991) (w : Nat) : occB nbrC[u]! w = occC u w := by
  unfold occC
  by_cases hl : u % 2997 < 2835
  · rw [show Nat.blt (Nat.mod u 2997) 2835 = true from nblt.2 hl]
    change _ = anyN 36 (fun k => Nat.beq (nbC u k) w)
    apply Bool.eq_iff_iff.2
    rw [occB_iff, anyN_iff, nbrC_size hu hl]
    constructor
    · rintro ⟨k, hk, e⟩
      exact ⟨k, hk, by rw [← nbrC_low hu hl hk, e]; exact Nat.beq_refl w⟩
    · rintro ⟨k, hk, e⟩
      exact ⟨k, hk, by rw [nbrC_low hu hl hk]; exact nbeq.1 e⟩
  · rw [show Nat.blt (Nat.mod u 2997) 2835 = false from nblt_f hl, nbrC_of_ge hu (by omega)]
    rfl

theorem adjB_nbrC {u w : Nat} (hu : u < 8991) (hw : w < 8991) : adjB nbrC u w = adjC u w := by
  unfold adjB adjC
  rw [occB_nbrC hu, occB_nbrC hw, L2G.bne_eq, L2G.bIf_or, L2G.bAnd_and]

@[expose] def BaseH : Prop := ∀ x < 2835, baseK x = true

theorem base_at (H : BaseH) {x : Nat} (hx : x < 2835) {k : Nat} (hk : k < 36) :
    nbK x k < 2997 ∧ nbK x k ≠ x ∧ (∀ j < k, nbK x j ≠ nbK x k) ∧
      (nbK x k < 2835 → ∃ j < 36, nbK (nbK x k) j = x ∧
        (voltK x k + voltK (nbK x k) j) % 3 = 0) := by
  have h := H x hx
  unfold baseK baseG at h
  rw [sB, sB] at h
  have h1 := allN_get h hk
  rw [sB, band, band, band, nblt, not_true] at h1
  obtain ⟨c1, c2, c3, c4⟩ := h1
  refine ⟨c1, nbeq_f c2, fun j hj e => ?_, fun hy => ?_⟩
  · have := allN_get c3 hj
    rw [not_true] at this
    exact nbeq_f this e
  · rw [show Nat.ble 2835 (pgv (L2NB.F x) k) = false from nble_f (Nat.not_le.2 hy), sB, sB,
      anyN_iff] at c4
    obtain ⟨j, hj, e⟩ := c4
    rw [band, nbeq, nbeq] at e
    exact ⟨j, hj, e.1, e.2⟩

theorem nbK_lt (H : BaseH) {x k : Nat} (hx : x < 2835) (hk : k < 36) : nbK x k < 2997 :=
  (base_at H hx hk).1

theorem nbK_ne (H : BaseH) {x k : Nat} (hx : x < 2835) (hk : k < 36) : nbK x k ≠ x :=
  (base_at H hx hk).2.1

end CertificateChecks.KernelSpor.L2CG

end
