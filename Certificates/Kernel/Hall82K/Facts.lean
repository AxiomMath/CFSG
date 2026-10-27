module

public import CFSG.Certificates.Kernel.Hall82K.SoundX1
public import CFSG.Certificates.Kernel.Hall82K.SoundRed
public import CFSG.Certificates.Kernel.Hall82K.SoundConj
import CFSG.Certificates.Kernel.Common.ForallTreeFrom
import Certificates.Kernel.Hall82K.Bridge
import Certificates.Kernel.Hall82K.X1
import Certificates.Kernel.Hall82K.C5
import Certificates.Kernel.Hall82K.MGens
import Certificates.Kernel.Hall82K.Reducible
import Certificates.Kernel.Hall82K.Extra
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock

public section

namespace CFSG.KC.Hall82K

open CFSG.ComponentClassification.AS81.Hexa CFSG.CGT.Hall82

#kc_forall_tree_from ch840004conj_all (fun b => conjRowK b = true) 0 64 ch840004conj.b

#kc_forall_tree_from ch840004red_all (fun x => bor (Nat.beq (bitN q0K x) 1) (srchK 5 x) = true) 1 63
  ch840004red.r

theorem conj_all : ∀ b < 64, conjRowK b = true := fun b hb => by
  have h : conjRowK (0 + b) = true := ch840004conj_all b hb
  rwa [Nat.zero_add] at h

theorem red_all : ∀ x, 1 ≤ x → x < 64 → bor (Nat.beq (bitN q0K x) 1) (srchK 5 x) = true :=
  fun x h1 h2 => by
    have h : bor (Nat.beq (bitN q0K (1 + (x - 1))) 1) (srchK 5 (1 + (x - 1))) = true :=
      ch840004red_all (x - 1) (by change x - 1 < 63; omega)
    rwa [Nat.add_sub_cancel' h1] at h

theorem lift_k : ∀ a : Fin 3 → Fin 64,
    (∀ i j, hallXi a i * hallXi a j * (hallXi a i)⁻¹ * (hallXi a j)⁻¹ = 1 ∨
      hallXi a i * hallXi a j * (hallXi a i)⁻¹ * (hallXi a j)⁻¹ = transl 5) →
    (∀ i, hallXi a i * hallXi a i = 1 ∨ hallXi a i * hallXi a i = transl 5) →
    (∀ s ∈ hexaM, s 5 = 5 → ∀ i, ∃ u, InHallU u ∧ ∃ e, s * hallXi a i * s⁻¹ =
      transl u * hallXProd a e) →
    ∀ i, InHallU (a i) :=
  lift_of ch840004br_rm ch840004ex_rminv ch840004lift

theorem xcode_mul_k : ∀ x ∈ hallX1, ∀ y ∈ hallX1, xcode (x * y) = xorF (xcode x) (xcode y) :=
  xcode_mul_of ch840004br_rm ch840004ex_rminv ch840004x1_mul

theorem xcode_eq_zero_k : ∀ x ∈ hallX1, xcode x = 0 ↔ x = 1 ∨ x = transl 5 :=
  xcode_eq_zero_of ch840004br_rm ch840004ex_rminv ch840004x1_zero

theorem xcode_surj_k : ∀ k, ∃ x ∈ hallX1, xcode x = k :=
  xcode_surj_of ch840004br_rm ch840004ex_rminv ch840004x1_surj

theorem xcode_sq_k : ∀ x ∈ hallX1, x * x = transl 5 ↔ hallQ0 (xcode x) = true :=
  xcode_sq_of ch840004br_rm ch840004ex_rminv ch840004br_q0 ch840004x1_sq

theorem xcode_orb_k : ∀ x ∈ hallX1, IsHallOrb (xcode x) → ∃ h, IsOvalVec h ∧ x = transl h :=
  xcode_orb_of ch840004br_rm ch840004ex_rminv ch840004x1_orb

theorem xcode_conj_k (hc : hexaCheck = true) :
    ∀ b, ∀ s ∈ hexaM, s 5 = 5 → ∃ σ ∈ hallS40, ∀ x ∈ hallX1,
      xcode (transl b * s * x * (transl b * s)⁻¹) = σ (xcode x) :=
  xcode_conj_of ch840004br_rm ch840004ex_rminv ch840004br_s40 ch840004c5_inv hc ch840004br_idx
    ch840004mg_kmask ch840004mg_code ch840004mg_k ch840004c5_srch conj_all

theorem xcode_conj_surj_k (hc : hexaCheck = true) (hst : hexaStabCheck = true) :
    ∀ σ ∈ hallS40, ∃ b, ∃ s ∈ hexaM, s 5 = 5 ∧ ∀ x ∈ hallX1,
      xcode (transl b * s * x * (transl b * s)⁻¹) = σ (xcode x) :=
  xcode_conj_surj_of ch840004br_rm ch840004ex_rminv ch840004br_s40 ch840004c5_inv hc hst
    conj_all ch840004conj_surj ch840004c5_oval ch840004ex_c5fix

theorem reducible_k :
    ∀ y : Fin 64 → Fin 64, (∀ k l, y (xorF k l) = xorF (y k) (y l)) →
      (∀ k, hallQ0 (y k) = hallQ0 k) → (∀ k, y k = 0 → k = 0) → GoodHall y →
      (∀ t ∈ hallS40, GoodHall (y ∘ t ∘ y)) →
      (∀ t ∈ hallS40, ∀ u ∈ hallS40, GoodHall (y ∘ t ∘ y ∘ u ∘ y)) →
      ∀ k, InHallW k → InHallW (y k) :=
  reducible_of_checks ch840004br_idx ch840004br_q0 ch840004br_qt ch840004br_w ch840004br_s40 red_all

end CFSG.KC.Hall82K
