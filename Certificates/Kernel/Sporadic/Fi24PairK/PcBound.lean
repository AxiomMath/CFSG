module

public import Certificates.Kernel.Sporadic.Fi24PairK.PcData
public import Certificates.Kernel.Sporadic.Fi24PairK.Pc.R0
public import Certificates.Kernel.Sporadic.Fi24PairK.Pc.A0
public import Certificates.Kernel.Sporadic.Fi24PairK.Pc.A1
public import Certificates.Kernel.Sporadic.Fi24PairK.Pc.A2
public import Certificates.Kernel.Sporadic.Fi24PairK.Pc.A3
public import Certificates.Kernel.Sporadic.Fi24PairK.Pc.B0
public import Certificates.Kernel.Sporadic.Fi24PairK.Pc.B1
public import Certificates.Kernel.Sporadic.Fi24PairK.Pc.B2
public import Certificates.Kernel.Sporadic.Fi24PairK.Pc.B3
public import CFSG.Certificates.Kernel.Spor.Fi24PairPcSound
import CFSG.Certificates.Kernel.Common.ForallTree

public section

namespace CFSG.KD.Fi24PairPc

open CFSG.KC CFSG.KC.Fi24PairK CFSG.KC.Fi24PairPc CFSG.KS.Fi24PairPc
open CFSG.KD.Fi24PairK (NV net)

#kc_forall_tree tAll (fun g => cT g = true) 441 CFSG.KD.Fi24PairPc.Ck.t
#kc_forall_tree aAll (fun g => cA g = true) 576 CFSG.KD.Fi24PairPc.Ck.a
#kc_forall_tree bAll (fun g => cB g = true) 529 CFSG.KD.Fi24PairPc.Ck.b
#kc_forall_tree gAll (fun g => gck g = true) 34 CFSG.KD.Fi24PairPc.Ck.g

theorem nthN_eq : ∀ (l : List Nat) (g : Nat) (h : g < l.length), nthN l g = l[g]
  | [], _, h => absurd h (by simp)
  | a :: l, 0, _ => rfl
  | a :: l, g + 1, h => nthN_eq l g (by simp at h; omega)

theorem gen_of {xs : List (List Nat)} {n : Nat} {ls : List Nat} {gw : List (List Nat)}
    (h : ∀ g < ls.length, genOK NV net xs n (nthN ls g) (nthLL gw g) = true) :
    ∀ l ∈ ls, ∃ r, genOK NV net xs n l r = true := by
  intro l hl
  obtain ⟨g, hg, rfl⟩ := List.mem_iff_getElem.1 hl
  refine ⟨nthLL gw g, ?_⟩
  rw [← nthN_eq ls g hg]
  exact h g hg

theorem blt_t {a b : Nat} (h : a < b) : Nat.blt a b = true := by
  rw [Nat.blt_eq]
  exact h

theorem blt_f {a b : Nat} (h : b ≤ a) : Nat.blt a b = false := by
  cases e : Nat.blt a b
  · rfl
  · rw [Nat.blt_eq] at e
    omega

theorem sub_add' (a g : Nat) : Nat.sub (a + g) a = g := Nat.add_sub_cancel_left a g

theorem genT : ∀ l ∈ lvT, ∃ r, genOK NV net J.xsT 21 l r = true := gen_of (gw := J.gwT) fun g hg => by
  have hg' : g < 10 := by simpa [lvT] using hg
  have := gAll g (by omega : g < 34)
  unfold gck at this
  rwa [blt_t hg'] at this

theorem genA : ∀ l ∈ lvA, ∃ r, genOK NV net J.xsA 24 l r = true := gen_of (gw := J.gwA) fun g hg => by
  have hg' : g < 12 := by simpa [lvA] using hg
  have := gAll (10 + g) (by omega : 10 + g < 34)
  unfold gck at this
  rwa [blt_f (by omega : 10 ≤ 10 + g), blt_t (by omega : 10 + g < 22), sub_add'] at this

theorem genB : ∀ l ∈ lvB, ∃ r, genOK NV net J.xsB 23 l r = true := gen_of (gw := J.gwB) fun g hg => by
  have hg' : g < 12 := by simpa [lvB] using hg
  have := gAll (22 + g) (by omega : 22 + g < 34)
  unfold gck at this
  rwa [blt_f (by omega : 10 ≤ 22 + g), blt_f (by omega : 22 ≤ 22 + g), sub_add'] at this

theorem prodT : ∏ j ∈ Finset.range 21, nthN J.psT j = 2 ^ 21 := by decide +kernel

theorem prodA : ∏ j ∈ Finset.range 24, nthN J.psA j = 2 ^ 21 * 27 := by decide +kernel

theorem prodB : ∏ j ∈ Finset.range 23, nthN J.psB j = 2 ^ 21 * 9 := by decide +kernel

theorem nzT : ∀ j z, z ∈ xW J.xsT j → z ≠ 0 := xW_ne_zero (by decide +kernel)

theorem nzA : ∀ j z, z ∈ xW J.xsA j → z ≠ 0 := xW_ne_zero (by decide +kernel)

theorem nzB : ∀ j z, z ∈ xW J.xsB j → z ≠ 0 := xW_ne_zero (by decide +kernel)

variable {L : ℤ → CFSG.Sporadic.Fi24.J}

theorem card_T0_le (hN : PtHyp L NV net) (hinv : ∀ z, z ≠ 0 → L (-z) = (L z)⁻¹) :
    Nat.card (Subgroup.closure {g | ∃ l ∈ lvT, g = L (Int.ofNat (l + 3))}) ≤ 2 ^ 21 :=
  prodT ▸ card_le_of hN hinv nzT (relOK_of_pcCk fun g hg => tAll g hg) genT

theorem card_A0_le (hN : PtHyp L NV net) (hinv : ∀ z, z ≠ 0 → L (-z) = (L z)⁻¹) :
    Nat.card (Subgroup.closure {g | ∃ l ∈ lvA, g = L (Int.ofNat (l + 3))}) ≤ 2 ^ 21 * 27 :=
  prodA ▸ card_le_of hN hinv nzA (relOK_of_pcCk fun g hg => aAll g hg) genA

theorem card_B0_le (hN : PtHyp L NV net) (hinv : ∀ z, z ≠ 0 → L (-z) = (L z)⁻¹) :
    Nat.card (Subgroup.closure {g | ∃ l ∈ lvB, g = L (Int.ofNat (l + 3))}) ≤ 2 ^ 21 * 9 :=
  prodB ▸ card_le_of hN hinv nzB (relOK_of_pcCk fun g hg => bAll g hg) genB

end CFSG.KD.Fi24PairPc

end
