module

public import CFSG.Certificates.Kernel.HNLocalSound
public import CFSG.Certificates.Kernel.Orders.HN.Data.Const
public import Certificates.Kernel.HNLocal.Data
import Certificates.Kernel.HNLocal.Checks.K
import Certificates.Kernel.HNLocal.Fix
import CFSG.Certificates.Kernel.J4Hub.BlockSound
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Fam.Lin
import CFSG.Open.Defs

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelHNChain

open CFSG.KC.Ord CFSG.KS.Ord CFSG.KC.HNLocal CFSG.KD.HNLocal
open scoped Matrix

noncomputable abbrev TL (XC TD : Nat → Nat) (N GA GB j : Nat) : Nat :=
  treeLeaf XC TD MSF N M CFSG.KD.OrdHN.L CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB
    CFSG.KD.OrdHN.ONE j

theorem treeSum_eq (XC TD : Nat → Nat) (N GA GB lo : Nat) : ∀ n,
    treeSum XC TD MSF N M CFSG.KD.OrdHN.L CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM GA GB
      CFSG.KD.OrdHN.ONE lo n = ∑ i ∈ Finset.range n, TL XC TD N GA GB (lo + i)
  | 0 => rfl
  | n + 1 => by
    change CFSG.KC.Loop.strictN (treeSum XC TD MSF N M CFSG.KD.OrdHN.L CFSG.KD.OrdHN.H CM3
      CFSG.KD.OrdHN.RM GA GB CFSG.KD.OrdHN.ONE lo n)
      (fun a => Nat.add a (TL XC TD N GA GB (Nat.add lo n))) = _
    rw [CFSG.KS.J4Hub.strictN_eq', treeSum_eq XC TD N GA GB lo n, Finset.sum_range_succ]
    rfl

theorem leaf_lt {XC TD : Nat → Nat} {N GA GB NL v : Nat}
    (h : Nat.beq (treeSum XC TD MSF N M CFSG.KD.OrdHN.L CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM
      GA GB CFSG.KD.OrdHN.ONE 0 NL) v = true) (hv : v < 2 ^ 50) :
    ∀ j < NL, TL XC TD N GA GB j < 2 ^ 50 := by
  intro j hj
  have hs := Nat.eq_of_beq_eq_true h
  rw [treeSum_eq] at hs
  have hle := Finset.single_le_sum (f := fun i => TL XC TD N GA GB (0 + i))
    (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 hj)
  rw [hs, Nat.zero_add] at hle
  exact lt_of_le_of_lt hle hv

theorem canon_one : Canon 5 133 13 CFSG.KD.OrdHN.ONE :=
  (one_sound CertificateChecks.KernelHNLocal.consts).1

theorem tree_child {XC TD : Nat → Nat} {N NL GA GB : Nat} (hGA : Canon 5 133 13 GA)
    (hGB : Canon 5 133 13 GB) (hleaf : ∀ j < NL, TL XC TD N GA GB j < 2 ^ 50)
    (h0 : TD 0 % 2 ^ 21 = 1) (hN : TD NL % 2 ^ 21 = N) (hNL : N ≤ 133 * NL)
    (hX : ∀ i < NL, XC i < 2 ^ 53200) (hpos : ∀ k < N, 0 < recX XC M k) {k : ℕ} (hk1 : 1 ≤ k)
    (hk : k < N) :
    ∃ p < k, CFSG.KS.HNLocal.CCanon (recX XC M k) ∧
      (CFSG.KS.HNLocal.cvec (recX XC M k) =
          (CFSG.KS.HNLocal.OM GA)ᵀ *ᵥ CFSG.KS.HNLocal.cvec (recX XC M p) ∨
        CFSG.KS.HNLocal.cvec (recX XC M k) =
          (CFSG.KS.HNLocal.OM GB)ᵀ *ᵥ CFSG.KS.HNLocal.cvec (recX XC M p)) := by
  have hsound := fun j (hj : j < NL) => CFSG.KS.HNLocal.treeLeaf_sound
    CertificateChecks.KernelHNLocal.consts masks msf cm hGA hGB canon_one (hleaf j hj)
  have hle : ∀ j ≤ NL, TD j % 2 ^ 21 ≤ N := by
    have key : ∀ d j, j + d = NL → TD j % 2 ^ 21 ≤ N := by
      intro d
      induction d with
      | zero => intro j hj; rw [show j = NL by omega, hN]
      | succ d ih =>
        intro j hj
        have h1 := (hsound j (by omega)).1
        have h2 := ih (j + 1) (by omega)
        omega
    intro j hj
    exact key (NL - j) j (by omega)
  have key : ∀ J ≤ NL, k < TD J % 2 ^ 21 →
      ∃ j < J, TD j % 2 ^ 21 ≤ k ∧ k < TD j % 2 ^ 21 + TD j / 2 ^ 21 % 512 := by
    intro J
    induction J with
    | zero => intro _ h; rw [h0] at h; omega
    | succ J ih =>
      intro hJ h
      by_cases hkJ : k < TD J % 2 ^ 21
      · obtain ⟨j, hj, h'⟩ := ih (by omega) hkJ
        exact ⟨j, by omega, h'⟩
      · refine ⟨J, by omega, by omega, ?_⟩
        rw [(hsound J (by omega)).1]
        exact h
  obtain ⟨j, hj, h1, h2⟩ := key NL le_rfl (by rw [hN]; exact hk)
  obtain ⟨hs, hch, -⟩ := hsound j hj
  have hj1 := hle (j + 1) (by omega)
  have hX' : ∀ i < TD (j + 1) % 2 ^ 21 / 133, XC i < 2 ^ 53200 := fun i hi =>
    hX i (by have := Nat.div_le_div_right (c := 133) hj1; omega)
  have hpos' : ∀ t < TD j / 2 ^ 21 % 512, 0 < recX XC M (TD j % 2 ^ 21 + t) := fun t ht =>
    hpos _ (by omega)
  obtain ⟨r, -, hpk, hcan, hv⟩ := hch hX' hpos' (k - TD j % 2 ^ 21) (by omega)
  have e : TD j % 2 ^ 21 + (k - TD j % 2 ^ 21) = k := by omega
  rw [e] at hpk hcan hv
  exact ⟨133 * j + r, hpk, hcan, hv⟩

theorem order_facts {XC SD : Nat → Nat} {N NL : Nat} (hNL : N ≤ 133 * NL)
    (h : sortRange XC SD N M 0 NL = true) :
    (0 < N → sig SD 0 < N) ∧ ∀ i, i + 1 < N → sig SD (i + 1) < N ∧
      recX XC M (sig SD i) < recX XC M (sig SD (i + 1)) := by
  have hleaf : ∀ m < NL, sortLeaf XC SD N M m = true := fun m hm => by
    have := CFSG.KS.HNLocal.sortRange_spec h m hm
    rwa [Nat.zero_add] at this
  refine ⟨fun hN => ?_, fun i hi => ?_⟩
  · have := (CFSG.KS.HNLocal.sortLeaf_spec (hleaf 0 (by omega))).1 (by omega)
    simpa using this
  · have h' := (CFSG.KS.HNLocal.sortLeaf_spec (hleaf (i / 133) (by omega))).2 (i % 133)
      (Nat.mod_lt _ (by norm_num)) (by omega)
    rw [show 133 * (i / 133) + i % 133 = i by omega] at h'
    exact h'

theorem tree_inj {XC SD : Nat → Nat} {N NL : Nat} (hNL : N ≤ 133 * NL)
    (h : sortRange XC SD N M 0 NL = true) :
    ∀ i < N, ∀ j < N, recX XC M i = recX XC M j → i = j :=
  CertificateChecks.KernelHNLocal.injOn_of_order (order_facts hNL h).1 (order_facts hNL h).2

theorem key_min_of_order {n : Nat} {key σ : Nat → Nat} (h0 : 0 < n → σ 0 < n)
    (h : ∀ i, i + 1 < n → σ (i + 1) < n ∧ key (σ i) < key (σ (i + 1))) :
    ∀ k < n, key (σ 0) ≤ key k := by
  have hlt : ∀ i < n, σ i < n := by
    intro i hi
    rcases i with _ | i
    · exact h0 (by omega)
    · exact (h i hi).1
  have hmono : ∀ i j, i < j → j < n → key (σ i) < key (σ j) := by
    intro i j hij hj
    induction j with
    | zero => omega
    | succ j ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h' | rfl
      · exact lt_trans (ih h' (by omega)) (h j hj).2
      · exact (h i hj).2
  have hinj : ∀ i < n, ∀ j < n, σ i = σ j → i = j := by
    intro i hi j hj e
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h' | h'
    · have := hmono i j h' hj; rw [e] at this; exact lt_irrefl _ this
    · have := hmono j i h' hi; rw [e] at this; exact lt_irrefl _ this
  let f : Fin n → Fin n := fun i => ⟨σ i, hlt i i.2⟩
  have hf : Function.Injective f := fun i j e => Fin.ext (hinj i i.2 j j.2 (congrArg Fin.val e))
  intro k hk
  obtain ⟨i, hi⟩ := (Finite.injective_iff_surjective.1 hf) ⟨k, hk⟩
  have ei : σ i = k := congrArg Fin.val hi
  rw [← ei]
  rcases Nat.eq_zero_or_pos i.val with h' | h'
  · have e0 : i = ⟨0, by omega⟩ := Fin.ext h'
    rw [e0]
  · exact (hmono 0 i h' i.2).le

theorem tree_pos {XC SD : Nat → Nat} {N NL : Nat} (hNL : N ≤ 133 * NL)
    (h : sortRange XC SD N M 0 NL = true) (h0 : Nat.ble 1 (recX XC M (sig SD 0)) = true) :
    ∀ k < N, 0 < recX XC M k := fun k hk =>
  Nat.lt_of_lt_of_le (Nat.le_of_ble_eq_true h0)
    (key_min_of_order (order_facts hNL h).1 (order_facts hNL h).2 k hk)

theorem chunks_lt {XC : Nat → Nat} {n : Nat}
    (h : CFSG.KC.Loop.allBelow n (n / 64 + 1) (fun i => Nat.beq (Nat.shiftRight (XC i) 53200) 0) =
      true) : ∀ i < n, XC i < 2 ^ 53200 := by
  intro i hi
  have := Nat.eq_of_beq_eq_true (CFSG.KS.HNLocal.allBelow_spec h i hi (by omega))
  rw [show (XC i).shiftRight 53200 = XC i / 2 ^ 53200 from Nat.shiftRight_eq_div_pow _ _] at this
  rcases Nat.div_eq_zero_iff.1 this with h' | h'
  · exact absurd h' (Nat.two_pow_pos _).ne'
  · exact h'

end CertificateChecks.KernelHNChain

end
