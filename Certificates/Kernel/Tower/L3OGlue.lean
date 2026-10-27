module

public import CFSG.Certificates.Kernel.Tower.OutSound
public import Certificates.Kernel.Tower.L3TGlue
public import Certificates.Kernel.Tower.L3OChecks
import CFSG.Certificates.Kernel.Common.ForallTree
public import Certificates.Data.CFSGNative.SCATWreath

public section

namespace Certificates.KernelTower

open Certificates.KernelTower CFSG.OddStandard.AltStdSmall4.Tower

#kc_forall_tree ch36408_l3o_all (fun t => ch36408_l3o t = true) 448
  Certificates.KernelTower.ch36408_l3o

theorem l3o_ok {f j : Nat} (hf : f < 28) (hj : j < 16) : l3o f j = true := by
  have hlt : 16 * f + j < 448 := by omega
  have h := ch36408_l3o_all (16 * f + j) hlt
  have e1 : Nat.div (16 * f + j) 16 = f := by
    change (16 * f + j) / 16 = f
    omega
  have e2 : Nat.mod (16 * f + j) 16 = j := by
    change (16 * f + j) % 16 = j
    omega
  rw [ch36408_l3o, e1, e2] at h
  exact h

variable (D : ExtData (Grp wrS)) {f : Nat}

theorem l3_gen (hf : f < 28)
    (hFA : ∀ c < 8192, l16 (wrA (Nat.add 2 (l16 (l3P f) 0))) c < 8192 ∧
      D.α (subModel_wr.decW c) = subModel_wr.decW (l16 (wrA (Nat.add 2 (l16 (l3P f) 0))) c))
    (hdg : subModel_wr.decW (l16 (l3P f) 1) = D.g) :
    ∀ y : CycExt D, y ∈ Subgroup.closure
      {z | ∃ i < 4, z = dec2 D subModel_wr.decW (l16 (l3G f) i)} := by
  have M := l3_model D hf hFA hdg
  set C := Subgroup.closure {z | ∃ i < 4, z = dec2 D subModel_wr.decW (l16 (l3G f) i)}
  obtain ⟨hGU, hW, hW1, -⟩ := tgtOK_parts ((l3_parts hf).2 0 (by omega))
  have hw : ∀ n w, wevN (l3M f) (l3G f) n w < 16384 ∧
      dec2 D subModel_wr.decW (wevN (l3M f) (l3G f) n w) ∈ C := by
    intro n
    induction n with
    | zero =>
      intro w
      have e : wevN (l3M f) (l3G f) 0 w = 0 := rfl
      rw [e, M.dec_zero]
      exact ⟨M.zero_lt, C.one_mem⟩
    | succ n ih =>
      intro w
      have e : wevN (l3M f) (l3G f) (n + 1) w = Bool.rec (motive := fun _ => Nat)
          (l3M f (l16 (l3G f) (Nat.land (Nat.sub (Nat.land w 7) 1) 3))
            (wevN (l3M f) (l3G f) n (Nat.shiftRight w 3))) 0 (Nat.beq (Nat.land w 7) 0) := rfl
      rw [e]
      have hi : Nat.land (Nat.sub (Nat.land w 7) 1) 3 < 4 :=
        Nat.lt_succ_of_le (Nat.and_le_right : Nat.land (Nat.sub (Nat.land w 7) 1) 3 ≤ 3)
      obtain ⟨h1, h2⟩ := ih (Nat.shiftRight w 3)
      cases Nat.beq (Nat.land w 7) 0 <;> dsimp only
      · refine ⟨M.mul_lt _ (hGU _ hi).1 _ h1, ?_⟩
        rw [M.dec_mul _ (hGU _ hi).1 _ h1]
        exact C.mul_mem (Subgroup.subset_closure ⟨_, hi, rfl⟩) h2
      · rw [M.dec_zero]
        exact ⟨M.zero_lt, C.one_mem⟩
  have hGS : ∀ i < 4, dec2 D subModel_wr.decW (2 * l16 wGS i) ∈ C := by
    intro i hi
    have h := (hw 21 (l64 (l3Wd f) i)).2
    have e : wevN (l3M f) (l3G f) 21 (l64 (l3Wd f) i) = 2 * l16 wGS i := (hW i hi).1
    rwa [e] at h
  have h1 : dec2 D subModel_wr.decW 1 ∈ C := by
    have h := (hw 21 (l64 (l3Wd f) 4)).2
    have e : wevN (l3M f) (l3G f) 21 (l64 (l3Wd f) 4) = 1 := hW1
    rwa [e] at h
  have hev : ∀ d, ∀ c < 8192, ptDep wrPT c = d → dec2 D subModel_wr.decW (2 * c) ∈ C := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro c hc hd
      by_cases h0 : c = 0
      · rw [h0, Nat.mul_zero, M.dec_zero]
        exact C.one_mem
      · obtain ⟨hgi, hpar, hdep, hmul⟩ := treeB_get ch36408_tree hc h0
        have hg := treeB_gen ch36408_tree hgi
        have e : 2 * c = l3M f (2 * l16 wGS (ptGi wrPT c)) (2 * ptPar wrPT c) := by
          rw [l3M_even, hmul]
        rw [e, M.dec_mul _ (by omega) _ (by omega)]
        exact C.mul_mem (hGS _ hgi) (ih _ (hd ▸ hdep) _ hpar rfl)
  intro y
  obtain ⟨k, hk, rfl⟩ := M.surj y (Subgroup.mem_top y)
  have he := hev _ (k / 2) (by omega) rfl
  rcases Nat.mod_two_eq_zero_or_one k with h | h
  · have e : k = 2 * (k / 2) := by omega
    rw [e]
    exact he
  · have e : k = l3M f (2 * (k / 2)) 1 := by
      rw [l3M_one (by omega)]
      omega
    rw [e, M.dec_mul _ (by omega) _ (by omega)]
    exact C.mul_mem he h1

theorem l3_bc (hf : f < 28)
    (hFA : ∀ c < 8192, l16 (wrA (Nat.add 2 (l16 (l3P f) 0))) c < 8192 ∧
      D.α (subModel_wr.decW c) = subModel_wr.decW (l16 (wrA (Nat.add 2 (l16 (l3P f) 0))) c))
    (hdg : subModel_wr.decW (l16 (l3P f) 1) = D.g) {j : Nat} (hj : j < 16)
    (β : CycExt D →* CycExt D)
    (hβ : ∀ i < 4, β (dec2 D subModel_wr.decW (l16 (l3G f) i)) =
      dec2 D subModel_wr.decW (l16 (l3Im f j) i)) :
    ∀ k < 16384, β (dec2 D subModel_wr.decW k) = dec2 D subModel_wr.decW (l3bc f j k) := by
  have M := l3_model D hf hFA hdg
  obtain ⟨hIM, hb, -⟩ := famB_parts (ch36408_l3_all hf)
  have hz : ∀ k < 16384, l3M f 2 k = k ^^^ 2 := fun _ hk => l3M_two hk
  have hzc := l3_center D hf hFA
  have hX : ∀ a < 16384, ∀ b < 16384,
      xbit (l3X f j) (l3M f a b) = xbit (l3X f j) a ^^^ xbit (l3X f j) b :=
    fun _ ha _ hb => l3_chi D hf hFA hj ha hb
  have hz2 : dec2 D subModel_wr.decW 2 * dec2 D subModel_wr.decW 2 = 1 := by
    rw [← M.dec_mul 2 (by omega) 2 (by omega), hz 2 (by omega)]
    exact M.dec_zero
  obtain ⟨h1, h2⟩ := tgt_beta0 M hz hzc hX ((l3_parts hf).2 j hj) hIM hb β hβ hz2
  have hT := famB_table M ch36408_tree (fun _ _ _ _ => l3M_even) (ch36408_l3_all hf) _ h1
  set β₀ := tgtBeta0 M (l3X f j) hz2 hzc hX β
  have hb0 : ∀ k < 16384, Bool.rec (motive := fun _ => Nat)
      (l16 (wrL3 (Nat.add (Nat.mul 34 f) 1)) (Nat.shiftRight k 1))
      (l3M f (l16 (wrL3 (Nat.add (Nat.mul 34 f) 1)) (Nat.shiftRight k 1)) (l16 (l3P f) 2))
      (Nat.beq (Nat.land k 1) 1) < 16384 ∧
      β₀ (dec2 D subModel_wr.decW k) = dec2 D subModel_wr.decW (Bool.rec (motive := fun _ => Nat)
        (l16 (wrL3 (Nat.add (Nat.mul 34 f) 1)) (Nat.shiftRight k 1))
        (l3M f (l16 (wrL3 (Nat.add (Nat.mul 34 f) 1)) (Nat.shiftRight k 1)) (l16 (l3P f) 2))
        (Nat.beq (Nat.land k 1) 1)) := by
    intro k hk
    have e1 : Nat.shiftRight k 1 = k / 2 := shr1 k
    have e3 : Nat.land k 1 = k % 2 := Nat.and_one_is_mod k
    rw [e1, e3]
    obtain ⟨hF, hTk⟩ := hT (k / 2) (by omega)
    rcases Nat.mod_two_eq_zero_or_one k with h | h
    · have hbq : Nat.beq (k % 2) 1 = false := by rw [h]; rfl
      rw [hbq]
      refine ⟨hF, ?_⟩
      have e : k = 2 * (k / 2) := by omega
      conv_lhs => rw [e]
      exact hTk
    · have hbq : Nat.beq (k % 2) 1 = true := by rw [h]; rfl
      rw [hbq]
      refine ⟨M.mul_lt _ hF _ hb, ?_⟩
      have e : k = l3M f (2 * (k / 2)) 1 := by
        rw [l3M_one (by omega)]
        omega
      conv_lhs => rw [e]
      rw [M.dec_mul _ (by omega) _ (by omega), map_mul, hTk, h2, M.dec_mul _ hF _ hb]
  intro k hk
  obtain ⟨hlt, hval⟩ := hb0 k hk
  have hap := tgtBeta0_apply M (l3X f j) hz2 hzc hX β hk
  have hβk : β (dec2 D subModel_wr.decW k) =
      dec2 D subModel_wr.decW 2 ^ xbit (l3X f j) k * β₀ (dec2 D subModel_wr.decW k) := by
    rw [hap, ← mul_assoc, pow_mul_self hz2 (xbit_le _ _), one_mul]
  rw [hβk, hval]
  set c0 := Bool.rec (motive := fun _ => Nat)
    (l16 (wrL3 (Nat.add (Nat.mul 34 f) 1)) (Nat.shiftRight k 1))
    (l3M f (l16 (wrL3 (Nat.add (Nat.mul 34 f) 1)) (Nat.shiftRight k 1)) (l16 (l3P f) 2))
    (Nat.beq (Nat.land k 1) 1)
  have hc1 : c0 ^^^ 2 * xbit (l3X f j) k < 16384 :=
    Nat.xor_lt_two_pow (n := 14) hlt (by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (xbit_le (l3X f j) k) with h | h <;> rw [h] <;>
        norm_num)
  have h := pow_dec_xor M hz hc1 (xbit_le (l3X f j) k)
  rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero] at h
  have e : l3bc f j k = c0 ^^^ 2 * xbit (l3X f j) k := rfl
  rw [e, h]

theorem l3_out (hf : f < 28)
    (hFA : ∀ c < 8192, l16 (wrA (Nat.add 2 (l16 (l3P f) 0))) c < 8192 ∧
      D.α (subModel_wr.decW c) = subModel_wr.decW (l16 (wrA (Nat.add 2 (l16 (l3P f) 0))) c))
    (hdg : subModel_wr.decW (l16 (l3P f) 1) = D.g) {j : Nat} (hj : j < 16)
    (D' : ExtData (CycExt D))
    (hβ : ∀ i < 4, D'.α (dec2 D subModel_wr.decW (l16 (l3G f) i)) =
      dec2 D subModel_wr.decW (l16 (l3Im f j) i))
    (hg : D'.g = dec2 D subModel_wr.decW (l3g2 f j)) :
    ∀ x : CycExt D', x.d = true → ¬ IsPInv x := by
  obtain ⟨hGU, -⟩ := tgtOK_parts ((l3_parts hf).2 j hj)
  exact outB_sound (l3_model D hf hFA hdg) D' (l3_gen D hf hFA hdg)
    (fun i hi => (hGU i hi).1) (fun i hi => ⟨(hGU i hi).2, hβ i hi⟩)
    (l3_invol D hf hFA hdg hj D' hβ hg)
    (l3_bc D hf hFA hdg hj D'.α.toMonoidHom hβ) (l3o_ok hf hj)

end Certificates.KernelTower
