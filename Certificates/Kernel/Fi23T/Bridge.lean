module

public import Certificates.Kernel.Fi23T.Spec
public import Certificates.Kernel.Fi23T.Lists
public import Certificates.Kernel.Fi23C.Group
public import Certificates.Kernel.Fi23T.Graph

public section

set_option maxRecDepth 400000

open Pointwise

namespace CertificateChecks.KernelFi23T

open CFSG.KC.Enum CFSG.KC.Fi23K CFSG.KC.Fi23T CFSG.KC.Fi23C CFSG.KD.Fi23K CFSG.KD.Fi23T
  CFSG.KS.PC CertificateChecks.KernelFi23M
open CFSG.Sporadic.Fi23.Native (dWord)
open CertificateChecks.KernelFi23C (cp cJ_cp cp_eqv cp_inv cp_inj cp_zero cp_step labW)

@[expose] def fp (n : ℕ) : Fin 31671 := ⟨n % 31671, Nat.mod_lt _ (by norm_num)⟩

theorem fp_val {n : ℕ} (h : n < 31671) : (fp n).val = n := Nat.mod_eq_of_lt h

theorem fp_eq {n : ℕ} (h : n < 31671) : fp n = ⟨n, h⟩ := Fin.ext (fp_val h)

theorem fp_of (x : Fin 31671) : fp x.val = x := Fin.ext (fp_val x.isLt)

theorem smul_eq_of_maps {g : Equiv.Perm (Fin 31671)} {T : Finset (Fin 31671)}
    (h : ∀ x ∈ T, g x ∈ T) : g • T = T := by
  have hsub : g • T ⊆ T := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_smul_finset.1 hy
    exact h x hx
  exact Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_smul_finset])

theorem card_filter_maps (g : Equiv.Perm (Fin 31671)) (T : Finset (Fin 31671)) :
    (T.filter fun x => g x ∈ T).card = (g • T ∩ T).card := by
  refine Finset.card_nbij' (fun x => g x) (fun y => g⁻¹ y) (fun x hx => ?_) (fun y hy => ?_)
    (fun x _ => perm_inv_apply g x) (fun y _ => perm_apply_inv g y)
  · rw [Finset.mem_coe, Finset.mem_filter] at hx
    rw [Finset.mem_coe, Finset.mem_inter]
    exact ⟨Finset.smul_mem_smul_finset hx.1, hx.2⟩
  · rw [Finset.mem_coe, Finset.mem_inter] at hy
    beta_reduce
    rw [Finset.mem_coe, Finset.mem_filter, perm_apply_inv]
    exact ⟨Finset.inv_smul_mem_iff.2 hy.1, hy.2⟩

theorem filter_range_len (f : ℕ → Bool) :
    ∀ n, ((List.range n).filter f).length = ((Finset.range n).filter fun i => f i = true).card
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.filter_append, List.length_append, filter_range_len f n,
      Finset.range_add_one, Finset.filter_insert]
    by_cases h : f n = true
    · rw [if_pos h, Finset.card_insert_of_notMem (by simp)]
      simp [h]
    · rw [if_neg h]
      simp [h]

section


@[expose] noncomputable def tau (x : Fin 31671) : Equiv.Perm (Fin 31671) := cp x.val

@[expose] noncomputable def A0 : Subgroup (Equiv.Perm (Fin 31671)) :=
  Subgroup.closure {phiX wα, phiX wβ}

theorem cJ_tau {k x : ℕ} (hk : k < 31671) (hx : x < 31671) :
    fp (cJ G k x) = tau (fp k) (fp x) := by
  rw [cJ_cp hk hx, fp_of, tau, fp_val hk, fp_eq hx]

theorem alpha_mem : phiX wα ∈ A0 := Subgroup.subset_closure (by simp)

theorem beta_mem : phiX wβ ∈ A0 := Subgroup.subset_closure (by simp)

theorem A0_le : A0 ≤ phiX.range := by
  rw [A0, Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact ⟨wα, rfl⟩
  · exact ⟨wβ, rfl⟩

theorem word_mem (w : List ℕ) :
    phiX (w.map fun x => if x = 0 then wα else wβ).prod ∈ A0 := by
  rw [map_list_prod]
  refine A0.list_prod_mem fun y hy => ?_
  obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hy
  obtain ⟨x, -, rfl⟩ := List.mem_map.1 hg
  split_ifs
  · exact alpha_mem
  · exact beta_mem

theorem wD_mem : phiX wD ∈ A0 := by
  have e : phiX wD = phiX (dWord.map fun x => if x = 0 then wα else wβ).prod ^ 7 :=
    ActsAs.ext phiX_wD CertificateChecks.KernelFi23C.acts_dWord7
  rw [e]
  exact pow_mem (word_mem _) 7

theorem cp_A0 : ∀ k < 31671, cp k ∈ A0 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    by_cases h0 : k = 0
    · subst h0
      rw [cp_zero]
      exact wD_mem
    · have hp := (tr_pt hk h0).1
      have hl : phiX (labW k) ∈ A0 := by
        unfold labW
        split_ifs
        · exact alpha_mem
        · exact beta_mem
      rw [cp_step hk h0]
      exact mul_mem (mul_mem hl (ih _ hp (by omega))) (inv_mem hl)

theorem tsys : TSys A0 tau where
  mem x := cp_A0 x.val x.isLt
  conj g hg x := by
    obtain ⟨g', rfl⟩ := A0_le hg
    exact cp_eqv g' x.isLt
  sq x := mul_eq_one_iff_eq_inv.2 (cp_inv x.val).symm
  inj x y h := Fin.ext (cp_inj x.isLt y.isLt h)

@[expose] def Ltr (p : ℕ) : Prop := p < 31671 ∨ p = 31710 ∨ p = 31711

@[expose] noncomputable def lP (p : ℕ) : Equiv.Perm (Fin 31671) :=
  if p < 31671 then cp p else if p = 31710 then phiX wα else phiX wβ

@[expose] noncomputable def wP (w : List ℕ) : Equiv.Perm (Fin 31671) := (w.map lP).prod

theorem lP_val {p : ℕ} (hp : Ltr p) (y : Fin 31671) : (lP p y).val = lJ G p y.val := by
  rcases hp with hp | rfl | rfl
  · rw [lP, if_pos hp, lJ_pt _ hp, cJ_cp hp y.isLt]
  · rw [lP, if_neg (by norm_num), if_pos rfl, lJ_reg _ (by norm_num)]
    exact phiX_wα y.val y.isLt
  · rw [lP, if_neg (by norm_num), if_neg (by norm_num), lJ_reg _ (by norm_num)]
    exact phiX_wβ y.val y.isLt

theorem lP_mem {p : ℕ} (hp : Ltr p) : lP p ∈ A0 := by
  rcases hp with hp | rfl | rfl
  · rw [lP, if_pos hp]
    exact cp_A0 p hp
  · rw [lP, if_neg (by norm_num), if_pos rfl]
    exact alpha_mem
  · rw [lP, if_neg (by norm_num), if_neg (by norm_num)]
    exact beta_mem

theorem lP_pt {p : ℕ} (hp : p < 31671) : lP p = tau (fp p) := by
  rw [lP, if_pos hp, tau, fp_val hp]

theorem wP_cons (p : ℕ) (w : List ℕ) : wP (p :: w) = lP p * wP w := by
  rw [wP, wP, List.map_cons, List.prod_cons]

theorem wP_nil : wP [] = 1 := rfl

theorem wP_val : ∀ w : List ℕ, (∀ p ∈ w, Ltr p) → ∀ y : Fin 31671, (wP w y).val = wJ G w y.val
  | [], _, _ => rfl
  | p :: w, hw, y => by
    rw [wP_cons, Equiv.Perm.mul_apply, lP_val (hw p (by simp)), wJ_cons,
      wP_val w (fun q hq => hw q (by simp [hq])) y]

theorem wP_mem : ∀ w : List ℕ, (∀ p ∈ w, Ltr p) → wP w ∈ A0
  | [], _ => one_mem _
  | p :: w, hw => by
    rw [wP_cons]
    exact mul_mem (lP_mem (hw p (by simp))) (wP_mem w fun q hq => hw q (by simp [hq]))

theorem wJ_lt {w : List ℕ} (hw : ∀ p ∈ w, Ltr p) {y : ℕ} (hy : y < 31671) : wJ G w y < 31671 := by
  rw [← fp_val hy, ← wP_val w hw]
  exact Fin.isLt _

theorem fp_wJ {w : List ℕ} (hw : ∀ p ∈ w, Ltr p) {y : ℕ} (hy : y < 31671) :
    fp (wJ G w y) = wP w (fp y) := by
  rw [← fp_val hy, ← wP_val w hw, fp_of, fp_val hy]

@[expose] noncomputable def T0 : Finset (Fin 31671) := Finset.univ.filter fun x => tb H 1 x.val < 3240

theorem mem_T0 {x : Fin 31671} : x ∈ T0 ↔ tb H 1 x.val < 3240 := by
  rw [T0, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

theorem memS_T0 {y : ℕ} (hy : y < 31671) : memS H 0 3240 y = true ↔ fp y ∈ T0 := by
  rw [memS_iff, mem_T0, fp_val hy]

theorem t_spec : (∀ i < 3240, tb H 0 i < 31671 ∧ tb H 1 (tb H 0 i) = i) ∧
    ∀ x < 31671, (tb H 1 x < 3240 ∧ tb H 0 (tb H 1 x) = x) ∨ tb H 1 x = 3240 :=
  ⟨(listK_spec t_list).1, (listK_spec t_list).2.2⟩

theorem T0_pt {i : ℕ} (hi : i < 3240) : fp (tb H 0 i) ∈ T0 := by
  obtain ⟨h1, h2⟩ := t_spec.1 i hi
  rw [mem_T0, fp_val h1, h2]
  exact hi

theorem T0_idx {x : Fin 31671} (hx : x ∈ T0) : fp (tb H 0 (tb H 1 x.val)) = x := by
  rw [mem_T0] at hx
  rcases t_spec.2 x.val x.isLt with h | h
  · rw [h.2, fp_of]
  · omega

theorem T0_card : T0.card = 3240 := by
  rw [← Finset.card_range 3240]
  refine Finset.card_nbij' (fun x => tb H 1 x.val) (fun i => fp (tb H 0 i)) (fun x hx => ?_)
    (fun i hi => T0_pt (Finset.mem_range.1 hi)) (fun x hx => T0_idx hx) (fun i hi => ?_)
  · rw [Finset.mem_coe] at hx
    exact Finset.mem_range.2 (mem_T0.1 hx)
  · rw [Finset.mem_coe] at hi
    obtain ⟨h1, h2⟩ := t_spec.1 i (Finset.mem_range.1 hi)
    beta_reduce
    rw [fp_val h1, h2]

theorem notMem_T0 {y : ℕ} (hy : y < 31671) : domTc H y = true ↔ fp y ∉ T0 := by
  unfold domTc
  rw [Bool.not_eq_true', ← Bool.not_eq_true, memS_T0 hy]

theorem domT_iff {y : ℕ} (hy : y < 31671) : domT H y = true ↔ fp y ∈ T0 := memS_T0 hy

theorem domW_iff {w : List ℕ} (hw : ∀ p ∈ w, Ltr p) {y : ℕ} (hy : y < 31671) :
    domW G H w y = true ↔ wP w (fp y) ∉ T0 := by
  unfold domW
  rw [Bool.not_eq_true', ← Bool.not_eq_true, memS_T0 (wJ_lt hw hy), fp_wJ hw hy]

theorem pres_eq {w : List ℕ} (hw : ∀ p ∈ w, Ltr p) (h : presK G H 0 3240 w = true) :
    wP w • T0 = T0 := by
  refine smul_eq_of_maps fun x hx => ?_
  have h1 := presK_spec h (tb H 1 x.val) (mem_T0.1 hx)
  rw [← T0_idx hx, ← fp_wJ hw (t_spec.1 _ (mem_T0.1 hx)).1, mem_T0,
    fp_val (wJ_lt hw (t_spec.1 _ (mem_T0.1 hx)).1)]
  exact h1

theorem qL_lt : ∀ q ∈ qL, q < 31671 := by decide

theorem q_mem {w : List ℕ} (hw : ∀ p ∈ w, Ltr p) (h : qK G H w = true) {q : ℕ} (hq : q ∈ qL) :
    wP w (fp q) ∈ T0 := by
  have h1 := qK_spec h q hq
  rw [← fp_wJ hw (qL_lt q hq), mem_T0, fp_val (wJ_lt hw (qL_lt q hq))]
  exact h1

theorem cnt_eq {w : List ℕ} (hw : ∀ p ∈ w, Ltr p) {c : ℕ} (h : cntK G H w c = true) :
    (wP w • T0 ∩ T0).card = c := by
  rw [← cntK_spec h, filter_range_len, ← card_filter_maps]
  refine Finset.card_nbij' (fun x => tb H 1 x.val) (fun i => fp (tb H 0 i)) (fun x hx => ?_)
    (fun i hi => ?_) (fun x hx => T0_idx (Finset.mem_filter.1 hx).1) (fun i hi => ?_)
  · rw [Finset.mem_coe, Finset.mem_filter] at hx
    rw [Finset.mem_coe, Finset.mem_filter]
    refine ⟨Finset.mem_range.2 (mem_T0.1 hx.1), ?_⟩
    have hlt := (t_spec.1 _ (mem_T0.1 hx.1)).1
    rw [memS_T0 (wJ_lt hw hlt), fp_wJ hw hlt, T0_idx hx.1]
    exact hx.2
  · rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hi
    rw [Finset.mem_coe, Finset.mem_filter]
    have hlt := (t_spec.1 _ hi.1).1
    refine ⟨T0_pt hi.1, ?_⟩
    rw [← fp_wJ hw hlt, ← memS_T0 (wJ_lt hw hlt)]
    exact hi.2
  · rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hi
    obtain ⟨h1, h2⟩ := t_spec.1 i hi.1
    beta_reduce
    rw [fp_val h1, h2]

@[expose] def NodeOK (b gr ng : ℕ) (dom : ℕ → Bool) (s j : ℕ) : Prop :=
  tb H b j < 31671 ∧ dom (tb H b j) = true ∧ tb H (b + 3) (tb H b j) = j ∧
    (j = s → tb H (b + 1) j = j) ∧
    (j ≠ s → s ≤ tb H (b + 1) j ∧ tb H (b + 1) j < j ∧ tb H (b + 2) j < ng ∧
      cJ G (tb H gr (tb H (b + 2) j)) (tb H b (tb H (b + 1) j)) = tb H b j)

theorem nodes_of {b gr ng : ℕ} {dom : ℕ → Bool} {s lo c : ℕ}
    (h : trK G H b gr ng dom s lo c = true) : ∀ j, lo ≤ j → j < lo + c → NodeOK b gr ng dom s j :=
  fun _ h1 h2 => trK_spec h h1 h2

theorem nodes_app {Q : ℕ → Prop} {a b c : ℕ} (h1 : ∀ j, a ≤ j → j < b → Q j)
    (h2 : ∀ j, b ≤ j → j < c → Q j) : ∀ j, a ≤ j → j < c → Q j := fun j ha hc => by
  by_cases hb : j < b
  · exact h1 j ha hb
  · exact h2 j (by omega) hc

theorem forest_orb {b gr ng : ℕ} {dom : ℕ → Bool} {X : Set (Fin 31671)}
    (hX : ∀ l < ng, tb H gr l < 31671 ∧ fp (tb H gr l) ∈ X) {s e : ℕ}
    (hN : ∀ j, s ≤ j → j < e → NodeOK b gr ng dom s j) :
    ∀ j, s ≤ j → j < e → fp (tb H b j) ∈ Orb tau X (fp (tb H b s)) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hs he
    by_cases hj : j = s
    · subst hj
      exact orb_self _ _ _
    · obtain ⟨-, -, -, -, hn⟩ := hN j hs he
      obtain ⟨h1, h2, h3, h4⟩ := hn hj
      have hr := ih _ h2 h1 (by omega)
      have hrlt := (hN _ h1 (by omega)).1
      obtain ⟨hgl, hgX⟩ := hX _ h3
      rw [← h4, cJ_tau hgl hrlt]
      exact orb_step hr hgX

@[expose] noncomputable def band (b : ℕ) (dom : ℕ → Bool) (lo hi : ℕ) : Finset (Fin 31671) :=
  Finset.univ.filter fun x => dom x.val = true ∧ lo ≤ tb H (b + 3) x.val ∧ tb H (b + 3) x.val < hi

theorem mem_band {b : ℕ} {dom : ℕ → Bool} {lo hi : ℕ} {x : Fin 31671} :
    x ∈ band b dom lo hi ↔ dom x.val = true ∧ lo ≤ tb H (b + 3) x.val ∧ tb H (b + 3) x.val < hi := by
  rw [band, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

theorem band_card {b gr ng : ℕ} {dom : ℕ → Bool} {lo hi : ℕ} (hlh : lo ≤ hi)
    (hN : ∀ j, lo ≤ j → j < hi → ∃ s, NodeOK b gr ng dom s j)
    (hcov : ∀ x < 31671, dom x = true → tb H b (tb H (b + 3) x) = x) :
    (band b dom lo hi).card = hi - lo := by
  rw [← Nat.card_Ico lo hi]
  refine Finset.card_nbij' (fun x => tb H (b + 3) x.val) (fun j => fp (tb H b j)) (fun x hx => ?_)
    (fun j hj => ?_) (fun x hx => ?_) (fun j hj => ?_)
  · rw [Finset.mem_coe, mem_band] at hx
    exact Finset.mem_Ico.2 ⟨hx.2.1, hx.2.2⟩
  · rw [Finset.mem_coe, Finset.mem_Ico] at hj
    obtain ⟨s, h1, h2, h3, -⟩ := hN j hj.1 hj.2
    rw [Finset.mem_coe, mem_band, fp_val h1, h3]
    exact ⟨h2, hj.1, hj.2⟩
  · rw [Finset.mem_coe, mem_band] at hx
    beta_reduce
    rw [hcov x.val x.isLt hx.1, fp_of]
  · rw [Finset.mem_coe, Finset.mem_Ico] at hj
    obtain ⟨s, h1, -, h3, -⟩ := hN j hj.1 hj.2
    beta_reduce
    rw [fp_val h1, h3]

end

end CertificateChecks.KernelFi23T

end
