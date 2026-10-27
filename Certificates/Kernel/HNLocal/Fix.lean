module

public import Certificates.Kernel.HNLocal.Regs
public import CFSG.Certificates.Kernel.HNLocalSound
public import CFSG.Certificates.Kernel.Orders.HN.Data.Const
import Certificates.Kernel.HNLocal.Checks.K
import Certificates.Kernel.HNLocal.Checks.R
import Certificates.Kernel.HN3166.Seed
import CFSG.Certificates.Kernel.Orders.HN.Checks.K
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelHNLocal

open CFSG.KC.Ord CFSG.KS.Ord CFSG.KC.HNLocal CFSG.KD.HNLocal CFSG.Sporadic.F5
open CFSG.Sporadic.HN.LocalK
open scoped Matrix

local notation "Dt" => CFSG.Sporadic.HN.Native.hnData

private theorem andB_true {a b : Bool} (h : andB a b = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all [andB]

private theorem bAnd_true {a b : Bool} (h : bAnd(a, b) = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all

theorem rootsOK_spec {RB : Nat → Nat} {vld : Nat → Bool} {lo : Nat} :
    ∀ hi, rootsOK RB vld lo hi = true → ∀ i, lo ≤ i → i < hi → vld (RB i) = true
  | 0, _, i, _, h => absurd h (Nat.not_lt_zero i)
  | hi + 1, h, i, h1, h2 => by
    obtain ⟨h3, h4⟩ := andB_true h
    rcases Nat.lt_succ_iff_lt_or_eq.1 h2 with h2 | rfl
    · exact rootsOK_spec hi h3 i h1 h2
    · have hb : Nat.ble lo i = true := Nat.ble_eq.mpr h1
      rw [hb] at h4
      exact h4

theorem consts : constsOK 5 13 1729 133 9 CFSG.KD.OrdHN.L CFSG.KD.OrdHN.H CFSG.KD.OrdHN.CM
    CFSG.KD.OrdHN.RM CFSG.KD.OrdHN.ONE CFSG.KD.OrdHN.LV CFSG.KD.OrdHN.HV = true := CFSG.KD.OrdHN.consts

theorem canon_of_valid {X : Nat} (h : validM 5 229957 CFSG.KD.OrdHN.L CFSG.KD.OrdHN.H X = true) :
    Canon 5 133 13 X := by
  have h' : validM 5 (133 * 1729) CFSG.KD.OrdHN.L CFSG.KD.OrdHN.H X = true := by
    rw [show (133 * 1729 : Nat) = 229957 by norm_num]
    exact h
  exact validM_canon (d := 133) (S := 1729) consts h'

theorem canon_root {r : Nat} (h0 : 0 < r) (h1 : r < 48) : Canon 5 133 13 (RB r) :=
  canon_of_valid (rootsOK_spec 48 roots r h0 h1)

theorem M_eq : M = 2 ^ 399 - 1 := by decide +kernel

theorem tp_sound {G X : Nat} (hX : Canon 5 133 13 X) (h : Nat.beq G (trM X) = true) :
    Canon 5 133 13 G ∧ CFSG.KS.HNLocal.OM G = (CFSG.KS.HNLocal.OM X)ᵀ := by
  rw [Nat.eq_of_beq_eq_true h]
  exact CFSG.KS.HNLocal.trM_sound hX

theorem cGA : Canon 5 133 13 GA ∧ CFSG.KS.HNLocal.OM GA = (CFSG.KS.HNLocal.OM (RB (0 + 1)))ᵀ :=
  tp_sound (canon_root (r := 1) (by norm_num) (by norm_num)) tp_GA
theorem cGB : Canon 5 133 13 GB ∧ CFSG.KS.HNLocal.OM GB = (CFSG.KS.HNLocal.OM (RB (1 + 1)))ᵀ :=
  tp_sound (canon_root (r := 2) (by norm_num) (by norm_num)) tp_GB
theorem cGX2 : Canon 5 133 13 GX2 ∧ CFSG.KS.HNLocal.OM GX2 = (CFSG.KS.HNLocal.OM (RB (2 + 1)))ᵀ :=
  tp_sound (canon_root (r := 3) (by norm_num) (by norm_num)) tp_GX2
theorem cGX3 : Canon 5 133 13 GX3 ∧ CFSG.KS.HNLocal.OM GX3 = (CFSG.KS.HNLocal.OM (RB (3 + 1)))ᵀ :=
  tp_sound (canon_root (r := 4) (by norm_num) (by norm_num)) tp_GX3
theorem cGT2 : Canon 5 133 13 GT2 ∧ CFSG.KS.HNLocal.OM GT2 = (CFSG.KS.HNLocal.OM (RB (12 + 1)))ᵀ :=
  tp_sound (canon_root (r := 13) (by norm_num) (by norm_num)) tp_GT2
theorem cGT4 : Canon 5 133 13 GT4 ∧ CFSG.KS.HNLocal.OM GT4 = (CFSG.KS.HNLocal.OM (RB (13 + 1)))ᵀ :=
  tp_sound (canon_root (r := 14) (by norm_num) (by norm_num)) tp_GT4

theorem mat_wG_of {j : Nat} (hj : j < 15) {G : Nat}
    (hG : CFSG.KS.HNLocal.OM G = (CFSG.KS.HNLocal.OM (RB (j + 1)))ᵀ) :
    mat Dt (wG j) = (CFSG.KS.HNLocal.OM G)ᵀ := by
  rw [hG, Matrix.transpose_transpose, mat_wG j hj]
  rfl

theorem smul_eq_of {j : Nat} (hj : j < 15) {G : Nat}
    (hG : CFSG.KS.HNLocal.OM G = (CFSG.KS.HNLocal.OM (RB (j + 1)))ᵀ) (v : Vec Dt) :
    wG j • v = (CFSG.KS.HNLocal.OM G)ᵀ *ᵥ v := by
  rw [smul_vec, mat_wG_of hj hG]
  rfl

theorem V0_lt : CFSG.KD.HNLocal.V0 < 2 ^ 399 := by decide +kernel

theorem fix_root {j : Nat} (hj : j < 15) {G : Nat} (hc : Canon 5 133 13 G)
    (hG : CFSG.KS.HNLocal.OM G = (CFSG.KS.HNLocal.OM (RB (j + 1)))ᵀ)
    (h : fixVec MS CFSG.KD.OrdHN.L CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM G V0 = true) :
    wG j • rootV = rootV := by
  rw [smul_eq_of hj hG]
  exact (CFSG.KS.HNLocal.fixVec_sound consts masks cm hc V0_lt h).2

theorem root_canon : CFSG.KS.HNLocal.CCanon V0 :=
  (CFSG.KS.HNLocal.fixVec_sound consts masks cm cGX2.1 V0_lt v0_GX2).1

theorem x2_root : wG 2 • rootV = rootV := fix_root (j := 2) (by norm_num) cGX2.1 cGX2.2 v0_GX2
theorem x3_root : wG 3 • rootV = rootV := fix_root (j := 3) (by norm_num) cGX3.1 cGX3.2 v0_GX3
theorem t2_root : wG 12 • rootV = rootV := fix_root (j := 12) (by norm_num) cGT2.1 cGT2.2 v0_GT2
theorem t4_root : wG 13 • rootV = rootV := fix_root (j := 13) (by norm_num) cGT4.1 cGT4.2 v0_GT4

theorem act_W {j : Nat} (hj : j < 15) {G : Nat} (hc : Canon 5 133 13 G)
    (hG : CFSG.KS.HNLocal.OM G = (CFSG.KS.HNLocal.OM (RB (j + 1)))ᵀ) {PI : Nat → Nat}
    {N c0 c1 c2 c3 n0 n1 n2 n3 : Nat}
    (h0 : actLeaf WC PI M MS CFSG.KD.OrdHN.L CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM N G c0 n0 = true)
    (h1 : actLeaf WC PI M MS CFSG.KD.OrdHN.L CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM N G c1 n1 = true)
    (h2 : actLeaf WC PI M MS CFSG.KD.OrdHN.L CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM N G c2 n2 = true)
    (h3 : actLeaf WC PI M MS CFSG.KD.OrdHN.L CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM N G c3 n3 = true)
    (hN : N = 462) (hc : c0 = 0 ∧ c1 = 1 ∧ c2 = 2 ∧ c3 = 3)
    (hn : n0 = 133 ∧ n1 = 133 ∧ n2 = 133 ∧ n3 = 63) :
    ∀ k : Fin 462, PI k.val < 462 ∧ CFSG.KS.HNLocal.CCanon (recX WC M (PI k.val)) ∧
      wG j • hnW k = CFSG.KS.HNLocal.cvec (recX WC (2 ^ 399 - 1) (PI k.val)) := by
  obtain ⟨e0, e1, e2, e3⟩ := hc
  obtain ⟨f0, f1, f2, f3⟩ := hn
  subst hN e0 e1 e2 e3 f0 f1 f2 f3
  intro k
  have key : ∀ c nr, nr ≤ 133 →
      actLeaf WC PI M MS CFSG.KD.OrdHN.L CFSG.KD.OrdHN.H CM3 CFSG.KD.OrdHN.RM 462 G c nr = true →
      ∀ r < nr, 133 * c + r = k.val → PI k.val < 462 ∧ CFSG.KS.HNLocal.CCanon (recX WC M (PI k.val)) ∧
        wG j • hnW k = CFSG.KS.HNLocal.cvec (recX WC (2 ^ 399 - 1) (PI k.val)) := by
    intro c nr hnr hc' r hr hk
    obtain ⟨hp, hcan, hv⟩ := CFSG.KS.HNLocal.actLeaf_sound consts masks cm hc hnr hc' r hr
    rw [hk] at hp hcan hv
    refine ⟨hp, hcan, ?_⟩
    rw [smul_eq_of hj hG, hnW, ← M_eq, ← hv]
  have hk := k.2
  rcases Nat.lt_or_ge k.val 133 with h | h
  · exact key 0 133 le_rfl h0 k.val h (by omega)
  rcases Nat.lt_or_ge k.val 266 with h' | h'
  · exact key 1 133 le_rfl h1 (k.val - 133) (by omega) (by omega)
  rcases Nat.lt_or_ge k.val 399 with h'' | h''
  · exact key 2 133 le_rfl h2 (k.val - 266) (by omega) (by omega)
  · exact key 3 63 (by norm_num) h3 (k.val - 399) (by omega) (by omega)

theorem pi_val {PI : Nat → Nat} {k : Fin 462} (h : PI k.val < 462) :
    (⟨PI k.val % 462, Nat.mod_lt _ (by norm_num)⟩ : Fin 462) = ⟨PI k.val, h⟩ :=
  Fin.ext (Nat.mod_eq_of_lt h)

theorem x2_W (k : Fin 462) : wG 2 • hnW k = hnW (pi2 k) := by
  obtain ⟨hp, -, hv⟩ := act_W (j := 2) (by norm_num) cGX2.1 cGX2.2 w_GX2_0 w_GX2_1 w_GX2_2 w_GX2_3
    rfl ⟨rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl, rfl⟩ k
  have e : pi2 k = ⟨PI2 k.val, hp⟩ := Fin.ext (Nat.mod_eq_of_lt hp)
  rw [hv, e]
  rfl

theorem x3_W (k : Fin 462) : wG 3 • hnW k = hnW (pi3 k) := by
  obtain ⟨hp, -, hv⟩ := act_W (j := 3) (by norm_num) cGX3.1 cGX3.2 w_GX3_0 w_GX3_1 w_GX3_2 w_GX3_3
    rfl ⟨rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl, rfl⟩ k
  have e : pi3 k = ⟨PI3 k.val, hp⟩ := Fin.ext (Nat.mod_eq_of_lt hp)
  rw [hv, e]
  rfl

theorem t2_W (k : Fin 462) : wG 12 • hnW k = hnW (pit2 k) := by
  obtain ⟨hp, -, hv⟩ := act_W (j := 12) (by norm_num) cGT2.1 cGT2.2 w_GT2_0 w_GT2_1 w_GT2_2 w_GT2_3
    rfl ⟨rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl, rfl⟩ k
  have e : pit2 k = ⟨PT2 k.val, hp⟩ := Fin.ext (Nat.mod_eq_of_lt hp)
  rw [hv, e]
  rfl

theorem t4_W (k : Fin 462) : wG 13 • hnW k = hnW (pit4 k) := by
  obtain ⟨hp, -, hv⟩ := act_W (j := 13) (by norm_num) cGT4.1 cGT4.2 w_GT4_0 w_GT4_1 w_GT4_2 w_GT4_3
    rfl ⟨rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl, rfl⟩ k
  have e : pit4 k = ⟨PT4 k.val, hp⟩ := Fin.ext (Nat.mod_eq_of_lt hp)
  rw [hv, e]
  rfl

theorem pi2_pi2 : ∀ k : Fin 462, pi2 (pi2 k) = k := by decide +kernel

theorem W_canon (k : Fin 462) : CFSG.KS.HNLocal.CCanon (recX WC M k.val) := by
  obtain ⟨hp, hc, -⟩ := act_W (j := 2) (by norm_num) cGX2.1 cGX2.2 w_GX2_0 w_GX2_1 w_GX2_2 w_GX2_3
    rfl ⟨rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl, rfl⟩ (pi2 k)
  have e : CFSG.KD.HNLocal.PI2 (pi2 k).val = k.val := by
    have := congrArg Fin.val (pi2_pi2 k)
    change PI2 (pi2 k).val % 462 = k.val at this
    rwa [Nat.mod_eq_of_lt hp] at this
  rw [e] at hc
  exact hc

theorem injOn_of_order {n : Nat} {key σ : Nat → Nat} (h0 : 0 < n → σ 0 < n)
    (h : ∀ i, i + 1 < n → σ (i + 1) < n ∧ key (σ i) < key (σ (i + 1))) :
    ∀ i < n, ∀ j < n, key i = key j → i = j := by
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
  have hfs := Finite.injective_iff_surjective.1 hf
  intro i hi j hj e
  obtain ⟨i', hi'⟩ := hfs ⟨i, hi⟩
  obtain ⟨j', hj'⟩ := hfs ⟨j, hj⟩
  have ei : σ i' = i := congrArg Fin.val hi'
  have ej : σ j' = j := congrArg Fin.val hj'
  by_contra hne
  have hne' : i' ≠ j' := fun e' => hne (by rw [← ei, ← ej, e'])
  rcases Nat.lt_or_gt_of_ne (fun e' => hne' (Fin.ext e')) with h' | h'
  · have := hmono i' j' h' j'.2; rw [ei, ej, e] at this; exact lt_irrefl _ this
  · have := hmono j' i' h' i'.2; rw [ei, ej, e] at this; exact lt_irrefl _ this

theorem hnW_injective : Function.Injective hnW := by
  have hs : ∀ m < 4, (133 * m < 462 → sig SW (133 * m) < 462) ∧ ∀ u < 133, 133 * m + u + 1 < 462 →
      sig SW (133 * m + u + 1) < 462 ∧
        recX WC M (sig SW (133 * m + u)) < recX WC M (sig SW (133 * m + u + 1)) := by
    intro m hm
    apply CFSG.KS.HNLocal.sortLeaf_spec
    interval_cases m
    · exact wsort
    · exact wsort1
    · exact wsort2
    · exact wsort3
  have hinj := injOn_of_order (n := 462) (key := fun k => recX WC M k) (σ := sig SW)
    (fun _ => (hs 0 (by norm_num)).1 (by norm_num)) (fun i hi => by
      have h := (hs (i / 133) (by omega)).2 (i % 133) (Nat.mod_lt _ (by norm_num))
        (by omega)
      rw [show 133 * (i / 133) + i % 133 = i by omega] at h
      exact h)
  intro j k e
  apply Fin.ext
  apply hinj j.val j.2 k.val k.2
  apply CFSG.KS.HNLocal.cvec_inj (W_canon j) (W_canon k)
  rw [M_eq]
  exact e

theorem T_sq {j r : Nat} (hj : j < 15)
    (h : Nat.beq (CFSG.KD.HNLocal.mul (RB r) (RB r)) CFSG.KD.OrdHN.ONE = true) (hr : r = j + 1) :
    wG j ^ 2 = 1 := by
  subst hr
  have hc := canon_root (r := j + 1) (by omega) (by omega)
  have hm := (mulR_sound consts hc hc).2
  have e : mulR 5 13 1729 133 9 CFSG.KD.OrdHN.L CFSG.KD.OrdHN.H CFSG.KD.OrdHN.CM CFSG.KD.OrdHN.RM
      (RB (j + 1)) (RB (j + 1)) = CFSG.KD.OrdHN.ONE := Nat.eq_of_beq_eq_true h
  rw [e, (one_sound consts).2] at hm
  apply mat_injective Dt
  rw [CertificateChecks.KernelHN.mat_pow', mat_wG j hj]
  rw [pow_two]
  exact hm.symm

theorem t2_sq : wG 12 ^ 2 = 1 := T_sq (by norm_num) t2sq rfl
theorem t4_sq : wG 13 ^ 2 = 1 := T_sq (by norm_num) t4sq rfl

theorem trace_wG {j r v w : Nat} (hj : j < 15) (h : Nat.beq (traceL (RB r)) v = true)
    (hr : r = j + 1) (hv : v = w) : (mat Dt (wG j)).trace = (w : ZMod 5) := by
  subst hr hv
  rw [mat_wG j hj]
  have := CFSG.KS.HNLocal.traceL_sound (canon_root (r := j + 1) (by omega) (by omega))
  rw [Nat.eq_of_beq_eq_true h] at this
  exact this.symm

theorem trace_t2 : (mat Dt (wG 12)).trace = 1 := by
  have := trace_wG (j := 12) (w := 1) (by norm_num) trc2 rfl rfl
  simpa using this

theorem trace_t4 : (mat Dt (wG 13)).trace = 0 := by
  have := trace_wG (j := 13) (w := 0) (by norm_num) trc4 rfl rfl
  simpa using this

theorem trace_one : (mat Dt (1 : J Dt)).trace = 3 := by
  have e : mat Dt (1 : J Dt) = 1 := rfl
  rw [e, Matrix.trace_one, Fintype.card_fin]
  decide

theorem t2_ne_one : wG 12 ≠ 1 := fun h => by
  have := trace_t2
  rw [h, trace_one] at this
  exact absurd this (by decide)

theorem t4_ne_one : wG 13 ≠ 1 := fun h => by
  have := trace_t4
  rw [h, trace_one] at this
  exact absurd this (by decide)

theorem trace_ne : (mat Dt (wG 12)).trace ≠ (mat Dt (wG 13)).trace := by
  rw [trace_t2, trace_t4]
  decide

theorem wG14 : wG 14 = wG 2 := by
  apply mat_injective Dt
  rw [mat_wG 14 (by norm_num), mat_wG 2 (by norm_num)]
  have e := Nat.eq_of_beq_eq_true w14
  exact congrArg CFSG.KS.HNLocal.OM e

end CertificateChecks.KernelHNLocal

end
