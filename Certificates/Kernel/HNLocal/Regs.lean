module

public import CFSG.Sporadic.HN.LocalK
public import CFSG.Sporadic.HN.Commutant
public import Certificates.Kernel.HNLocal.Data
public import Certificates.Data.Kernel.HNMultK
public import CFSG.Certificates.Kernel.Spor.OrdSound
public import CFSG.Certificates.Kernel.Orders.HN.Data.Const
import Certificates.Kernel.HNLocal.Checks.R
import Certificates.Kernel.HN3166.Ord
import Certificates.Kernel.HN3166.Seed
import Certificates.Kernel.VecCert.WordProg
import CFSG.Certificates.Kernel.Orders.HN.Data.Sel
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.Kernel.HNLocalSound
public import CFSG.Sporadic.Th.F2Spec

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelHNLocal

open CFSG.KC.Ord CFSG.KS.Ord CFSG.KC.HNMult CFSG.KD.HNLocal CFSG.Sporadic.F5 CFSG.Sporadic.HN.LocalK
open CFSG.Sporadic.Fi23 CFSG.Sporadic.Th

local notation "Dt" => CFSG.Sporadic.HN.Native.hnData

local notation "OM" => ordMat 5 (CFSG.Sporadic.F5.Native.F5Data.d CFSG.Sporadic.HN.Native.hnData) 13 1729

local notation "MUL" => CFSG.KD.HNLocal.mul

private theorem andB_true {a b : Bool} (h : andB a b = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all [andB]

theorem decL_eq (w : List ℕ) : decL w = w.map letC := by
  induction w with
  | nil => rfl
  | cons c w ih =>
    change List.cons (letC c) (decL w) = _
    rw [ih, List.map_cons]

@[expose] noncomputable def lm (c : ℕ) : Matrix (Fin (Dt).d) (Fin (Dt).d) (ZMod 5) :=
  OM (letM RB 47 (letC c))

@[expose] noncomputable def Mr (g : ℕ) : Matrix (Fin (Dt).d) (Fin (Dt).d) (ZMod 5) := OM (RB (g + 1))

@[expose] noncomputable def Mi (g : ℕ) : Matrix (Fin (Dt).d) (Fin (Dt).d) (ZMod 5) := OM (RB (48 + g))

theorem mul_comm_of_one {d : ℕ} {A B : Matrix (Fin d) (Fin d) (ZMod 5)} (h : A * B = 1) :
    B * A = 1 :=
  mul_eq_one_comm.mp h

theorem lm_eq (c : ℕ) : lm c = if c % 2 = 1 then Mr (c / 2) else Mi (c / 2) := by
  unfold lm Mr Mi
  rw [CertificateChecks.KernelWP.letC_div]
  by_cases h : c % 2 = 1
  · simp only [h, decide_true, if_true]
    rfl
  · simp only [h, decide_false, if_false]
    change OM (RB (Nat.add (Nat.succ 47) (c / 2))) = _
    rfl

theorem sound {rels : List (List (ℕ × Bool))} (hb : relsBounded rels 47 = true)
    (hr : ∀ r < lenRels rels, relOK RB MUL rels 47 CFSG.KD.OrdHN.ONE r = true ∨
      ∃ s < r, relDupOK rels s r = true) :
    (∀ g < 47, ordMat 5 133 13 1729 (RB (g + 1)) * ordMat 5 133 13 1729 (RB (47 + 1 + g)) = 1) ∧
      ∀ v ∈ rels, (v.map fun x => ordMat 5 133 13 1729 (letM RB 47 x)).prod = 1 :=
  rels_sound (p := 5) (d := 133) (w := 13) (S := 1729) (T := 9) (L := CFSG.KD.OrdHN.L)
    (H := CFSG.KD.OrdHN.H) (CM := CFSG.KD.OrdHN.CM) (RM := CFSG.KD.OrdHN.RM)
    (ONE := CFSG.KD.OrdHN.ONE) (LV := CFSG.KD.OrdHN.LV) (HV := CFSG.KD.OrdHN.HV)
    (nb := 229957) (Lg := 47) (RB := RB) CFSG.KD.OrdHN.consts rfl roots invs hb hr

theorem pair (g : ℕ) (hg : g < 47) : Mr g * Mi g = 1 := by
  have h := (sound (rels := []) rfl (fun r hr => absurd hr (Nat.not_lt_zero r))).1 g hg
  have e : 47 + 1 + g = 48 + g := by omega
  rw [e] at h
  exact h

theorem relW_one {w : List ℕ} (h : relW RB MUL 47 CFSG.KD.OrdHN.ONE w = true) :
    (w.map lm).prod = 1 := by
  obtain ⟨hb, hr⟩ := andB_true h
  have hs := (sound hb (fun r hr' => by
      have h1 : r = 0 := by
        have : lenRels (List.cons (decL w) List.nil) = 1 := rfl
        omega
      subst h1
      exact Or.inl hr)).2 (decL w) List.mem_cons_self
  rw [decL_eq, List.map_map] at hs
  exact hs

theorem range_spec {lo : ℕ} :
    ∀ n, relWRange RB MUL 47 CFSG.KD.OrdHN.ONE WDL lo n = true →
      ∀ k < n, relW RB MUL 47 CFSG.KD.OrdHN.ONE (WDL (lo + k)) = true
  | 0, _, k, hk => absurd hk (Nat.not_lt_zero k)
  | n + 1, h, k, hk => by
    obtain ⟨h1, h2⟩ := andB_true h
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · exact range_spec n h1 k hk
    · exact h2

theorem word_one {k : ℕ} (hk : k < 45) : ((WDL k).map lm).prod = 1 := by
  have h := range_spec 45 rws k hk
  rw [Nat.zero_add] at h
  exact relW_one h

theorem word_root {k g : ℕ} (hk : k < 45) (hg : g < 47) {u : List ℕ} (hu : WDL k = u ++ [2 * g]) :
    (u.map lm).prod = Mr g := by
  have h := word_one hk
  rw [hu, List.map_append, List.prod_append, List.map_singleton, List.prod_singleton,
    lm_eq, if_neg (by omega : ¬ 2 * g % 2 = 1), Nat.mul_div_cancel_left g (by norm_num)] at h
  have h2 : Mi g * Mr g = 1 := mul_comm_of_one (pair g hg)
  calc (u.map lm).prod = (u.map lm).prod * (Mi g * Mr g) := by rw [h2, mul_one]
    _ = Mr g := by rw [← mul_assoc, h, one_mul]

@[expose] def slpCode (z : ℤ) : ℕ :=
  2 * (if z.natAbs ≤ 2 then z.natAbs - 1 else z.natAbs - 3) + (if 0 < z then 1 else 0)

theorem tie_w : ∀ j < 15, 2 ≤ j →
    WDL (j - 2) = CFSG.Sporadic.HN.Local.Native.invWords[j]!.map slpCode ++ [2 * j] := by
  decide +kernel

theorem bnd_w : ∀ j < 15, ∀ z ∈ CFSG.Sporadic.HN.Local.Native.invWords[j]!,
    (z = 1 ∨ z = -1 ∨ z = 2 ∨ z = -2) ∨ (3 ≤ z.natAbs ∧ z.natAbs - 3 < j) := by
  decide +kernel

theorem words01 : CFSG.Sporadic.HN.Local.Native.invWords[0]! = [1] ∧
    CFSG.Sporadic.HN.Local.Native.invWords[1]! = [2] := by
  decide +kernel

noncomputable abbrev matHom : J Dt →* Matrix (Fin (Dt).d) (Fin (Dt).d) (ZMod 5) :=
  (Units.coeHom _).comp (J Dt).subtype

theorem mat_eq (x : J Dt) : mat Dt x = matHom x := rfl

theorem mat_prod (l : List (J Dt)) : mat Dt l.prod = (l.map (mat Dt)).prod := by
  rw [mat_eq, map_list_prod]
  rfl

theorem mat_inv_of {x : J Dt} {g : ℕ} (hg : g < 47) (hx : mat Dt x = Mr g) :
    mat Dt x⁻¹ = Mi g := by
  have h1 : mat Dt x⁻¹ * mat Dt x = 1 := by
    rw [mat_eq, mat_eq, ← map_mul, inv_mul_cancel, map_one]
  calc mat Dt x⁻¹ = mat Dt x⁻¹ * (Mr g * Mi g) := by rw [pair g hg, mul_one]
    _ = Mi g := by rw [← mul_assoc, ← hx, h1, one_mul]

theorem mat_a : mat Dt (a Dt) = Mr 0 := by
  rw [mat_a' CertificateChecks.KernelHN.det_mA, CertificateChecks.KernelHN.o_mA]
  exact congrArg OM (Nat.eq_of_beq_eq_true ra).symm

theorem mat_b : mat Dt (b Dt) = Mr 1 := by
  rw [mat_b' CertificateChecks.KernelHN.det_mB, CertificateChecks.KernelHN.o_mB]
  exact congrArg OM (Nat.eq_of_beq_eq_true rb).symm

theorem wG0 : wG 0 = a Dt := by
  change slpG (genG Dt) CFSG.Sporadic.HN.Local.Native.invWords 0 = _
  rw [slpG_eq, words01.1]
  simp [wordG, genG]

theorem wG1 : wG 1 = b Dt := by
  change slpG (genG Dt) CFSG.Sporadic.HN.Local.Native.invWords 1 = _
  rw [slpG_eq, words01.2]
  simp [wordG, genG]

theorem mat_wordG {f : ℤ → J Dt} (w : List ℤ) :
    mat Dt (wordG f w) = (w.map fun z => mat Dt (f z)).prod := by
  unfold wordG
  rw [mat_prod, List.map_map]
  rfl

theorem mat_wG : ∀ j < 15, mat Dt (wG j) = Mr j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    rcases Nat.lt_or_ge j 2 with h2 | h2
    · interval_cases j
      · rw [wG0, mat_a]
      · rw [wG1, mat_b]
    · have hw := word_root (k := j - 2) (by omega) (by omega) (tie_w j hj h2)
      rw [← hw]
      change mat Dt (slpG (genG Dt) CFSG.Sporadic.HN.Local.Native.invWords j) = _
      rw [slpG_eq, mat_wordG, List.map_map]
      congr 1
      refine List.map_congr_left fun z hz => ?_
      beta_reduce
      change _ = lm (slpCode z)
      rw [lm_eq]
      have hai := mat_inv_of (x := a Dt) (g := 0) (by norm_num) mat_a
      have hbi := mat_inv_of (x := b Dt) (g := 1) (by norm_num) mat_b
      rcases bnd_w j hj z hz with (rfl | rfl | rfl | rfl) | ⟨h3, h4⟩
      · simp [genG, slpCode, mat_a]
      · simp [genG, slpCode, hai]
      · simp [genG, slpCode, mat_b]
      · simp [genG, slpCode, hbi]
      · have hz2 : ¬ z.natAbs ≤ 2 := by omega
        rw [if_neg hz2, if_pos h4]
        have hk : slpCode z / 2 = z.natAbs - 3 := by
          unfold slpCode
          rw [if_neg hz2]
          split_ifs <;> omega
        rw [hk]
        have hg' := ih (z.natAbs - 3) h4 (by omega)
        by_cases hp : 0 < z
        · have hc : slpCode z % 2 = 1 := by
            unfold slpCode
            rw [if_neg hz2, if_pos hp]
            omega
          rw [if_pos hp, if_pos hc]
          exact hg'
        · have hc : ¬ slpCode z % 2 = 1 := by
            unfold slpCode
            rw [if_neg hz2, if_neg hp]
            omega
          rw [if_neg hp, if_neg hc]
          exact mat_inv_of (by omega) hg'

@[expose] noncomputable def pw (a : ℕ) : List ℕ := WDL (13 + a)

@[expose] noncomputable def phalf (a : ℕ) : ℕ := ((pw a).length - 2) / 2

@[expose] noncomputable def pcs (a : ℕ) : List ℕ := (pw a).take (phalf a)

@[expose] noncomputable def ptc (a : ℕ) : ℕ := (pw a)[phalf a]!

@[expose] def invC (u : List ℕ) : List ℕ := (u.map fun c => if c % 2 = 1 then c - 1 else c + 1).reverse

theorem tie_partner : ∀ a < 32, pw a = pcs a ++ [ptc a] ++ invC (pcs a) ++ [2 * (15 + a)] ∧
    (ptc a = 25 ∨ ptc a = 27) ∧ ∀ c ∈ pcs a, c < 4 := by
  decide +kernel

@[expose] noncomputable def elAB (c : ℕ) : J Dt :=
  if c = 1 then a Dt else if c = 0 then (a Dt)⁻¹ else if c = 3 then b Dt else (b Dt)⁻¹

theorem mat_elAB {c : ℕ} (hc : c < 4) : mat Dt (elAB c) = lm c := by
  have hai := mat_inv_of (x := a Dt) (g := 0) (by norm_num) mat_a
  have hbi := mat_inv_of (x := b Dt) (g := 1) (by norm_num) mat_b
  rw [lm_eq]
  interval_cases c
  · simp [elAB, hai]
  · simp [elAB, mat_a]
  · simp [elAB, hbi]
  · simp [elAB, mat_b]

theorem lm_inv {c : ℕ} (hc : c < 94) :
    lm c * lm (if c % 2 = 1 then c - 1 else c + 1) = 1 := by
  rw [lm_eq, lm_eq]
  by_cases h : c % 2 = 1
  · rw [if_pos h, if_pos h, if_neg (by omega), show (c - 1) / 2 = c / 2 by omega]
    exact pair _ (by omega)
  · rw [if_neg h, if_neg h, if_pos (by omega), show (c + 1) / 2 = c / 2 by omega]
    exact mul_comm_of_one (pair _ (by omega))

theorem prod_invC {u : List ℕ} (hu : ∀ c ∈ u, c < 4) : (u.map lm).prod * ((invC u).map lm).prod = 1 := by
  induction u with
  | nil => simp [invC]
  | cons c u ih =>
    have hc := hu c List.mem_cons_self
    have ih' := ih fun c' hc' => hu c' (List.mem_cons_of_mem _ hc')
    have e : invC (c :: u) = invC u ++ [if c % 2 = 1 then c - 1 else c + 1] := by
      simp [invC]
    rw [e, List.map_cons, List.prod_cons, List.map_append, List.prod_append, List.map_singleton,
      List.prod_singleton, mul_assoc, ← mul_assoc ((u.map lm).prod), ih', one_mul, lm_inv (by omega)]

@[expose] noncomputable def hP (a : ℕ) : J Dt := ((pcs a).map elAB).prod

@[expose] noncomputable def pIdx (a : ℕ) : ℕ := (ptc a - 25) / 2

theorem mat_hP {a : ℕ} (ha : a < 32) : mat Dt (hP a) = ((pcs a).map lm).prod := by
  unfold hP
  rw [mat_prod, List.map_map]
  congr 1
  exact List.map_congr_left fun c hc => mat_elAB ((tie_partner a ha).2.2 c hc)

theorem mat_partner {a : ℕ} (ha : a < 32) :
    OM (RP a) = mat Dt (hP a * wG (12 + pIdx a) * (hP a)⁻¹) ∧ pIdx a < 2 := by
  obtain ⟨hw, ht, hcs⟩ := tie_partner a ha
  have hidx : pIdx a < 2 ∧ ptc a = 2 * (12 + pIdx a) + 1 := by
    unfold pIdx
    rcases ht with h | h <;> rw [h] <;> norm_num
  refine ⟨?_, hidx.1⟩
  have hroot := word_root (k := 13 + a) (g := 15 + a) (by omega) (by omega)
    (u := pcs a ++ [ptc a] ++ invC (pcs a)) (by rw [← hw]; rfl)
  have hinv : mat Dt (hP a)⁻¹ = ((invC (pcs a)).map lm).prod := by
    have h1 : mat Dt (hP a) * ((invC (pcs a)).map lm).prod = 1 := by
      rw [mat_hP ha]; exact prod_invC hcs
    have h2 : mat Dt (hP a)⁻¹ * mat Dt (hP a) = 1 := by
      rw [mat_eq, mat_eq, ← map_mul, inv_mul_cancel, map_one]
    calc mat Dt (hP a)⁻¹ = mat Dt (hP a)⁻¹ * (mat Dt (hP a) * ((invC (pcs a)).map lm).prod) := by
          rw [h1, mul_one]
      _ = _ := by rw [← mul_assoc, h2, one_mul]
  have ht' : lm (ptc a) = mat Dt (wG (12 + pIdx a)) := by
    rw [hidx.2, lm_eq, if_pos (by omega), show (2 * (12 + pIdx a) + 1) / 2 = 12 + pIdx a by omega,
      mat_wG _ (by omega)]
  change OM (RB (Nat.add 16 a)) = _
  have e : Nat.add 16 a = 15 + a + 1 := by change 16 + a = 15 + a + 1; omega
  rw [e]
  change Mr (15 + a) = _
  rw [← hroot, mat_eq, map_mul, map_mul, ← mat_eq, ← mat_eq, ← mat_eq, mat_hP ha, hinv, ← ht',
    List.map_append, List.map_append, List.prod_append, List.prod_append, List.map_singleton,
    List.prod_singleton]

end CertificateChecks.KernelHNLocal

end
