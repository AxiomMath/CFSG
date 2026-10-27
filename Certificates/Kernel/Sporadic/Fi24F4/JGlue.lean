module

public import Certificates.Kernel.Sporadic.Fi24F4.JSw
public import Certificates.Kernel.Sporadic.Fi24F4.JX
public import Certificates.Kernel.Sporadic.Fi24R2W.Group
public import CFSG.Sporadic.Fi24I301.Facts

public section

namespace CFSG.KD.Fi24F4

open CFSG.KC CFSG.KC.Fi24R2W CFSG.KC.Fi24F4J CFSG.KD.Fi24Net CFSG.KS.Fi24Kit
open CFSG.Sporadic.Fi24I301 CFSG.Sporadic.FischerOddCore CFSG.Sporadic.Th
open CertificateChecks.KernelSpor.Fi24R2W
open CFSG.Sporadic.Fi24 (J)

theorem swc_all : ∀ i < 5, swc i = true := by
  intro i hi
  interval_cases i
  exacts [Ck.swc0, Ck.swc1, Ck.swc2, Ck.swc3, Ck.swc4]

theorem sxc_all : ∀ i < 5, sxc i = true := by
  intro i hi
  interval_cases i
  exacts [Ck.sxc0, Ck.sxc1, Ck.sxc2, Ck.sxc3, Ck.sxc4]

theorem cubec_all : ∀ i < 5, cubec i = true := by
  intro i hi
  interval_cases i
  exacts [Ck.cubec0, Ck.cubec1, Ck.cubec2, Ck.cubec3, Ck.cubec4]

theorem commc_all : ∀ n < 25, commc n = true := by
  intro n hn
  interval_cases n
  exacts [Ck.commc0, Ck.commc1, Ck.commc2, Ck.commc3, Ck.commc4, Ck.commc5, Ck.commc6, Ck.commc7,
    Ck.commc8, Ck.commc9, Ck.commc10, Ck.commc11, Ck.commc12, Ck.commc13, Ck.commc14, Ck.commc15,
    Ck.commc16, Ck.commc17, Ck.commc18, Ck.commc19, Ck.commc20, Ck.commc21, Ck.commc22,
    Ck.commc23, Ck.commc24]

theorem snc_all : ∀ k < 2, snc k = true := by
  intro k hk
  interval_cases k
  exacts [Ck.snc0, Ck.snc1]

theorem relc_all : ∀ n < 10, relc n = true := by
  intro n hn
  interval_cases n
  exacts [Ck.relc0, Ck.relc1, Ck.relc2, Ck.relc3, Ck.relc4, Ck.relc5, Ck.relc6, Ck.relc7,
    Ck.relc8, Ck.relc9]

section Words

theorem prodC_repL (w : List ℕ) : ∀ n, prodC (repL w n) = prodC w ^ n
  | 0 => rfl
  | n + 1 => by
    change prodC (w ++ repL w n) = _
    rw [prodC_append, prodC_repL w n, pow_succ']

theorem prodC_prodW (X : List (List ℕ)) (e : List ℕ) :
    prodC (prodW X e) = prodC (nthW X 0) ^ nthV e 0 * (prodC (nthW X 1) ^ nthV e 1 *
      (prodC (nthW X 2) ^ nthV e 2 * (prodC (nthW X 3) ^ nthV e 3 *
        prodC (nthW X 4) ^ nthV e 4))) := by
  unfold prodW
  simp only [prodC_append, prodC_repL]

theorem repL_lt {w : List ℕ} (h : ∀ l ∈ w, l < 26) : ∀ n, ∀ l ∈ repL w n, l < 26
  | 0, l, hl => absurd hl List.not_mem_nil
  | n + 1, l, hl => by
    change l ∈ w ++ repL w n at hl
    rcases List.mem_append.1 hl with h' | h'
    · exact h l h'
    · exact repL_lt h n l h'

theorem moves_ne {w : List ℕ} (hw : ∀ l ∈ w, l < 26) {b : ℕ} (hb : b < 306936)
    (h : moves NW w b = true) : prodC w ≠ 1 := by
  intro h1
  unfold moves at h
  rw [walkN_eq, List.reverse_reverse, ← (idx_prodC w hw b hb).1, h1, idx_one, Nat.beq_refl] at h
  exact Bool.noConfusion h

theorem differ_ne {u v : List ℕ} (hu : ∀ l ∈ u, l < 26) (hv : ∀ l ∈ v, l < 26) {b : ℕ}
    (hb : b < 306936) (h : differ NW u v b = true) : prodC u ≠ prodC v := by
  intro h1
  unfold differ at h
  rw [walkN_eq, walkN_eq, List.reverse_reverse, List.reverse_reverse,
    ← (idx_prodC u hu b hb).1, ← (idx_prodC v hv b hb).1, h1, Nat.beq_refl] at h
  exact Bool.noConfusion h

end Words

section Bray

theorem prodC_cwL {z : ℤ} (hz : z = 1 ∨ z = -1 ∨ z = 2 ∨ z = -2) :
    prodC (cwL SA SB z) = letterJC z := by
  rcases hz with rfl | rfl | rfl | rfl
  · change prodC SA = _
    rw [← fi24Ca_eq]
    simp [letterJC]
  · change prodC (CFSG.KC.Fi24R2W.invC SA) = _
    rw [prodC_invC, ← fi24Ca_eq]
    simp [letterJC]
  · change prodC SB = _
    rw [← fi24Cb_eq]
    simp [letterJC]
  · change prodC (CFSG.KC.Fi24R2W.invC SB) = _
    rw [prodC_invC, ← fi24Cb_eq]
    simp [letterJC]

theorem prodC_cw : ∀ w : List ℤ, (∀ z ∈ w, z = 1 ∨ z = -1 ∨ z = 2 ∨ z = -2) →
    prodC (cw SA SB w) = wordG letterJC w
  | [], _ => rfl
  | z :: w, h => by
    change prodC (cwL SA SB z ++ cw SA SB w) = _
    rw [prodC_append, prodC_cwL (h z List.mem_cons_self),
      prodC_cw w (fun z' hz' => h z' (List.mem_cons_of_mem _ hz'))]
    unfold wordG
    rw [List.map_cons, List.prod_cons]

theorem prodC_cwQ : ∀ w : List ℤ,
    prodC (cwQ SA SB w) = wordG (fun z => if z = 1 then fi24Ca else fi24Cb) w
  | [] => rfl
  | z :: w => by
    change prodC (_ ++ cwQ SA SB w) = _
    rw [prodC_append, prodC_cwQ w]
    unfold wordG
    rw [List.map_cons, List.prod_cons]
    congr 1
    rcases z with (_ | _ | m) | m
    · change prodC SB = _
      rw [← fi24Cb_eq]
      rfl
    · change prodC SA = _
      rw [← fi24Ca_eq]
      rfl
    · change prodC SB = _
      rw [← fi24Cb_eq, if_neg (by intro h; injection h with h; omega)]
    · change prodC SB = _
      rw [← fi24Cb_eq, if_neg (by intro h; cases h)]

theorem letters_ok : (∀ i < 5, ∀ z ∈ gW i, z = 1 ∨ z = -1 ∨ z = 2 ∨ z = -2) ∧
    (∀ k < 2, ∀ z ∈ nW k, z = 1 ∨ z = -1 ∨ z = 2 ∨ z = -2) := by decide

theorem codes_ok : (∀ i < 5, (∀ l ∈ cw SA SB (gW i), l < 26) ∧ (∀ l ∈ nthW J.sw i, l < 26) ∧
      (∀ l ∈ nthW J.sx i, l < 26)) ∧
    (∀ k < 2, (∀ l ∈ cw SA SB (nW k), l < 26) ∧ (∀ l ∈ nthW J.sn k, l < 26) ∧
      ∀ l ∈ CFSG.KC.Fi24R2W.invC (nthW J.sn k), l < 26) ∧
    (∀ e < 13, (∀ l ∈ cwQ SA SB (qW.getD e ([], 0)).1, l < 26) ∧ (∀ l ∈ nthW J.sq e, l < 26)) := by
  decide +kernel

theorem gW_eq : ∀ i < 5, genWords[i]! = gW i := by decide

theorem nW_eq : ∀ k < 2, nWords[k]! = nW k := by decide

theorem xJ_eq {i : ℕ} (hi : i < 5) : xJ i = prodC (nthW J.sx i) := by
  obtain ⟨h1, h2, h3⟩ := codes_ok.1 i hi
  have hw : wordG letterJC genWords[i]! = prodC (nthW J.sw i) := by
    rw [gW_eq i hi, ← prodC_cw _ (letters_ok.1 i hi)]
    exact eq_of_stage h1 h2 (swc_all i hi)
  unfold xJ
  rw [hw, ← prodC_repL]
  exact eq_of_stage (repL_lt h2 4) h3 (sxc_all i hi)

end Bray

end CFSG.KD.Fi24F4

end
