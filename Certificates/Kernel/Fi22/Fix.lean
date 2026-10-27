module

public import Certificates.Kernel.Fi22.Center
public import CFSG.Certificates.Kernel.Fi22.Bound2.Data.M
public import CFSG.Certificates.Kernel.Fi22.Bound2.Rels
import CFSG.Certificates.Kernel.Fi22.Fix.Checks.Base
import CFSG.Certificates.Kernel.Fi22.Fix.Checks.E
import CFSG.Certificates.Kernel.Fi22.Fix.Checks.W0
import CFSG.Certificates.Kernel.Fi22.Fix.Checks.W1
import CFSG.Certificates.Kernel.Fi22.Fix.Checks.W2
import CFSG.Certificates.Kernel.Fi22.Fix.Checks.W3
import CFSG.Certificates.Kernel.Fi22.Fix.Checks.W4
import CFSG.Certificates.Kernel.Fi22.Fix.Checks.W5
import CFSG.Certificates.Kernel.Fi22.Fix.Checks.W6
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Fi22.Fix.Sel

public section

namespace CertificateChecks.KernelFi22

open CFSG.KC CFSG.KC.LceS CFSG.KC.HOrb CFSG.KC.Fi22F CFSG.Certificates CFSG.Certificates.LCE
  CertificateChecks.KernelCo2

noncomputable abbrev ev (g : ℕ) : PG :=
  bval tg (wWord (CFSG.KC.Fi22K.subY (7 + g))) (wLen (CFSG.KC.Fi22K.subY (7 + g)))

@[expose] noncomputable def eIdx (W n q : ℕ) : ℕ := Nat.shiftRight (byte (wWord W) (n - 1 - q)) 1

@[expose] noncomputable def revE (W n k : ℕ) : PG := ((List.range k).map fun q => ev (eIdx W n q)).prod

theorem revE_succ (W n k : ℕ) : revE W n (k + 1) = revE W n k * ev (eIdx W n k) := by
  simp [revE, List.range_succ]

theorem bval_snoc {G : Type*} [Group G] (gen : ℕ → G) (W k : ℕ) :
    bval gen W (k + 1) = bval gen W k * letV gen (wLet W k) := by
  simp [bval, List.range_succ]

@[expose] noncomputable def preW (W n S k : ℕ) : PG :=
  if k ≤ n then revE W n k else revE W n n * bval tg (wWord S) (k - n)

theorem preW_zero {W n S : ℕ} : preW W n S 0 = 1 := by simp [preW, revE]

theorem preW_e {W n S k : ℕ} (hk : k < n) : preW W n S (k + 1) = preW W n S k * ev (eIdx W n k) := by
  simp only [preW, show k + 1 ≤ n from hk, show k ≤ n by omega, ↓reduceIte, revE_succ]

theorem preW_h {W n S k : ℕ} (hk : n ≤ k) :
    preW W n S (k + 1) = preW W n S k * letV tg (wLet (wWord S) (k - n)) := by
  unfold preW
  by_cases h : k ≤ n
  · have e : k = n := by omega
    subst e
    simp [show ¬ k + 1 ≤ k by omega, bval]
  · simp only [h, show ¬ k + 1 ≤ n by omega, ↓reduceIte, show k + 1 - n = k - n + 1 by omega, bval_snoc,
      mul_assoc]

theorem preW_end {W n S m : ℕ} (hm : 0 < m) : preW W n S (n + m) = revE W n n * bval tg (wWord S) m := by
  simp [preW, show ¬ n + m ≤ n by omega]

theorem wLet_clean {W n k : ℕ} (hW : W < 2 ^ (8 * n)) (hk : n ≤ k) : wLet W k = 0 := by
  rw [wLet_eq, Nat.div_eq_of_lt (lt_of_lt_of_le hW (Nat.pow_le_pow_right (by norm_num) (by omega)))]

theorem lettersBelow_spec {W n b : ℕ} (h : HO.lettersBelow W n b = true) : ∀ q < n, wLet W q < b := by
  induction n with
  | zero => intro q hq; omega
  | succ n ih =>
    intro q hq
    have h' : andB (HO.lettersBelow W n b) (Nat.blt (wLet W n) b) = true := h
    obtain ⟨h1, h2⟩ := KB.andB_true h'
    rcases Nat.lt_succ_iff_lt_or_eq.mp hq with hq | rfl
    · exact ih h1 q hq
    · simpa using h2

theorem letters_all {e b n : ℕ} (he : HO.entOK e b n = true) (hb : 0 < b) : ∀ k, wLet (wWord e) k < b := by
  obtain ⟨h1, h2⟩ := KB.andB_true he
  obtain ⟨-, h3⟩ := KB.andB_true h2
  intro k
  by_cases hk : k < wLen e
  · exact lettersBelow_spec h3 k hk
  · rw [wLet_clean (by simpa [Nat.shiftLeft_eq] using h1) (by omega)]
    exact hb

theorem eIdx_lt {W : ℕ} (h : HO.entOK W (nat_lit 12) (nat_lit 1023) = true) (n k : ℕ) : eIdx W n k < 6 := by
  have := letters_all h (by norm_num) (n - 1 - k)
  unfold eIdx
  have e : byte (wWord W) (n - 1 - k) = wLet (wWord W) (n - 1 - k) := rfl
  rw [e]
  change wLet (wWord W) (n - 1 - k) >>> 1 < 6
  rw [Nat.shiftRight_eq_div_pow]
  change wLet (wWord W) (n - 1 - k) < 12 at this
  omega

theorem fixE0 {rep : ℕ → PG} (hL : ∀ c < 4, Acts HB rep CFSG.KD.Fi22F.LV (Lsel c) (letV tg c)) :
    Acts HB rep CFSG.KD.Fi22F.LV CFSG.KD.Fi22F.E0 (ev 0) := by
  have hS : HO.entOK (CFSG.KC.Fi22K.subY 7) (nat_lit 4) (nat_lit 1023) = true := by quickRfl
  have hb : ∀ k, Acts HB rep CFSG.KD.Fi22F.LV (hBase (CFSG.KC.Fi22K.subY 7) 0 k) (letV tg (wLet (wWord (CFSG.KC.Fi22K.subY 7)) k)) :=
    fun k => hL _ (letters_all hS (by norm_num) k)
  have a0 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QEs0 0) (bval tg (wWord (CFSG.KC.Fi22K.subY 7)) 0) := acts_id CFSG.KD.Fi22F.eI0
  have a1 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QEs0 8) (bval tg (wWord (CFSG.KC.Fi22K.subY 7)) 8) :=
    chain_acts (pre := fun k => bval tg (wWord (CFSG.KC.Fi22K.subY 7)) k) CFSG.KD.Fi22F.e0s0 (fun k _ _ => hb k)
      (fun k _ _ => bval_snoc tg _ k) a0
  have a2 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QEs0 16) (bval tg (wWord (CFSG.KC.Fi22K.subY 7)) 16) :=
    chain_acts (pre := fun k => bval tg (wWord (CFSG.KC.Fi22K.subY 7)) k) CFSG.KD.Fi22F.e0s1 (fun k _ _ => hb k)
      (fun k _ _ => bval_snoc tg _ k) a1
  have a3 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QEs0 24) (bval tg (wWord (CFSG.KC.Fi22K.subY 7)) 24) :=
    chain_acts (pre := fun k => bval tg (wWord (CFSG.KC.Fi22K.subY 7)) k) CFSG.KD.Fi22F.e0s2 (fun k _ _ => hb k)
      (fun k _ _ => bval_snoc tg _ k) a2
  have a4 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QEs0 31) (bval tg (wWord (CFSG.KC.Fi22K.subY 7)) 31) :=
    chain_acts (pre := fun k => bval tg (wWord (CFSG.KC.Fi22K.subY 7)) k) CFSG.KD.Fi22F.e0s3 (fun k _ _ => hb k)
      (fun k _ _ => bval_snoc tg _ k) a3
  have e1 : CFSG.KD.Fi22F.QEs0 31 = CFSG.KD.Fi22F.E0 := Nat.eq_of_beq_eq_true CFSG.KD.Fi22F.eE0
  have e2 : wLen (CFSG.KC.Fi22K.subY 7) = 31 := Nat.eq_of_beq_eq_true (by quickRfl)
  rw [e1] at a4
  change Acts HB rep CFSG.KD.Fi22F.LV CFSG.KD.Fi22F.E0 (bval tg (wWord (CFSG.KC.Fi22K.subY 7)) (wLen (CFSG.KC.Fi22K.subY 7)))
  rw [e2]
  exact a4

theorem fixE1 {rep : ℕ → PG} (hL : ∀ c < 4, Acts HB rep CFSG.KD.Fi22F.LV (Lsel c) (letV tg c)) :
    Acts HB rep CFSG.KD.Fi22F.LV CFSG.KD.Fi22F.E1 (ev 1) := by
  have hS : HO.entOK (CFSG.KC.Fi22K.subY 8) (nat_lit 4) (nat_lit 1023) = true := by quickRfl
  have hb : ∀ k, Acts HB rep CFSG.KD.Fi22F.LV (hBase (CFSG.KC.Fi22K.subY 8) 0 k) (letV tg (wLet (wWord (CFSG.KC.Fi22K.subY 8)) k)) :=
    fun k => hL _ (letters_all hS (by norm_num) k)
  have a0 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QEs1 0) (bval tg (wWord (CFSG.KC.Fi22K.subY 8)) 0) := acts_id CFSG.KD.Fi22F.eI1
  have a1 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QEs1 8) (bval tg (wWord (CFSG.KC.Fi22K.subY 8)) 8) :=
    chain_acts (pre := fun k => bval tg (wWord (CFSG.KC.Fi22K.subY 8)) k) CFSG.KD.Fi22F.e1s0 (fun k _ _ => hb k)
      (fun k _ _ => bval_snoc tg _ k) a0
  have a2 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QEs1 16) (bval tg (wWord (CFSG.KC.Fi22K.subY 8)) 16) :=
    chain_acts (pre := fun k => bval tg (wWord (CFSG.KC.Fi22K.subY 8)) k) CFSG.KD.Fi22F.e1s1 (fun k _ _ => hb k)
      (fun k _ _ => bval_snoc tg _ k) a1
  have a3 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QEs1 24) (bval tg (wWord (CFSG.KC.Fi22K.subY 8)) 24) :=
    chain_acts (pre := fun k => bval tg (wWord (CFSG.KC.Fi22K.subY 8)) k) CFSG.KD.Fi22F.e1s2 (fun k _ _ => hb k)
      (fun k _ _ => bval_snoc tg _ k) a2
  have a4 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QEs1 29) (bval tg (wWord (CFSG.KC.Fi22K.subY 8)) 29) :=
    chain_acts (pre := fun k => bval tg (wWord (CFSG.KC.Fi22K.subY 8)) k) CFSG.KD.Fi22F.e1s3 (fun k _ _ => hb k)
      (fun k _ _ => bval_snoc tg _ k) a3
  have e1 : CFSG.KD.Fi22F.QEs1 29 = CFSG.KD.Fi22F.E1 := Nat.eq_of_beq_eq_true CFSG.KD.Fi22F.eE1
  have e2 : wLen (CFSG.KC.Fi22K.subY 8) = 29 := Nat.eq_of_beq_eq_true (by quickRfl)
  rw [e1] at a4
  change Acts HB rep CFSG.KD.Fi22F.LV CFSG.KD.Fi22F.E1 (bval tg (wWord (CFSG.KC.Fi22K.subY 8)) (wLen (CFSG.KC.Fi22K.subY 8)))
  rw [e2]
  exact a4

theorem fixE2 {rep : ℕ → PG} (hL : ∀ c < 4, Acts HB rep CFSG.KD.Fi22F.LV (Lsel c) (letV tg c)) :
    Acts HB rep CFSG.KD.Fi22F.LV CFSG.KD.Fi22F.E2 (ev 2) := by
  have hS : HO.entOK (CFSG.KC.Fi22K.subY 9) (nat_lit 4) (nat_lit 1023) = true := by quickRfl
  have hb : ∀ k, Acts HB rep CFSG.KD.Fi22F.LV (hBase (CFSG.KC.Fi22K.subY 9) 0 k) (letV tg (wLet (wWord (CFSG.KC.Fi22K.subY 9)) k)) :=
    fun k => hL _ (letters_all hS (by norm_num) k)
  have a0 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QEs2 0) (bval tg (wWord (CFSG.KC.Fi22K.subY 9)) 0) := acts_id CFSG.KD.Fi22F.eI2
  have a1 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QEs2 8) (bval tg (wWord (CFSG.KC.Fi22K.subY 9)) 8) :=
    chain_acts (pre := fun k => bval tg (wWord (CFSG.KC.Fi22K.subY 9)) k) CFSG.KD.Fi22F.e2s0 (fun k _ _ => hb k)
      (fun k _ _ => bval_snoc tg _ k) a0
  have a2 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QEs2 16) (bval tg (wWord (CFSG.KC.Fi22K.subY 9)) 16) :=
    chain_acts (pre := fun k => bval tg (wWord (CFSG.KC.Fi22K.subY 9)) k) CFSG.KD.Fi22F.e2s1 (fun k _ _ => hb k)
      (fun k _ _ => bval_snoc tg _ k) a1
  have a3 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QEs2 24) (bval tg (wWord (CFSG.KC.Fi22K.subY 9)) 24) :=
    chain_acts (pre := fun k => bval tg (wWord (CFSG.KC.Fi22K.subY 9)) k) CFSG.KD.Fi22F.e2s2 (fun k _ _ => hb k)
      (fun k _ _ => bval_snoc tg _ k) a2
  have a4 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QEs2 27) (bval tg (wWord (CFSG.KC.Fi22K.subY 9)) 27) :=
    chain_acts (pre := fun k => bval tg (wWord (CFSG.KC.Fi22K.subY 9)) k) CFSG.KD.Fi22F.e2s3 (fun k _ _ => hb k)
      (fun k _ _ => bval_snoc tg _ k) a3
  have e1 : CFSG.KD.Fi22F.QEs2 27 = CFSG.KD.Fi22F.E2 := Nat.eq_of_beq_eq_true CFSG.KD.Fi22F.eE2
  have e2 : wLen (CFSG.KC.Fi22K.subY 9) = 27 := Nat.eq_of_beq_eq_true (by quickRfl)
  rw [e1] at a4
  change Acts HB rep CFSG.KD.Fi22F.LV CFSG.KD.Fi22F.E2 (bval tg (wWord (CFSG.KC.Fi22K.subY 9)) (wLen (CFSG.KC.Fi22K.subY 9)))
  rw [e2]
  exact a4

theorem fixE3 {rep : ℕ → PG} (hL : ∀ c < 4, Acts HB rep CFSG.KD.Fi22F.LV (Lsel c) (letV tg c)) :
    Acts HB rep CFSG.KD.Fi22F.LV CFSG.KD.Fi22F.E3 (ev 3) := by
  have hS : HO.entOK (CFSG.KC.Fi22K.subY 10) (nat_lit 4) (nat_lit 1023) = true := by quickRfl
  have hb : ∀ k, Acts HB rep CFSG.KD.Fi22F.LV (hBase (CFSG.KC.Fi22K.subY 10) 0 k) (letV tg (wLet (wWord (CFSG.KC.Fi22K.subY 10)) k)) :=
    fun k => hL _ (letters_all hS (by norm_num) k)
  have a0 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QEs3 0) (bval tg (wWord (CFSG.KC.Fi22K.subY 10)) 0) := acts_id CFSG.KD.Fi22F.eI3
  have a1 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QEs3 8) (bval tg (wWord (CFSG.KC.Fi22K.subY 10)) 8) :=
    chain_acts (pre := fun k => bval tg (wWord (CFSG.KC.Fi22K.subY 10)) k) CFSG.KD.Fi22F.e3s0 (fun k _ _ => hb k)
      (fun k _ _ => bval_snoc tg _ k) a0
  have a2 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QEs3 16) (bval tg (wWord (CFSG.KC.Fi22K.subY 10)) 16) :=
    chain_acts (pre := fun k => bval tg (wWord (CFSG.KC.Fi22K.subY 10)) k) CFSG.KD.Fi22F.e3s1 (fun k _ _ => hb k)
      (fun k _ _ => bval_snoc tg _ k) a1
  have a3 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QEs3 24) (bval tg (wWord (CFSG.KC.Fi22K.subY 10)) 24) :=
    chain_acts (pre := fun k => bval tg (wWord (CFSG.KC.Fi22K.subY 10)) k) CFSG.KD.Fi22F.e3s2 (fun k _ _ => hb k)
      (fun k _ _ => bval_snoc tg _ k) a2
  have a4 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QEs3 25) (bval tg (wWord (CFSG.KC.Fi22K.subY 10)) 25) :=
    chain_acts (pre := fun k => bval tg (wWord (CFSG.KC.Fi22K.subY 10)) k) CFSG.KD.Fi22F.e3s3 (fun k _ _ => hb k)
      (fun k _ _ => bval_snoc tg _ k) a3
  have e1 : CFSG.KD.Fi22F.QEs3 25 = CFSG.KD.Fi22F.E3 := Nat.eq_of_beq_eq_true CFSG.KD.Fi22F.eE3
  have e2 : wLen (CFSG.KC.Fi22K.subY 10) = 25 := Nat.eq_of_beq_eq_true (by quickRfl)
  rw [e1] at a4
  change Acts HB rep CFSG.KD.Fi22F.LV CFSG.KD.Fi22F.E3 (bval tg (wWord (CFSG.KC.Fi22K.subY 10)) (wLen (CFSG.KC.Fi22K.subY 10)))
  rw [e2]
  exact a4

theorem fixE4 {rep : ℕ → PG} (hL : ∀ c < 4, Acts HB rep CFSG.KD.Fi22F.LV (Lsel c) (letV tg c)) :
    Acts HB rep CFSG.KD.Fi22F.LV CFSG.KD.Fi22F.E4 (ev 4) := by
  have hS : HO.entOK (CFSG.KC.Fi22K.subY 11) (nat_lit 4) (nat_lit 1023) = true := by quickRfl
  have hb : ∀ k, Acts HB rep CFSG.KD.Fi22F.LV (hBase (CFSG.KC.Fi22K.subY 11) 0 k) (letV tg (wLet (wWord (CFSG.KC.Fi22K.subY 11)) k)) :=
    fun k => hL _ (letters_all hS (by norm_num) k)
  have a0 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QEs4 0) (bval tg (wWord (CFSG.KC.Fi22K.subY 11)) 0) := acts_id CFSG.KD.Fi22F.eI4
  have a1 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QEs4 8) (bval tg (wWord (CFSG.KC.Fi22K.subY 11)) 8) :=
    chain_acts (pre := fun k => bval tg (wWord (CFSG.KC.Fi22K.subY 11)) k) CFSG.KD.Fi22F.e4s0 (fun k _ _ => hb k)
      (fun k _ _ => bval_snoc tg _ k) a0
  have a2 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QEs4 16) (bval tg (wWord (CFSG.KC.Fi22K.subY 11)) 16) :=
    chain_acts (pre := fun k => bval tg (wWord (CFSG.KC.Fi22K.subY 11)) k) CFSG.KD.Fi22F.e4s1 (fun k _ _ => hb k)
      (fun k _ _ => bval_snoc tg _ k) a1
  have a3 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QEs4 24) (bval tg (wWord (CFSG.KC.Fi22K.subY 11)) 24) :=
    chain_acts (pre := fun k => bval tg (wWord (CFSG.KC.Fi22K.subY 11)) k) CFSG.KD.Fi22F.e4s2 (fun k _ _ => hb k)
      (fun k _ _ => bval_snoc tg _ k) a2
  have a4 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QEs4 25) (bval tg (wWord (CFSG.KC.Fi22K.subY 11)) 25) :=
    chain_acts (pre := fun k => bval tg (wWord (CFSG.KC.Fi22K.subY 11)) k) CFSG.KD.Fi22F.e4s3 (fun k _ _ => hb k)
      (fun k _ _ => bval_snoc tg _ k) a3
  have e1 : CFSG.KD.Fi22F.QEs4 25 = CFSG.KD.Fi22F.E4 := Nat.eq_of_beq_eq_true CFSG.KD.Fi22F.eE4
  have e2 : wLen (CFSG.KC.Fi22K.subY 11) = 25 := Nat.eq_of_beq_eq_true (by quickRfl)
  rw [e1] at a4
  change Acts HB rep CFSG.KD.Fi22F.LV CFSG.KD.Fi22F.E4 (bval tg (wWord (CFSG.KC.Fi22K.subY 11)) (wLen (CFSG.KC.Fi22K.subY 11)))
  rw [e2]
  exact a4

theorem fixE5 {rep : ℕ → PG} (hL : ∀ c < 4, Acts HB rep CFSG.KD.Fi22F.LV (Lsel c) (letV tg c)) :
    Acts HB rep CFSG.KD.Fi22F.LV CFSG.KD.Fi22F.E5 (ev 5) := by
  have hS : HO.entOK (CFSG.KC.Fi22K.subY 12) (nat_lit 4) (nat_lit 1023) = true := by quickRfl
  have hb : ∀ k, Acts HB rep CFSG.KD.Fi22F.LV (hBase (CFSG.KC.Fi22K.subY 12) 0 k) (letV tg (wLet (wWord (CFSG.KC.Fi22K.subY 12)) k)) :=
    fun k => hL _ (letters_all hS (by norm_num) k)
  have a0 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QEs5 0) (bval tg (wWord (CFSG.KC.Fi22K.subY 12)) 0) := acts_id CFSG.KD.Fi22F.eI5
  have a1 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QEs5 8) (bval tg (wWord (CFSG.KC.Fi22K.subY 12)) 8) :=
    chain_acts (pre := fun k => bval tg (wWord (CFSG.KC.Fi22K.subY 12)) k) CFSG.KD.Fi22F.e5s0 (fun k _ _ => hb k)
      (fun k _ _ => bval_snoc tg _ k) a0
  have a2 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QEs5 16) (bval tg (wWord (CFSG.KC.Fi22K.subY 12)) 16) :=
    chain_acts (pre := fun k => bval tg (wWord (CFSG.KC.Fi22K.subY 12)) k) CFSG.KD.Fi22F.e5s1 (fun k _ _ => hb k)
      (fun k _ _ => bval_snoc tg _ k) a1
  have a3 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QEs5 24) (bval tg (wWord (CFSG.KC.Fi22K.subY 12)) 24) :=
    chain_acts (pre := fun k => bval tg (wWord (CFSG.KC.Fi22K.subY 12)) k) CFSG.KD.Fi22F.e5s2 (fun k _ _ => hb k)
      (fun k _ _ => bval_snoc tg _ k) a2
  have a4 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QEs5 29) (bval tg (wWord (CFSG.KC.Fi22K.subY 12)) 29) :=
    chain_acts (pre := fun k => bval tg (wWord (CFSG.KC.Fi22K.subY 12)) k) CFSG.KD.Fi22F.e5s3 (fun k _ _ => hb k)
      (fun k _ _ => bval_snoc tg _ k) a3
  have e1 : CFSG.KD.Fi22F.QEs5 29 = CFSG.KD.Fi22F.E5 := Nat.eq_of_beq_eq_true CFSG.KD.Fi22F.eE5
  have e2 : wLen (CFSG.KC.Fi22K.subY 12) = 29 := Nat.eq_of_beq_eq_true (by quickRfl)
  rw [e1] at a4
  change Acts HB rep CFSG.KD.Fi22F.LV CFSG.KD.Fi22F.E5 (bval tg (wWord (CFSG.KC.Fi22K.subY 12)) (wLen (CFSG.KC.Fi22K.subY 12)))
  rw [e2]
  exact a4

theorem fixW0 {rep : ℕ → PG} (hL : ∀ c < 4, Acts HB rep CFSG.KD.Fi22F.LV (Lsel c) (letV tg c))
    (hE : ∀ g < 6, Acts HB rep CFSG.KD.Fi22F.LV (Esel g) (ev g)) :
    ∀ i < nP, rep (lv CFSG.KD.Fi22F.LV i) * (revE (CFSG.KD.Fi22KM.WJs 0) 431 431 * bval tg (wWord (CFSG.KC.Fi22B.sub 0)) 1) * (rep (lv CFSG.KD.Fi22F.LV i))⁻¹ ∈ HB := by
  have hS : HO.entOK (CFSG.KC.Fi22B.sub 0) (nat_lit 4) (nat_lit 1023) = true := by quickRfl
  have hWo : HO.entOK (CFSG.KD.Fi22KM.WJs 0) (nat_lit 12) (nat_lit 1023) = true := by quickRfl
  have hb : ∀ k, Acts HB rep CFSG.KD.Fi22F.LV (hBase (CFSG.KC.Fi22B.sub 0) 431 k) (letV tg (wLet (wWord (CFSG.KC.Fi22B.sub 0)) (k - 431))) :=
    fun k => hL _ (letters_all hS (by norm_num) _)
  have he : ∀ k, Acts HB rep CFSG.KD.Fi22F.LV (eBase (CFSG.KD.Fi22KM.WJs 0) 431 k) (ev (eIdx (CFSG.KD.Fi22KM.WJs 0) 431 k)) :=
    fun k => hE _ (eIdx_lt hWo 431 k)
  have a0 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs0 0) (preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0) 0) := by
    rw [preW_zero]
    exact acts_id CFSG.KD.Fi22F.wI0
  have a1 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs0 8) (preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0) 8) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0)) CFSG.KD.Fi22F.w0s0 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 8 ≤ 431))) a0
  have a2 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs0 16) (preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0) 16) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0)) CFSG.KD.Fi22F.w0s1 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 16 ≤ 431))) a1
  have a3 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs0 24) (preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0) 24) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0)) CFSG.KD.Fi22F.w0s2 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 24 ≤ 431))) a2
  have a4 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs0 32) (preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0) 32) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0)) CFSG.KD.Fi22F.w0s3 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 32 ≤ 431))) a3
  have a5 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs0 40) (preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0) 40) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0)) CFSG.KD.Fi22F.w0s4 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 40 ≤ 431))) a4
  have a6 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs0 48) (preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0) 48) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0)) CFSG.KD.Fi22F.w0s5 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 48 ≤ 431))) a5
  have a7 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs0 56) (preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0) 56) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0)) CFSG.KD.Fi22F.w0s6 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 56 ≤ 431))) a6
  have a8 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs0 64) (preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0) 64) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0)) CFSG.KD.Fi22F.w0s7 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 64 ≤ 431))) a7
  have a9 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs0 72) (preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0) 72) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0)) CFSG.KD.Fi22F.w0s8 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 72 ≤ 431))) a8
  have a10 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs0 80) (preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0) 80) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0)) CFSG.KD.Fi22F.w0s9 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 80 ≤ 431))) a9
  have a11 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs0 88) (preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0) 88) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0)) CFSG.KD.Fi22F.w0s10 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 88 ≤ 431))) a10
  have a12 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs0 96) (preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0) 96) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0)) CFSG.KD.Fi22F.w0s11 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 96 ≤ 431))) a11
  have a13 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs0 104) (preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0) 104) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0)) CFSG.KD.Fi22F.w0s12 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 104 ≤ 431))) a12
  have a14 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs0 112) (preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0) 112) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0)) CFSG.KD.Fi22F.w0s13 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 112 ≤ 431))) a13
  have a15 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs0 120) (preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0) 120) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0)) CFSG.KD.Fi22F.w0s14 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 120 ≤ 431))) a14
  have a16 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs0 128) (preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0) 128) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0)) CFSG.KD.Fi22F.w0s15 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 128 ≤ 431))) a15
  have a17 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs0 136) (preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0) 136) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0)) CFSG.KD.Fi22F.w0s16 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 136 ≤ 431))) a16
  have a18 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs0 144) (preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0) 144) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0)) CFSG.KD.Fi22F.w0s17 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 144 ≤ 431))) a17
  have a19 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs0 152) (preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0) 152) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0)) CFSG.KD.Fi22F.w0s18 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 152 ≤ 431))) a18
  have a20 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs0 160) (preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0) 160) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0)) CFSG.KD.Fi22F.w0s19 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 160 ≤ 431))) a19
  have a21 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs0 168) (preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0) 168) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0)) CFSG.KD.Fi22F.w0s20 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 168 ≤ 431))) a20
  have a22 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs0 176) (preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0) 176) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0)) CFSG.KD.Fi22F.w0s21 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 176 ≤ 431))) a21
  have a23 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs0 184) (preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0) 184) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0)) CFSG.KD.Fi22F.w0s22 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 184 ≤ 431))) a22
  have a24 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs0 192) (preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0) 192) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0)) CFSG.KD.Fi22F.w0s23 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 192 ≤ 431))) a23
  have a25 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs0 200) (preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0) 200) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0)) CFSG.KD.Fi22F.w0s24 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 200 ≤ 431))) a24
  have a26 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs0 208) (preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0) 208) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0)) CFSG.KD.Fi22F.w0s25 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 208 ≤ 431))) a25
  have a27 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs0 216) (preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0) 216) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0)) CFSG.KD.Fi22F.w0s26 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 216 ≤ 431))) a26
  have a28 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs0 224) (preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0) 224) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0)) CFSG.KD.Fi22F.w0s27 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 224 ≤ 431))) a27
  have a29 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs0 232) (preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0) 232) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0)) CFSG.KD.Fi22F.w0s28 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 232 ≤ 431))) a28
  have a30 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs0 240) (preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0) 240) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0)) CFSG.KD.Fi22F.w0s29 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 240 ≤ 431))) a29
  have a31 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs0 248) (preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0) 248) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0)) CFSG.KD.Fi22F.w0s30 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 248 ≤ 431))) a30
  have a32 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs0 256) (preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0) 256) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0)) CFSG.KD.Fi22F.w0s31 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 256 ≤ 431))) a31
  have a33 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs0 264) (preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0) 264) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0)) CFSG.KD.Fi22F.w0s32 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 264 ≤ 431))) a32
  have a34 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs0 272) (preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0) 272) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0)) CFSG.KD.Fi22F.w0s33 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 272 ≤ 431))) a33
  have a35 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs0 280) (preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0) 280) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0)) CFSG.KD.Fi22F.w0s34 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 280 ≤ 431))) a34
  have a36 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs0 288) (preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0) 288) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0)) CFSG.KD.Fi22F.w0s35 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 288 ≤ 431))) a35
  have a37 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs0 296) (preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0) 296) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0)) CFSG.KD.Fi22F.w0s36 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 296 ≤ 431))) a36
  have a38 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs0 304) (preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0) 304) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0)) CFSG.KD.Fi22F.w0s37 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 304 ≤ 431))) a37
  have a39 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs0 312) (preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0) 312) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0)) CFSG.KD.Fi22F.w0s38 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 312 ≤ 431))) a38
  have a40 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs0 320) (preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0) 320) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0)) CFSG.KD.Fi22F.w0s39 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 320 ≤ 431))) a39
  have a41 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs0 328) (preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0) 328) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0)) CFSG.KD.Fi22F.w0s40 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 328 ≤ 431))) a40
  have a42 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs0 336) (preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0) 336) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0)) CFSG.KD.Fi22F.w0s41 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 336 ≤ 431))) a41
  have a43 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs0 344) (preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0) 344) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0)) CFSG.KD.Fi22F.w0s42 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 344 ≤ 431))) a42
  have a44 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs0 352) (preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0) 352) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0)) CFSG.KD.Fi22F.w0s43 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 352 ≤ 431))) a43
  have a45 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs0 360) (preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0) 360) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0)) CFSG.KD.Fi22F.w0s44 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 360 ≤ 431))) a44
  have a46 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs0 368) (preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0) 368) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0)) CFSG.KD.Fi22F.w0s45 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 368 ≤ 431))) a45
  have a47 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs0 376) (preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0) 376) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0)) CFSG.KD.Fi22F.w0s46 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 376 ≤ 431))) a46
  have a48 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs0 384) (preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0) 384) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0)) CFSG.KD.Fi22F.w0s47 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 384 ≤ 431))) a47
  have a49 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs0 392) (preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0) 392) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0)) CFSG.KD.Fi22F.w0s48 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 392 ≤ 431))) a48
  have a50 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs0 400) (preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0) 400) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0)) CFSG.KD.Fi22F.w0s49 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 400 ≤ 431))) a49
  have a51 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs0 408) (preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0) 408) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0)) CFSG.KD.Fi22F.w0s50 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 408 ≤ 431))) a50
  have a52 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs0 416) (preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0) 416) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0)) CFSG.KD.Fi22F.w0s51 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 416 ≤ 431))) a51
  have a53 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs0 424) (preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0) 424) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0)) CFSG.KD.Fi22F.w0s52 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 424 ≤ 431))) a52
  have a54 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs0 431) (preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0) 431) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0)) CFSG.KD.Fi22F.w0s53 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 431 ≤ 431))) a53
  have a55 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs0 432) (preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0) 432) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 0) 431 (CFSG.KC.Fi22B.sub 0)) CFSG.KD.Fi22F.h0s0 (fun k _ _ => hb k)
      (fun k hk _ => preW_h (Nat.le_trans (by decide : 431 ≤ 431) hk)) a54
  have hid : idOK (CFSG.KD.Fi22F.QWs0 432) = true := CFSG.KD.Fi22F.wF0
  rw [preW_end (by decide : 0 < 1)] at a55
  intro i hi
  have e := Nat.eq_of_beq_eq_true (every hid i hi)
  have := (a55 i hi).2
  rwa [e] at this

theorem fixW1 {rep : ℕ → PG} (hL : ∀ c < 4, Acts HB rep CFSG.KD.Fi22F.LV (Lsel c) (letV tg c))
    (hE : ∀ g < 6, Acts HB rep CFSG.KD.Fi22F.LV (Esel g) (ev g)) :
    ∀ i < nP, rep (lv CFSG.KD.Fi22F.LV i) * (revE (CFSG.KD.Fi22KM.WJs 1) 102 102 * bval tg (wWord (CFSG.KC.Fi22B.sub 1)) 9) * (rep (lv CFSG.KD.Fi22F.LV i))⁻¹ ∈ HB := by
  have hS : HO.entOK (CFSG.KC.Fi22B.sub 1) (nat_lit 4) (nat_lit 1023) = true := by quickRfl
  have hWo : HO.entOK (CFSG.KD.Fi22KM.WJs 1) (nat_lit 12) (nat_lit 1023) = true := by quickRfl
  have hb : ∀ k, Acts HB rep CFSG.KD.Fi22F.LV (hBase (CFSG.KC.Fi22B.sub 1) 102 k) (letV tg (wLet (wWord (CFSG.KC.Fi22B.sub 1)) (k - 102))) :=
    fun k => hL _ (letters_all hS (by norm_num) _)
  have he : ∀ k, Acts HB rep CFSG.KD.Fi22F.LV (eBase (CFSG.KD.Fi22KM.WJs 1) 102 k) (ev (eIdx (CFSG.KD.Fi22KM.WJs 1) 102 k)) :=
    fun k => hE _ (eIdx_lt hWo 102 k)
  have a0 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs1 0) (preW (CFSG.KD.Fi22KM.WJs 1) 102 (CFSG.KC.Fi22B.sub 1) 0) := by
    rw [preW_zero]
    exact acts_id CFSG.KD.Fi22F.wI1
  have a1 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs1 8) (preW (CFSG.KD.Fi22KM.WJs 1) 102 (CFSG.KC.Fi22B.sub 1) 8) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 1) 102 (CFSG.KC.Fi22B.sub 1)) CFSG.KD.Fi22F.w1s0 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 8 ≤ 102))) a0
  have a2 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs1 16) (preW (CFSG.KD.Fi22KM.WJs 1) 102 (CFSG.KC.Fi22B.sub 1) 16) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 1) 102 (CFSG.KC.Fi22B.sub 1)) CFSG.KD.Fi22F.w1s1 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 16 ≤ 102))) a1
  have a3 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs1 24) (preW (CFSG.KD.Fi22KM.WJs 1) 102 (CFSG.KC.Fi22B.sub 1) 24) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 1) 102 (CFSG.KC.Fi22B.sub 1)) CFSG.KD.Fi22F.w1s2 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 24 ≤ 102))) a2
  have a4 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs1 32) (preW (CFSG.KD.Fi22KM.WJs 1) 102 (CFSG.KC.Fi22B.sub 1) 32) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 1) 102 (CFSG.KC.Fi22B.sub 1)) CFSG.KD.Fi22F.w1s3 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 32 ≤ 102))) a3
  have a5 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs1 40) (preW (CFSG.KD.Fi22KM.WJs 1) 102 (CFSG.KC.Fi22B.sub 1) 40) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 1) 102 (CFSG.KC.Fi22B.sub 1)) CFSG.KD.Fi22F.w1s4 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 40 ≤ 102))) a4
  have a6 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs1 48) (preW (CFSG.KD.Fi22KM.WJs 1) 102 (CFSG.KC.Fi22B.sub 1) 48) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 1) 102 (CFSG.KC.Fi22B.sub 1)) CFSG.KD.Fi22F.w1s5 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 48 ≤ 102))) a5
  have a7 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs1 56) (preW (CFSG.KD.Fi22KM.WJs 1) 102 (CFSG.KC.Fi22B.sub 1) 56) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 1) 102 (CFSG.KC.Fi22B.sub 1)) CFSG.KD.Fi22F.w1s6 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 56 ≤ 102))) a6
  have a8 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs1 64) (preW (CFSG.KD.Fi22KM.WJs 1) 102 (CFSG.KC.Fi22B.sub 1) 64) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 1) 102 (CFSG.KC.Fi22B.sub 1)) CFSG.KD.Fi22F.w1s7 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 64 ≤ 102))) a7
  have a9 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs1 72) (preW (CFSG.KD.Fi22KM.WJs 1) 102 (CFSG.KC.Fi22B.sub 1) 72) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 1) 102 (CFSG.KC.Fi22B.sub 1)) CFSG.KD.Fi22F.w1s8 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 72 ≤ 102))) a8
  have a10 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs1 80) (preW (CFSG.KD.Fi22KM.WJs 1) 102 (CFSG.KC.Fi22B.sub 1) 80) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 1) 102 (CFSG.KC.Fi22B.sub 1)) CFSG.KD.Fi22F.w1s9 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 80 ≤ 102))) a9
  have a11 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs1 88) (preW (CFSG.KD.Fi22KM.WJs 1) 102 (CFSG.KC.Fi22B.sub 1) 88) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 1) 102 (CFSG.KC.Fi22B.sub 1)) CFSG.KD.Fi22F.w1s10 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 88 ≤ 102))) a10
  have a12 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs1 96) (preW (CFSG.KD.Fi22KM.WJs 1) 102 (CFSG.KC.Fi22B.sub 1) 96) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 1) 102 (CFSG.KC.Fi22B.sub 1)) CFSG.KD.Fi22F.w1s11 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 96 ≤ 102))) a11
  have a13 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs1 102) (preW (CFSG.KD.Fi22KM.WJs 1) 102 (CFSG.KC.Fi22B.sub 1) 102) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 1) 102 (CFSG.KC.Fi22B.sub 1)) CFSG.KD.Fi22F.w1s12 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 102 ≤ 102))) a12
  have a14 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs1 110) (preW (CFSG.KD.Fi22KM.WJs 1) 102 (CFSG.KC.Fi22B.sub 1) 110) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 1) 102 (CFSG.KC.Fi22B.sub 1)) CFSG.KD.Fi22F.h1s0 (fun k _ _ => hb k)
      (fun k hk _ => preW_h (Nat.le_trans (by decide : 102 ≤ 102) hk)) a13
  have a15 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs1 111) (preW (CFSG.KD.Fi22KM.WJs 1) 102 (CFSG.KC.Fi22B.sub 1) 111) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 1) 102 (CFSG.KC.Fi22B.sub 1)) CFSG.KD.Fi22F.h1s1 (fun k _ _ => hb k)
      (fun k hk _ => preW_h (Nat.le_trans (by decide : 102 ≤ 110) hk)) a14
  have hid : idOK (CFSG.KD.Fi22F.QWs1 111) = true := CFSG.KD.Fi22F.wF1
  rw [preW_end (by decide : 0 < 9)] at a15
  intro i hi
  have e := Nat.eq_of_beq_eq_true (every hid i hi)
  have := (a15 i hi).2
  rwa [e] at this

theorem fixW2 {rep : ℕ → PG} (hL : ∀ c < 4, Acts HB rep CFSG.KD.Fi22F.LV (Lsel c) (letV tg c))
    (hE : ∀ g < 6, Acts HB rep CFSG.KD.Fi22F.LV (Esel g) (ev g)) :
    ∀ i < nP, rep (lv CFSG.KD.Fi22F.LV i) * (revE (CFSG.KD.Fi22KM.WJs 2) 220 220 * bval tg (wWord (CFSG.KC.Fi22B.sub 2)) 9) * (rep (lv CFSG.KD.Fi22F.LV i))⁻¹ ∈ HB := by
  have hS : HO.entOK (CFSG.KC.Fi22B.sub 2) (nat_lit 4) (nat_lit 1023) = true := by quickRfl
  have hWo : HO.entOK (CFSG.KD.Fi22KM.WJs 2) (nat_lit 12) (nat_lit 1023) = true := by quickRfl
  have hb : ∀ k, Acts HB rep CFSG.KD.Fi22F.LV (hBase (CFSG.KC.Fi22B.sub 2) 220 k) (letV tg (wLet (wWord (CFSG.KC.Fi22B.sub 2)) (k - 220))) :=
    fun k => hL _ (letters_all hS (by norm_num) _)
  have he : ∀ k, Acts HB rep CFSG.KD.Fi22F.LV (eBase (CFSG.KD.Fi22KM.WJs 2) 220 k) (ev (eIdx (CFSG.KD.Fi22KM.WJs 2) 220 k)) :=
    fun k => hE _ (eIdx_lt hWo 220 k)
  have a0 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs2 0) (preW (CFSG.KD.Fi22KM.WJs 2) 220 (CFSG.KC.Fi22B.sub 2) 0) := by
    rw [preW_zero]
    exact acts_id CFSG.KD.Fi22F.wI2
  have a1 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs2 8) (preW (CFSG.KD.Fi22KM.WJs 2) 220 (CFSG.KC.Fi22B.sub 2) 8) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 2) 220 (CFSG.KC.Fi22B.sub 2)) CFSG.KD.Fi22F.w2s0 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 8 ≤ 220))) a0
  have a2 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs2 16) (preW (CFSG.KD.Fi22KM.WJs 2) 220 (CFSG.KC.Fi22B.sub 2) 16) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 2) 220 (CFSG.KC.Fi22B.sub 2)) CFSG.KD.Fi22F.w2s1 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 16 ≤ 220))) a1
  have a3 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs2 24) (preW (CFSG.KD.Fi22KM.WJs 2) 220 (CFSG.KC.Fi22B.sub 2) 24) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 2) 220 (CFSG.KC.Fi22B.sub 2)) CFSG.KD.Fi22F.w2s2 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 24 ≤ 220))) a2
  have a4 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs2 32) (preW (CFSG.KD.Fi22KM.WJs 2) 220 (CFSG.KC.Fi22B.sub 2) 32) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 2) 220 (CFSG.KC.Fi22B.sub 2)) CFSG.KD.Fi22F.w2s3 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 32 ≤ 220))) a3
  have a5 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs2 40) (preW (CFSG.KD.Fi22KM.WJs 2) 220 (CFSG.KC.Fi22B.sub 2) 40) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 2) 220 (CFSG.KC.Fi22B.sub 2)) CFSG.KD.Fi22F.w2s4 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 40 ≤ 220))) a4
  have a6 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs2 48) (preW (CFSG.KD.Fi22KM.WJs 2) 220 (CFSG.KC.Fi22B.sub 2) 48) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 2) 220 (CFSG.KC.Fi22B.sub 2)) CFSG.KD.Fi22F.w2s5 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 48 ≤ 220))) a5
  have a7 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs2 56) (preW (CFSG.KD.Fi22KM.WJs 2) 220 (CFSG.KC.Fi22B.sub 2) 56) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 2) 220 (CFSG.KC.Fi22B.sub 2)) CFSG.KD.Fi22F.w2s6 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 56 ≤ 220))) a6
  have a8 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs2 64) (preW (CFSG.KD.Fi22KM.WJs 2) 220 (CFSG.KC.Fi22B.sub 2) 64) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 2) 220 (CFSG.KC.Fi22B.sub 2)) CFSG.KD.Fi22F.w2s7 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 64 ≤ 220))) a7
  have a9 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs2 72) (preW (CFSG.KD.Fi22KM.WJs 2) 220 (CFSG.KC.Fi22B.sub 2) 72) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 2) 220 (CFSG.KC.Fi22B.sub 2)) CFSG.KD.Fi22F.w2s8 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 72 ≤ 220))) a8
  have a10 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs2 80) (preW (CFSG.KD.Fi22KM.WJs 2) 220 (CFSG.KC.Fi22B.sub 2) 80) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 2) 220 (CFSG.KC.Fi22B.sub 2)) CFSG.KD.Fi22F.w2s9 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 80 ≤ 220))) a9
  have a11 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs2 88) (preW (CFSG.KD.Fi22KM.WJs 2) 220 (CFSG.KC.Fi22B.sub 2) 88) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 2) 220 (CFSG.KC.Fi22B.sub 2)) CFSG.KD.Fi22F.w2s10 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 88 ≤ 220))) a10
  have a12 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs2 96) (preW (CFSG.KD.Fi22KM.WJs 2) 220 (CFSG.KC.Fi22B.sub 2) 96) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 2) 220 (CFSG.KC.Fi22B.sub 2)) CFSG.KD.Fi22F.w2s11 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 96 ≤ 220))) a11
  have a13 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs2 104) (preW (CFSG.KD.Fi22KM.WJs 2) 220 (CFSG.KC.Fi22B.sub 2) 104) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 2) 220 (CFSG.KC.Fi22B.sub 2)) CFSG.KD.Fi22F.w2s12 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 104 ≤ 220))) a12
  have a14 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs2 112) (preW (CFSG.KD.Fi22KM.WJs 2) 220 (CFSG.KC.Fi22B.sub 2) 112) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 2) 220 (CFSG.KC.Fi22B.sub 2)) CFSG.KD.Fi22F.w2s13 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 112 ≤ 220))) a13
  have a15 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs2 120) (preW (CFSG.KD.Fi22KM.WJs 2) 220 (CFSG.KC.Fi22B.sub 2) 120) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 2) 220 (CFSG.KC.Fi22B.sub 2)) CFSG.KD.Fi22F.w2s14 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 120 ≤ 220))) a14
  have a16 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs2 128) (preW (CFSG.KD.Fi22KM.WJs 2) 220 (CFSG.KC.Fi22B.sub 2) 128) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 2) 220 (CFSG.KC.Fi22B.sub 2)) CFSG.KD.Fi22F.w2s15 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 128 ≤ 220))) a15
  have a17 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs2 136) (preW (CFSG.KD.Fi22KM.WJs 2) 220 (CFSG.KC.Fi22B.sub 2) 136) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 2) 220 (CFSG.KC.Fi22B.sub 2)) CFSG.KD.Fi22F.w2s16 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 136 ≤ 220))) a16
  have a18 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs2 144) (preW (CFSG.KD.Fi22KM.WJs 2) 220 (CFSG.KC.Fi22B.sub 2) 144) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 2) 220 (CFSG.KC.Fi22B.sub 2)) CFSG.KD.Fi22F.w2s17 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 144 ≤ 220))) a17
  have a19 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs2 152) (preW (CFSG.KD.Fi22KM.WJs 2) 220 (CFSG.KC.Fi22B.sub 2) 152) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 2) 220 (CFSG.KC.Fi22B.sub 2)) CFSG.KD.Fi22F.w2s18 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 152 ≤ 220))) a18
  have a20 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs2 160) (preW (CFSG.KD.Fi22KM.WJs 2) 220 (CFSG.KC.Fi22B.sub 2) 160) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 2) 220 (CFSG.KC.Fi22B.sub 2)) CFSG.KD.Fi22F.w2s19 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 160 ≤ 220))) a19
  have a21 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs2 168) (preW (CFSG.KD.Fi22KM.WJs 2) 220 (CFSG.KC.Fi22B.sub 2) 168) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 2) 220 (CFSG.KC.Fi22B.sub 2)) CFSG.KD.Fi22F.w2s20 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 168 ≤ 220))) a20
  have a22 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs2 176) (preW (CFSG.KD.Fi22KM.WJs 2) 220 (CFSG.KC.Fi22B.sub 2) 176) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 2) 220 (CFSG.KC.Fi22B.sub 2)) CFSG.KD.Fi22F.w2s21 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 176 ≤ 220))) a21
  have a23 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs2 184) (preW (CFSG.KD.Fi22KM.WJs 2) 220 (CFSG.KC.Fi22B.sub 2) 184) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 2) 220 (CFSG.KC.Fi22B.sub 2)) CFSG.KD.Fi22F.w2s22 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 184 ≤ 220))) a22
  have a24 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs2 192) (preW (CFSG.KD.Fi22KM.WJs 2) 220 (CFSG.KC.Fi22B.sub 2) 192) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 2) 220 (CFSG.KC.Fi22B.sub 2)) CFSG.KD.Fi22F.w2s23 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 192 ≤ 220))) a23
  have a25 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs2 200) (preW (CFSG.KD.Fi22KM.WJs 2) 220 (CFSG.KC.Fi22B.sub 2) 200) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 2) 220 (CFSG.KC.Fi22B.sub 2)) CFSG.KD.Fi22F.w2s24 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 200 ≤ 220))) a24
  have a26 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs2 208) (preW (CFSG.KD.Fi22KM.WJs 2) 220 (CFSG.KC.Fi22B.sub 2) 208) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 2) 220 (CFSG.KC.Fi22B.sub 2)) CFSG.KD.Fi22F.w2s25 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 208 ≤ 220))) a25
  have a27 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs2 216) (preW (CFSG.KD.Fi22KM.WJs 2) 220 (CFSG.KC.Fi22B.sub 2) 216) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 2) 220 (CFSG.KC.Fi22B.sub 2)) CFSG.KD.Fi22F.w2s26 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 216 ≤ 220))) a26
  have a28 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs2 220) (preW (CFSG.KD.Fi22KM.WJs 2) 220 (CFSG.KC.Fi22B.sub 2) 220) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 2) 220 (CFSG.KC.Fi22B.sub 2)) CFSG.KD.Fi22F.w2s27 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 220 ≤ 220))) a27
  have a29 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs2 228) (preW (CFSG.KD.Fi22KM.WJs 2) 220 (CFSG.KC.Fi22B.sub 2) 228) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 2) 220 (CFSG.KC.Fi22B.sub 2)) CFSG.KD.Fi22F.h2s0 (fun k _ _ => hb k)
      (fun k hk _ => preW_h (Nat.le_trans (by decide : 220 ≤ 220) hk)) a28
  have a30 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs2 229) (preW (CFSG.KD.Fi22KM.WJs 2) 220 (CFSG.KC.Fi22B.sub 2) 229) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 2) 220 (CFSG.KC.Fi22B.sub 2)) CFSG.KD.Fi22F.h2s1 (fun k _ _ => hb k)
      (fun k hk _ => preW_h (Nat.le_trans (by decide : 220 ≤ 228) hk)) a29
  have hid : idOK (CFSG.KD.Fi22F.QWs2 229) = true := CFSG.KD.Fi22F.wF2
  rw [preW_end (by decide : 0 < 9)] at a30
  intro i hi
  have e := Nat.eq_of_beq_eq_true (every hid i hi)
  have := (a30 i hi).2
  rwa [e] at this

theorem fixW3 {rep : ℕ → PG} (hL : ∀ c < 4, Acts HB rep CFSG.KD.Fi22F.LV (Lsel c) (letV tg c))
    (hE : ∀ g < 6, Acts HB rep CFSG.KD.Fi22F.LV (Esel g) (ev g)) :
    ∀ i < nP, rep (lv CFSG.KD.Fi22F.LV i) * (revE (CFSG.KD.Fi22KM.WJs 3) 130 130 * bval tg (wWord (CFSG.KC.Fi22B.sub 3)) 5) * (rep (lv CFSG.KD.Fi22F.LV i))⁻¹ ∈ HB := by
  have hS : HO.entOK (CFSG.KC.Fi22B.sub 3) (nat_lit 4) (nat_lit 1023) = true := by quickRfl
  have hWo : HO.entOK (CFSG.KD.Fi22KM.WJs 3) (nat_lit 12) (nat_lit 1023) = true := by quickRfl
  have hb : ∀ k, Acts HB rep CFSG.KD.Fi22F.LV (hBase (CFSG.KC.Fi22B.sub 3) 130 k) (letV tg (wLet (wWord (CFSG.KC.Fi22B.sub 3)) (k - 130))) :=
    fun k => hL _ (letters_all hS (by norm_num) _)
  have he : ∀ k, Acts HB rep CFSG.KD.Fi22F.LV (eBase (CFSG.KD.Fi22KM.WJs 3) 130 k) (ev (eIdx (CFSG.KD.Fi22KM.WJs 3) 130 k)) :=
    fun k => hE _ (eIdx_lt hWo 130 k)
  have a0 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs3 0) (preW (CFSG.KD.Fi22KM.WJs 3) 130 (CFSG.KC.Fi22B.sub 3) 0) := by
    rw [preW_zero]
    exact acts_id CFSG.KD.Fi22F.wI3
  have a1 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs3 8) (preW (CFSG.KD.Fi22KM.WJs 3) 130 (CFSG.KC.Fi22B.sub 3) 8) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 3) 130 (CFSG.KC.Fi22B.sub 3)) CFSG.KD.Fi22F.w3s0 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 8 ≤ 130))) a0
  have a2 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs3 16) (preW (CFSG.KD.Fi22KM.WJs 3) 130 (CFSG.KC.Fi22B.sub 3) 16) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 3) 130 (CFSG.KC.Fi22B.sub 3)) CFSG.KD.Fi22F.w3s1 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 16 ≤ 130))) a1
  have a3 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs3 24) (preW (CFSG.KD.Fi22KM.WJs 3) 130 (CFSG.KC.Fi22B.sub 3) 24) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 3) 130 (CFSG.KC.Fi22B.sub 3)) CFSG.KD.Fi22F.w3s2 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 24 ≤ 130))) a2
  have a4 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs3 32) (preW (CFSG.KD.Fi22KM.WJs 3) 130 (CFSG.KC.Fi22B.sub 3) 32) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 3) 130 (CFSG.KC.Fi22B.sub 3)) CFSG.KD.Fi22F.w3s3 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 32 ≤ 130))) a3
  have a5 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs3 40) (preW (CFSG.KD.Fi22KM.WJs 3) 130 (CFSG.KC.Fi22B.sub 3) 40) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 3) 130 (CFSG.KC.Fi22B.sub 3)) CFSG.KD.Fi22F.w3s4 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 40 ≤ 130))) a4
  have a6 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs3 48) (preW (CFSG.KD.Fi22KM.WJs 3) 130 (CFSG.KC.Fi22B.sub 3) 48) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 3) 130 (CFSG.KC.Fi22B.sub 3)) CFSG.KD.Fi22F.w3s5 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 48 ≤ 130))) a5
  have a7 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs3 56) (preW (CFSG.KD.Fi22KM.WJs 3) 130 (CFSG.KC.Fi22B.sub 3) 56) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 3) 130 (CFSG.KC.Fi22B.sub 3)) CFSG.KD.Fi22F.w3s6 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 56 ≤ 130))) a6
  have a8 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs3 64) (preW (CFSG.KD.Fi22KM.WJs 3) 130 (CFSG.KC.Fi22B.sub 3) 64) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 3) 130 (CFSG.KC.Fi22B.sub 3)) CFSG.KD.Fi22F.w3s7 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 64 ≤ 130))) a7
  have a9 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs3 72) (preW (CFSG.KD.Fi22KM.WJs 3) 130 (CFSG.KC.Fi22B.sub 3) 72) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 3) 130 (CFSG.KC.Fi22B.sub 3)) CFSG.KD.Fi22F.w3s8 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 72 ≤ 130))) a8
  have a10 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs3 80) (preW (CFSG.KD.Fi22KM.WJs 3) 130 (CFSG.KC.Fi22B.sub 3) 80) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 3) 130 (CFSG.KC.Fi22B.sub 3)) CFSG.KD.Fi22F.w3s9 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 80 ≤ 130))) a9
  have a11 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs3 88) (preW (CFSG.KD.Fi22KM.WJs 3) 130 (CFSG.KC.Fi22B.sub 3) 88) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 3) 130 (CFSG.KC.Fi22B.sub 3)) CFSG.KD.Fi22F.w3s10 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 88 ≤ 130))) a10
  have a12 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs3 96) (preW (CFSG.KD.Fi22KM.WJs 3) 130 (CFSG.KC.Fi22B.sub 3) 96) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 3) 130 (CFSG.KC.Fi22B.sub 3)) CFSG.KD.Fi22F.w3s11 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 96 ≤ 130))) a11
  have a13 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs3 104) (preW (CFSG.KD.Fi22KM.WJs 3) 130 (CFSG.KC.Fi22B.sub 3) 104) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 3) 130 (CFSG.KC.Fi22B.sub 3)) CFSG.KD.Fi22F.w3s12 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 104 ≤ 130))) a12
  have a14 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs3 112) (preW (CFSG.KD.Fi22KM.WJs 3) 130 (CFSG.KC.Fi22B.sub 3) 112) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 3) 130 (CFSG.KC.Fi22B.sub 3)) CFSG.KD.Fi22F.w3s13 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 112 ≤ 130))) a13
  have a15 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs3 120) (preW (CFSG.KD.Fi22KM.WJs 3) 130 (CFSG.KC.Fi22B.sub 3) 120) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 3) 130 (CFSG.KC.Fi22B.sub 3)) CFSG.KD.Fi22F.w3s14 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 120 ≤ 130))) a14
  have a16 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs3 128) (preW (CFSG.KD.Fi22KM.WJs 3) 130 (CFSG.KC.Fi22B.sub 3) 128) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 3) 130 (CFSG.KC.Fi22B.sub 3)) CFSG.KD.Fi22F.w3s15 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 128 ≤ 130))) a15
  have a17 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs3 130) (preW (CFSG.KD.Fi22KM.WJs 3) 130 (CFSG.KC.Fi22B.sub 3) 130) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 3) 130 (CFSG.KC.Fi22B.sub 3)) CFSG.KD.Fi22F.w3s16 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 130 ≤ 130))) a16
  have a18 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs3 135) (preW (CFSG.KD.Fi22KM.WJs 3) 130 (CFSG.KC.Fi22B.sub 3) 135) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 3) 130 (CFSG.KC.Fi22B.sub 3)) CFSG.KD.Fi22F.h3s0 (fun k _ _ => hb k)
      (fun k hk _ => preW_h (Nat.le_trans (by decide : 130 ≤ 130) hk)) a17
  have hid : idOK (CFSG.KD.Fi22F.QWs3 135) = true := CFSG.KD.Fi22F.wF3
  rw [preW_end (by decide : 0 < 5)] at a18
  intro i hi
  have e := Nat.eq_of_beq_eq_true (every hid i hi)
  have := (a18 i hi).2
  rwa [e] at this

theorem fixW4 {rep : ℕ → PG} (hL : ∀ c < 4, Acts HB rep CFSG.KD.Fi22F.LV (Lsel c) (letV tg c))
    (hE : ∀ g < 6, Acts HB rep CFSG.KD.Fi22F.LV (Esel g) (ev g)) :
    ∀ i < nP, rep (lv CFSG.KD.Fi22F.LV i) * (revE (CFSG.KD.Fi22KM.WJs 4) 244 244 * bval tg (wWord (CFSG.KC.Fi22B.sub 4)) 8) * (rep (lv CFSG.KD.Fi22F.LV i))⁻¹ ∈ HB := by
  have hS : HO.entOK (CFSG.KC.Fi22B.sub 4) (nat_lit 4) (nat_lit 1023) = true := by quickRfl
  have hWo : HO.entOK (CFSG.KD.Fi22KM.WJs 4) (nat_lit 12) (nat_lit 1023) = true := by quickRfl
  have hb : ∀ k, Acts HB rep CFSG.KD.Fi22F.LV (hBase (CFSG.KC.Fi22B.sub 4) 244 k) (letV tg (wLet (wWord (CFSG.KC.Fi22B.sub 4)) (k - 244))) :=
    fun k => hL _ (letters_all hS (by norm_num) _)
  have he : ∀ k, Acts HB rep CFSG.KD.Fi22F.LV (eBase (CFSG.KD.Fi22KM.WJs 4) 244 k) (ev (eIdx (CFSG.KD.Fi22KM.WJs 4) 244 k)) :=
    fun k => hE _ (eIdx_lt hWo 244 k)
  have a0 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs4 0) (preW (CFSG.KD.Fi22KM.WJs 4) 244 (CFSG.KC.Fi22B.sub 4) 0) := by
    rw [preW_zero]
    exact acts_id CFSG.KD.Fi22F.wI4
  have a1 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs4 8) (preW (CFSG.KD.Fi22KM.WJs 4) 244 (CFSG.KC.Fi22B.sub 4) 8) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 4) 244 (CFSG.KC.Fi22B.sub 4)) CFSG.KD.Fi22F.w4s0 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 8 ≤ 244))) a0
  have a2 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs4 16) (preW (CFSG.KD.Fi22KM.WJs 4) 244 (CFSG.KC.Fi22B.sub 4) 16) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 4) 244 (CFSG.KC.Fi22B.sub 4)) CFSG.KD.Fi22F.w4s1 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 16 ≤ 244))) a1
  have a3 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs4 24) (preW (CFSG.KD.Fi22KM.WJs 4) 244 (CFSG.KC.Fi22B.sub 4) 24) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 4) 244 (CFSG.KC.Fi22B.sub 4)) CFSG.KD.Fi22F.w4s2 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 24 ≤ 244))) a2
  have a4 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs4 32) (preW (CFSG.KD.Fi22KM.WJs 4) 244 (CFSG.KC.Fi22B.sub 4) 32) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 4) 244 (CFSG.KC.Fi22B.sub 4)) CFSG.KD.Fi22F.w4s3 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 32 ≤ 244))) a3
  have a5 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs4 40) (preW (CFSG.KD.Fi22KM.WJs 4) 244 (CFSG.KC.Fi22B.sub 4) 40) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 4) 244 (CFSG.KC.Fi22B.sub 4)) CFSG.KD.Fi22F.w4s4 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 40 ≤ 244))) a4
  have a6 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs4 48) (preW (CFSG.KD.Fi22KM.WJs 4) 244 (CFSG.KC.Fi22B.sub 4) 48) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 4) 244 (CFSG.KC.Fi22B.sub 4)) CFSG.KD.Fi22F.w4s5 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 48 ≤ 244))) a5
  have a7 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs4 56) (preW (CFSG.KD.Fi22KM.WJs 4) 244 (CFSG.KC.Fi22B.sub 4) 56) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 4) 244 (CFSG.KC.Fi22B.sub 4)) CFSG.KD.Fi22F.w4s6 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 56 ≤ 244))) a6
  have a8 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs4 64) (preW (CFSG.KD.Fi22KM.WJs 4) 244 (CFSG.KC.Fi22B.sub 4) 64) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 4) 244 (CFSG.KC.Fi22B.sub 4)) CFSG.KD.Fi22F.w4s7 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 64 ≤ 244))) a7
  have a9 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs4 72) (preW (CFSG.KD.Fi22KM.WJs 4) 244 (CFSG.KC.Fi22B.sub 4) 72) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 4) 244 (CFSG.KC.Fi22B.sub 4)) CFSG.KD.Fi22F.w4s8 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 72 ≤ 244))) a8
  have a10 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs4 80) (preW (CFSG.KD.Fi22KM.WJs 4) 244 (CFSG.KC.Fi22B.sub 4) 80) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 4) 244 (CFSG.KC.Fi22B.sub 4)) CFSG.KD.Fi22F.w4s9 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 80 ≤ 244))) a9
  have a11 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs4 88) (preW (CFSG.KD.Fi22KM.WJs 4) 244 (CFSG.KC.Fi22B.sub 4) 88) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 4) 244 (CFSG.KC.Fi22B.sub 4)) CFSG.KD.Fi22F.w4s10 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 88 ≤ 244))) a10
  have a12 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs4 96) (preW (CFSG.KD.Fi22KM.WJs 4) 244 (CFSG.KC.Fi22B.sub 4) 96) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 4) 244 (CFSG.KC.Fi22B.sub 4)) CFSG.KD.Fi22F.w4s11 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 96 ≤ 244))) a11
  have a13 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs4 104) (preW (CFSG.KD.Fi22KM.WJs 4) 244 (CFSG.KC.Fi22B.sub 4) 104) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 4) 244 (CFSG.KC.Fi22B.sub 4)) CFSG.KD.Fi22F.w4s12 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 104 ≤ 244))) a12
  have a14 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs4 112) (preW (CFSG.KD.Fi22KM.WJs 4) 244 (CFSG.KC.Fi22B.sub 4) 112) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 4) 244 (CFSG.KC.Fi22B.sub 4)) CFSG.KD.Fi22F.w4s13 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 112 ≤ 244))) a13
  have a15 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs4 120) (preW (CFSG.KD.Fi22KM.WJs 4) 244 (CFSG.KC.Fi22B.sub 4) 120) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 4) 244 (CFSG.KC.Fi22B.sub 4)) CFSG.KD.Fi22F.w4s14 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 120 ≤ 244))) a14
  have a16 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs4 128) (preW (CFSG.KD.Fi22KM.WJs 4) 244 (CFSG.KC.Fi22B.sub 4) 128) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 4) 244 (CFSG.KC.Fi22B.sub 4)) CFSG.KD.Fi22F.w4s15 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 128 ≤ 244))) a15
  have a17 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs4 136) (preW (CFSG.KD.Fi22KM.WJs 4) 244 (CFSG.KC.Fi22B.sub 4) 136) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 4) 244 (CFSG.KC.Fi22B.sub 4)) CFSG.KD.Fi22F.w4s16 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 136 ≤ 244))) a16
  have a18 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs4 144) (preW (CFSG.KD.Fi22KM.WJs 4) 244 (CFSG.KC.Fi22B.sub 4) 144) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 4) 244 (CFSG.KC.Fi22B.sub 4)) CFSG.KD.Fi22F.w4s17 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 144 ≤ 244))) a17
  have a19 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs4 152) (preW (CFSG.KD.Fi22KM.WJs 4) 244 (CFSG.KC.Fi22B.sub 4) 152) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 4) 244 (CFSG.KC.Fi22B.sub 4)) CFSG.KD.Fi22F.w4s18 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 152 ≤ 244))) a18
  have a20 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs4 160) (preW (CFSG.KD.Fi22KM.WJs 4) 244 (CFSG.KC.Fi22B.sub 4) 160) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 4) 244 (CFSG.KC.Fi22B.sub 4)) CFSG.KD.Fi22F.w4s19 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 160 ≤ 244))) a19
  have a21 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs4 168) (preW (CFSG.KD.Fi22KM.WJs 4) 244 (CFSG.KC.Fi22B.sub 4) 168) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 4) 244 (CFSG.KC.Fi22B.sub 4)) CFSG.KD.Fi22F.w4s20 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 168 ≤ 244))) a20
  have a22 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs4 176) (preW (CFSG.KD.Fi22KM.WJs 4) 244 (CFSG.KC.Fi22B.sub 4) 176) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 4) 244 (CFSG.KC.Fi22B.sub 4)) CFSG.KD.Fi22F.w4s21 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 176 ≤ 244))) a21
  have a23 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs4 184) (preW (CFSG.KD.Fi22KM.WJs 4) 244 (CFSG.KC.Fi22B.sub 4) 184) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 4) 244 (CFSG.KC.Fi22B.sub 4)) CFSG.KD.Fi22F.w4s22 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 184 ≤ 244))) a22
  have a24 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs4 192) (preW (CFSG.KD.Fi22KM.WJs 4) 244 (CFSG.KC.Fi22B.sub 4) 192) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 4) 244 (CFSG.KC.Fi22B.sub 4)) CFSG.KD.Fi22F.w4s23 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 192 ≤ 244))) a23
  have a25 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs4 200) (preW (CFSG.KD.Fi22KM.WJs 4) 244 (CFSG.KC.Fi22B.sub 4) 200) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 4) 244 (CFSG.KC.Fi22B.sub 4)) CFSG.KD.Fi22F.w4s24 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 200 ≤ 244))) a24
  have a26 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs4 208) (preW (CFSG.KD.Fi22KM.WJs 4) 244 (CFSG.KC.Fi22B.sub 4) 208) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 4) 244 (CFSG.KC.Fi22B.sub 4)) CFSG.KD.Fi22F.w4s25 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 208 ≤ 244))) a25
  have a27 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs4 216) (preW (CFSG.KD.Fi22KM.WJs 4) 244 (CFSG.KC.Fi22B.sub 4) 216) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 4) 244 (CFSG.KC.Fi22B.sub 4)) CFSG.KD.Fi22F.w4s26 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 216 ≤ 244))) a26
  have a28 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs4 224) (preW (CFSG.KD.Fi22KM.WJs 4) 244 (CFSG.KC.Fi22B.sub 4) 224) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 4) 244 (CFSG.KC.Fi22B.sub 4)) CFSG.KD.Fi22F.w4s27 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 224 ≤ 244))) a27
  have a29 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs4 232) (preW (CFSG.KD.Fi22KM.WJs 4) 244 (CFSG.KC.Fi22B.sub 4) 232) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 4) 244 (CFSG.KC.Fi22B.sub 4)) CFSG.KD.Fi22F.w4s28 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 232 ≤ 244))) a28
  have a30 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs4 240) (preW (CFSG.KD.Fi22KM.WJs 4) 244 (CFSG.KC.Fi22B.sub 4) 240) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 4) 244 (CFSG.KC.Fi22B.sub 4)) CFSG.KD.Fi22F.w4s29 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 240 ≤ 244))) a29
  have a31 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs4 244) (preW (CFSG.KD.Fi22KM.WJs 4) 244 (CFSG.KC.Fi22B.sub 4) 244) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 4) 244 (CFSG.KC.Fi22B.sub 4)) CFSG.KD.Fi22F.w4s30 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 244 ≤ 244))) a30
  have a32 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs4 252) (preW (CFSG.KD.Fi22KM.WJs 4) 244 (CFSG.KC.Fi22B.sub 4) 252) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 4) 244 (CFSG.KC.Fi22B.sub 4)) CFSG.KD.Fi22F.h4s0 (fun k _ _ => hb k)
      (fun k hk _ => preW_h (Nat.le_trans (by decide : 244 ≤ 244) hk)) a31
  have hid : idOK (CFSG.KD.Fi22F.QWs4 252) = true := CFSG.KD.Fi22F.wF4
  rw [preW_end (by decide : 0 < 8)] at a32
  intro i hi
  have e := Nat.eq_of_beq_eq_true (every hid i hi)
  have := (a32 i hi).2
  rwa [e] at this

theorem fixW5 {rep : ℕ → PG} (hL : ∀ c < 4, Acts HB rep CFSG.KD.Fi22F.LV (Lsel c) (letV tg c))
    (hE : ∀ g < 6, Acts HB rep CFSG.KD.Fi22F.LV (Esel g) (ev g)) :
    ∀ i < nP, rep (lv CFSG.KD.Fi22F.LV i) * (revE (CFSG.KD.Fi22KM.WJs 5) 216 216 * bval tg (wWord (CFSG.KC.Fi22B.sub 5)) 11) * (rep (lv CFSG.KD.Fi22F.LV i))⁻¹ ∈ HB := by
  have hS : HO.entOK (CFSG.KC.Fi22B.sub 5) (nat_lit 4) (nat_lit 1023) = true := by quickRfl
  have hWo : HO.entOK (CFSG.KD.Fi22KM.WJs 5) (nat_lit 12) (nat_lit 1023) = true := by quickRfl
  have hb : ∀ k, Acts HB rep CFSG.KD.Fi22F.LV (hBase (CFSG.KC.Fi22B.sub 5) 216 k) (letV tg (wLet (wWord (CFSG.KC.Fi22B.sub 5)) (k - 216))) :=
    fun k => hL _ (letters_all hS (by norm_num) _)
  have he : ∀ k, Acts HB rep CFSG.KD.Fi22F.LV (eBase (CFSG.KD.Fi22KM.WJs 5) 216 k) (ev (eIdx (CFSG.KD.Fi22KM.WJs 5) 216 k)) :=
    fun k => hE _ (eIdx_lt hWo 216 k)
  have a0 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs5 0) (preW (CFSG.KD.Fi22KM.WJs 5) 216 (CFSG.KC.Fi22B.sub 5) 0) := by
    rw [preW_zero]
    exact acts_id CFSG.KD.Fi22F.wI5
  have a1 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs5 8) (preW (CFSG.KD.Fi22KM.WJs 5) 216 (CFSG.KC.Fi22B.sub 5) 8) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 5) 216 (CFSG.KC.Fi22B.sub 5)) CFSG.KD.Fi22F.w5s0 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 8 ≤ 216))) a0
  have a2 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs5 16) (preW (CFSG.KD.Fi22KM.WJs 5) 216 (CFSG.KC.Fi22B.sub 5) 16) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 5) 216 (CFSG.KC.Fi22B.sub 5)) CFSG.KD.Fi22F.w5s1 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 16 ≤ 216))) a1
  have a3 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs5 24) (preW (CFSG.KD.Fi22KM.WJs 5) 216 (CFSG.KC.Fi22B.sub 5) 24) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 5) 216 (CFSG.KC.Fi22B.sub 5)) CFSG.KD.Fi22F.w5s2 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 24 ≤ 216))) a2
  have a4 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs5 32) (preW (CFSG.KD.Fi22KM.WJs 5) 216 (CFSG.KC.Fi22B.sub 5) 32) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 5) 216 (CFSG.KC.Fi22B.sub 5)) CFSG.KD.Fi22F.w5s3 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 32 ≤ 216))) a3
  have a5 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs5 40) (preW (CFSG.KD.Fi22KM.WJs 5) 216 (CFSG.KC.Fi22B.sub 5) 40) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 5) 216 (CFSG.KC.Fi22B.sub 5)) CFSG.KD.Fi22F.w5s4 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 40 ≤ 216))) a4
  have a6 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs5 48) (preW (CFSG.KD.Fi22KM.WJs 5) 216 (CFSG.KC.Fi22B.sub 5) 48) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 5) 216 (CFSG.KC.Fi22B.sub 5)) CFSG.KD.Fi22F.w5s5 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 48 ≤ 216))) a5
  have a7 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs5 56) (preW (CFSG.KD.Fi22KM.WJs 5) 216 (CFSG.KC.Fi22B.sub 5) 56) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 5) 216 (CFSG.KC.Fi22B.sub 5)) CFSG.KD.Fi22F.w5s6 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 56 ≤ 216))) a6
  have a8 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs5 64) (preW (CFSG.KD.Fi22KM.WJs 5) 216 (CFSG.KC.Fi22B.sub 5) 64) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 5) 216 (CFSG.KC.Fi22B.sub 5)) CFSG.KD.Fi22F.w5s7 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 64 ≤ 216))) a7
  have a9 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs5 72) (preW (CFSG.KD.Fi22KM.WJs 5) 216 (CFSG.KC.Fi22B.sub 5) 72) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 5) 216 (CFSG.KC.Fi22B.sub 5)) CFSG.KD.Fi22F.w5s8 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 72 ≤ 216))) a8
  have a10 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs5 80) (preW (CFSG.KD.Fi22KM.WJs 5) 216 (CFSG.KC.Fi22B.sub 5) 80) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 5) 216 (CFSG.KC.Fi22B.sub 5)) CFSG.KD.Fi22F.w5s9 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 80 ≤ 216))) a9
  have a11 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs5 88) (preW (CFSG.KD.Fi22KM.WJs 5) 216 (CFSG.KC.Fi22B.sub 5) 88) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 5) 216 (CFSG.KC.Fi22B.sub 5)) CFSG.KD.Fi22F.w5s10 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 88 ≤ 216))) a10
  have a12 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs5 96) (preW (CFSG.KD.Fi22KM.WJs 5) 216 (CFSG.KC.Fi22B.sub 5) 96) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 5) 216 (CFSG.KC.Fi22B.sub 5)) CFSG.KD.Fi22F.w5s11 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 96 ≤ 216))) a11
  have a13 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs5 104) (preW (CFSG.KD.Fi22KM.WJs 5) 216 (CFSG.KC.Fi22B.sub 5) 104) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 5) 216 (CFSG.KC.Fi22B.sub 5)) CFSG.KD.Fi22F.w5s12 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 104 ≤ 216))) a12
  have a14 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs5 112) (preW (CFSG.KD.Fi22KM.WJs 5) 216 (CFSG.KC.Fi22B.sub 5) 112) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 5) 216 (CFSG.KC.Fi22B.sub 5)) CFSG.KD.Fi22F.w5s13 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 112 ≤ 216))) a13
  have a15 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs5 120) (preW (CFSG.KD.Fi22KM.WJs 5) 216 (CFSG.KC.Fi22B.sub 5) 120) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 5) 216 (CFSG.KC.Fi22B.sub 5)) CFSG.KD.Fi22F.w5s14 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 120 ≤ 216))) a14
  have a16 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs5 128) (preW (CFSG.KD.Fi22KM.WJs 5) 216 (CFSG.KC.Fi22B.sub 5) 128) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 5) 216 (CFSG.KC.Fi22B.sub 5)) CFSG.KD.Fi22F.w5s15 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 128 ≤ 216))) a15
  have a17 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs5 136) (preW (CFSG.KD.Fi22KM.WJs 5) 216 (CFSG.KC.Fi22B.sub 5) 136) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 5) 216 (CFSG.KC.Fi22B.sub 5)) CFSG.KD.Fi22F.w5s16 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 136 ≤ 216))) a16
  have a18 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs5 144) (preW (CFSG.KD.Fi22KM.WJs 5) 216 (CFSG.KC.Fi22B.sub 5) 144) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 5) 216 (CFSG.KC.Fi22B.sub 5)) CFSG.KD.Fi22F.w5s17 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 144 ≤ 216))) a17
  have a19 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs5 152) (preW (CFSG.KD.Fi22KM.WJs 5) 216 (CFSG.KC.Fi22B.sub 5) 152) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 5) 216 (CFSG.KC.Fi22B.sub 5)) CFSG.KD.Fi22F.w5s18 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 152 ≤ 216))) a18
  have a20 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs5 160) (preW (CFSG.KD.Fi22KM.WJs 5) 216 (CFSG.KC.Fi22B.sub 5) 160) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 5) 216 (CFSG.KC.Fi22B.sub 5)) CFSG.KD.Fi22F.w5s19 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 160 ≤ 216))) a19
  have a21 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs5 168) (preW (CFSG.KD.Fi22KM.WJs 5) 216 (CFSG.KC.Fi22B.sub 5) 168) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 5) 216 (CFSG.KC.Fi22B.sub 5)) CFSG.KD.Fi22F.w5s20 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 168 ≤ 216))) a20
  have a22 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs5 176) (preW (CFSG.KD.Fi22KM.WJs 5) 216 (CFSG.KC.Fi22B.sub 5) 176) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 5) 216 (CFSG.KC.Fi22B.sub 5)) CFSG.KD.Fi22F.w5s21 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 176 ≤ 216))) a21
  have a23 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs5 184) (preW (CFSG.KD.Fi22KM.WJs 5) 216 (CFSG.KC.Fi22B.sub 5) 184) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 5) 216 (CFSG.KC.Fi22B.sub 5)) CFSG.KD.Fi22F.w5s22 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 184 ≤ 216))) a22
  have a24 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs5 192) (preW (CFSG.KD.Fi22KM.WJs 5) 216 (CFSG.KC.Fi22B.sub 5) 192) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 5) 216 (CFSG.KC.Fi22B.sub 5)) CFSG.KD.Fi22F.w5s23 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 192 ≤ 216))) a23
  have a25 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs5 200) (preW (CFSG.KD.Fi22KM.WJs 5) 216 (CFSG.KC.Fi22B.sub 5) 200) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 5) 216 (CFSG.KC.Fi22B.sub 5)) CFSG.KD.Fi22F.w5s24 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 200 ≤ 216))) a24
  have a26 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs5 208) (preW (CFSG.KD.Fi22KM.WJs 5) 216 (CFSG.KC.Fi22B.sub 5) 208) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 5) 216 (CFSG.KC.Fi22B.sub 5)) CFSG.KD.Fi22F.w5s25 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 208 ≤ 216))) a25
  have a27 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs5 216) (preW (CFSG.KD.Fi22KM.WJs 5) 216 (CFSG.KC.Fi22B.sub 5) 216) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 5) 216 (CFSG.KC.Fi22B.sub 5)) CFSG.KD.Fi22F.w5s26 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 216 ≤ 216))) a26
  have a28 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs5 224) (preW (CFSG.KD.Fi22KM.WJs 5) 216 (CFSG.KC.Fi22B.sub 5) 224) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 5) 216 (CFSG.KC.Fi22B.sub 5)) CFSG.KD.Fi22F.h5s0 (fun k _ _ => hb k)
      (fun k hk _ => preW_h (Nat.le_trans (by decide : 216 ≤ 216) hk)) a27
  have a29 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs5 227) (preW (CFSG.KD.Fi22KM.WJs 5) 216 (CFSG.KC.Fi22B.sub 5) 227) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 5) 216 (CFSG.KC.Fi22B.sub 5)) CFSG.KD.Fi22F.h5s1 (fun k _ _ => hb k)
      (fun k hk _ => preW_h (Nat.le_trans (by decide : 216 ≤ 224) hk)) a28
  have hid : idOK (CFSG.KD.Fi22F.QWs5 227) = true := CFSG.KD.Fi22F.wF5
  rw [preW_end (by decide : 0 < 11)] at a29
  intro i hi
  have e := Nat.eq_of_beq_eq_true (every hid i hi)
  have := (a29 i hi).2
  rwa [e] at this

theorem fixW6 {rep : ℕ → PG} (hL : ∀ c < 4, Acts HB rep CFSG.KD.Fi22F.LV (Lsel c) (letV tg c))
    (hE : ∀ g < 6, Acts HB rep CFSG.KD.Fi22F.LV (Esel g) (ev g)) :
    ∀ i < nP, rep (lv CFSG.KD.Fi22F.LV i) * (revE (CFSG.KD.Fi22KM.WJs 6) 173 173 * bval tg (wWord (CFSG.KC.Fi22B.sub 6)) 17) * (rep (lv CFSG.KD.Fi22F.LV i))⁻¹ ∈ HB := by
  have hS : HO.entOK (CFSG.KC.Fi22B.sub 6) (nat_lit 4) (nat_lit 1023) = true := by quickRfl
  have hWo : HO.entOK (CFSG.KD.Fi22KM.WJs 6) (nat_lit 12) (nat_lit 1023) = true := by quickRfl
  have hb : ∀ k, Acts HB rep CFSG.KD.Fi22F.LV (hBase (CFSG.KC.Fi22B.sub 6) 173 k) (letV tg (wLet (wWord (CFSG.KC.Fi22B.sub 6)) (k - 173))) :=
    fun k => hL _ (letters_all hS (by norm_num) _)
  have he : ∀ k, Acts HB rep CFSG.KD.Fi22F.LV (eBase (CFSG.KD.Fi22KM.WJs 6) 173 k) (ev (eIdx (CFSG.KD.Fi22KM.WJs 6) 173 k)) :=
    fun k => hE _ (eIdx_lt hWo 173 k)
  have a0 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs6 0) (preW (CFSG.KD.Fi22KM.WJs 6) 173 (CFSG.KC.Fi22B.sub 6) 0) := by
    rw [preW_zero]
    exact acts_id CFSG.KD.Fi22F.wI6
  have a1 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs6 8) (preW (CFSG.KD.Fi22KM.WJs 6) 173 (CFSG.KC.Fi22B.sub 6) 8) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 6) 173 (CFSG.KC.Fi22B.sub 6)) CFSG.KD.Fi22F.w6s0 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 8 ≤ 173))) a0
  have a2 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs6 16) (preW (CFSG.KD.Fi22KM.WJs 6) 173 (CFSG.KC.Fi22B.sub 6) 16) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 6) 173 (CFSG.KC.Fi22B.sub 6)) CFSG.KD.Fi22F.w6s1 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 16 ≤ 173))) a1
  have a3 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs6 24) (preW (CFSG.KD.Fi22KM.WJs 6) 173 (CFSG.KC.Fi22B.sub 6) 24) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 6) 173 (CFSG.KC.Fi22B.sub 6)) CFSG.KD.Fi22F.w6s2 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 24 ≤ 173))) a2
  have a4 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs6 32) (preW (CFSG.KD.Fi22KM.WJs 6) 173 (CFSG.KC.Fi22B.sub 6) 32) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 6) 173 (CFSG.KC.Fi22B.sub 6)) CFSG.KD.Fi22F.w6s3 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 32 ≤ 173))) a3
  have a5 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs6 40) (preW (CFSG.KD.Fi22KM.WJs 6) 173 (CFSG.KC.Fi22B.sub 6) 40) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 6) 173 (CFSG.KC.Fi22B.sub 6)) CFSG.KD.Fi22F.w6s4 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 40 ≤ 173))) a4
  have a6 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs6 48) (preW (CFSG.KD.Fi22KM.WJs 6) 173 (CFSG.KC.Fi22B.sub 6) 48) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 6) 173 (CFSG.KC.Fi22B.sub 6)) CFSG.KD.Fi22F.w6s5 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 48 ≤ 173))) a5
  have a7 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs6 56) (preW (CFSG.KD.Fi22KM.WJs 6) 173 (CFSG.KC.Fi22B.sub 6) 56) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 6) 173 (CFSG.KC.Fi22B.sub 6)) CFSG.KD.Fi22F.w6s6 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 56 ≤ 173))) a6
  have a8 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs6 64) (preW (CFSG.KD.Fi22KM.WJs 6) 173 (CFSG.KC.Fi22B.sub 6) 64) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 6) 173 (CFSG.KC.Fi22B.sub 6)) CFSG.KD.Fi22F.w6s7 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 64 ≤ 173))) a7
  have a9 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs6 72) (preW (CFSG.KD.Fi22KM.WJs 6) 173 (CFSG.KC.Fi22B.sub 6) 72) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 6) 173 (CFSG.KC.Fi22B.sub 6)) CFSG.KD.Fi22F.w6s8 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 72 ≤ 173))) a8
  have a10 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs6 80) (preW (CFSG.KD.Fi22KM.WJs 6) 173 (CFSG.KC.Fi22B.sub 6) 80) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 6) 173 (CFSG.KC.Fi22B.sub 6)) CFSG.KD.Fi22F.w6s9 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 80 ≤ 173))) a9
  have a11 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs6 88) (preW (CFSG.KD.Fi22KM.WJs 6) 173 (CFSG.KC.Fi22B.sub 6) 88) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 6) 173 (CFSG.KC.Fi22B.sub 6)) CFSG.KD.Fi22F.w6s10 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 88 ≤ 173))) a10
  have a12 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs6 96) (preW (CFSG.KD.Fi22KM.WJs 6) 173 (CFSG.KC.Fi22B.sub 6) 96) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 6) 173 (CFSG.KC.Fi22B.sub 6)) CFSG.KD.Fi22F.w6s11 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 96 ≤ 173))) a11
  have a13 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs6 104) (preW (CFSG.KD.Fi22KM.WJs 6) 173 (CFSG.KC.Fi22B.sub 6) 104) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 6) 173 (CFSG.KC.Fi22B.sub 6)) CFSG.KD.Fi22F.w6s12 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 104 ≤ 173))) a12
  have a14 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs6 112) (preW (CFSG.KD.Fi22KM.WJs 6) 173 (CFSG.KC.Fi22B.sub 6) 112) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 6) 173 (CFSG.KC.Fi22B.sub 6)) CFSG.KD.Fi22F.w6s13 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 112 ≤ 173))) a13
  have a15 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs6 120) (preW (CFSG.KD.Fi22KM.WJs 6) 173 (CFSG.KC.Fi22B.sub 6) 120) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 6) 173 (CFSG.KC.Fi22B.sub 6)) CFSG.KD.Fi22F.w6s14 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 120 ≤ 173))) a14
  have a16 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs6 128) (preW (CFSG.KD.Fi22KM.WJs 6) 173 (CFSG.KC.Fi22B.sub 6) 128) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 6) 173 (CFSG.KC.Fi22B.sub 6)) CFSG.KD.Fi22F.w6s15 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 128 ≤ 173))) a15
  have a17 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs6 136) (preW (CFSG.KD.Fi22KM.WJs 6) 173 (CFSG.KC.Fi22B.sub 6) 136) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 6) 173 (CFSG.KC.Fi22B.sub 6)) CFSG.KD.Fi22F.w6s16 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 136 ≤ 173))) a16
  have a18 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs6 144) (preW (CFSG.KD.Fi22KM.WJs 6) 173 (CFSG.KC.Fi22B.sub 6) 144) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 6) 173 (CFSG.KC.Fi22B.sub 6)) CFSG.KD.Fi22F.w6s17 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 144 ≤ 173))) a17
  have a19 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs6 152) (preW (CFSG.KD.Fi22KM.WJs 6) 173 (CFSG.KC.Fi22B.sub 6) 152) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 6) 173 (CFSG.KC.Fi22B.sub 6)) CFSG.KD.Fi22F.w6s18 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 152 ≤ 173))) a18
  have a20 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs6 160) (preW (CFSG.KD.Fi22KM.WJs 6) 173 (CFSG.KC.Fi22B.sub 6) 160) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 6) 173 (CFSG.KC.Fi22B.sub 6)) CFSG.KD.Fi22F.w6s19 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 160 ≤ 173))) a19
  have a21 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs6 168) (preW (CFSG.KD.Fi22KM.WJs 6) 173 (CFSG.KC.Fi22B.sub 6) 168) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 6) 173 (CFSG.KC.Fi22B.sub 6)) CFSG.KD.Fi22F.w6s20 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 168 ≤ 173))) a20
  have a22 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs6 173) (preW (CFSG.KD.Fi22KM.WJs 6) 173 (CFSG.KC.Fi22B.sub 6) 173) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 6) 173 (CFSG.KC.Fi22B.sub 6)) CFSG.KD.Fi22F.w6s21 (fun k _ _ => he k)
      (fun k _ hk => preW_e (Nat.lt_of_lt_of_le hk (by decide : 173 ≤ 173))) a21
  have a23 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs6 181) (preW (CFSG.KD.Fi22KM.WJs 6) 173 (CFSG.KC.Fi22B.sub 6) 181) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 6) 173 (CFSG.KC.Fi22B.sub 6)) CFSG.KD.Fi22F.h6s0 (fun k _ _ => hb k)
      (fun k hk _ => preW_h (Nat.le_trans (by decide : 173 ≤ 173) hk)) a22
  have a24 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs6 189) (preW (CFSG.KD.Fi22KM.WJs 6) 173 (CFSG.KC.Fi22B.sub 6) 189) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 6) 173 (CFSG.KC.Fi22B.sub 6)) CFSG.KD.Fi22F.h6s1 (fun k _ _ => hb k)
      (fun k hk _ => preW_h (Nat.le_trans (by decide : 173 ≤ 181) hk)) a23
  have a25 : Acts HB rep CFSG.KD.Fi22F.LV (CFSG.KD.Fi22F.QWs6 190) (preW (CFSG.KD.Fi22KM.WJs 6) 173 (CFSG.KC.Fi22B.sub 6) 190) :=
    chain_acts (pre := preW (CFSG.KD.Fi22KM.WJs 6) 173 (CFSG.KC.Fi22B.sub 6)) CFSG.KD.Fi22F.h6s2 (fun k _ _ => hb k)
      (fun k hk _ => preW_h (Nat.le_trans (by decide : 173 ≤ 189) hk)) a24
  have hid : idOK (CFSG.KD.Fi22F.QWs6 190) = true := CFSG.KD.Fi22F.wF6
  rw [preW_end (by decide : 0 < 17)] at a25
  intro i hi
  have e := Nat.eq_of_beq_eq_true (every hid i hi)
  have := (a25 i hi).2
  rwa [e] at this

theorem fix_center : ∀ j < 7, revE (CFSG.KD.Fi22KM.WJs j) (wLen (CFSG.KD.Fi22KM.WJs j)) (wLen (CFSG.KD.Fi22KM.WJs j)) *
    bval tg (wWord (CFSG.KC.Fi22B.sub j)) (wLen (CFSG.KC.Fi22B.sub j)) ∈ Subgroup.center PG := by
  obtain ⟨rep, hrep0, hwalk⟩ := bray_walk
  have h0 : rep (lv CFSG.KD.Fi22F.LV 0) = 1 := by rw [Nat.eq_of_beq_eq_true CFSG.KD.Fi22F.lv0, hrep0]
  have hL : ∀ c < 4, Acts HB rep CFSG.KD.Fi22F.LV (Lsel c) (letV tg c) := by
    intro c hc
    interval_cases c
    · exact acts_let tg hwalk (by norm_num) CFSG.KD.Fi22F.let0 CFSG.KD.Fi22F.rg0
    · exact acts_let tg hwalk (by norm_num) CFSG.KD.Fi22F.let1 CFSG.KD.Fi22F.rg1
    · exact acts_let tg hwalk (by norm_num) CFSG.KD.Fi22F.let2 CFSG.KD.Fi22F.rg2
    · exact acts_let tg hwalk (by norm_num) CFSG.KD.Fi22F.let3 CFSG.KD.Fi22F.rg3
  have hE : ∀ g < 6, Acts HB rep CFSG.KD.Fi22F.LV (Esel g) (ev g) := by
    intro g hg
    interval_cases g
    exacts [fixE0 hL, fixE1 hL, fixE2 hL, fixE3 hL, fixE4 hL, fixE5 hL]
  have hL' : ∀ c < 4, ∃ L, Acts HB rep CFSG.KD.Fi22F.LV L (letV tg c) := fun c hc => ⟨_, hL c hc⟩
  intro j hj
  apply center_of_fix h0 hL'
  interval_cases j
  · have hn : wLen (CFSG.KD.Fi22KM.WJs 0) = 431 := Nat.eq_of_beq_eq_true (by quickRfl)
    have hm : wLen (CFSG.KC.Fi22B.sub 0) = 1 := Nat.eq_of_beq_eq_true (by quickRfl)
    rw [hn, hm]
    exact fixW0 hL hE
  · have hn : wLen (CFSG.KD.Fi22KM.WJs 1) = 102 := Nat.eq_of_beq_eq_true (by quickRfl)
    have hm : wLen (CFSG.KC.Fi22B.sub 1) = 9 := Nat.eq_of_beq_eq_true (by quickRfl)
    rw [hn, hm]
    exact fixW1 hL hE
  · have hn : wLen (CFSG.KD.Fi22KM.WJs 2) = 220 := Nat.eq_of_beq_eq_true (by quickRfl)
    have hm : wLen (CFSG.KC.Fi22B.sub 2) = 9 := Nat.eq_of_beq_eq_true (by quickRfl)
    rw [hn, hm]
    exact fixW2 hL hE
  · have hn : wLen (CFSG.KD.Fi22KM.WJs 3) = 130 := Nat.eq_of_beq_eq_true (by quickRfl)
    have hm : wLen (CFSG.KC.Fi22B.sub 3) = 5 := Nat.eq_of_beq_eq_true (by quickRfl)
    rw [hn, hm]
    exact fixW3 hL hE
  · have hn : wLen (CFSG.KD.Fi22KM.WJs 4) = 244 := Nat.eq_of_beq_eq_true (by quickRfl)
    have hm : wLen (CFSG.KC.Fi22B.sub 4) = 8 := Nat.eq_of_beq_eq_true (by quickRfl)
    rw [hn, hm]
    exact fixW4 hL hE
  · have hn : wLen (CFSG.KD.Fi22KM.WJs 5) = 216 := Nat.eq_of_beq_eq_true (by quickRfl)
    have hm : wLen (CFSG.KC.Fi22B.sub 5) = 11 := Nat.eq_of_beq_eq_true (by quickRfl)
    rw [hn, hm]
    exact fixW5 hL hE
  · have hn : wLen (CFSG.KD.Fi22KM.WJs 6) = 173 := Nat.eq_of_beq_eq_true (by quickRfl)
    have hm : wLen (CFSG.KC.Fi22B.sub 6) = 17 := Nat.eq_of_beq_eq_true (by quickRfl)
    rw [hn, hm]
    exact fixW6 hL hE

end CertificateChecks.KernelFi22

end
