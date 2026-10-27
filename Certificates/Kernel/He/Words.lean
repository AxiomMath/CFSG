module

public import CFSG.Certificates.Kernel.LceSTabSound
public import CFSG.Certificates.Kernel.CosetBounds
public import CFSG.Certificates.Kernel.He.Bound.RelsTC
import all CFSG.Certificates.Kernel.CosetBounds

public section

namespace CertificateChecks.KernelHe

open CFSG.KC CFSG.KC.LceS CFSG.Certificates CFSG.Certificates.LCE TauCeti

theorem wLet_eq (W i : ℕ) : wLet W i = W / 2 ^ (8 * i) % 256 := by
  change W >>> (8 * i) &&& (2 ^ 8 - 1) = _
  rw [Nat.shiftRight_eq_div_pow, Nat.and_two_pow_sub_one_eq_mod]

theorem wLet_div (W i : ℕ) : wLet W (i + 1) = wLet (W / 256) i := by
  rw [wLet_eq, wLet_eq, Nat.mul_succ, Nat.pow_add, Nat.mul_comm (2 ^ (8 * i)),
    ← Nat.div_div_eq_div_mul]

theorem wLet_zero {c W : ℕ} (hc : c < 256) : wLet (c + 256 * W) 0 = c := by
  rw [wLet_eq]
  omega

theorem bval_succ {G : Type*} [Group G] (gen : ℕ → G) (W n : ℕ) :
    bval gen W (n + 1) = letV gen (wLet W 0) * bval gen (W / 256) n := by
  simp only [bval, List.range_succ_eq_map, List.map_cons, List.prod_cons, List.map_map]
  congr 2
  apply List.map_congr_left
  intro i _
  exact congrArg (letV gen) (wLet_div W i)

theorem bval_zero {G : Type*} [Group G] (gen : ℕ → G) (W : ℕ) : bval gen W 0 = 1 := rfl

theorem bval_const {G : Type*} [Group G] (gen : ℕ → G) (c : ℕ) :
    ∀ (n W : ℕ), (∀ i < n, wLet W i = c) → bval gen W n = letV gen c ^ n
  | 0, _, _ => by rw [bval_zero, pow_zero]
  | n + 1, W, h => by
    rw [bval_succ, h 0 (Nat.succ_pos n), bval_const gen c n (W / 256) (fun i hi => by
      rw [← wLet_div]
      exact h (i + 1) (by omega)), pow_succ']

theorem letV_code {G : Type*} [Group G] (gen : ℕ → G) (l : ℕ × Bool) (hl : l.1 < 127) :
    letV gen (HeB.code l) = if l.2 then gen l.1 else (gen l.1)⁻¹ := by
  obtain ⟨g, b⟩ := l
  have hg : g < 127 := hl
  unfold letV HeB.code
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> split_ifs with h1 h2 <;>
    first | omega | (congr 2; omega)

theorem code_lt (l : ℕ × Bool) (hl : l.1 < 127) : HeB.code l < 256 := by
  obtain ⟨g, b⟩ := l
  have hg : g < 127 := hl
  cases b <;> simp [HeB.code] <;> omega

theorem bval_wordNat {G : Type*} [Group G] (gen : ℕ → G) :
    ∀ w : List (ℕ × Bool), (∀ l ∈ w, l.1 < 127) →
      bval gen (HeB.wordNat w) w.length = KB.sword gen w
  | [], _ => by simp [bval, KB.sword]
  | l :: w, h => by
    have hl := h l (by simp)
    have hc := code_lt l hl
    have hdiv : (HeB.code l + 256 * HeB.wordNat w) / 256 = HeB.wordNat w := by omega
    rw [List.length_cons, bval_succ, HeB.wordNat, wLet_zero hc, hdiv,
      bval_wordNat gen w (fun l' hl' => h l' (by simp [hl'])), letV_code gen l hl]
    simp [KB.sword]

theorem wordNat_lt : ∀ w : List (ℕ × Bool), (∀ l ∈ w, l.1 < 127) →
    HeB.wordNat w < 2 ^ (8 * w.length)
  | [], _ => by simp [HeB.wordNat]
  | l :: w, h => by
    have hc := code_lt l (h l (by simp))
    have ih := wordNat_lt w (fun l' hl' => h l' (by simp [hl']))
    rw [HeB.wordNat, List.length_cons, Nat.mul_succ, Nat.pow_add]
    have e : (2 : ℕ) ^ 8 = 256 := rfl
    rw [e]
    generalize 2 ^ (8 * w.length) = X at ih ⊢
    omega

theorem wWord_ent (w : List (ℕ × Bool)) (h : w.length < 1024) :
    wWord (HeB.ent w) = HeB.wordNat w := by
  change (4 * w.length + 4096 * HeB.wordNat w) >>> 12 = _
  rw [Nat.shiftRight_eq_div_pow]
  omega

theorem wLen_ent (w : List (ℕ × Bool)) (h : w.length < 1024) :
    wLen (HeB.ent w) = w.length := by
  change (4 * w.length + 4096 * HeB.wordNat w) >>> 2 &&& (2 ^ 10 - 1) = _
  rw [Nat.shiftRight_eq_div_pow, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem letters_small : ∀ w ∈ Sporadic.hePresentation.relatorLetters,
    w.length < 1024 ∧ ∀ l ∈ w, l.1 < 127 := by
  rw [HeB.relatorLetters_eq]
  decide

theorem rel_eq (r : ℕ) : HeB.rel r = HeB.list.getD r 0 := by
  rcases Nat.lt_or_ge r 7 with h | h
  · interval_cases r <;> rfl
  · have e : ∀ k < 7, Nat.beq r k = false := fun k hk =>
      Bool.eq_false_iff.mpr (fun hc => by rw [Nat.beq_eq] at hc; omega)
    simp only [HeB.rel, e 0 (by omega), e 1 (by omega), e 2 (by omega), e 3 (by omega),
      e 4 (by omega), e 5 (by omega), e 6 (by omega)]
    rw [List.getD_eq_default _ _ (by simp [HeB.list]; omega)]

theorem rel_ok (r : ℕ) :
    wWord (HeB.rel r) < 2 ^ (8 * wLen (HeB.rel r)) ∧
      bval (KB.tcGen Sporadic.hePresentation) (wWord (HeB.rel r)) (wLen (HeB.rel r)) = 1 := by
  rw [rel_eq, ← HeB.relatorLetters_ent, List.getD_eq_getElem?_getD, List.getElem?_map]
  rcases hw : Sporadic.hePresentation.relatorLetters[r]? with _ | w
  · exact ⟨by decide, rfl⟩
  · have hmem := List.mem_of_getElem? hw
    obtain ⟨hlen, hl⟩ := letters_small w hmem
    simp only [Option.map_some, Option.getD_some]
    rw [wWord_ent w hlen, wLen_ent w hlen]
    exact ⟨wordNat_lt w hl, (bval_wordNat _ w hl).trans (KB.sword_relatorLetters _ w hmem)⟩

end CertificateChecks.KernelHe

end
