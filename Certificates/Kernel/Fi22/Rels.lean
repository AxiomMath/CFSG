module

public import Certificates.Kernel.Co2.Words
public import CFSG.Certificates.Kernel.Fi22.Bound.RelsTC
public import CFSG.Certificates.Kernel.Fi22.Bound2.Rels
import CFSG.Certificates.Kernel.Common.Harness
public import Mathlib.Tactic.IntervalCases

public section

namespace CertificateChecks.KernelFi22

open CFSG.KC CFSG.KC.LceS CFSG.Certificates CFSG.Certificates.LCE CertificateChecks.KernelCo2

abbrev P : TauCeti.GroupPresentation := TauCeti.Sporadic.fi22Presentation

abbrev PG : Type := PresentedGroup P.relatorSet

noncomputable abbrev tg : ℕ → PG := pgen P.relatorSet

theorem gens_eq : P.generatorCount = 2 := by
  simp [TauCeti.GroupPresentation.generatorCount, TauCeti.Sporadic.fi22Presentation_generatorNames]

theorem wordNat_eq (w : List (ℕ × Bool)) : Fi22B.wordNat w = Co2B.wordNat w := by
  induction w with
  | nil => rfl
  | cons l w ih => simp only [Fi22B.wordNat, Co2B.wordNat, Fi22B.code, Co2B.code, ih]

theorem ent_eq (w : List (ℕ × Bool)) : Fi22B.ent w = Co2B.ent w := by
  simp only [Fi22B.ent, Co2B.ent, wordNat_eq]

theorem rel_val : ∀ r < 13, bval tg (wWord (Fi22B.rel r)) (wLen (Fi22B.rel r)) = 1 := by
  have hl := Fi22B.relatorLetters_ent
  have hb : ∀ w ∈ P.relatorLetters, (∀ l ∈ w, l.1 < 127) ∧ w.length < 1024 := by
    rw [CFSG.KD.OrdFi22.rels_eq]
    decide
  have hlen : (P.relatorLetters.map Fi22B.ent).length = 13 := by rw [hl]; rfl
  intro r hr
  have e : Fi22B.rel r = (P.relatorLetters.map Fi22B.ent)[r]'(by omega) := by
    rw [List.getElem_of_eq hl]
    interval_cases r <;> rfl
  rw [e, List.getElem_map, ent_eq]
  have hm := List.getElem_mem (l := P.relatorLetters) (n := r) (by
    rw [List.length_map] at hlen
    omega)
  rw [bval_ent _ _ (hb _ hm).1 (hb _ hm).2]
  exact swd_relatorLetters P _ hm

theorem rel_ge {r : ℕ} (h : 13 ≤ r) : Fi22B.rel r = 0 := by
  have hb : ∀ i < 13, Nat.beq r i = false := fun i hi =>
    Bool.eq_false_iff.mpr fun h' => by
      have := Nat.eq_of_beq_eq_true h'
      omega
  simp only [Fi22B.rel, hb 0 (by norm_num), hb 1 (by norm_num), hb 2 (by norm_num), hb 3 (by norm_num),
    hb 4 (by norm_num), hb 5 (by norm_num), hb 6 (by norm_num), hb 7 (by norm_num), hb 8 (by norm_num),
    hb 9 (by norm_num), hb 10 (by norm_num), hb 11 (by norm_num), hb 12 (by norm_num)]

theorem sub_ge {r : ℕ} (h : 7 ≤ r) : Fi22B.sub r = 0 := by
  have hb : ∀ i < 7, Nat.beq r i = false := fun i hi =>
    Bool.eq_false_iff.mpr fun h' => by
      have := Nat.eq_of_beq_eq_true h'
      omega
  simp only [Fi22B.sub, hb 0 (by norm_num), hb 1 (by norm_num), hb 2 (by norm_num), hb 3 (by norm_num),
    hb 4 (by norm_num), hb 5 (by norm_num), hb 6 (by norm_num)]

theorem rel_norm : relsNorm Fi22B.rel (nat_lit 13) = true := by quickRfl

theorem rel_all : ∀ r, wWord (Fi22B.rel r) < 2 ^ (8 * wLen (Fi22B.rel r)) ∧
    bval tg (wWord (Fi22B.rel r)) (wLen (Fi22B.rel r)) = 1 := by
  intro r
  by_cases hr : r < 13
  · exact ⟨relsNorm_spec rel_norm r hr, rel_val r hr⟩
  · rw [rel_ge (by omega)]
    exact ⟨by decide, rfl⟩

theorem swd_rel {w : List (ℕ × Bool)} (hw : w ∈ CFSG.KD.OrdFi22.rels) : swd tg w = 1 := by
  rw [← CFSG.KD.OrdFi22.rels_eq] at hw
  exact swd_relatorLetters P w hw

theorem a_sq : tg 0 * tg 0 = 1 := by
  have h := swd_rel (w := [(0, true), (0, true)]) (by decide)
  simpa [swd] using h

theorem swd_append {G : Type*} [Group G] (gen : ℕ → G) (a b : List (ℕ × Bool)) :
    swd gen (a ++ b) = swd gen a * swd gen b := by
  simp [swd, List.map_append, List.prod_append]

theorem swd_rep {G : Type*} [Group G] (gen : ℕ → G) (w : List (ℕ × Bool)) (n : ℕ) :
    swd gen (List.replicate n w).flatten = swd gen w ^ n := by
  induction n with
  | zero => simp [swd]
  | succ n ih => rw [List.replicate_succ, List.flatten_cons, swd_append, ih, pow_succ']

theorem b_pow : tg 1 ^ 13 = 1 := by
  have h := swd_rel (w := (List.replicate 13 [(1, true)]).flatten) (by decide)
  rw [swd_rep] at h
  simpa [swd] using h

theorem ab_pow : (tg 0 * tg 1) ^ 11 = 1 := by
  have h := swd_rel (w := (List.replicate 11 [(0, true), (1, true)]).flatten) (by decide)
  rw [swd_rep] at h
  simpa [swd] using h

theorem closure_tg : Subgroup.closure (tg '' {g | 2 * g < nat_lit 4}) = ⊤ := by
  rw [← closure_pgen P.relatorSet]
  congr 2
  ext g
  change 2 * g < 4 ↔ g < P.generatorCount
  rw [gens_eq]
  omega

end CertificateChecks.KernelFi22

end
