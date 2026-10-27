module

public import Certificates.Kernel.Misc.Sp4Cen.FactsS
import CFSG.Certificates.Kernel.LocalQTPermSound

public section

namespace CertificateChecks.KernelMisc.Sp4Cen

open Matrix CFSG.KD.Sp4Cen CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.GL4 CFSG.KC.Misc.Clos
  CFSG.KC.Misc.Sp4Cen
open Certificates.GL4 (GL4 sg)
open Certificates.A5GL42 (Mat4 ofCode)

@[expose] noncomputable def fW (g : GL4) : Mat4 := (g : Mat4)ᵀ * W0m * (g : Mat4)

theorem fW_mul (g h : GL4) : fW (g * h) = (h : Mat4)ᵀ * fW g * (h : Mat4) := by
  simp only [fW, Units.val_mul, Matrix.transpose_mul, Matrix.mul_assoc]

theorem fW_eq_iff (g h : GL4) : fW g = fW h ↔ g * h⁻¹ ∈ stabW := by
  have hv : ((h⁻¹ : GL4) : Mat4) * (h : Mat4) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hv' : (h : Mat4) * ((h⁻¹ : GL4) : Mat4) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  change fW g = fW h ↔ fW (g * h⁻¹) = W0m
  rw [fW_mul]
  constructor
  · intro e
    calc ((h⁻¹ : GL4) : Mat4)ᵀ * fW g * ((h⁻¹ : GL4) : Mat4)
        = ((h⁻¹ : GL4) : Mat4)ᵀ * ((h : Mat4)ᵀ * W0m * (h : Mat4)) * ((h⁻¹ : GL4) : Mat4) := by
          rw [e, fW]
      _ = ((h : Mat4) * ((h⁻¹ : GL4) : Mat4))ᵀ * W0m * ((h : Mat4) * ((h⁻¹ : GL4) : Mat4)) := by
          rw [Matrix.transpose_mul]
          simp only [Matrix.mul_assoc]
      _ = W0m := by rw [hv', Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
  · intro e
    calc fW g = (((h⁻¹ : GL4) : Mat4) * (h : Mat4))ᵀ * fW g * (((h⁻¹ : GL4) : Mat4) * (h : Mat4)) := by
          rw [hv, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
      _ = (h : Mat4)ᵀ * (((h⁻¹ : GL4) : Mat4)ᵀ * fW g * ((h⁻¹ : GL4) : Mat4)) * (h : Mat4) := by
          rw [Matrix.transpose_mul]
          simp only [Matrix.mul_assoc]
      _ = fW h := by rw [e, fW]

theorem card_stabW : Nat.card stabW = 720 := by rw [← sb_eq_stab, sb_exact.1]

theorem index_stabW : stabW.index = 28 := by
  have h := Subgroup.card_mul_index stabW
  rw [card_stabW, card_GL4] at h
  omega

theorem exists_fm (g : GL4) : ∃ k < 28, fW g = ofCode (FM k) := by
  classical
  choose! u hu using form_spec.1
  have hinj : Function.Injective fun k : Fin 28 => (QuotientGroup.mk (u k)⁻¹ : GL4 ⧸ stabW) := by
    intro a b e
    simp only [QuotientGroup.eq, inv_inv] at e
    have hf := (fW_eq_iff (u a) (u b)).2 e
    rw [fW, fW, hu a a.2, hu b b.2] at hf
    exact Fin.ext (form_spec.2 a a.2 b b.2 (ofCode_inj (fm_lt a.2) (fm_lt b.2) hf))
  have hcard : Nat.card (GL4 ⧸ stabW) = 28 := index_stabW
  have hbij : Function.Bijective fun k : Fin 28 => (QuotientGroup.mk (u k)⁻¹ : GL4 ⧸ stabW) :=
    hinj.bijective_of_nat_card_le (by rw [hcard, Nat.card_eq_fintype_card, Fintype.card_fin])
  obtain ⟨k, hk⟩ := hbij.2 (QuotientGroup.mk g⁻¹)
  simp only [QuotientGroup.eq, inv_inv] at hk
  refine ⟨k, k.2, ?_⟩
  rw [← hu k k.2]
  exact (fW_eq_iff g (u k)).2 (by simpa using stabW.inv_mem hk)

theorem fm_tree {k : ℕ} (hk : k < 28) (hs : isStart k = false) :
    ∃ p < k, blk p = blk k ∧ ∃ l < 2, FM k = formF (FM p) (SG2 l) := by
  have h := (CFSG.KC.LQT.P.allN_iff _ _).1 (andB_iff.1 sp4_form_ok).2 k hk
  rw [formAt, CFSG.KC.LQT.P.letB_eq, andB_iff, andB_iff, andB_iff, andB_iff, orB_iff] at h
  rcases h.2.2.1 with h1 | h1
  · rw [hs] at h1
    exact absurd h1 (by decide)
  · rw [CFSG.KC.LQT.P.letB_eq, CFSG.KC.LQT.P.letB_eq, CFSG.KC.LQT.P.letB_eq, andB_iff, andB_iff,
      andB_iff] at h1
    exact ⟨_, Nat.blt_eq.mp h1.1, Nat.eq_of_beq_eq_true h1.2.1, _, Nat.blt_eq.mp h1.2.2.1,
      Nat.eq_of_beq_eq_true h1.2.2.2⟩

theorem sg2_mem {l : ℕ} (hl : l < 2) : ∃ s ∈ SB, enc4 s = SG2 l := by
  have hc : SG2 l ∈ [S0, S1] := by
    interval_cases l
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
  obtain ⟨s, hs⟩ := exists_of_invOK (gens_inv _ hc)
  have hl' : ∀ c ∈ [S0, S1], c < 65536 := fun c hc' => by
    obtain ⟨u, hu⟩ := exists_of_invOK (gens_inv c hc')
    rw [← hu]
    exact code4_lt _
  refine ⟨s, Subgroup.subset_closure ((mem_pset_iff hl').2 (by rw [hs]; exact hc)), hs⟩

theorem exists_fW_iff {Z : Subgroup GL4} (hZ : stabW ≤ Z) (g : GL4) :
    (∃ z ∈ Z, fW z = fW g) ↔ g ∈ Z := by
  constructor
  · rintro ⟨z, hz, e⟩
    have h := hZ ((fW_eq_iff z g).1 e)
    have : g = (z * g⁻¹)⁻¹ * z := by group
    rw [this]
    exact Z.mul_mem (Z.inv_mem h) hz
  · intro hg
    exact ⟨g, hg, rfl⟩

@[expose] def st (b : ℕ) : ℕ := if b = 0 then 0 else if b = 1 then 1 else 16

theorem st_start : ∀ k < 28, isStart k = true → st (blk k) = k := by decide

theorem blk_iff {Z : Subgroup GL4} (hZ : SB ≤ Z) :
    ∀ k < 28, (∃ z ∈ Z, fW z = ofCode (FM k)) ↔ (∃ z ∈ Z, fW z = ofCode (FM (st (blk k)))) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    cases hs : isStart k
    · obtain ⟨p, hpk, hb, l, hl, e⟩ := fm_tree hk hs
      obtain ⟨s, hsZ, hse⟩ := sg2_mem hl
      obtain ⟨y, hy⟩ := form_spec.1 p (by omega)
      have hsZ' : stabW ≤ Z := sb_eq_stab ▸ hZ
      have hk' : ofCode (FM k) = fW (y * s) := by
        rw [e, ← hse, ofCode_formF_enc, fW_mul, fW, hy]
      have hp' : ofCode (FM p) = fW y := by rw [fW, hy]
      rw [← hb, ← ih p hpk (by omega), hk', hp', exists_fW_iff hsZ', exists_fW_iff hsZ']
      constructor
      · intro h
        have : y = y * s * s⁻¹ := by group
        rw [this]
        exact Z.mul_mem h (Z.inv_mem (hZ hsZ))
      · intro h
        exact Z.mul_mem h (hZ hsZ)
    · rw [st_start k hk hs]

theorem fm0 : FM 0 = W0 := Nat.eq_of_beq_eq_true (andB_iff.1 sp4_form_ok).1

theorem fW_one : fW 1 = ofCode (FM 0) := by
  rw [fW, Units.val_one, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one, fm0, W0m]

open Classical in
theorem card_Z {Z : Subgroup GL4} (hZ : SB ≤ Z) :
    Nat.card Z = 720 * ((Finset.range 28).filter fun k => ∃ z ∈ Z, fW z = ofCode (FM k)).card := by
  have hsZ : stabW ≤ Z := sb_eq_stab ▸ hZ
  choose! idx hidx using exists_fm
  set t := (Finset.range 28).filter fun k => ∃ z ∈ Z, fW z = ofCode (FM k) with ht
  have hmaps : ((Finset.univ.filter fun g : GL4 => g ∈ Z : Finset GL4) : Set GL4).MapsTo idx t := by
    intro g hg
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hg
    simp only [ht, Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq]
    exact ⟨(hidx g).1, g, hg, (hidx g).2⟩
  have hfibs : ∀ b ∈ t,
      ((Finset.univ.filter fun g : GL4 => g ∈ Z).filter fun g => idx g = b).card = 720 := by
    intro b hb
    obtain ⟨hb28, z0, hz0, e0⟩ : b < 28 ∧ ∃ z ∈ Z, fW z = ofCode (FM b) := by
      simpa [ht] using hb
    have hfib : ((Finset.univ.filter fun g : GL4 => g ∈ Z).filter fun g => idx g = b) =
        (Finset.univ.filter fun g : GL4 => g ∈ stabW).image (· * z0) := by
      ext g
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · rintro ⟨hg, hi⟩
        have e1 : fW g = fW z0 := by rw [(hidx g).2, hi, e0]
        exact ⟨g * z0⁻¹, (fW_eq_iff g z0).1 e1, by group⟩
      · rintro ⟨s, hs, rfl⟩
        have hsz : s * z0 ∈ Z := Z.mul_mem (hsZ hs) hz0
        refine ⟨hsz, ?_⟩
        have e1 : fW (s * z0) = ofCode (FM b) := by
          rw [← e0, fW_eq_iff]
          simpa using hs
        rw [(hidx (s * z0)).2] at e1
        exact form_spec.2 _ (hidx _).1 b hb28 (ofCode_inj (fm_lt (hidx _).1) (fm_lt hb28) e1)
    rw [hfib, Finset.card_image_of_injective _ (mul_left_injective z0), ← Fintype.card_subtype,
      ← Nat.card_eq_fintype_card, card_stabW]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_eq_sum_card_fiberwise hmaps,
    Finset.sum_congr rfl hfibs, Finset.sum_const, smul_eq_mul, mul_comm]

theorem blk_cases : ∀ k < 28, blk k = 0 ∨ blk k = 1 ∨ blk k = 2 := by decide

theorem st_val : ∀ k < 28, st (blk k) = (if blk k = 0 then 0 else if blk k = 1 then 1 else 16) := by
  decide

theorem cnt_eq (a b : Bool) : ((Finset.range 28).filter fun k =>
    blk k = 0 ∨ (blk k = 1 ∧ a = true) ∨ (blk k = 2 ∧ b = true)).card =
    1 + (if a then 15 else 0) + (if b then 12 else 0) := by
  cases a <;> cases b <;> decide

theorem sb_max {Z : Subgroup GL4} (hZ : SB ≤ Z) : Z = SB ∨ Z = ⊤ := by
  classical
  have h0 : ∃ z ∈ Z, fW z = ofCode (FM 0) := ⟨1, Z.one_mem, fW_one⟩
  have key : ∀ k ∈ Finset.range 28, (∃ z ∈ Z, fW z = ofCode (FM k)) ↔
      (blk k = 0 ∨ (blk k = 1 ∧ decide (∃ z ∈ Z, fW z = ofCode (FM 1)) = true) ∨
        (blk k = 2 ∧ decide (∃ z ∈ Z, fW z = ofCode (FM 16)) = true)) := by
    intro k hk
    have hk' := Finset.mem_range.1 hk
    rw [blk_iff hZ k hk', st_val k hk']
    rcases blk_cases k hk' with h | h | h <;> simp [h, h0]
  have hn := card_Z hZ
  rw [Finset.filter_congr key, cnt_eq] at hn
  have hdvd : Nat.card Z ∣ 20160 := card_GL4 ▸ Subgroup.card_subgroup_dvd_card Z
  generalize decide (∃ z ∈ Z, fW z = ofCode (FM 1)) = a at hn
  generalize decide (∃ z ∈ Z, fW z = ofCode (FM 16)) = b at hn
  cases a <;> cases b <;>
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.reduceAdd, Nat.reduceMul] at hn <;>
    rw [hn] at hdvd
  · left
    exact (Subgroup.eq_of_le_of_card_ge hZ (le_of_eq (by rw [hn, sb_exact.1]))).symm
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · right
    exact Subgroup.eq_top_of_card_eq Z (by rw [hn, card_GL4])

end CertificateChecks.KernelMisc.Sp4Cen

end
