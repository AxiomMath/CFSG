module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.U43ConfigCases
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CU43Cover

public section

namespace CertificateChecks.KernelU43Coset8

open Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.PairNative CFSG.Sporadic.SmallOddCore
  CFSG.EvenSporadicStandard.M24Std.CU43 CFSG.EvenSporadicStandard.HSStd.U43

section Rels


theorem dP_pow_four : dP ^ 4 = 1 := by
  have h := checks.2.2.1
  simp only [relCheck, Bool.and_eq_true] at h
  exact (eqA_iff (rep_powA rep_dP 4) rep_idA).1 h.1.1

theorem fP_sq : fP ^ 2 = 1 := by
  have h := checks.2.2.1
  simp only [relCheck, Bool.and_eq_true] at h
  exact (eqA_iff (rep_powA rep_fP 2) rep_idA).1 h.1.2

theorem fP_dP_fP : fP * (dP * fP) = dP ^ 3 := by
  have h := checks.2.2.1
  simp only [relCheck, Bool.and_eq_true] at h
  exact (eqA_iff (rep_compA rep_fP (rep_compA rep_dP rep_fP)) (rep_powA rep_dP 3)).1 h.2

theorem dP_pow_mul_fP (b : ℕ) : dP ^ b * fP = fP * dP ^ (3 * b) := by
  have hf : fP * fP = 1 := by rw [← sq]; exact fP_sq
  have h1 : dP * fP = fP * dP ^ 3 := by
    calc dP * fP = fP * fP * (dP * fP) := by rw [hf, one_mul]
      _ = fP * dP ^ 3 := by rw [mul_assoc, fP_dP_fP]
  induction b with
  | zero => simp
  | succ b ih =>
    calc dP ^ (b + 1) * fP = dP ^ b * (dP * fP) := by rw [pow_succ, mul_assoc]
      _ = dP ^ b * fP * dP ^ 3 := by rw [h1, mul_assoc]
      _ = fP * dP ^ (3 * (b + 1)) := by rw [ih, mul_assoc, ← pow_add]; ring_nf

theorem tP_mul_mulIdx' {k k' : ℕ} (hk' : k' < 8) : tP k * tP k' = tP (mulIdx k k') := by
  have hd : ∀ m, dP ^ m = dP ^ (m % 4) := fun m => pow_eq_pow_mod m dP_pow_four
  have hf : ∀ m, fP ^ m = fP ^ (m % 2) := fun m => pow_eq_pow_mod m fP_sq
  unfold tP
  rcases (by omega : k' / 4 = 0 ∨ k' / 4 = 1) with h0 | h1
  · have e1 : mulIdx k k' / 4 = k / 4 % 2 := by unfold mulIdx; split_ifs <;> omega
    have e2 : mulIdx k k' % 4 = (k % 4 + k' % 4) % 4 := by unfold mulIdx; split_ifs <;> omega
    rw [e1, e2, h0, pow_zero, one_mul, ← hf (k / 4), ← hd (k % 4 + k' % 4), mul_assoc,
      ← pow_add]
  · have e1 : mulIdx k k' / 4 = (k / 4 + 1) % 2 := by unfold mulIdx; split_ifs <;> omega
    have e2 : mulIdx k k' % 4 = (3 * (k % 4) + k' % 4) % 4 := by
      unfold mulIdx; split_ifs <;> omega
    rw [e1, e2, h1, pow_one, ← hf (k / 4 + 1), ← hd (3 * (k % 4) + k' % 4)]
    calc fP ^ (k / 4) * dP ^ (k % 4) * (fP * dP ^ (k' % 4))
        = fP ^ (k / 4) * (dP ^ (k % 4) * fP) * dP ^ (k' % 4) := by simp only [mul_assoc]
      _ = fP ^ (k / 4) * fP * (dP ^ (3 * (k % 4)) * dP ^ (k' % 4)) := by
          rw [dP_pow_mul_fP]; simp only [mul_assoc]
      _ = fP ^ (k / 4 + 1) * dP ^ (3 * (k % 4) + k' % 4) := by rw [pow_succ, pow_add]

theorem dihedralCheck_true : dihedralCheck = true := by
  simp only [dihedralCheck, List.all_eq_true, List.mem_range]
  intro k _ k' hk'
  exact (eqA_iff (rep_compA (rep_tArr k) (rep_tArr k')) (rep_tArr _)).2 (tP_mul_mulIdx' hk')

end Rels

section Counts


theorem card_inf_centralizer_conj_norm {n : Equiv.Perm (Fin 820)}
    (hn : n ∈ normalizer (P : Set (Equiv.Perm (Fin 820)))) (t : Equiv.Perm (Fin 820)) :
    Nat.card ↥(P ⊓ centralizer ({n * t * n⁻¹} : Set (Equiv.Perm (Fin 820)))) =
      Nat.card ↥(P ⊓ centralizer ({t} : Set (Equiv.Perm (Fin 820)))) := by
  have hmem : ∀ x, x ∈ P ↔ n * x * n⁻¹ ∈ P := fun x => mem_normalizer_iff.1 hn x
  have hmem' : ∀ x, x ∈ P ↔ n⁻¹ * x * n ∈ P := fun x => by
    have := mem_normalizer_iff.1 (inv_mem hn) x
    simpa using this
  refine Nat.card_congr
    { toFun := fun z => ⟨n⁻¹ * z * n, mem_inf.2 ⟨(hmem' _).1 (mem_inf.1 z.2).1, ?_⟩⟩
      invFun := fun z => ⟨n * z * n⁻¹, mem_inf.2 ⟨(hmem _).1 (mem_inf.1 z.2).1, ?_⟩⟩
      left_inv := fun z => by ext1; simp [mul_assoc]
      right_inv := fun z => by ext1; simp [mul_assoc] }
  · have h := mem_centralizer_singleton_iff.1 (mem_inf.1 z.2).2
    refine mem_centralizer_singleton_iff.2 ?_
    calc n⁻¹ * ↑z * n * t = n⁻¹ * (↑z * (n * t * n⁻¹)) * n := by group
      _ = n⁻¹ * (n * t * n⁻¹ * ↑z) * n := by rw [h]
      _ = t * (n⁻¹ * ↑z * n) := by group
  · have h := mem_centralizer_singleton_iff.1 (mem_inf.1 z.2).2
    refine mem_centralizer_singleton_iff.2 ?_
    calc n * ↑z * n⁻¹ * (n * t * n⁻¹) = n * (↑z * t) * n⁻¹ := by group
      _ = n * (t * ↑z) * n⁻¹ := by rw [h]
      _ = n * t * n⁻¹ * (n * ↑z * n⁻¹) := by group

theorem tP_mul_tP_two {k : ℕ} (hk : k < 8) : tP k * tP 2 = tP 2 * tP k := by
  rw [tP_mul_mulIdx' (by norm_num : 2 < 8), tP_mul_mulIdx' hk]
  congr 1
  interval_cases k <;> decide

theorem exists_comm_rP8 {k : ℕ} (hk : k < 8) :
    ∃ g₀ ∈ P, g₀ * tP k * rP 8 = rP 8 * (g₀ * tP k) := by
  obtain ⟨g, hg, hrg, hr2⟩ := rP_mem_InvCoset (by norm_num : 8 < 9)
  have hc2 : repCoset[8]! = 2 := by decide
  rw [hc2] at hrg
  have hn := tP_mem_normalizer k
  have hrR : rP 8 ∈ R := by rw [hrg]; exact R.mul_mem (P_le_R hg) (tP_mem_R (by norm_num))
  have hrP : rP 8 ∉ P := by
    intro h
    apply tP_mul_inv_not_mem (by norm_num : 2 < 8) (by norm_num : 0 < 8) (by norm_num)
    rw [tP_zero, inv_one, mul_one]
    have : tP 2 = g⁻¹ * rP 8 := by rw [hrg]; group
    rw [this]
    exact P.mul_mem (P.inv_mem hg) h
  set β := tP k * rP 8 * (tP k)⁻¹ with hβ
  have hβR : β ∈ R :=
    R.mul_mem (R.mul_mem (tP_mem_R hk) hrR) (R.inv_mem (tP_mem_R hk))
  have hβ2 : β * β = 1 := by
    calc β * β = tP k * (rP 8 * rP 8) * (tP k)⁻¹ := by rw [hβ]; group
      _ = 1 := by rw [hr2]; group
  have hcos : β * (rP 8)⁻¹ ∈ P := by
    have hgc : tP k * g * (tP k)⁻¹ ∈ P := (mem_normalizer_iff.1 hn g).1 hg
    have e : β * (rP 8)⁻¹ = tP k * g * (tP k)⁻¹ * g⁻¹ := by
      have h2 : tP k * tP 2 * (tP k)⁻¹ = tP 2 := by rw [tP_mul_tP_two hk]; group
      calc β * (rP 8)⁻¹ = tP k * g * (tP k)⁻¹ * (tP k * tP 2 * (tP k)⁻¹) * (tP 2)⁻¹ * g⁻¹ := by
            rw [hβ, hrg]; group
        _ = tP k * g * (tP k)⁻¹ * g⁻¹ := by rw [h2]; group
    rw [e]
    exact P.mul_mem hgc (P.inv_mem hg)
  have hc8 : Nat.card ↥(P ⊓ centralizer ({rP 8} : Set (Equiv.Perm (Fin 820)))) = 720 := by
    rw [card_inf_centralizer_rP (by norm_num : 8 < 9)]; decide
  have hcβ : Nat.card ↥(P ⊓ centralizer ({β} : Set (Equiv.Perm (Fin 820)))) = 720 := by
    rw [hβ, card_inf_centralizer_conj_norm hn, hc8]
  obtain ⟨c, hc, hβc⟩ := same_coset_conj hrR hrP hr2 hβR hβ2 hcos hc8 hcβ
  refine ⟨c⁻¹, P.inv_mem hc, ?_⟩
  calc c⁻¹ * tP k * rP 8 = c⁻¹ * (tP k * rP 8 * (tP k)⁻¹) * tP k := by group
    _ = c⁻¹ * (c * rP 8 * c⁻¹) * tP k := by rw [← hβ, hβc]
    _ = rP 8 * (c⁻¹ * tP k) := by group

theorem card_comm_cos8' {k : ℕ} (hk : k < 8) :
    Nat.card {g : P // (g : Equiv.Perm (Fin 820)) * tP k * rP 8 =
      rP 8 * ((g : Equiv.Perm (Fin 820)) * tP k)} = 720 := by
  obtain ⟨g₀, hg₀, h₀⟩ := exists_comm_rP8 hk
  have h720 : repCent[8]! = 720 := by decide
  rw [← h720, ← card_comm_rep (by norm_num : 8 < 9)]
  have key : ∀ g : Equiv.Perm (Fin 820),
      g * tP k * rP 8 = rP 8 * (g * tP k) ↔ g * g₀⁻¹ * rP 8 = rP 8 * (g * g₀⁻¹) := by
    intro g
    have hx : g * tP k = g * g₀⁻¹ * (g₀ * tP k) := by group
    rw [hx, mul_assoc (g * g₀⁻¹) (g₀ * tP k) (rP 8), h₀,
      ← mul_assoc (g * g₀⁻¹) (rP 8) (g₀ * tP k), ← mul_assoc (rP 8) (g * g₀⁻¹) (g₀ * tP k)]
    exact mul_left_inj (g₀ * tP k)
  exact Nat.card_congr
    { toFun := fun x => ⟨⟨x.1.1 * g₀⁻¹, P.mul_mem x.1.2 (P.inv_mem hg₀)⟩, (key _).1 x.2⟩
      invFun := fun y => ⟨⟨y.1.1 * g₀, P.mul_mem y.1.2 hg₀⟩, (key _).2 (by
        simpa [mul_assoc] using y.2)⟩
      left_inv := fun x => by ext1; ext1; simp
      right_inv := fun y => by ext1; ext1; simp }

theorem centCosetCounts_true : centCosetCounts = true := by
  classical
  simp only [centCosetCounts, List.all_eq_true, List.mem_range, beq_iff_eq]
  intro k hk
  rw [← card_eq_countW_P (f := commW (tArr k) [reps[8]!])
    (Pr := fun g => g * tP k * rP 8 = rP 8 * (g * tP k))]
  · exact card_comm_cos8' hk
  · intro w g hw _
    have hH : RepW 820 (tArr k :: w) (g * tP k) := RepW.cons (rep_tArr k) hw
    simp only [commW, List.all_cons, List.all_nil, Bool.and_true]
    exact allLt_comm_iff hH (rep_rP (by norm_num : 8 < 9))

theorem cosetCheck8_true : cosetCheck8 = true := by
  rw [cosetCheck8, dihedralCheck_true, centCosetCounts_true, Bool.and_self]

end Counts

end CertificateChecks.KernelU43Coset8
