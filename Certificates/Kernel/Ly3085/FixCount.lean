
module

public import Certificates.Kernel.Ly3085.FixCountBase

public import Certificates.Kernel.Ly3085.FixO1
public import Certificates.Kernel.Ly3085.Discharge

public section

noncomputable section

namespace CertificateChecks.KernelLy.Omega

open CFSG.Sporadic.Ly CFSG.Sporadic.LySchreier CFSG.Sporadic.LySchreier.Native
open CFSG.Sporadic.Ly.Omega CFSG.KS.LyOm CFSG.KC.LyOm CFSG.KC.LL CFSG.KC.Loop
open CertificateChecks.KernelSporSch
open Matrix MulAction

theorem card_fix_omega
    [LySeed]
    {x : J} (hx : x ∈ lyH) :
    Nat.card {y : orbit J opE // x • y = y} =
      ∑ i : Fin 5, Nat.card {y : orbit lyH (repOp i.val) // (⟨x, hx⟩ : lyH) • y = y} := by
  classical
  obtain ⟨-, hcov, hd, -⟩ := F1_all
  rw [card_fix_finset x opE _ hcov, Finset.filter_biUnion, Finset.card_biUnion]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [card_fix_finset (⟨x, hx⟩ : lyH) (repOp i.val) (subO i) (by
      unfold subO
      rw [Set.Finite.coe_toFinset])]
    rfl
  · intro i _ j _ hij
    exact Finset.disjoint_filter_filter (hd hij)

theorem card_stab_le
    [LySeed]
    {X : Type*} [MulAction lyH X] (q : X) {b n : ℕ} (hb : b ≤ Nat.card (orbit lyH q))
    (hbn : b * n = 5859000000) : Nat.card (stabilizer lyH q) ≤ n := by
  have h1 := orbit_stab q
  rw [F1.2.1] at h1
  have hb0 : 0 < b := by
    rcases Nat.eq_zero_or_pos b with h | h
    · rw [h] at hbn
      omega
    · exact h
  have : b * Nat.card (stabilizer lyH q) ≤ b * n := by
    rw [hbn, ← h1]
    exact Nat.mul_le_mul_right _ hb
  exact Nat.le_of_mul_le_mul_left this hb0

theorem card_stab_eq
    [LySeed]
    (p : LyOperator) {o n : ℕ} (ho : Nat.card (orbit lyH p) = o) (hon : o * n = 5859000000)
    (hn : 0 < o) : Nat.card (stabilizer lyH p) = n := by
  have h1 := orbit_stab p
  rw [F1.2.1, ho, ← hon] at h1
  exact Nat.eq_of_mul_eq_mul_left hn h1

theorem stab_counts
    [LySeed] :
    (Nat.card (stabilizer lyH (gRep 2 • opE)) = 6048 ∧
      Nat.card {h : lyH // h ∈ stabilizer lyH (pairOp (gRep 2 • opE)) ∧ cls 0 (restr7 (h : J))} = 63 ∧
      Nat.card {h : lyH // h ∈ stabilizer lyH (pairOp (gRep 2 • opE)) ∧ cls 1 (restr7 (h : J))} = 672 ∧
      Nat.card {h : lyH // h ∈ stabilizer lyH (pairOp (gRep 2 • opE)) ∧ cls 2 (restr7 (h : J))} = 0 ∧
      Nat.card {h : lyH // h ∈ stabilizer lyH (pairOp (gRep 2 • opE)) ∧ cls 3 (restr7 (h : J))} = 0) ∧
    (Nat.card (stabilizer lyH (gRep 3 • opE)) = 2880 ∧
      Nat.card {h : lyH // h ∈ stabilizer lyH (pairOp (gRep 3 • opE)) ∧ cls 0 (restr7 (h : J))} = 211 ∧
      Nat.card {h : lyH // h ∈ stabilizer lyH (pairOp (gRep 3 • opE)) ∧ cls 1 (restr7 (h : J))} = 168 ∧
      Nat.card {h : lyH // h ∈ stabilizer lyH (pairOp (gRep 3 • opE)) ∧ cls 2 (restr7 (h : J))} = 0 ∧
      Nat.card {h : lyH // h ∈ stabilizer lyH (pairOp (gRep 3 • opE)) ∧ cls 3 (restr7 (h : J))} = 0) ∧
    (Nat.card (stabilizer lyH (gRep 4 • opE)) = 1008 ∧
      Nat.card {h : lyH // h ∈ stabilizer lyH (pairOp (gRep 4 • opE)) ∧ cls 0 (restr7 (h : J))} = 105 ∧
      Nat.card {h : lyH // h ∈ stabilizer lyH (pairOp (gRep 4 • opE)) ∧ cls 1 (restr7 (h : J))} = 168 ∧
      Nat.card {h : lyH // h ∈ stabilizer lyH (pairOp (gRep 4 • opE)) ∧ cls 2 (restr7 (h : J))} = 0 ∧
      Nat.card {h : lyH // h ∈ stabilizer lyH (pairOp (gRep 4 • opE)) ∧ cls 3 (restr7 (h : J))} =
        0) := by
  obtain ⟨-, -, -, -, -, o2, o3, o4⟩ := F1_all
  have p2 : 968750 ≤ Nat.card (orbit lyH (pairOp (gRep 2 • opE))) :=
    card_orbit_o2_sp.trans (card_orbit_le_of_map (G := lyH) Prod.snd
      (fun h x => Prod.smul_snd h x) (pairOp (gRep 2 • opE)))
  obtain ⟨g20, g21⟩ := k2_gens
  obtain ⟨g30, g31, g32⟩ := k3_gens
  obtain ⟨g40, g41, g42, g43⟩ := k4_gens
  exact ⟨⟨card_stab_eq _ o2 (by norm_num) (by norm_num),
      h2_counts _ g20 g21 (card_stab_le _ p2 (by norm_num))⟩,
    ⟨card_stab_eq _ o3 (by norm_num) (by norm_num),
      h3_counts _ g30 g31 g32 (card_stab_le _ card_orbit_o3_pair (by norm_num))⟩,
    ⟨card_stab_eq _ o4 (by norm_num) (by norm_num),
      h4_counts _ g40 g41 g42 g43 (card_stab_le _ card_orbit_o4_pair (by norm_num))⟩⟩

theorem fix_le
    [LySeed]
    {x : J} (hx : x ∈ lyH) (k : ℕ) (hk : cls k (restr7 x)) {kc b1 b2 b3 b4 : ℕ}
    (hC : Nat.card (Subgroup.centralizer ({(⟨x, hx⟩ : lyH)} : Set lyH)) ≤ kc)
    (h1 : Nat.card {y : orbit lyH (gRep 1 • opE) // (⟨x, hx⟩ : lyH) • y = y} ≤ b1)
    (h2 : kc * Nat.card {h : lyH // h ∈ stabilizer lyH (pairOp (gRep 2 • opE)) ∧
      cls k (restr7 (h : J))} ≤ b2 * 6048)
    (h3 : kc * Nat.card {h : lyH // h ∈ stabilizer lyH (pairOp (gRep 3 • opE)) ∧
      cls k (restr7 (h : J))} ≤ b3 * 2880)
    (h4 : kc * Nat.card {h : lyH // h ∈ stabilizer lyH (pairOp (gRep 4 • opE)) ∧
      cls k (restr7 (h : J))} ≤ b4 * 1008) :
    Nat.card {y : orbit J opE // x • y = y} ≤ 1 + b1 + b2 + b3 + b4 := by
  obtain ⟨⟨s2, -⟩, ⟨s3, -⟩, ⟨s4, -⟩⟩ := stab_counts
  obtain ⟨-, -, -, o0, -⟩ := F1_all
  rw [card_fix_omega hx, Fin.sum_univ_five]
  have e1 : repOp (1 : Fin 5).val = gRep 1 • opE := repOp_pos (by decide)
  have e2 : repOp (2 : Fin 5).val = gRep 2 • opE := repOp_pos (by decide)
  have e3 : repOp (3 : Fin 5).val = gRep 3 • opE := repOp_pos (by decide)
  have e4 : repOp (4 : Fin 5).val = gRep 4 • opE := repOp_pos (by decide)
  have e0 : repOp (0 : Fin 5).val = opE := repOp_zero
  rw [e0, e1, e2, e3, e4]
  have f0 : Nat.card {y : orbit lyH opE // (⟨x, hx⟩ : lyH) • y = y} ≤ 1 := by
    have : Finite (orbit lyH opE) := Nat.finite_of_card_ne_zero (by rw [o0]; norm_num)
    have := Nat.card_le_card_of_injective (Subtype.val : {y : orbit lyH opE //
      (⟨x, hx⟩ : lyH) • y = y} → orbit lyH opE) Subtype.val_injective
    omega
  have c2 := conj_count_le (p := gRep 2 • opE) (stab_le_pair _) k (t := ⟨x, hx⟩) hk
  have c3 := conj_count_le (p := gRep 3 • opE) (stab_le_pair _) k (t := ⟨x, hx⟩) hk
  have c4 := conj_count_le (p := gRep 4 • opE) (stab_le_pair _) k (t := ⟨x, hx⟩) hk
  have f2 := fix_bound s2 (by norm_num) c2 hC h2
  have f3 := fix_bound s3 (by norm_num) c3 hC h3
  have f4 := fix_bound s4 (by norm_num) c4 hC h4
  omega

theorem fix_counts
    [LySeed] :
    Nat.card {y : orbit J opE // lyt • y = y} ≤ 2772 ∧
      Nat.card {y : orbit J opE // lyYB • y = y} ≤ 243 ∧
      Nat.card {y : orbit J opE // lyTA • y = y} ≤ 156 ∧
      Nat.card {y : orbit J opE // lyTB • y = y} ≤ 6 := by
  obtain ⟨k0, k1, k2, k3⟩ := class_facts
  obtain ⟨⟨-, a0, a1, a2, a3⟩, ⟨-, b0, b1, b2, b3⟩, ⟨-, c0, c1, c2, c3⟩⟩ := stab_counts
  obtain ⟨-, -, -, -, o1, -⟩ := F1_all
  obtain ⟨⟨pT, eT⟩, ⟨pY, eY⟩, ⟨pA, eA⟩, ⟨pB, eB⟩⟩ := px_facts
  have hY : lyYB ∈ lyH := wordJ_mem _
  have hA : lyTA ∈ lyH := wordJ_mem _
  have hB : lyTB ∈ lyH := wordJ_mem _
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h1 := o1_fix_le o1 lyt_mem_lyH pT eT CFSG.KD.LyOm.o1xt
    rw [o1_sum CFSG.KD.LyO1.FixTT.all CFSG.KD.LyO1.sumTT] at h1
    have := fix_le lyt_mem_lyH 0 k0 card_centralizer_t h1 (b2 := 150) (b3 := 1055) (b4 := 1500)
      (by rw [a0]; try norm_num) (by rw [b0]; try norm_num) (by rw [c0]; try norm_num)
    omega
  · have h1 := o1_fix_le o1 hY pY eY CFSG.KD.LyOm.o1xy
    rw [o1_sum CFSG.KD.LyO1.FixYB.all CFSG.KD.LyO1.sumYB] at h1
    have := fix_le hY 1 k1 card_centralizer_yB h1 (b2 := 80) (b3 := 42) (b4 := 120)
      (by rw [a1]; try norm_num) (by rw [b1]; try norm_num) (by rw [c1]; try norm_num)
    omega
  · have h1 := o1_fix_le o1 hA pA eA CFSG.KD.LyOm.o1xa
    rw [o1_sum CFSG.KD.LyO1.FixTA.all CFSG.KD.LyO1.sumTA] at h1
    have := fix_le hA 2 k2 le_rfl h1 (b2 := 0) (b3 := 0) (b4 := 0)
      (by rw [a2]; try norm_num) (by rw [b2]; try norm_num) (by rw [c2]; try norm_num)
    omega
  · have h1 := o1_fix_le o1 hB pB eB CFSG.KD.LyOm.o1xb
    rw [o1_sum CFSG.KD.LyO1.FixTB.all CFSG.KD.LyO1.sumTB] at h1
    have := fix_le hB 3 k3 le_rfl h1 (b2 := 0) (b3 := 0) (b4 := 0)
      (by rw [a3]; try norm_num) (by rw [b3]; try norm_num) (by rw [c3]; try norm_num)
    omega

end CertificateChecks.KernelLy.Omega

end

end
