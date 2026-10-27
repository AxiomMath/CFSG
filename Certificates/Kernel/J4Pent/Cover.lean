module

public import Certificates.Kernel.J4Pent.Count
public import Certificates.Kernel.J4Count.HOrder
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Red0
public import CFSG.Sporadic.J4.QT2LocX0NMainBase
public import CFSG.Sporadic.J4.QTRankInvProof
public import Certificates.Kernel.J4Count.FixCEChecks
public import Certificates.Kernel.J4Count.FixCEEltBase

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelJ4Pent

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2
open CFSG.KC.J4Pent CFSG.KD.J4Pent CFSG.KC.J4Q CFSG.KD.J4Q CertificateChecks.KernelJ4Q
open CertificateChecks.KernelJ4Count.FixCE (PR PR_of PR_eq PR_one inv_smul_PR row_toVec)
open CFSG.Sporadic.SmallF2 (toVecD toVecD_apply)
open CFSG.QuasithinUnique.A5 MulAction

noncomputable abbrev rho (p : ℕ) : Row := toRow (toVecD 112 p)

theorem rho_inj {p q : ℕ} (hp : p < 2 ^ 112) (hq : q < 2 ^ 112) (h : rho p = rho q) : p = q := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < 112
  · have e := congrArg (fun r => ofRow r ⟨j, hj⟩) h
    change toVecD 112 p ⟨j, hj⟩ = toVecD 112 q ⟨j, hj⟩ at e
    rw [toVecD_apply, toVecD_apply] at e
    revert e
    cases p.testBit j <;> cases q.testBit j <;> simp
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hp (Nat.pow_le_pow_right (n := 2) (by omega)
      (show 112 ≤ j by omega))), Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hq
      (Nat.pow_le_pow_right (n := 2) (by omega) (show 112 ≤ j by omega)))]

theorem act {g : J} {m : ℕ} (hg : PR g m) {p : ℕ} (hp : p < 2 ^ 112) :
    g⁻¹ • rho p = rho (vecJ (2 ^ 112 - 1) p m) := by
  rw [← rm_eq]
  exact inv_smul_PR hg hp

theorem act' {g : J} {m : ℕ} (hg : PR g⁻¹ m) {p : ℕ} (hp : p < 2 ^ 112) :
    g • rho p = rho (vecJ (2 ^ 112 - 1) p m) := by
  have h := act hg hp
  rwa [inv_inv] at h

theorem rho_v2N (a : V2) : rho (v2N a) = toRow a.toVec := (row_toVec a).symm

theorem PR_Ai : PR (a⁻¹ : J) Ai := PR_of (m := Ai) (base_invs 0) (Mx_a_inv matFacts)
theorem PR_Bi : PR (b⁻¹ : J) Bi := PR_of (m := Bi) (base_invs 1) (Mx_b_inv matFacts)
theorem PR_B : PR (b : J) B := PR_of rowsB_enc (QT.Mx_b matFacts)

theorem PR_F : PR fiveElt (getN one XG 0) :=
  PR_of (x0Gen_enc (by omega)) (Mx_fiveElt matFacts)

theorem PR_U {j : ℕ} (hj : j < 11) : PR (uJ j) (Mf j) :=
  PR_of (uTab_enc j (by rw [Us_length]; exact hj)) (Mx_uJ matFacts hj)

theorem PR_X0 {k : J} (hk : k ∈ X0Sub) :
    ∃ t < 6720, PR k (CFSG.KD.X0O.MSF t) := by
  obtain ⟨t, ht, hMx⟩ := (mem_X0Sub_iff matFacts).1 hk
  exact ⟨t, ht, PR_of (msf_enc ht) hMx⟩

theorem X0_of_lt {t : ℕ} (ht : t < 6720) :
    ∃ g ∈ X0Sub, PR g (CFSG.KD.X0O.MSF t) := by
  obtain ⟨g, hg, hMx⟩ := mem_X0Sub_of_lt matFacts t ht
  exact ⟨g, hg, PR_of (msf_enc ht) hMx⟩

theorem msf_zero : CFSG.KD.X0O.MSF 0 = one :=
  Nat.eq_of_beq_eq_true (xAt_dec (k := 0) (by decide)).1

theorem eq_one_of_PR0 {k : J} (hk : PR k (CFSG.KD.X0O.MSF 0)) : k = 1 := by
  rw [msf_zero] at hk
  exact PR_eq hk PR_one

theorem laneR_lt (l : ℕ) : laneV R l < 2 ^ 112 := by
  have h := laneV_lt R l
  rwa [wf_parts.1.1] at h

noncomputable abbrev qL (l : ℕ) : Row := rho (laneV R l)

theorem lane_strict {l m : ℕ} (hlm : l < m) (hm : m < NL) : laneV R l < laneV R m := by
  have hi := incrS_spec (N := NL) (R := R) (by rw [← ONES_eq]; exact incr_ok)
  induction m with
  | zero => omega
  | succ m ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hlm with h | h
    · exact lt_trans (ih h (by omega)) (hi m hm)
    · rw [h]
      exact hi m hm

theorem lane_le {l : ℕ} (hl : l < NL) {k : J} (hk : k ∈ X0Sub) :
    ∃ p, k • qL l = rho p ∧ laneV R l ≤ p ∧ p < 2 ^ 112 := by
  obtain ⟨t, ht, hPR⟩ := PR_X0 (X0Sub.inv_mem hk)
  rcases Nat.eq_zero_or_pos t with rfl | ht0
  · have := eq_one_of_PR0 hPR
    rw [inv_eq_one] at this
    subst this
    exact ⟨laneV R l, one_smul _ _, le_rfl, laneR_lt l⟩
  · refine ⟨vecJ (2 ^ 112 - 1) (laneV R l) (CFSG.KD.X0O.MSF t), act' hPR (laneR_lt l), ?_,
      vecJ_lt _ _⟩
    have h := (canon_lane ht0 ht hl).1
    rwa [rm_eq] at h

theorem lane_fix {l : ℕ} (hl : l < NL) {k : J} (hk : k ∈ X0Sub)
    (hfix : k • qL l = qL l) {t : ℕ} (ht : t < 6720) (hPR : PR k⁻¹ (CFSG.KD.X0O.MSF t)) :
    t = 0 ∨ (l, t) ∈ FXL := by
  rcases Nat.eq_zero_or_pos t with rfl | ht0
  · exact Or.inl rfl
  · right
    rw [act' hPR (laneR_lt l)] at hfix
    have e := rho_inj (vecJ_lt _ _) (laneR_lt l) hfix
    rw [← rm_eq] at e
    exact fxl_mem ht0 ht ((canon_lane ht0 ht hl).2.1 e)

noncomputable abbrev orbL (l : ℕ) : Set Row := orbit (↥X0Sub) (qL l)

theorem mem_orbL {l : ℕ} {x : Row} : x ∈ orbL l ↔ ∃ k ∈ X0Sub, k • qL l = x := by
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k, k.2, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨k, hk⟩, rfl⟩

theorem card_stab_le {l : ℕ} (hl : l < NL) :
    Nat.card (stabilizer (↥X0Sub) (qL l)) ≤ 1 + cnt FXL l := by
  classical
  let T : Finset ℕ := insert 0 ((FXL.filter (fun p => p.1 == l)).map Prod.snd).toFinset
  have hT : T.card ≤ 1 + cnt FXL l := by
    refine (Finset.card_insert_le _ _).trans ?_
    rw [Nat.add_comm 1]
    refine Nat.add_le_add_right ((List.toFinset_card_le _).trans ?_) 1
    rw [List.length_map, cnt, List.countP_eq_length_filter]
  have hidx : ∀ k : stabilizer (↥X0Sub) (qL l), ∃ t, t ∈ T ∧ t < 6720 ∧
      PR ((k : ↥X0Sub) : J)⁻¹ (CFSG.KD.X0O.MSF t) := by
    intro k
    have hk : ((k : ↥X0Sub) : J) ∈ X0Sub := (k : ↥X0Sub).2
    obtain ⟨t, ht, hPR⟩ := PR_X0 (X0Sub.inv_mem hk)
    have hfix : ((k : ↥X0Sub) : J) • qL l = qL l := k.2
    refine ⟨t, ?_, ht, hPR⟩
    rcases lane_fix hl hk hfix ht hPR with h | h
    · rw [h]
      exact Finset.mem_insert_self _ _
    · refine Finset.mem_insert_of_mem (List.mem_toFinset.2 (List.mem_map.2 ⟨(l, t), ?_, rfl⟩))
      exact List.mem_filter.2 ⟨h, by simp⟩
  choose f hfT _ hfPR using hidx
  have hinj : Function.Injective fun k => (⟨f k, hfT k⟩ : T) := by
    intro k k' e
    have e' : f k = f k' := congrArg Subtype.val e
    have h1 := hfPR k
    rw [e'] at h1
    have := PR_eq h1 (hfPR k')
    rw [inv_inj] at this
    exact Subtype.ext (Subtype.ext this)
  calc Nat.card (stabilizer (↥X0Sub) (qL l)) ≤ Nat.card T := Nat.card_le_card_of_injective _ hinj
    _ = T.card := Nat.card_eq_finsetCard T
    _ ≤ 1 + cnt FXL l := hT

theorem card_orbL {l : ℕ} (hl : l < NL) :
    6720 / (1 + cnt FXL l) ≤ (orbL l).ncard := by
  have h1 := Subgroup.card_mul_index (stabilizer (↥X0Sub) (qL l))
  rw [index_stabilizer, card_X0Sub matFacts] at h1
  have h2 := card_stab_le hl
  have hpos : 0 < Nat.card (stabilizer (↥X0Sub) (qL l)) := Nat.card_pos
  calc 6720 / (1 + cnt FXL l) ≤ 6720 / Nat.card (stabilizer (↥X0Sub) (qL l)) :=
        Nat.div_le_div_left h2 hpos
    _ = (orbL l).ncard := by
        rw [← h1, Nat.mul_div_cancel_left _ hpos]

theorem orbL_disj {l m : ℕ} (hl : l < NL) (hm : m < NL)
    (hlm : l ≠ m) : Disjoint (orbL l) (orbL m) := by
  rw [Set.disjoint_left]
  intro x hxl hxm
  obtain ⟨k, hk, rfl⟩ := mem_orbL.1 hxl
  obtain ⟨k', hk', e⟩ := mem_orbL.1 hxm
  have key : ∀ {i j : ℕ}, i < NL → j < NL → ∀ {g : J}, g ∈ X0Sub → g • qL i = qL j →
      laneV R i ≤ laneV R j := by
    intro i j hi hj g hg e
    obtain ⟨p, hp, hle, hlt⟩ := lane_le hi hg
    rw [e] at hp
    rw [rho_inj (laneR_lt j) hlt hp]
    exact hle
  have e1 : (k'⁻¹ * k) • qL l = qL m := by rw [mul_smul, ← e, inv_smul_smul]
  have e2 : (k⁻¹ * k') • qL m = qL l := by rw [mul_smul, e, inv_smul_smul]
  have h1 := key hl hm (X0Sub.mul_mem (X0Sub.inv_mem hk') hk) e1
  have h2 := key hm hl (X0Sub.mul_mem (X0Sub.inv_mem hk) hk') e2
  rcases Nat.lt_or_gt_of_ne hlm with h | h
  · exact absurd (lane_strict h hm) (by omega)
  · exact absurd (lane_strict h hl) (by omega)

theorem step_elt (s : ℕ × ℕ × ℕ) (l : ℕ) : ∃ σ : J, ∀ x < 2 ^ 112,
    stepV Ai Bi B s.1 s.2.1 s.2.2 l x < 2 ^ 112 ∧
      rho (stepV Ai Bi B s.1 s.2.1 s.2.2 l x) = σ • rho x := by
  unfold stepV
  by_cases hA : s.1.testBit l
  · exact ⟨a, fun x hx => by
      rw [if_pos hA]
      exact ⟨vecJ_lt _ _, (act' PR_Ai hx).symm⟩⟩
  · by_cases hB : s.2.1.testBit l
    · exact ⟨b, fun x hx => by
        rw [if_neg hA, if_pos hB]
        exact ⟨vecJ_lt _ _, (act' PR_Bi hx).symm⟩⟩
    · by_cases hC : s.2.2.testBit l
      · exact ⟨b⁻¹, fun x hx => by
          rw [if_neg hA, if_neg hB, if_pos hC]
          exact ⟨vecJ_lt _ _, (act PR_B hx).symm⟩⟩
      · exact ⟨1, fun x hx => by
          rw [if_neg hA, if_neg hB, if_neg hC, one_smul]
          exact ⟨hx, rfl⟩⟩

theorem walk_elt (l : ℕ) : ∀ S : List (ℕ × ℕ × ℕ), ∃ w : J, ∀ x < 2 ^ 112,
    walkV Ai Bi B S l x < 2 ^ 112 ∧ rho (walkV Ai Bi B S l x) = w • rho x
  | [] => ⟨1, fun x hx => ⟨hx, (one_smul _ _).symm⟩⟩
  | s :: S => by
    obtain ⟨σ, hσ⟩ := step_elt s l
    obtain ⟨w, hw⟩ := walk_elt l S
    refine ⟨w * σ, fun x hx => ?_⟩
    have e : walkV Ai Bi B (s :: S) l x = walkV Ai Bi B S l (stepV Ai Bi B s.1 s.2.1 s.2.2 l x) :=
      rfl
    obtain ⟨h1, h2⟩ := hσ x hx
    obtain ⟨h3, h4⟩ := hw _ h1
    rw [e, mul_smul, ← h2]
    exact ⟨h3, h4⟩

theorem rho_iterF : ∀ (k : ℕ) {x : ℕ}, x < 2 ^ 112 →
    iterF k x < 2 ^ 112 ∧ rho (iterF k x) = (fiveElt⁻¹) ^ k • rho x
  | 0, x, hx => ⟨hx, (one_smul _ _).symm⟩
  | k + 1, x, hx => by
    obtain ⟨h1, h2⟩ := rho_iterF k hx
    rw [iterF_succ, ← act PR_F h1, h2, ← mul_smul, ← pow_succ']
    exact ⟨vecJ_lt _ _, rfl⟩

theorem walk_root {l : ℕ} (hl : l < NL) :
    ∃ w : J, (∀ x < 2 ^ 112, walkV Ai Bi B WS l x < 2 ^ 112 ∧
      rho (walkV Ai Bi B WS l x) = w • rho x) ∧ w • qL l = w₀ := by
  obtain ⟨w, hw⟩ := walk_elt l WS
  refine ⟨w, hw, ?_⟩
  have h := walk_lane (k := 0) (by omega) hl
  rw [laneV_target0 hl] at h
  have e : iterF 0 (laneV R l) = laneV R l := rfl
  rw [e] at h
  rw [← (hw _ (laneR_lt l)).2, h, rho_v2N]
  rfl

theorem orbL_sub {l : ℕ} (hl : l < NL) : orbL l ⊆ Pts := by
  intro x hx
  obtain ⟨k, -, rfl⟩ := mem_orbL.1 hx
  obtain ⟨w, -, hw⟩ := walk_root hl
  exact ⟨k * w⁻¹, by rw [mul_smul, ← hw, inv_smul_smul]⟩

theorem stab_w0 :
    stabilizer J w₀ = Hj := by
  have h := CertificateChecks.KernelJ4Count.stabilizer_v_eq_Hj'
  rwa [CertificateChecks.KernelJ4Count.v_eq_root] at h

theorem card_Pts :
    Pts.ncard = 173067389 := by
  have e : Pts = orbit J w₀ := by
    ext x
    rw [mem_orbit_iff]
    rfl
  have hs : stabilizer J w₀ = Hj := stab_w0
  have h1 := Subgroup.card_mul_index (stabilizer J w₀)
  rw [index_stabilizer, ← e, hs, CertificateChecks.KernelJ4Count.card_Hj',
    CertificateChecks.KernelJ4Hub.card_J'] at h1
  omega

noncomputable def orbF (l : ℕ) : Finset Row := (Set.toFinite (orbL l)).toFinset

noncomputable def ptsF : Finset Row := (Set.toFinite Pts).toFinset

open Classical in
@[irreducible] noncomputable def covU : Finset Row := (Finset.range NL).biUnion orbF

open Classical in
theorem mem_covU {x : Row} : x ∈ covU ↔ ∃ l < NL, x ∈ orbL l := by
  unfold covU orbF
  simp only [Finset.mem_biUnion, Finset.mem_range, Set.Finite.mem_toFinset, exists_prop]

theorem lanes_cover
    {p : Row} (hp : p ∈ Pts) : ∃ l < NL, p ∈ orbL l := by
  classical
  have hU : (covU).card = ∑ l ∈ Finset.range NL, (orbF l).card := by
    unfold covU
    refine Finset.card_biUnion fun l hl m hm hlm => ?_
    exact Set.Finite.disjoint_toFinset.2
      (orbL_disj (Finset.mem_range.1 hl) (Finset.mem_range.1 hm) hlm)
  have hge : 173067389 ≤ (covU).card := by
    rw [hU, ← sum_lanes]
    refine Finset.sum_le_sum fun l hl => ?_
    rw [orbF, ← Set.ncard_eq_toFinset_card]
    exact card_orbL (Finset.mem_range.1 hl)
  have hP : ptsF.card = 173067389 := by
    rw [ptsF, ← Set.ncard_eq_toFinset_card, card_Pts]
  have hsub : covU ⊆ ptsF := by
    intro x hx
    have h := (mem_covU (x := x)).1 hx
    obtain ⟨l, hl, hx⟩ := h
    rw [ptsF, Set.Finite.mem_toFinset]
    exact orbL_sub hl hx
  have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hP]; exact hge)
  have hpU : p ∈ covU := by
    rw [heq, ptsF, Set.Finite.mem_toFinset]
    exact hp
  exact mem_covU.1 hpU

section Eta

variable {G : Type*} [Group G]

theorem eta_len_zero (u : ℕ → G) (c : ℕ) : eta u 0 c = 1 := rfl

theorem eta_add (u : ℕ → G) (m : ℕ) : ∀ n c,
    eta u (m + n) c = eta u m c * eta (fun i => u (m + i)) n (c >>> m)
  | 0, c => by rw [Nat.add_zero, eta_len_zero, mul_one]
  | n + 1, c => by
    rw [← Nat.add_assoc, eta_succ, eta_add u m n c, eta_succ, mul_assoc, Nat.testBit_shiftRight]

theorem eta_congr (u : ℕ → G) : ∀ n {a b : ℕ}, (∀ i < n, a.testBit i = b.testBit i) →
    eta u n a = eta u n b
  | 0, _, _, _ => rfl
  | n + 1, a, b, h => by
    rw [eta_succ, eta_succ, eta_congr u n (fun i hi => h i (by omega)), h n (by omega)]

end Eta

theorem rho_prodV (j0 a : ℕ) : ∀ k, j0 + k ≤ 11 → ∀ x < 2 ^ 112,
    prodV Mf j0 a k x < 2 ^ 112 ∧
      rho (prodV Mf j0 a k x) = (eta (fun i => uJ (j0 + i)) k a)⁻¹ • rho x
  | 0, _, x, hx => ⟨hx, by rw [eta_len_zero, inv_one, one_smul]; rfl⟩
  | k + 1, hk, x, hx => by
    obtain ⟨h1, h2⟩ := rho_prodV j0 a k (by omega) x hx
    rw [prodV_succ, eta_succ]
    split_ifs with hb
    · rw [← act (PR_U (by omega)) h1, h2, ← mul_smul, mul_inv_rev]
      exact ⟨vecJ_lt _ _, rfl⟩
    · rw [mul_one]
      exact ⟨h1, h2⟩

theorem d4_wf : ∀ j < 30, (d4Reps[j]!).wf = true := by decide

theorem comm_of_X0 {κ : J} (hκ : κ ∈ X0Sub) :
    κ * fiveElt = fiveElt * κ := by
  exact (Subgroup.mem_centralizer_singleton_iff (G := ↥J) (g := fiveElt) (k := κ)).1
    (X0Sub_le_centralizer matFacts hκ)

theorem pent_lane
    {p : Row} {v : ↥J} (h : PentCand p v) :
    ∃ l < NL, ∃ κ ∈ X0Sub, κ • qL l = p ∧ PentCand (qL l) (κ⁻¹ * v * κ) := by
  have hp : p ∈ Pts := h.1
  obtain ⟨l, hl, hpl⟩ := lanes_cover hp
  obtain ⟨κ, hκ, hκp⟩ := mem_orbL.1 hpl
  exact ⟨l, hl, κ, hκ, hκp, pentCand_conj (comm_of_X0 hκ) hκp.symm h⟩

theorem pent_cover
    (p : Row) (v : ↥J)
    (h : PentCand p v) :
    ∃ k ∈ X0Sub, ∃ q ∈ {q : Row | ∃ w ∈ d4Reps.toList, q = toRow w.toVec}, p = k • q := by
  have hF : Finite J := CertificateChecks.KernelJ4Hub.finite_J
  obtain ⟨l, hl, κ, hκ, hκp, hq⟩ := pent_lane h
  obtain ⟨-, hv1, -, hR, hxne, hfix⟩ := hq
  obtain ⟨w, hw, hw0⟩ := walk_root hl
  have hE : w * (κ⁻¹ * v * κ) * w⁻¹ ∈ Eg uJ 11 := by
    obtain ⟨g, hg, hgE⟩ := hR
    have hh : w * g ∈ Hj := by
      rw [← stab_w0, mem_stabilizer_iff, mul_smul, hg, hw0]
    have e : w * (κ⁻¹ * v * κ) * w⁻¹ =
        (w * g) * (g⁻¹ * (κ⁻¹ * v * κ) * g) * (w * g)⁻¹ := by group
    rw [e]
    exact Hj_normalizes_Eg matFacts _ hh _ hgE
  obtain ⟨c, hc, hcv⟩ := (mem_Eg_iff (elem_uJ matFacts)).1 hE
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [eta_zero] at hcv
    apply hv1
    have e : κ⁻¹ * v * κ = w⁻¹ * (w * (κ⁻¹ * v * κ) * w⁻¹) * w := by group
    rw [e, hcv]
    group
  have hinv : ∃ n : ℕ, fiveElt⁻¹ = fiveElt ^ n := by
    refine ⟨orderOf fiveElt - 1, inv_eq_of_mul_eq_one_right ?_⟩
    rw [← pow_succ', Nat.sub_add_cancel (orderOf_pos fiveElt), pow_orderOf_eq_one]
  obtain ⟨n, hn⟩ := hinv
  have hz : ∀ k < 4, eta uJ 11 c • rho (laneV (Z.getD k []) l) = rho (laneV (Z.getD k []) l) := by
    intro k hk
    have hwl := walk_lane (k := k + 1) (by omega) hl
    rw [laneV_target_succ] at hwl
    obtain ⟨hi1, hi2⟩ := rho_iterF (k + 1) (laneR_lt l)
    have e : rho (laneV (Z.getD k []) l) = w • ((fiveElt⁻¹) ^ (k + 1) • qL l) := by
      rw [← hwl, (hw _ hi1).2, hi2]
    have hy : (κ⁻¹ * v * κ) • ((fiveElt⁻¹) ^ (k + 1) • qL l) = (fiveElt⁻¹) ^ (k + 1) • qL l := by
      rw [hn, ← pow_mul]
      exact hfix _
    rw [e, ← hcv, mul_smul, mul_smul, inv_smul_smul, hy]
  have hc' : c < 2048 := by simpa using hc
  have ha : c % 32 < 32 := Nat.mod_lt _ (by omega)
  have hb : c >>> 5 < 64 := by rw [Nat.shiftRight_eq_div_pow]; omega
  have hab : c % 32 ≠ 0 ∨ c >>> 5 ≠ 0 := by
    rw [Nat.shiftRight_eq_div_pow]
    by_cases h1 : c % 32 = 0
    · right
      omega
    · exact Or.inl h1
  have hlow : eta uJ 5 c = eta (fun i => uJ (0 + i)) 5 (c % 32) := by
    have e : (fun i => uJ (0 + i)) = uJ := funext fun i => by rw [Nat.zero_add]
    rw [e]
    refine eta_congr uJ 5 fun i hi => ?_
    rw [show (32 : ℕ) = 2 ^ 5 from rfl, Nat.testBit_mod_two_pow]
    simp [hi]
  have hsplit : eta uJ 11 c = eta (fun i => uJ (0 + i)) 5 (c % 32) *
      eta (fun i => uJ (5 + i)) 6 (c >>> 5) := by
    rw [show (11 : ℕ) = 5 + 6 from rfl, eta_add, hlow]
  have hel : Elem (fun i => uJ (5 + i)) 6 := by
    have h := elem_uJ matFacts
    exact ⟨fun j hj => h.sq (5 + j) (by omega),
      fun i hi j hj => h.comm (5 + i) (by omega) (5 + j) (by omega)⟩
  have hE2 : (eta (fun i => uJ (5 + i)) 6 (c >>> 5))⁻¹ = eta (fun i => uJ (5 + i)) 6 (c >>> 5) :=
    inv_eq_of_mul_eq_one_right (eta_sq hel _)
  have heq : ∀ k < 4, prodV Mf 0 (c % 32) 5 (laneV (Z.getD k []) l) =
      prodV Mf 5 (c >>> 5) 6 (laneV (Z.getD k []) l) := by
    intro k hk
    have hzl : laneV (Z.getD k []) l < 2 ^ 112 := by
      have := laneV_lt (Z.getD k []) l
      rwa [(Zk_parts hk).1] at this
    obtain ⟨a1, a2⟩ := rho_prodV 0 (c % 32) 5 (by omega) _ hzl
    obtain ⟨b1, b2⟩ := rho_prodV 5 (c >>> 5) 6 (by omega) _ hzl
    refine rho_inj a1 b1 ?_
    rw [a2, b2, hE2]
    have hzk := hz k hk
    rw [hsplit] at hzk
    calc (eta (fun i => uJ (0 + i)) 5 (c % 32))⁻¹ • rho (laneV (Z.getD k []) l)
        = (eta (fun i => uJ (0 + i)) 5 (c % 32))⁻¹ • ((eta (fun i => uJ (0 + i)) 5 (c % 32) *
            eta (fun i => uJ (5 + i)) 6 (c >>> 5)) • rho (laneV (Z.getD k []) l)) := by
          rw [hzk]
      _ = eta (fun i => uJ (5 + i)) 6 (c >>> 5) • rho (laneV (Z.getD k []) l) := by
          rw [mul_smul, inv_smul_smul]
  have hDL := etest_lane hl ha hb hab heq
  rcases des_lane hDL with hLF | ⟨j, hj, hjl⟩
  · exfalso
    apply hxne
    subst hLF
    have e := act PR_F (laneR_lt LF)
    rw [lf_fix] at e
    calc fiveElt • qL LF = fiveElt • (fiveElt⁻¹ • qL LF) := by rw [e]
      _ = qL LF := smul_inv_smul _ _
  · obtain ⟨g, hg, hPR⟩ := X0_of_lt (wd_lt hj)
    have hd := bnd_parts.2.2 j hj
    have hdl : v2N (d4Reps[j]!) < 2 ^ 112 := v2N_lt112 (d4_wf j hj)
    have e2 : vecJ (2 ^ 112 - 1) (v2N (d4Reps[j]!)) (CFSG.KD.X0O.MSF (WD.getD j (0, 0)).2) =
        laneV R l := by
      rw [← hd, wit_lane hj, hjl]
    have e := act hPR hdl
    rw [e2, rho_v2N] at e
    have hs : d4Reps.size = 30 := rfl
    refine ⟨κ * g⁻¹, X0Sub.mul_mem hκ (X0Sub.inv_mem hg), toRow (d4Reps[j]!).toVec,
      ⟨d4Reps[j]!, ?_, rfl⟩, ?_⟩
    · rw [getElem!_pos d4Reps j (by rw [hs]; exact hj)]
      exact Array.getElem_mem_toList _
    · rw [← hκp, mul_smul, e]

end CertificateChecks.KernelJ4Pent

end
