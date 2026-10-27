module

public import Certificates.Kernel.Fi23Pair.ChkDefs
public import CFSG.Certificates.Kernel.Fi23Pair.Sound
public import Certificates.Kernel.Fi23Pump.Glue
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabFi23Cent
import Certificates.Kernel.Fi23Pair.Chk
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import Mathlib

public section

namespace CertificateChecks.KernelFi23Pair

open CFSG.Sporadic.Th (idx idx_mul idx_one idx_of_lt)
open CFSG.Sporadic.Fi23 CFSG.KC.Fi23K CFSG.KC.Fi23Pump CFSG.KC.Fi23Pair CFSG.KD.Fi23K
  CFSG.KD.Fi23Pair CFSG.KS.Fi23Pump CFSG.KS.Fi23Pair CertificateChecks.KernelFi23Q
  CertificateChecks.KernelFi23Pump
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23 (t3)
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Sylow (eq_of_base)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Pair


theorem aR_ok : ∀ r ∈ aR, RegOK r := by
  have h : ∀ r ∈ aR, r < 10 ∨ (52 ≤ r ∧ r < 76) := by decide +kernel
  exact h

theorem bR_ok : ∀ r ∈ bR, RegOK r := by
  have h : ∀ r ∈ bR, r < 10 ∨ (52 ≤ r ∧ r < 76) := by decide +kernel
  exact h

theorem sR_ok : ∀ r ∈ sR, RegOK r := powW_ok (ok_append aR_ok bR_ok) 4

theorem t0R_prod : wE t0R = t3 0 := by
  have h := t3R_prod (c := 0) (by norm_num)
  exact h

theorem t0R_ok : ∀ r ∈ t0R, RegOK r := t3R_ok (c := 0) (by norm_num)

theorem wE_sR : wE sR = (wE aR * wE bR) ^ 4 := by
  unfold sR
  rw [wE_powW, wE_append]

theorem smul_eq_of_wv {w : List ℕ} (hw : ∀ r ∈ w, RegOK r) {x y : ℕ} (hx : x < 31671)
    (hy : y < 31671) (h : wv G w x = y) : wE w • (⟨x, hx⟩ : Fin 31671) = ⟨y, hy⟩ := by
  apply Fin.ext
  rw [← idx_of_lt (wE w) hx]
  unfold wE
  rw [← wvG_eq w hw x hx, h]

theorem ord_facts {w : List ℕ} (hw : ∀ r ∈ w, RegOK r) (h : ordK G 7 w t0R = true) :
    orderOf (wE w) = 7 ∧ wE w * t3 0 = t3 0 * wE w := by
  obtain ⟨h1, h2, h3⟩ := ordK_spec h
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have h7 : wE w ^ 7 = 1 := by
    rw [← wE_powW]
    refine eq_of_base fun t ht => ?_
    rw [idx_one]
    unfold wE
    rw [← wvG_eq _ (powW_ok hw 7) t (by omega), h1 t ht]
    rfl
  have hne : wE w ≠ 1 := by
    intro h1'
    refine h2 fun b hb => ?_
    rw [wvG_eq w hw b (by omega)]
    change idx 31671 (wE w) b = b
    rw [h1', idx_one]
  refine ⟨orderOf_eq_prime h7 hne, ?_⟩
  rw [← t0R_prod, ← wE_append, ← wE_append]
  refine eq_of_base fun t ht => ?_
  unfold wE
  rw [← wvG_eq _ (ok_append hw t0R_ok) t (by omega), ← wvG_eq _ (ok_append t0R_ok hw) t (by omega)]
  exact h3 t ht

theorem a_facts : orderOf (wE aR) = 7 ∧ wE aR * t3 0 = t3 0 * wE aR := by
  have h := ch214034a_ok
  unfold aK at h
  exact ord_facts aR_ok h

theorem b_facts : orderOf (wE bR) = 7 ∧ wE bR * t3 0 = t3 0 * wE bR := by
  have h := ch214034b_ok
  unfold bK at h
  exact ord_facts bR_ok h

@[expose] def root363 : Fin 31671 := ⟨363, by norm_num⟩

theorem s_facts : orderOf (wE sR) = 3 ∧ wE sR • root363 = root363 ∧ t3 0 • root363 = root363 := by
  have h := ch214034s_ok
  unfold sK at h
  obtain ⟨h1, h2, h3, h4⟩ := stK_spec h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3' : wE sR ^ 3 = 1 := by
    rw [← wE_powW]
    refine eq_of_base fun t ht => ?_
    rw [idx_one]
    unfold wE
    rw [← wvG_eq _ (powW_ok sR_ok 3) t (by omega), h1 t ht]
    rfl
  have hne : wE sR ≠ 1 := by
    intro h1'
    refine h2 fun b hb => ?_
    rw [wvG_eq sR sR_ok b (by omega)]
    change idx 31671 (wE sR) b = b
    rw [h1', idx_one]
  refine ⟨orderOf_eq_prime h3' hne, smul_eq_of_wv sR_ok _ _ h3, ?_⟩
  rw [← t0R_prod]
  exact smul_eq_of_wv t0R_ok _ _ h4

@[expose] def InOrbR (K : Subgroup J) (r x : ℕ) : Prop := ∃ g ∈ K, idx 31671 g r = x

theorem inOrbR_step {K : Subgroup J} {r : ℕ} {w : List ℕ} (hw : ∀ r ∈ w, RegOK r)
    (hy : wE w ∈ K) : ∀ q < 31671, InOrbR K r q → InOrbR K r (wv G w q) := by
  rintro q hq ⟨g, hg, hgq⟩
  refine ⟨wE w * g, K.mul_mem hy hg, ?_⟩
  rw [idx_mul, hgq, wvG_eq w hw q hq]
  rfl

theorem dvd_card_closure
    (hfix : Nat.card {r : Fin 31671 // t3 0 • r = r} = 351) :
    81 ∣ Nat.card (Subgroup.closure ({wE aR, wE bR} : Set J)) := by
  classical
  have : Finite J := Nat.finite_of_card_ne_zero (by rw [card_J]; norm_num)
  set K := Subgroup.closure ({wE aR, wE bR} : Set J) with hKdef
  have haK : wE aR ∈ K := Subgroup.subset_closure (Set.mem_insert _ _)
  have hbK : wE bR ∈ K := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hKle : K ≤ Subgroup.centralizer ({t3 0} : Set J) := by
    rw [hKdef, Subgroup.closure_le]
    intro y hy
    rcases hy with rfl | rfl
    · exact (Subgroup.mem_centralizer_singleton_iff (g := t3 0) (k := wE aR)).2 a_facts.2
    · exact (Subgroup.mem_centralizer_singleton_iff (g := t3 0) (k := wE bR)).2 b_facts.2
  have hKC : ∀ g ∈ K, g * t3 0 = t3 0 * g := fun g hg =>
    (Subgroup.mem_centralizer_singleton_iff (g := t3 0) (k := g)).1 (hKle hg)
  obtain ⟨so, sfix, tfix⟩ := s_facts
  have hsK : wE sR ∈ K := by
    rw [wE_sR]
    exact pow_mem (mul_mem haK hbK) 4
  have hos : Nat.card (MulAction.orbit K root363) * Nat.card (MulAction.stabilizer K root363) =
      Nat.card K := by
    have : Fintype K := Fintype.ofFinite K
    have : Fintype (MulAction.orbit K root363) := Fintype.ofFinite _
    have : Fintype (MulAction.stabilizer K root363) := Fintype.ofFinite _
    have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group K root363
    simpa [Nat.card_eq_fintype_card] using h
  have hle : Nat.card (MulAction.orbit K root363) ≤ 351 := by
    rw [← hfix]
    have hsub : MulAction.orbit K root363 ⊆ {r : Fin 31671 | t3 0 • r = r} := by
      rintro _ ⟨g, rfl⟩
      change t3 0 • ((g : J) • root363) = (g : J) • root363
      rw [← mul_smul, ← hKC g g.2, mul_smul, tfix]
    exact Nat.card_mono (Set.toFinite _) hsub
  have hge : 351 ≤ Nat.card (MulAction.orbit K root363) := by
    have hok : orbK G aR bR P 351 363 = true := by
      have h := ch214034orb_ok
      unfold orbOK at h
      exact h
    obtain ⟨hR, hinc⟩ := orbK_spec hok (InOrbR K 363) ⟨1, K.one_mem, idx_one 363⟩
      (inOrbR_step aR_ok haK) (inOrbR_step bR_ok hbK)
    have hmem : ∀ i : Fin 351, (⟨ptE (recP P i.1), (hR i.1 i.2).1⟩ : Fin 31671) ∈
        MulAction.orbit K root363 := by
      intro i
      obtain ⟨g, hg, hgi⟩ := (hR i.1 i.2).2
      refine ⟨⟨g, hg⟩, ?_⟩
      apply Fin.ext
      change ((g : J) • (⟨363, by norm_num⟩ : Fin 31671)).val = _
      rw [← idx_of_lt g (by norm_num : 363 < 31671), hgi]
    let φ : Fin 351 → MulAction.orbit K root363 := fun i => ⟨_, hmem i⟩
    have hφ : Function.Injective φ := by
      intro i j hij
      have e : ptE (recP P i.1) = ptE (recP P j.1) :=
        congrArg Fin.val (congrArg Subtype.val hij)
      rcases lt_trichotomy i.1 j.1 with h | h | h
      · exact absurd e (hinc _ _ h j.2).ne
      · exact Fin.ext h
      · exact absurd e (hinc _ _ h i.2).ne'
    have := Nat.card_le_card_of_injective φ hφ
    rwa [Nat.card_eq_fintype_card, Fintype.card_fin] at this
  have h3 : 3 ∣ Nat.card (MulAction.stabilizer K root363) := by
    have hm : (⟨wE sR, hsK⟩ : K) ∈ MulAction.stabilizer K root363 := by
      rw [MulAction.mem_stabilizer_iff]
      exact sfix
    have h := orderOf_dvd_natCard (⟨⟨wE sR, hsK⟩, hm⟩ : MulAction.stabilizer K root363)
    rwa [Subgroup.orderOf_mk, Subgroup.orderOf_mk, so] at h
  have horb : Nat.card (MulAction.orbit K root363) = 351 := le_antisymm hle hge
  rw [← hos, horb]
  obtain ⟨m, hm⟩ := h3
  rw [hm]
  exact ⟨13 * m, by ring⟩

end Pair

section Facts


open CFSG.HardMathSupport.Dickson.I271.TabFi23 in
theorem card_cent_t3_two_dvd :
    Nat.card ↥(Subgroup.centralizer ({t3 2} : Set J)) ∣ 135 * (2 * (2 ^ 17 * 3 ^ 9)) := by
  obtain ⟨t, ht, hf, hc⟩ := classData_cent t3_classData.2.2.1
  have h := card_cent_dvd_of_fixN ht (Or.inr (Or.inr hf))
  rw [hc]
  exact Nat.mul_dvd_mul_left _ (Nat.mul_dvd_mul_left _ h)

open CFSG.HardMathSupport.Dickson.I271.TabFi23 in
theorem fact_3A : ∃ a ∈ Subgroup.centralizer ({t3 0} : Set J),
    ∃ b ∈ Subgroup.centralizer ({t3 0} : Set J), orderOf a = 7 ∧ orderOf b = 7 ∧
      81 ∣ Nat.card (Subgroup.closure ({a, b} : Set J)) := by
  obtain ⟨-, p, -, hN, -⟩ := t3_classData.1
  exact ⟨wE aR, Subgroup.mem_centralizer_singleton_iff.2 a_facts.2, wE bR,
    Subgroup.mem_centralizer_singleton_iff.2 b_facts.2, a_facts.1, b_facts.1,
    dvd_card_closure hN⟩

open CFSG.HardMathSupport.Dickson.I271.TabFi23 in
theorem fact_3B : ¬ 7 ∣ Nat.card (Subgroup.centralizer ({t3 1} : Set J)) :=
  fun h => absurd (h.trans card_cent_t3_one_dvd) (by norm_num)

theorem fact_3C : ¬ 7 ∣ Nat.card (Subgroup.centralizer ({t3 2} : Set J)) :=
  fun h => absurd (h.trans card_cent_t3_two_dvd) (by norm_num)

open CFSG.HardMathSupport.Dickson.I271.TabFi23 in
theorem fact_3D : ¬ 7 ∣ Nat.card (Subgroup.centralizer ({t3 3} : Set J)) :=
  fun h => absurd (h.trans card_cent_t3_three_dvd) (by norm_num)

end Facts

end CertificateChecks.KernelFi23Pair

end
