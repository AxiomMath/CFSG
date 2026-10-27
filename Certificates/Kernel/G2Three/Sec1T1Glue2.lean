module

public import Certificates.Kernel.G2Three.Sec1T1Glue
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.TabHom
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.G2Three.Sec1.T1Glue

open Subgroup CFSG.KC.Ord CFSG.KC.Loop CFSG.KD.G2Three CFSG.KC.G2Three CFSG.KC.G2Three.Sec1
  CFSG.OddStandard.HigherRank.G2Three.Sec1Proof CFSG.OddStandard.HigherRank.G2Three.Sec1Proof.Tab
  CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.KD.G2Three.Sec1.T5Glue CFSG.Open

variable {G : Type} [Group G] [Finite G] (m : G23Model G)

attribute [local irreducible] uE1

theorem tabQ {Q : Type} [Group Q] {c : Q → ℕ} {f : ℕ → ℕ → ℕ}
    (hf : ∀ a b, f (c a) (c b) = c (a * b)) {Y YG POS PA PB : ℕ → ℕ} {h : ℕ → Q} {n k : ℕ}
    (hY0 : Y 0 = c 1) (hYG : ∀ s < k, YG s = c (h s))
    (hY : ∀ i < n * k, Y (POS i) = f (Y (i / k)) (YG (i % k)))
    (hpar : ∀ i < n - 1, PA i ≤ i ∧ PB i < k ∧ POS (PA i * k + PB i) = i + 1) :
    ∀ i < n, ∃ q ∈ closure (h '' {s | s < k}), Y i = c q := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    rcases i with _ | i
    · exact ⟨1, one_mem _, hY0⟩
    · obtain ⟨hpa, hpb, hpos⟩ := hpar i (by omega)
      obtain ⟨q, hq, hYq⟩ := ih (PA i) (by omega) (by omega)
      obtain ⟨hlt, hdv, hmd⟩ := flat_facts (by omega) (show PA i < n by omega) hpb
      have e := hY _ hlt
      rw [hpos, hdv, hmd, hYq, hYG _ hpb, hf] at e
      exact ⟨q * h (PB i), mul_mem hq (subset_closure ⟨PB i, hpb, rfl⟩), e⟩

theorem tab_hom {Q : Type} [Group Q] {c : Q → ℕ} (hc : Function.Injective c) {f : ℕ → ℕ → ℕ}
    (hf : ∀ a b, f (c a) (c b) = c (a * b))
    {X Gd Y YG POS PA PB : ℕ → ℕ} {n k : ℕ} {g : ℕ → G} {h : ℕ → Q}
    (htab : TabOf m.ρ X n (closure (g '' {s | s < k}) : Set G))
    (hinj : ∀ i < n, ∀ j < n, X i = X j → i = j)
    (hg : ∀ s < k, Enc m.ρ (Gd s) (g s)) (h0 : X 0 = ONEP)
    (hcl : ∀ i < n * k, POS i < n ∧ X (POS i) = MULP (X (i / k)) (Gd (i % k)))
    (hpar : ∀ i < n - 1, PA i ≤ i ∧ PB i < k ∧ POS (PA i * k + PB i) = i + 1)
    (hY0 : Y 0 = c 1) (hYG : ∀ s < k, YG s = c (h s))
    (hY : ∀ i < n * k, Y (POS i) = f (Y (i / k)) (YG (i % k))) :
    ∃ F : G → Q, (∀ i < n, ∀ x : G, Enc m.ρ (X i) x → c (F x) = Y i) ∧
      (∀ s < k, F (g s) = h s) ∧
      ∀ x ∈ closure (g '' {s | s < k}), ∀ y ∈ closure (g '' {s | s < k}), F (x * y) = F x * F y := by
  classical
  have hYc : ∀ i < n, ∃ q, Y i = c q := fun i hi => by
    obtain ⟨q, -, e⟩ := tabQ hf hY0 hYG hY hpar i hi
    exact ⟨q, e⟩
  let F : G → Q := fun x =>
    if hx : ∃ q, ∃ i < n, Enc m.ρ (X i) x ∧ c q = Y i then Classical.choose hx else 1
  have hF : ∀ i < n, ∀ x, Enc m.ρ (X i) x → c (F x) = Y i := by
    intro i hi x hx
    obtain ⟨q, hq⟩ := hYc i hi
    have hex : ∃ q, ∃ i < n, Enc m.ρ (X i) x ∧ c q = Y i := ⟨q, i, hi, hx, hq.symm⟩
    have e : F x = Classical.choose hex := dif_pos hex
    obtain ⟨i', hi', hx', hc'⟩ := Classical.choose_spec hex
    rw [e, hc', hinj i' hi' i hi (enc_inj hx' hx)]
  have hn : 0 < n := by
    obtain ⟨i, hi, -⟩ := htab.2 1 (one_mem _)
    omega
  have henc0 : Enc m.ρ (X 0) 1 := by
    rw [h0]
    exact enc_one m.ρ
  have hF1 : F 1 = 1 := hc (by rw [hF 0 hn 1 henc0, hY0])
  have hstep : ∀ x ∈ closure (g '' {s | s < k}), ∀ s < k, F (x * g s) = F x * h s := by
    intro x hx s hs
    obtain ⟨i, hi, hxi⟩ := htab.2 x hx
    obtain ⟨hlt, hdv, hmd⟩ := flat_facts (by omega) hi hs
    obtain ⟨hp, hXe⟩ := hcl _ hlt
    rw [hdv, hmd] at hXe
    have he : Enc m.ρ (X (POS (i * k + s))) (x * g s) := by
      rw [hXe]
      exact enc_mul m.ρ hxi (hg s hs)
    apply hc
    rw [hF _ hp _ he, hY _ hlt, hdv, hmd, ← hF i hi x hxi, hYG s hs, hf]
  have hFg : ∀ s < k, F (g s) = h s := fun s hs => by
    have := hstep 1 (one_mem _) s hs
    rwa [one_mul, hF1, one_mul] at this
  refine ⟨F, hF, hFg, ?_⟩
  set K := closure (g '' {s | s < k}) with hK
  let T : Submonoid G :=
    { carrier := {y | y ∈ K ∧ ∀ x ∈ K, F (x * y) = F x * F y}
      one_mem' := ⟨one_mem _, fun x _ => by rw [mul_one, hF1, mul_one]⟩
      mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, fun x hx => by
        rw [← mul_assoc, hb.2 _ (mul_mem hx ha.1), ha.2 x hx, hb.2 a ha.1, mul_assoc]⟩ }
  have hTinv : ∀ y ∈ T, y⁻¹ ∈ T := by
    intro y hy
    have ho := orderOf_pos y
    have e : y ^ (orderOf y - 1) * y = 1 := by
      rw [← pow_succ, Nat.sub_add_cancel ho, pow_orderOf_eq_one]
    rw [← eq_inv_of_mul_eq_one_left e]
    exact T.pow_mem hy _
  let T' : Subgroup G := { T with inv_mem' := fun {y} hy => hTinv y hy }
  have hle : K ≤ T' := by
    rw [hK, closure_le]
    rintro _ ⟨s, hs, rfl⟩
    refine ⟨subset_closure ⟨s, hs, rfl⟩, fun x hx => ?_⟩
    rw [hstep x hx s hs, hFg s hs]
  intro x hx y hy
  exact (hle hy).2 x hx

@[expose] def cm (A : Matrix (Fin 2) (Fin 2) (ZMod 3)) : ℕ :=
  (A 0 0).val + 3 * (A 0 1).val + 9 * (A 1 0).val + 27 * (A 1 1).val

theorem dg3_eq (c p : ℕ) : dg3 c p = c / p % 3 := rfl

theorem dg3_cm (A : Matrix (Fin 2) (Fin 2) (ZMod 3)) :
    dg3 (cm A) 1 = (A 0 0).val ∧ dg3 (cm A) 3 = (A 0 1).val ∧ dg3 (cm A) 9 = (A 1 0).val ∧
      dg3 (cm A) 27 = (A 1 1).val := by
  have h0 := (A 0 0).val_lt
  have h1 := (A 0 1).val_lt
  have h2 := (A 1 0).val_lt
  have h3 := (A 1 1).val_lt
  simp only [dg3_eq, cm]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

theorem MUL22_eq (a b : ℕ) : MUL22 a b =
    (dg3 a 1 * dg3 b 1 + dg3 a 3 * dg3 b 9) % 3 + 3 * ((dg3 a 1 * dg3 b 3 + dg3 a 3 * dg3 b 27) % 3) +
      (9 * ((dg3 a 9 * dg3 b 1 + dg3 a 27 * dg3 b 9) % 3) +
        27 * ((dg3 a 9 * dg3 b 3 + dg3 a 27 * dg3 b 27) % 3)) := rfl

theorem MUL22_cm (A B : Matrix (Fin 2) (Fin 2) (ZMod 3)) : MUL22 (cm A) (cm B) = cm (A * B) := by
  obtain ⟨a0, a1, a2, a3⟩ := dg3_cm A
  obtain ⟨b0, b1, b2, b3⟩ := dg3_cm B
  rw [MUL22_eq, a0, a1, a2, a3, b0, b1, b2, b3]
  simp only [cm, Matrix.mul_apply, Fin.sum_univ_two, ZMod.val_add, ZMod.val_mul, ← Nat.add_mod]
  omega

theorem cm_inj {A B : Matrix (Fin 2) (Fin 2) (ZMod 3)} (h : cm A = cm B) : A = B := by
  obtain ⟨a0, a1, a2, a3⟩ := dg3_cm A
  obtain ⟨b0, b1, b2, b3⟩ := dg3_cm B
  rw [h] at a0 a1 a2 a3
  ext i j
  fin_cases i <;> fin_cases j
  · exact ZMod.val_injective _ (a0.symm.trans b0)
  · exact ZMod.val_injective _ (a1.symm.trans b1)
  · exact ZMod.val_injective _ (a2.symm.trans b2)
  · exact ZMod.val_injective _ (a3.symm.trans b3)

@[expose] def cSL (A : Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) : ℕ := cm A.1

theorem cSL_inj : Function.Injective cSL := fun _ _ h => Subtype.ext (cm_inj h)

theorem MUL22_cSL (A B : Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) :
    MUL22 (cSL A) (cSL B) = cSL (A * B) := MUL22_cm A.1 B.1

@[expose] def slG (s : ℕ) : Matrix.SpecialLinearGroup (Fin 2) (ZMod 3) :=
  if s = 0 then ⟨!![0, 1; 2, 2], by rw [Matrix.det_fin_two_of]; decide⟩
  else ⟨!![0, 2; 1, 0], by rw [Matrix.det_fin_two_of]; decide⟩

theorem r1KG_cSL : ∀ s < 2, R1KG s = cSL (slG s) := by
  intro s hs
  interval_cases s
  · exact (Nat.eq_of_beq_eq_true (m := 75) (by quickRfl)).trans (by decide)
  · exact (Nat.eq_of_beq_eq_true (m := 15) (by quickRfl)).trans (by decide)

theorem cSL_one : cSL 1 = 28 := by decide

theorem K1_iso : Nonempty (↥(frameOf m).K₁ ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) := by
  have h := r1_K1
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hp, hcP⟩, -⟩ := h
  have hy := r1_kY
  simp only [Bool.and_eq_true] at hy
  obtain ⟨hyF, hyS⟩ := hy
  have hcl := closP_at hcP (by norm_num)
  have hY := closF_at hyF (by norm_num)
  simp only [Nat.zero_add] at hcl hY
  obtain ⟨htab, -, hinj⟩ := tabK1 m
  have hg : ∀ s < 2, Enc m.ρ (R1U (R1K1G s)) (uE1 m (R1K1G s)) :=
    fun s hs => enc_uE1 m (by interval_cases s <;> simp [r1KG.1, r1KG.2.1])
  obtain ⟨F, hF, -, hmul⟩ := tab_hom m cSL_inj MUL22_cSL (g := fun s => uE1 m (R1K1G s))
    (Gd := fun s => R1U (R1K1G s)) (h := slG) htab hinj hg r1_ones.2.2.1 (fun i hi => hcl i hi)
    (parK_at hp (by norm_num)) (by rw [r1_ones.2.2.2.2.2.2.2.2.2.1, cSL_one]) r1KG_cSL
    (fun i hi => (hY i hi).2)
  rw [← K1_eq]
  set K := closure ((fun s => uE1 m (R1K1G s)) '' {s | s < 2})
  let φ : ↥K →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3) :=
    MonoidHom.mk' (fun x => F x) (fun x y => hmul x x.2 y y.2)
  have hYinj := sort_inj hyS (by norm_num)
  have hφ : Function.Injective φ := by
    intro x y hxy
    obtain ⟨i, hi, hxi⟩ := htab.2 x x.2
    obtain ⟨j, hj, hyj⟩ := htab.2 y y.2
    have e : R1KY i = R1KY j := by
      rw [← hF i hi x hxi, ← hF j hj y hyj]
      exact congrArg cSL hxy
    have hij := hYinj i hi j hj e
    subst hij
    exact Subtype.ext (enc_unique m.inj hxi hyj)
  have hcard : Nat.card K = Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) := by
    rw [(tabK1 m).2.1, card_SL23]
  exact ⟨MulEquiv.ofBijective φ (hφ.bijective_of_nat_card_le hcard.ge)⟩

theorem K2_iso : Nonempty (↥(frameOf m).K₂ ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) := by
  obtain ⟨e⟩ := K1_iso m
  have h := sigma_K1 m
  rw [← h]
  exact ⟨(Subgroup.equivMapOfInjective _ _ (MulAut.conj (frameOf m).σ).injective).symm.trans e⟩

@[expose] def c3 (p : Equiv.Perm (Fin 3)) : ℕ := (p 0).val + 4 * (p 1).val + 16 * (p 2).val

theorem MUL3_c3 : ∀ p q : Equiv.Perm (Fin 3), MUL3 (c3 p) (c3 q) = c3 (p * q) := by decide

theorem c3_inj : ∀ p q : Equiv.Perm (Fin 3), c3 p = c3 q → p = q := by decide

theorem c3_lt (p : Equiv.Perm (Fin 3)) : c3 p < 64 := by
  have h0 := (p 0).isLt
  have h1 := (p 1).isLt
  have h2 := (p 2).isLt
  simp only [c3]
  omega

@[expose] def c33 (x : Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) : ℕ := c3 x.1 + 64 * c3 x.2

theorem c33_parts (x : Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) :
    Nat.land (c33 x) 63 = c3 x.1 ∧ Nat.shiftRight (c33 x) 6 = c3 x.2 := by
  have h := c3_lt x.1
  have e63 : (63 : ℕ) = 2 ^ 6 - 1 := by norm_num
  change c33 x &&& 63 = _ ∧ c33 x >>> 6 = _
  rw [e63, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
  simp only [c33, Nat.reducePow]
  constructor <;> omega

theorem MUL33_c33 (x y : Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) :
    MUL33 (c33 x) (c33 y) = c33 (x * y) := by
  obtain ⟨hx1, hx2⟩ := c33_parts x
  obtain ⟨hy1, hy2⟩ := c33_parts y
  change Nat.add (MUL3 (Nat.land (c33 x) 63) (Nat.land (c33 y) 63))
    (Nat.shiftLeft (MUL3 (Nat.shiftRight (c33 x) 6) (Nat.shiftRight (c33 y) 6)) 6) = _
  rw [hx1, hx2, hy1, hy2, MUL3_c3, MUL3_c3]
  change c3 (x.1 * y.1) + c3 (x.2 * y.2) <<< 6 = _
  rw [Nat.shiftLeft_eq]
  simp only [c33, Prod.fst_mul, Prod.snd_mul, Nat.reducePow]
  omega

theorem c33_inj : Function.Injective c33 := by
  intro x y h
  obtain ⟨hx1, hx2⟩ := c33_parts x
  obtain ⟨hy1, hy2⟩ := c33_parts y
  rw [h] at hx1 hx2
  exact Prod.ext (c3_inj _ _ (hx1.symm.trans hy1)) (c3_inj _ _ (hx2.symm.trans hy2))

@[expose] def pG (s : ℕ) : Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3) :=
  [(finRotate 3 ^ 2, finRotate 3 ^ 2), (finRotate 3, finRotate 3 ^ 2),
    (Equiv.swap 1 2, Equiv.swap 1 2), (1, Equiv.swap 1 2)].getD s 1

@[expose] def pU (s : ℕ) : Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3) :=
  [(finRotate 3, finRotate 3), 1, (finRotate 3, finRotate 3 ^ 2), 1,
    (Equiv.swap 1 2, Equiv.swap 1 2), 1, 1, 1].getD s 1

theorem r1PG_c33 : ∀ s < 4, R1PG s = c33 (pG s) := by
  intro s hs
  interval_cases s
  · exact (Nat.eq_of_beq_eq_true (m := 1170) (by quickRfl)).trans (by decide)
  · exact (Nat.eq_of_beq_eq_true (m := 1161) (by quickRfl)).trans (by decide)
  · exact (Nat.eq_of_beq_eq_true (m := 1560) (by quickRfl)).trans (by decide)
  · exact (Nat.eq_of_beq_eq_true (m := 1572) (by quickRfl)).trans (by decide)

theorem r1PU_c33 : ∀ s < 8, R1PU s = c33 (pU s) := by
  intro s hs
  interval_cases s
  · exact (Nat.eq_of_beq_eq_true (m := 585) (by quickRfl)).trans (by decide)
  · exact (Nat.eq_of_beq_eq_true (m := 2340) (by quickRfl)).trans (by decide)
  · exact (Nat.eq_of_beq_eq_true (m := 1161) (by quickRfl)).trans (by decide)
  · exact (Nat.eq_of_beq_eq_true (m := 2340) (by quickRfl)).trans (by decide)
  · exact (Nat.eq_of_beq_eq_true (m := 1560) (by quickRfl)).trans (by decide)
  · exact (Nat.eq_of_beq_eq_true (m := 2340) (by quickRfl)).trans (by decide)
  · exact (Nat.eq_of_beq_eq_true (m := 2340) (by quickRfl)).trans (by decide)
  · exact (Nat.eq_of_beq_eq_true (m := 2340) (by quickRfl)).trans (by decide)

theorem c33_one : c33 1 = 2340 := by decide

theorem pG_closure : closure (pG '' {s | s < 4}) = ⊤ := by
  have h := r1_pI
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hp, hcF⟩, hs⟩ := h
  have hY := closF_at hcF (by norm_num)
  simp only [Nat.zero_add] at hY
  have hq := tabQ (n := 36) (k := 4) MUL33_c33 (by rw [r1_ones.2.2.2.2.2.2.2.2.2.2.2, c33_one]) r1PG_c33
    (fun i hi => (hY i hi).2) (parK_at hp (by norm_num))
  choose q hqmem hqc using hq
  have hinj := sort_inj hs (by norm_num)
  let e : Fin 36 → closure (pG '' {s | s < 4}) := fun i => ⟨q i i.2, hqmem i i.2⟩
  have he : Function.Injective e := fun i j hij => Fin.ext (hinj i i.2 j j.2 (by
    rw [hqc i i.2, hqc j j.2]
    exact congrArg (fun x => c33 x.1) hij))
  have h36 := Nat.card_le_card_of_injective e he
  have hle := Subgroup.card_le_card_group (closure (pG '' {s | s < 4}))
  rw [Nat.card_eq_fintype_card (α := Fin 36), Fintype.card_fin] at h36
  apply Subgroup.eq_top_of_card_eq
  rw [card_S3S3] at hle ⊢
  omega

theorem H_hom : ∃ F : G → Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3),
    (∀ i < 576, ∀ x : G, Enc m.ρ (R1H i) x → c33 (F x) = R1PY i) ∧
    (∀ s < 3, F (uE1 m (R1HG s)) = pG s) ∧
    ∀ x ∈ g23H m, ∀ y ∈ g23H m, F (x * y) = F x * F y := by
  have key : ∀ i lo, closP R1H (fun s => R1U (R1HG s)) R1HPOS 576 3 lo 432 7 = true → lo ≤ i →
      i < lo + 432 → R1HPOS i < 576 ∧ R1H (R1HPOS i) = MULP (R1H (i / 3)) (R1U (R1HG (i % 3))) := by
    intro i lo h h1 h2
    have := closP_at h (by norm_num) (i - lo) (by omega)
    rw [Nat.add_sub_cancel' h1] at this
    exact this
  have hcl : ∀ i < 576 * 3,
      R1HPOS i < 576 ∧ R1H (R1HPOS i) = MULP (R1H (i / 3)) (R1U (R1HG (i % 3))) := by
    intro i hi
    by_cases h0 : i < 432
    · exact key i 0 r1_closH0 (by omega) (by omega)
    by_cases h1 : i < 864
    · exact key i 432 r1_closH1 (by omega) (by omega)
    by_cases h2 : i < 1296
    · exact key i 864 r1_closH2 (by omega) (by omega)
    · exact key i 1296 r1_closH3 (by omega) (by omega)
  have keyY : ∀ i lo, closF MUL33 R1PY R1PG R1HPOS 576 3 lo 432 7 = true → lo ≤ i →
      i < lo + 432 → R1PY (R1HPOS i) = MUL33 (R1PY (i / 3)) (R1PG (i % 3)) := by
    intro i lo h h1 h2
    have := closF_at h (by norm_num) (i - lo) (by omega)
    rw [Nat.add_sub_cancel' h1] at this
    exact this.2
  have hY : ∀ i < 576 * 3, R1PY (R1HPOS i) = MUL33 (R1PY (i / 3)) (R1PG (i % 3)) := by
    intro i hi
    by_cases h0 : i < 432
    · exact keyY i 0 r1_pY0 (by omega) (by omega)
    by_cases h1 : i < 864
    · exact keyY i 432 r1_pY1 (by omega) (by omega)
    by_cases h2 : i < 1296
    · exact keyY i 864 r1_pY2 (by omega) (by omega)
    · exact keyY i 1296 r1_pY3 (by omega) (by omega)
  have hG : ∀ s < 3, R1HG s < 37 := by
    intro s hs
    interval_cases s <;> exact Nat.blt_eq.mp (by quickRfl)
  obtain ⟨F, hF, hFg, hmul⟩ := tab_hom m c33_inj MUL33_c33 (g := fun s => uE1 m (R1HG s))
    (Gd := fun s => R1U (R1HG s)) (h := pG) (tabH m) (H_inj) (fun s hs => enc_uE1 m (hG s hs))
    r1_ones.2.1 hcl (parK_at r1_parH (by norm_num))
    (by rw [r1_ones.2.2.2.2.2.2.2.2.2.2.1, c33_one]) (fun s hs => r1PG_c33 s (by omega)) hY
  rw [H_eq] at hmul
  exact ⟨F, hF, hFg, hmul⟩

theorem F_one_of {Q : Type} [Group Q] {H : Subgroup G} {F : G → Q}
    (hF : ∀ x ∈ H, ∀ y ∈ H, F (x * y) = F x * F y) : F 1 = 1 := by
  have := hF 1 (one_mem _) 1 (one_mem _)
  rw [mul_one] at this
  exact mul_eq_left.mp this.symm

theorem conj_of_gens {Q : Type} [Group Q] {S : Set G} {F : G → Q} {σ : G} {t : Q}
    (hσ2 : σ * σ = 1) (ht2 : t * t = 1) (hconj : ∀ h ∈ closure S, σ * h * σ⁻¹ ∈ closure S)
    (hF : ∀ x ∈ closure S, ∀ y ∈ closure S, F (x * y) = F x * F y)
    (hS : ∀ x ∈ S, F (σ * x * σ⁻¹) = t * F x * t) :
    ∀ h ∈ closure S, F (σ * h * σ⁻¹) = t * F h * t := by
  have hF1 : F 1 = 1 := F_one_of hF
  have hFinv : ∀ x ∈ closure S, F x⁻¹ = (F x)⁻¹ := fun x hx => by
    have := hF x hx x⁻¹ (inv_mem hx)
    rw [mul_inv_cancel, hF1] at this
    exact eq_inv_of_mul_eq_one_right this.symm
  have hti : t⁻¹ = t := (eq_inv_of_mul_eq_one_left ht2).symm
  intro h hh
  induction hh using Subgroup.closure_induction with
  | mem x hx => exact hS x hx
  | one => rw [mul_one, mul_inv_cancel, hF1, mul_one, ht2]
  | mul x y hx hy ihx ihy =>
    have e : σ * (x * y) * σ⁻¹ = (σ * x * σ⁻¹) * (σ * y * σ⁻¹) := by group
    rw [e, hF _ (hconj x hx) _ (hconj y hy), ihx, ihy, hF x hx y hy]
    calc t * F x * t * (t * F y * t) = t * F x * (t * t) * F y * t := by group
      _ = t * (F x * F y) * t := by rw [ht2, mul_one, mul_assoc t]
  | inv x hx ih =>
    have e : σ * x⁻¹ * σ⁻¹ = (σ * x * σ⁻¹)⁻¹ := by group
    rw [e, hFinv _ (hconj x hx), ih, hFinv x hx]
    calc (t * F x * t)⁻¹ = t⁻¹ * (F x)⁻¹ * t⁻¹ := by group
      _ = t * (F x)⁻¹ * t := by rw [hti]

theorem ext_sigma {Q : Type} [Group Q] {H T : Subgroup G} {σ : G} {F : G → Q} {t : Q}
    (hσ2 : σ * σ = 1) (hσH : σ ∉ H) (hconjH : ∀ h ∈ H, σ * h * σ⁻¹ ∈ H)
    (hT : ∀ g ∈ T, g ∈ H ∨ g * σ ∈ H) (hHT : H ≤ T) (hσT : σ ∈ T)
    (hF : ∀ x ∈ H, ∀ y ∈ H, F (x * y) = F x * F y) (ht2 : t * t = 1)
    (hFc : ∀ h ∈ H, F (σ * h * σ⁻¹) = t * F h * t) :
    ∃ φ : ↥T →* Q, (∀ (h : G) (hh : h ∈ H), φ ⟨h, hHT hh⟩ = F h) ∧ φ ⟨σ, hσT⟩ = t := by
  classical
  have hσi : σ⁻¹ = σ := (eq_inv_of_mul_eq_one_left hσ2).symm
  let F' : G → Q := fun g => if g ∈ H then F g else F (g * σ) * t
  have hA : ∀ a ∈ H, F' a = F a := fun a ha => if_pos ha
  have hB : ∀ a ∈ H, F' (a * σ) = F a * t := fun a ha => by
    have hn : a * σ ∉ H := fun h => hσH (by
      have := mul_mem (inv_mem ha) h
      rwa [← mul_assoc, inv_mul_cancel, one_mul] at this)
    have e : a * σ * σ = a := by rw [mul_assoc, hσ2, mul_one]
    change (if a * σ ∈ H then F (a * σ) else F (a * σ * σ) * t) = _
    rw [if_neg hn, e]
  have hform : ∀ g ∈ T, ∃ a ∈ H, a = g ∨ a * σ = g := by
    intro g hg
    rcases hT g hg with h | h
    · exact ⟨g, h, Or.inl rfl⟩
    · refine ⟨g * σ, h, Or.inr ?_⟩
      rw [mul_assoc, hσ2, mul_one]
  have hmul : ∀ x ∈ T, ∀ y ∈ T, F' (x * y) = F' x * F' y := by
    intro x hx y hy
    obtain ⟨a, ha, rfl | rfl⟩ := hform x hx <;> obtain ⟨b, hb, rfl | rfl⟩ := hform y hy
    · rw [hA _ (mul_mem ha hb), hA a ha, hA b hb, hF a ha b hb]
    · rw [← mul_assoc, hB _ (mul_mem ha hb), hA a ha, hB b hb, hF a ha b hb, mul_assoc]
    · have hc := hconjH b hb
      have e : a * σ * b = a * (σ * b * σ⁻¹) * σ := by group
      rw [e, hB _ (mul_mem ha hc), hB a ha, hA b hb, hF a ha _ hc, hFc b hb]
      calc F a * (t * F b * t) * t = F a * t * F b * (t * t) := by group
        _ = F a * t * F b := by rw [ht2, mul_one]
    · have hc := hconjH b hb
      have e : a * σ * (b * σ) = a * (σ * b * σ⁻¹) := by rw [hσi]; group
      rw [e, hA _ (mul_mem ha hc), hB a ha, hB b hb, hF a ha _ hc, hFc b hb]
      group
  refine ⟨MonoidHom.mk' (fun x => F' x) (fun x y => hmul x x.2 y y.2), fun h hh => hA h hh, ?_⟩
  change F' σ = t
  have := hB 1 (one_mem _)
  rwa [one_mul, F_one_of hF, one_mul] at this

theorem F_closure_one {Q : Type} [Group Q] {H : Subgroup G} {F : G → Q}
    (hF : ∀ x ∈ H, ∀ y ∈ H, F (x * y) = F x * F y) {S : Set G} (hSH : closure S ≤ H)
    (hS : ∀ x ∈ S, F x = 1) : ∀ x ∈ closure S, F x = 1 := by
  have hF1 := F_one_of hF
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact hS x hx
  | one => exact hF1
  | mul x y hx hy ihx ihy => rw [hF x (hSH hx) y (hSH hy), ihx, ihy, mul_one]
  | inv x hx ih =>
    have := hF x (hSH hx) x⁻¹ (inv_mem (hSH hx))
    rw [mul_inv_cancel, hF1, ih, one_mul] at this
    exact this.symm

theorem secProp_iso {Q : Type} [Group Q] [Finite Q] {P B : Subgroup G} (hBP : B ≤ P)
    (φ : ↥P →* Q) (hφ : Function.Surjective φ) (hker : ∀ x : ↥P, (x : G) ∈ B → φ x = 1)
    (hcard : Nat.card P = Nat.card Q * Nat.card B) :
    SecProp P B (fun Y _ _ _ => Nonempty (Y ≃* Q)) ∧ ∀ x : ↥P, φ x = 1 → (x : G) ∈ B := by
  have hle : B.subgroupOf P ≤ φ.ker := fun x hx => hker x hx
  have hidx : φ.ker.index = Nat.card Q := by
    rw [Subgroup.index_eq_card]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toEquiv
  have hcB : Nat.card (B.subgroupOf P) = Nat.card B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBP).toEquiv
  have hQ : 0 < Nat.card Q := Nat.card_pos
  have hck : Nat.card φ.ker = Nat.card B := by
    have h := Subgroup.card_mul_index φ.ker
    rw [hidx, hcard, mul_comm] at h
    exact Nat.eq_of_mul_eq_mul_left hQ h
  have heq : B.subgroupOf P = φ.ker :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hck, hcB])
  have hn : (B.subgroupOf P).Normal := by
    rw [heq]
    infer_instance
  refine ⟨⟨hn, ⟨(QuotientGroup.quotientMulEquivOfEq heq).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hφ)⟩⟩, fun x hx => ?_⟩
  have hx' : x ∈ B.subgroupOf P := by
    rw [heq]
    exact hx
  exact mem_subgroupOf.mp hx'

theorem A_le_T1 : (frameOf m).A ≤ g23T1 m := (A_le_H m).trans (H_le_T1 m)

theorem T1_hom : ∃ φ : ↥(g23T1 m) →* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3),
    Function.Surjective φ ∧ (∀ x : ↥(g23T1 m), (x : G) ∈ (frameOf m).A → φ x = 1) ∧
    ∀ s < 8, ∀ hs : uE1 m s ∈ g23T1 m, φ ⟨uE1 m s, hs⟩ = pU s := by
  obtain ⟨F, hF, hFg, hmul⟩ := H_hom m
  have hgS := r1_genH
  simp only [Bool.and_eq_true] at hgS
  obtain ⟨hgI, hgW⟩ := hgS
  have hpg := r1_pGen
  simp only [Bool.and_eq_true] at hpg
  obtain ⟨⟨hpI, hpC⟩, -⟩ := hpg
  have hσ2 := sigma_sq m
  have ht2 : pG 3 * pG 3 = 1 := by decide
  have hFU : ∀ s < 8, F (uE1 m s) = pU s := fun s hs => by
    obtain ⟨hlt, he⟩ := idxK_at hpI (by norm_num) s hs
    obtain ⟨-, he'⟩ := idxK_at hgI (by norm_num) s hs
    apply c33_inj
    rw [hF _ hlt _ (by rw [he']; exact enc_uE1 m (by omega)), he, r1PU_c33 s hs]
  have hS : ∀ x ∈ (fun s => uE1 m (R1HG s)) '' {s | s < 3},
      F ((frameOf m).σ * x * (frameOf m).σ⁻¹) = pG 3 * F x * pG 3 := by
    rintro _ ⟨s, hs, rfl⟩
    have hs' : s < 3 := hs
    obtain ⟨hlt, he⟩ := idxK_at hgW (by norm_num) s hs'
    have hG : R1HG s < 37 := by interval_cases s <;> exact Nat.blt_eq.mp (by quickRfl)
    have henc := enc_SWP m.ρ (sigma_rho m) hσ2 (enc_uE1 m hG)
    rw [← he] at henc
    have hc := Nat.eq_of_beq_eq_true (allBelow_g2 hpC (by norm_num) s hs')
    apply c33_inj
    rw [hF _ hlt _ henc, hc, r1PG_c33 3 (by norm_num), r1PG_c33 s (by omega), MUL33_c33,
      MUL33_c33, hFg s hs']
  have hmul' : ∀ x ∈ closure ((fun s => uE1 m (R1HG s)) '' {s | s < 3}),
      ∀ y ∈ closure ((fun s => uE1 m (R1HG s)) '' {s | s < 3}), F (x * y) = F x * F y := by
    rw [H_eq]
    exact hmul
  have hFc := conj_of_gens hσ2 ht2 (S := (fun s => uE1 m (R1HG s)) '' {s | s < 3})
    (fun h hh => by
      rw [H_eq] at hh ⊢
      exact sigma_conj_H m hh) hmul' hS
  rw [H_eq] at hFc
  obtain ⟨φ, hφH, hφσ⟩ := ext_sigma hσ2 (sigma_not_mem_H m) (fun h hh => sigma_conj_H m hh)
    (fun g hg => T1_cases m hg) (H_le_T1 m) (sigma_mem_T1 m) hmul ht2 hFc
  refine ⟨φ, ?_, ?_, ?_⟩
  · have hle : closure (pG '' {s | s < 4}) ≤ φ.range := by
      rw [closure_le]
      rintro _ ⟨s, hs, rfl⟩
      have hs' : s < 4 := hs
      rcases Nat.lt_or_ge s 3 with h3 | h3
      · exact ⟨⟨_, H_le_T1 m (uE1_mem m (R1HG s))⟩, (hφH _ (uE1_mem m _)).trans (hFg s h3)⟩
      · obtain rfl : s = 3 := by omega
        exact ⟨_, hφσ⟩
    rw [pG_closure, top_le_iff] at hle
    exact MonoidHom.range_eq_top.mp hle
  · rintro ⟨x, hxT⟩ hx
    have hAG : ∀ s < 4, R1AG s < 8 ∧ pU (R1AG s) = 1 := by
      intro s hs
      obtain ⟨h0, h1, h2, h3⟩ := r1AG
      interval_cases s
      · rw [h0]
        exact ⟨by norm_num, rfl⟩
      · rw [h1]
        exact ⟨by norm_num, rfl⟩
      · rw [h2]
        exact ⟨by norm_num, rfl⟩
      · rw [h3]
        exact ⟨by norm_num, rfl⟩
    have hx' : x ∈ closure ((fun s => uE1 m (R1AG s)) '' {s | s < 4}) := by
      rw [A_eq]
      exact hx
    have h1 := F_closure_one hmul (by rw [A_eq]; exact A_le_H m) (by
      rintro _ ⟨s, hs, rfl⟩
      obtain ⟨hlt, hp⟩ := hAG s hs
      rw [hFU _ hlt, hp]) x hx'
    exact (hφH x (A_le_H m hx)).trans h1
  · intro s hs hsT
    exact (hφH _ (uE1_mem m s)).trans (hFU s hs)

theorem T1_S3S3 : SecProp (g23T1 m) (frameOf m).A
    (fun Y _ _ _ => Nonempty (Y ≃* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) := by
  obtain ⟨φ, hs, hA, -⟩ := T1_hom m
  exact (secProp_iso (A_le_T1 m) φ hs hA (by rw [card_T1, card_S3S3, card_A])).1

theorem isFrob18 {Y : Type} [Group Y] (hY : Nat.card Y = 18) {w₁ w₂ d : Y}
    (hgen : closure ({w₁, w₂, d} : Set Y) = ⊤) (h1 : w₁ ^ 3 = 1) (h2 : w₂ ^ 3 = 1)
    (hc : w₁ * w₂ = w₂ * w₁) (hd2 : d * d = 1) (hd1 : d ≠ 1) (hw1 : w₁ ≠ 1)
    (hi1 : d * w₁ * d⁻¹ = w₁⁻¹) (hi2 : d * w₂ * d⁻¹ = w₂⁻¹) : IsFrobeniusOfOrder 18 Y := by
  set W := closure ({w₁, w₂} : Set Y) with hW
  have hc' : Commute w₁ w₂ := hc
  have hc1 : ∀ x ∈ W, Commute x w₁ ∧ Commute x w₂ := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | hx
      · exact ⟨Commute.refl _, hc'⟩
      · rw [Set.mem_singleton_iff] at hx
        rw [hx]
        exact ⟨hc'.symm, Commute.refl _⟩
    | one => exact ⟨Commute.one_left _, Commute.one_left _⟩
    | mul x y _ _ ihx ihy => exact ⟨ihx.1.mul_left ihy.1, ihx.2.mul_left ihy.2⟩
    | inv x _ ih => exact ⟨ih.1.inv_left, ih.2.inv_left⟩
  have hcomm : ∀ x ∈ W, ∀ y ∈ W, Commute x y := by
    intro x hx y hy
    induction hy using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with rfl | hy
      · exact (hc1 x hx).1
      · rw [Set.mem_singleton_iff] at hy
        rw [hy]
        exact (hc1 x hx).2
    | one => exact Commute.one_right _
    | mul y z _ _ ihy ihz => exact ihy.mul_right ihz
    | inv y _ ih => exact ih.inv_right
  have hcube : ∀ x ∈ W, x ^ 3 = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | hx
      · exact h1
      · rw [Set.mem_singleton_iff] at hx
        rw [hx]
        exact h2
    | one => exact one_pow _
    | mul x y hx hy ihx ihy => rw [(hcomm x hx y hy).mul_pow, ihx, ihy, one_mul]
    | inv x _ ih => rw [inv_pow, ih, inv_one]
  have hinv : ∀ x ∈ W, d * x * d⁻¹ = x⁻¹ := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | hx
      · exact hi1
      · rw [Set.mem_singleton_iff] at hx
        rw [hx]
        exact hi2
    | one => rw [mul_one, mul_inv_cancel, inv_one]
    | mul x y hx hy ihx ihy =>
      have e : d * (x * y) * d⁻¹ = (d * x * d⁻¹) * (d * y * d⁻¹) := by group
      rw [e, ihx, ihy, mul_inv_rev, ((hcomm x hx y hy).inv_inv).eq]
    | inv x _ ih =>
      have e : d * x⁻¹ * d⁻¹ = (d * x * d⁻¹)⁻¹ := by group
      rw [e, ih]
  have hd_norm : d ∈ normalizer (W : Set Y) := by
    rw [mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      rw [hinv h hh]
      exact inv_mem hh
    · intro hh
      have h' := hinv _ hh
      have e : d * (d * h * d⁻¹) * d⁻¹ = h := by
        calc d * (d * h * d⁻¹) * d⁻¹ = (d * d) * h * (d * d)⁻¹ := by group
          _ = h := by rw [hd2, one_mul, inv_one, mul_one]
      rw [e] at h'
      rw [h']
      exact inv_mem hh
  have hWn : W.Normal := by
    rw [← normalizer_eq_top_iff, eq_top_iff, ← hgen, closure_le]
    intro x hx
    rcases hx with rfl | rfl | hx
    · exact le_normalizer (subset_closure (Set.mem_insert _ _))
    · exact le_normalizer (subset_closure (Set.mem_insert_of_mem _ rfl))
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact hd_norm
  have hd_ord : orderOf d = 2 := orderOf_eq_prime (by rw [pow_two]; exact hd2) hd1
  have hD : ∀ x ∈ zpowers d, x = 1 ∨ x = d := by
    intro x hx
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hx
    rw [← zpow_mod_orderOf, hd_ord]
    simp only [Nat.cast_ofNat]
    rcases Int.emod_two_eq_zero_or_one n with h | h
    · rw [h]
      exact Or.inl (zpow_zero d)
    · rw [h]
      exact Or.inr (zpow_one d)
  refine ⟨hY, W, zpowers d, hWn, ?_, ?_, ?_, ?_, ?_⟩
  · rw [eq_top_iff, ← hgen, closure_le]
    intro x hx
    rcases hx with rfl | rfl | hx
    · exact mem_sup_left (subset_closure (Set.mem_insert _ _))
    · exact mem_sup_left (subset_closure (Set.mem_insert_of_mem _ rfl))
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact mem_sup_right (mem_zpowers d)
  · rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxW, hxD⟩ := mem_inf.mp hx
    rw [mem_bot]
    rcases hD x hxD with h | h
    · exact h
    · exfalso
      rw [h] at hxW
      have h3 := hcube d hxW
      apply hd1
      calc d = d ^ 3 * (d * d)⁻¹ := by group
        _ = 1 := by rw [h3, hd2, inv_one, one_mul]
  · intro h
    apply hw1
    have hm : w₁ ∈ W := subset_closure (Set.mem_insert _ _)
    rw [h, mem_bot] at hm
    exact hm
  · intro h
    apply hd1
    have hm : d ∈ zpowers d := mem_zpowers d
    rw [h, mem_bot] at hm
    exact hm
  · intro d' hd' hd'1 w hw hcw
    rcases hD d' hd' with h | h
    · exact absurd h hd'1
    · rw [h] at hcw
      have e1 : w⁻¹ = w := by
        rw [← hinv w hw, hcw, mul_inv_cancel_right]
      have hww : w * w = 1 := by
        nth_rewrite 2 [← e1]
        exact mul_inv_cancel w
      have h3 := hcube w hw
      calc w = w ^ 3 * (w * w)⁻¹ := by group
        _ = 1 := by rw [h3, hww, inv_one, one_mul]

theorem b1_mem_A : (frameOf m).b₁ ∈ (frameOf m).A := by
  rw [SFrame.A]
  exact subset_closure (by simp)

theorem b2_mem_A : (frameOf m).b₂ ∈ (frameOf m).A := by
  rw [SFrame.A]
  exact subset_closure (by simp)

abbrev Aq : Subgroup ↥(g23H m) := (frameOf m).A.subgroupOf (g23H m)

theorem Aq_normal : (Aq m).Normal :=
  (normal_subgroupOf_iff_le_normalizer (A_le_H m)).mpr (H_norm_A m)

theorem Aq_hom [(Aq m).Normal] : ∃ ψ : ↥(g23H m) ⧸ Aq m →* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3),
    Function.Injective ψ ∧
      ∀ s < 8, ψ (QuotientGroup.mk (⟨uE1 m s, uE1_mem m s⟩ : ↥(g23H m))) = pU s := by
  obtain ⟨φ, hs, hA, hU⟩ := T1_hom m
  have hker := (secProp_iso (A_le_T1 m) φ hs hA (by rw [card_T1, card_S3S3, card_A])).2
  let φH : ↥(g23H m) →* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3) :=
    φ.comp (Subgroup.inclusion (H_le_T1 m))
  have hA'ker : Aq m = φH.ker := by
    ext x
    rw [mem_subgroupOf, MonoidHom.mem_ker]
    exact ⟨fun hx => hA _ hx, fun hx => hker _ hx⟩
  let ψ := QuotientGroup.lift (Aq m) φH (le_of_eq hA'ker)
  have hψmk : ∀ x : ↥(g23H m), ψ (QuotientGroup.mk x) = φH x := fun x => rfl
  refine ⟨ψ, ?_, fun s hs => hU s hs _⟩
  rw [injective_iff_map_eq_one]
  intro a ha
  induction a using QuotientGroup.induction_on with
  | H x =>
    rw [hψmk] at ha
    rw [QuotientGroup.eq_one_iff, hA'ker]
    exact ha

theorem Aq_card [(Aq m).Normal] : Nat.card (↥(g23H m) ⧸ Aq m) = 18 := by
  have h := Subgroup.card_mul_index (Aq m)
  have hcA : Nat.card (Aq m) = 32 := by
    rw [← card_A m]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (A_le_H m)).toEquiv
  rw [hcA, card_H, Subgroup.index_eq_card] at h
  omega

theorem Aq_gen [(Aq m).Normal] :
    closure ({QuotientGroup.mk (s := Aq m) ⟨uE1 m 0, uE1_mem m 0⟩,
      QuotientGroup.mk (s := Aq m) ⟨uE1 m 2, uE1_mem m 2⟩,
      QuotientGroup.mk (s := Aq m) ⟨uE1 m 4, uE1_mem m 4⟩} : Set (↥(g23H m) ⧸ Aq m)) = ⊤ := by
  · rw [eq_top_iff]
    rintro y -
    induction y using QuotientGroup.induction_on with
    | H x =>
      obtain ⟨x, hx⟩ := x
      have hx' := hx
      rw [g23H_eq] at hx'
      revert hx
      induction hx' using Subgroup.closure_induction with
      | mem x hxS =>
        intro hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hxS
        rcases hxS with rfl | rfl | rfl | rfl | rfl
        · have e : (⟨(frameOf m).u₁, hx⟩ : ↥(g23H m)) = ⟨uE1 m 0, uE1_mem m 0⟩ :=
            Subtype.ext (uE1_u1 m).symm
          rw [e]
          exact subset_closure (Set.mem_insert _ _)
        · have e : (QuotientGroup.mk (⟨(frameOf m).b₁, hx⟩ : ↥(g23H m)) : ↥(g23H m) ⧸ Aq m) = 1 :=
            (QuotientGroup.eq_one_iff _).mpr (mem_subgroupOf.mpr (b1_mem_A m))
          rw [e]
          exact one_mem _
        · have e : (⟨(frameOf m).u₂, hx⟩ : ↥(g23H m)) = ⟨uE1 m 2, uE1_mem m 2⟩ :=
            Subtype.ext (uE1_u2 m).symm
          rw [e]
          exact subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
        · have e : (QuotientGroup.mk (⟨(frameOf m).b₂, hx⟩ : ↥(g23H m)) : ↥(g23H m) ⧸ Aq m) = 1 :=
            (QuotientGroup.eq_one_iff _).mpr (mem_subgroupOf.mpr (b2_mem_A m))
          rw [e]
          exact one_mem _
        · have e : (⟨(frameOf m).h₀, hx⟩ : ↥(g23H m)) = ⟨uE1 m 4, uE1_mem m 4⟩ :=
            Subtype.ext (uE1_h0 m).symm
          rw [e]
          exact subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
      | one =>
        intro hx
        exact one_mem _
      | mul x y hx hy ihx ihy =>
        intro hxy
        have hxH : x ∈ g23H m := by
          rw [g23H_eq]
          exact hx
        have hyH : y ∈ g23H m := by
          rw [g23H_eq]
          exact hy
        exact mul_mem (ihx hxH) (ihy hyH)
      | inv x hx ih =>
        intro hxi
        have hxH : x ∈ g23H m := by
          rw [g23H_eq]
          exact hx
        exact inv_mem (ih hxH)

theorem A_frob_quot [(Aq m).Normal] : IsFrobeniusOfOrder 18 (↥(g23H m) ⧸ Aq m) := by
  obtain ⟨ψ, hψ, hv⟩ := Aq_hom m
  have e0 := hv 0 (by norm_num)
  have e2 := hv 2 (by norm_num)
  have e4 := hv 4 (by norm_num)
  refine isFrob18 (Aq_card m) (Aq_gen m) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · apply hψ
    rw [map_pow, e0, map_one]
    decide
  · apply hψ
    rw [map_pow, e2, map_one]
    decide
  · apply hψ
    rw [map_mul, map_mul, e0, e2]
    decide
  · apply hψ
    rw [map_mul, e4, map_one]
    decide
  · intro h
    have h' := congrArg ψ h
    rw [e4, map_one] at h'
    exact absurd h' (by decide)
  · intro h
    have h' := congrArg ψ h
    rw [e0, map_one] at h'
    exact absurd h' (by decide)
  · apply hψ
    rw [map_mul, map_mul, map_inv, map_inv, e0, e4]
    decide
  · apply hψ
    rw [map_mul, map_mul, map_inv, map_inv, e2, e4]
    decide

theorem A_frob : SecProp (g23H m) (frameOf m).A (fun Y _ _ _ => IsFrobeniusOfOrder 18 Y) :=
  ⟨Aq_normal m, @A_frob_quot G _ _ m (Aq_normal m)⟩

end CFSG.KD.G2Three.Sec1.T1Glue

end
