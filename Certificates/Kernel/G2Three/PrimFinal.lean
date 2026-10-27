module

public import Certificates.Kernel.G2Three.PrimChecksI
public import Certificates.Kernel.G2Three.PrimChecksO
public import Certificates.Kernel.G2Three.K7bFinal
public import CFSG.Certificates.Kernel.G2Three.PrimSound
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87G2ThreeMaxMain
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.G2Three

open CFSG.KS.Mat3 CFSG.KC.Ord CFSG.KC.Loop CFSG.KC.G2Three Certificates.G2ThreeMax
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87.G2ThreeCert CFSG.RankThree.PartTwo.Census.Carrier.G2Three

theorem M_eq_dec14 (a : Array ℕ) : M a = dec14 a.toList := by
  ext r c
  simp only [M, dec14, Matrix.of_apply, bang_eq]

theorem gen_lt {k : ℕ} (hk : k < 8) : K7G k = k7bGen K7G k := by
  unfold k7bGen
  rw [Nat.blt_eq.mpr hk, cond_true]

theorem canon_K7G {k : ℕ} (hk : k < 8) : Canon3 196 (K7G k) := by
  rw [gen_lt hk, ← pk_gen k]
  exact pk_canon (canon_gen k)

theorem mat3_K7G {k : ℕ} (hk : k < 8) : mat3 14 196 (K7G k) = M (genArr k) := by
  rw [gen_lt hk, ← pk_gen k, mat3_pk_eq (canon_gen k), M_eq_dec14]

theorem canon_ONE : Canon3 196 ONE := by
  rw [← pk_idArr]
  exact pk_canon canon_idArr

theorem mat3_ONE : mat3 14 196 ONE = 1 := by
  rw [← pk_idArr, mat3_pk_eq canon_idArr, ← M_eq_dec14, M_idArr]

theorem mat3_MUL {a b : ℕ} (ha : Canon3 196 a) (hb : Canon3 196 b) :
    Canon3 196 (MUL a b) ∧ mat3 14 196 (MUL a b) = mat3 14 196 a * mat3 14 196 b :=
  mul3s_sound consts_ok ha hb

set_option exponentiation.threshold 400 in
theorem TOP_eq : TOP = 2 ^ 392 := (Nat.shiftLeft_eq 1 392).trans (Nat.one_mul _)

set_option exponentiation.threshold 400 in
theorem canon_of_canK {P : ℕ} (h : canK P = true) : Canon3 196 P := by
  unfold canK at h
  rw [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, TOP_eq] at h
  refine ⟨h.1, fun t ht => ?_⟩
  have h3 : P &&& (P >>> 196) = 0 := h.2
  have h2 := congrArg (fun x => Nat.testBit x t) h3
  simp only [Nat.testBit_and, Nat.testBit_shiftRight, Nat.zero_testBit, ht, Bool.true_and] at h2
  exact h2

theorem inv8_eq {s : ℕ} (hs : s < 8) : inv8 s = Certificates.G2ThreeMax.invK s := by
  interval_cases s <;> rfl

theorem lt_of_ltK {w : List ℕ} (h : ltK w = true) : ∀ k ∈ w, k < 8 := by
  intro k hk
  unfold ltK at h
  rw [List.all_eq_true] at h
  exact Nat.blt_eq.mp (h k hk)

theorem cK_sound {GA GB CA CB : ℕ → ℕ} (h : cK GA GB CA CB = true) :
    ∀ k < 4, CA k = GA (2 * k) ∧ CB k = GB (2 * k) := by
  intro k hk
  have h1 := allBelow_g2 h (by decide) k hk
  simp only [Bool.and_eq_true, Nat.beq_eq] at h1
  exact h1

theorem wA_mat : ∀ w : List ℕ, (∀ k ∈ w, k < 8) →
    Canon3 196 (wA K7G w) ∧ mat3 14 196 (wA K7G w) = M (wordArr w)
  | [], _ => by
    refine ⟨canon_ONE, ?_⟩
    change mat3 14 196 ONE = _
    rw [mat3_ONE, wordArr_nil, M_idArr]
  | k :: w, h => by
    have hk := h k List.mem_cons_self
    obtain ⟨c, e⟩ := wA_mat w fun j hj => h j (List.mem_cons_of_mem _ hj)
    obtain ⟨c2, e2⟩ := mat3_MUL (canon_K7G hk) c
    change Canon3 196 (MUL (K7G k) (wA K7G w)) ∧ mat3 14 196 (MUL (K7G k) (wA K7G w)) = _
    refine ⟨c2, ?_⟩
    rw [e2, e, mat3_K7G hk, wordArr_cons, M_mmul]

section Act

variable {G : Type} [Group G] (ρ : G →* Matrix.GeneralLinearGroup (Fin 14) (ZMod 3)) (ψ : G →* G)
  (gens : ℕ → G)

@[expose] def gwK (w : List ℕ) : G := (w.map gens).prod

theorem act_eq (g : G) {A B P : ℕ} (hA : Canon3 196 A) (hB : Canon3 196 B) (hP : Canon3 196 P)
    (hgA : mat3 14 196 A = ((ρ g : Matrix.GeneralLinearGroup (Fin 14) (ZMod 3)) : Mat3))
    (hgB : mat3 14 196 B =
      (((ρ (ψ g))⁻¹ : Matrix.GeneralLinearGroup (Fin 14) (ZMod 3)) : Mat3)) :
    (⟨mat3 14 196 (actK A B P)⟩ : TwPt ρ ψ) = g • (⟨mat3 14 196 P⟩ : TwPt ρ ψ) := by
  obtain ⟨c1, e1⟩ := mat3_MUL hA hP
  obtain ⟨-, e2⟩ := mat3_MUL c1 hB
  apply TwPt.ext
  rw [twPt_smul_val]
  change mat3 14 196 (MUL (MUL A P) B) = _
  rw [e2, e1, hgA, hgB]

variable {ρ ψ gens}

theorem wA_ok (hρ : ∀ k < 8, ((ρ (gens k) : Matrix.GeneralLinearGroup (Fin 14) (ZMod 3)) : Mat3) =
      M (genArr k)) :
    ∀ w : List ℕ, (∀ k ∈ w, k < 8) → Canon3 196 (wA K7G w) ∧
      mat3 14 196 (wA K7G w) = ((ρ (gwK gens w) : Matrix.GeneralLinearGroup (Fin 14) (ZMod 3)) : Mat3)
  | [], _ => by
    refine ⟨canon_ONE, ?_⟩
    change mat3 14 196 ONE = _
    rw [mat3_ONE]
    simp [gwK]
  | k :: w, h => by
    have hk := h k List.mem_cons_self
    obtain ⟨c, e⟩ := wA_ok hρ w fun j hj => h j (List.mem_cons_of_mem _ hj)
    obtain ⟨c2, e2⟩ := mat3_MUL (canon_K7G hk) c
    change Canon3 196 (MUL (K7G k) (wA K7G w)) ∧ mat3 14 196 (MUL (K7G k) (wA K7G w)) = _
    refine ⟨c2, ?_⟩
    rw [e2, e, mat3_K7G hk, ← hρ k hk]
    simp [gwK, map_mul]

theorem wB_ok {σ : List ℕ} (hσ : ∀ k < 8, σ.getD k 0 < 8)
    (hρ : ∀ k < 8, ((ρ (gens k) : Matrix.GeneralLinearGroup (Fin 14) (ZMod 3)) : Mat3) =
      M (genArr k))
    (hinv : ∀ k < 8, gens (Certificates.G2ThreeMax.invK k) = (gens k)⁻¹)
    (hψ : ∀ k < 8, ψ (gens k) = gens (σ.getD k 0)) :
    ∀ w : List ℕ, (∀ k ∈ w, k < 8) → ∀ acc, Canon3 196 acc →
      Canon3 196 (w.foldl (fun acc k => MUL (twG K7G σ k) acc) acc) ∧
      mat3 14 196 (w.foldl (fun acc k => MUL (twG K7G σ k) acc) acc) =
        (((ρ (ψ (gwK gens w)))⁻¹ : Matrix.GeneralLinearGroup (Fin 14) (ZMod 3)) : Mat3) *
          mat3 14 196 acc
  | [], _, acc, _ => by
    refine ⟨by assumption, ?_⟩
    simp [gwK]
  | k :: w, h, acc, hacc => by
    have hk := h k List.mem_cons_self
    have hs := hσ k hk
    have hB : Canon3 196 (twG K7G σ k) := canon_K7G (inv8_eq hs ▸ invK_lt hs)
    have mB : mat3 14 196 (twG K7G σ k) =
        (((ρ (ψ (gens k)))⁻¹ : Matrix.GeneralLinearGroup (Fin 14) (ZMod 3)) : Mat3) := by
      unfold twG
      rw [inv8_eq hs, mat3_K7G (invK_lt hs), ← hρ _ (invK_lt hs), hinv _ hs, hψ k hk, map_inv]
    obtain ⟨c2, e2⟩ := mat3_MUL hB hacc
    obtain ⟨c3, e3⟩ := wB_ok hσ hρ hinv hψ w (fun j hj => h j (List.mem_cons_of_mem _ hj)) _ c2
    rw [List.foldl_cons]
    refine ⟨c3, ?_⟩
    rw [e3, e2, mB]
    simp only [gwK, List.map_cons, List.prod_cons, map_mul, mul_inv_rev, Units.val_mul, mul_assoc]

theorem twG_ok {σ : List ℕ} (hσ : ∀ k < 8, σ.getD k 0 < 8)
    (hρ : ∀ k < 8, ((ρ (gens k) : Matrix.GeneralLinearGroup (Fin 14) (ZMod 3)) : Mat3) =
      M (genArr k))
    (hinv : ∀ k < 8, gens (Certificates.G2ThreeMax.invK k) = (gens k)⁻¹)
    (hψ : ∀ k < 8, ψ (gens k) = gens (σ.getD k 0)) {k : ℕ} (hk : k < 8) :
    Canon3 196 (twG K7G σ k) ∧ mat3 14 196 (twG K7G σ k) =
      (((ρ (ψ (gens k)))⁻¹ : Matrix.GeneralLinearGroup (Fin 14) (ZMod 3)) : Mat3) := by
  have hs := hσ k hk
  refine ⟨canon_K7G (inv8_eq hs ▸ invK_lt hs), ?_⟩
  unfold twG
  rw [inv8_eq hs, mat3_K7G (invK_lt hs), ← hρ _ (invK_lt hs), hinv _ hs, hψ k hk, map_inv]

theorem rho_word (hρ : ∀ k < 8, ((ρ (gens k) : Matrix.GeneralLinearGroup (Fin 14) (ZMod 3)) : Mat3) =
      M (genArr k)) :
    ∀ w : List ℕ, (∀ k ∈ w, k < 8) →
      ((ρ (gwK gens w) : Matrix.GeneralLinearGroup (Fin 14) (ZMod 3)) : Mat3) = M (wordArr w)
  | [], _ => by simp [gwK, wordArr_nil, M_idArr]
  | k :: w, h => by
    rw [wordArr_cons, M_mmul, ← rho_word hρ w (fun j hj => h j (List.mem_cons_of_mem _ hj)),
      ← hρ k (h k List.mem_cons_self)]
    simp [gwK, map_mul]

theorem closure_even (hgen : Subgroup.closure (gens '' {k | k < 8}) = ⊤)
    (hinv : ∀ k < 8, gens (Certificates.G2ThreeMax.invK k) = (gens k)⁻¹) :
    Subgroup.closure ((fun k => gens (2 * k)) '' {k | k < 4}) = ⊤ := by
  rw [eq_top_iff, ← hgen, Subgroup.closure_le]
  rintro _ ⟨k, hk, rfl⟩
  have hk' : k < 8 := hk
  rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
  · exact Subgroup.subset_closure ⟨j, (by omega : j < 4), rfl⟩
  · have e : Certificates.G2ThreeMax.invK (2 * j) = 2 * j + 1 := by
      unfold Certificates.G2ThreeMax.invK
      rw [if_pos (by omega)]
    rw [← e, hinv _ (by omega)]
    exact Subgroup.inv_mem _ (Subgroup.subset_closure ⟨j, (by omega : j < 4), rfl⟩)

theorem coatom_recs {σ base : List ℕ}
    {X CA CB IMG LAB HP HS ROOTS HA HB RA RB RL RC TP TD EU EV : ℕ → ℕ}
    {W : ℕ → List ℕ} {N nh m S nc hiS hiR hiT : ℕ}
    (hgen : Subgroup.closure (gens '' {k | k < 8}) = ⊤)
    (hρ : ∀ k < 8, ((ρ (gens k) : Matrix.GeneralLinearGroup (Fin 14) (ZMod 3)) : Mat3) =
      M (genArr k))
    (hinv : ∀ k < 8, gens (Certificates.G2ThreeMax.invK k) = (gens k)⁻¹)
    (hσ : ∀ k < 8, σ.getD k 0 < 8) (hψ : ∀ k < 8, ψ (gens k) = gens (σ.getD k 0))
    (hb : ltK base = true)
    (hc0 : cK K7G (twG K7G σ) CA CB = true) (hx0 : Nat.beq (X 0) (wA K7G base) = true)
    (hN : 0 < N) (hNS : N ≤ nc * S) (hS : S ≤ 64 * hiS) (hnh : nh ≤ 64) (hm : m ≤ 64 * hiR)
    (hmm : m * m ≤ 64 * hiT)
    (hcl : ∀ c < nc, closK X CA CB IMG N c S hiS = true)
    (hfo : ∀ c < nc, forK X HA HB LAB HP HS ROOTS N nh m c S hiS = true)
    (hh : hK (X 0) K7G (twG K7G σ) HA HB W nh = true)
    (hr : rootK X K7G (twG K7G σ) RA RB RL RC ROOTS N m hiR = true)
    (ht : trK X RA RB LAB TP TD EU EV N m hiT = true)
    (hnt : ntK X CA CB = true) :
    IsCoatom (MulAction.stabilizer G (⟨M (wordArr base)⟩ : TwPt ρ ψ)) := by
  have hbl := lt_of_ltK hb
  have hX0 : (⟨M (wordArr base)⟩ : TwPt ρ ψ) = ⟨mat3 14 196 (X 0)⟩ := by
    rw [Nat.eq_of_beq_eq_true hx0, (wA_ok hρ base hbl).2, rho_word hρ base hbl]
  rw [hX0]
  refine prim_coatom (dec := fun P => (⟨mat3 14 196 P⟩ : TwPt ρ ψ)) (gc := fun k => gens (2 * k))
    (gw := gwK gens) (closure_even hgen hinv) ?_ ?_ ?_ hN hNS hS hnh hm hmm hcl hfo hh hr ht hnt
  · intro k hk P hP
    obtain ⟨ea, eb⟩ := cK_sound hc0 k hk
    have hk8 : 2 * k < 8 := by omega
    obtain ⟨cB, eB⟩ := twG_ok hσ hρ hinv hψ hk8
    rw [ea, eb]
    exact act_eq ρ ψ (gens (2 * k)) (canon_K7G hk8) cB (canon_of_canK hP)
      (by rw [mat3_K7G hk8, hρ _ hk8]) eB
  · intro w hw P hP
    have hl := lt_of_ltK hw
    obtain ⟨cA, eA⟩ := wA_ok hρ w hl
    obtain ⟨cB, eB⟩ := wB_ok hσ hρ hinv hψ w hl ONE canon_ONE
    rw [mat3_ONE, mul_one] at eB
    exact act_eq ρ ψ _ cA cB (canon_of_canK hP) eA eB
  · intro P Q hP hQ h
    exact mat3_inj rfl (canon_of_canK hP) (canon_of_canK hQ) (congrArg TwPt.val h)

end Act

section Inputs

variable {G : Type} [Group G] {ρ : G →* Matrix.GeneralLinearGroup (Fin 14) (ZMod 3)} {ψ : G →* G}
  {gens : ℕ → G}

theorem coatom_inner (hgen : Subgroup.closure (gens '' {k | k < 8}) = ⊤)
    (hρ : ∀ k < 8, ((ρ (gens k) : Matrix.GeneralLinearGroup (Fin 14) (ZMod 3)) : Mat3) =
      M (genArr k))
    (hinv : ∀ k < 8, gens (Certificates.G2ThreeMax.invK k) = (gens k)⁻¹)
    (hψ : ∀ k < 8, ψ (gens k) = gens innerInput.sigma[k]!) :
    IsCoatom (MulAction.stabilizer G (⟨M (wordArr innerInput.base)⟩ : TwPt ρ ψ)) :=
  coatom_recs (σ := innerInput.sigma) hgen hρ hinv (fun k hk => by interval_cases k <;> decide)
    (fun k hk => by
      rw [hψ k hk]
      congr 1
      interval_cases k <;> decide)
    (by decide) ch5182i_c ch5182i_x0 (N := 7371) (nc := 15) (S := 512) (nh := 10) (m := 32)
    (hiS := 8) (hiR := 1) (hiT := 16) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (fun c hc => by
      interval_cases c
      exacts [ch5182i_cl0, ch5182i_cl1, ch5182i_cl2, ch5182i_cl3, ch5182i_cl4, ch5182i_cl5,
        ch5182i_cl6, ch5182i_cl7, ch5182i_cl8, ch5182i_cl9, ch5182i_cl10, ch5182i_cl11,
        ch5182i_cl12, ch5182i_cl13, ch5182i_cl14])
    (fun c hc => by
      interval_cases c
      exacts [ch5182i_fo0, ch5182i_fo1, ch5182i_fo2, ch5182i_fo3, ch5182i_fo4, ch5182i_fo5,
        ch5182i_fo6, ch5182i_fo7, ch5182i_fo8, ch5182i_fo9, ch5182i_fo10, ch5182i_fo11,
        ch5182i_fo12, ch5182i_fo13, ch5182i_fo14])
    ch5182i_h ch5182i_root ch5182i_tr ch5182i_nt

theorem coatom_outer (hgen : Subgroup.closure (gens '' {k | k < 8}) = ⊤)
    (hρ : ∀ k < 8, ((ρ (gens k) : Matrix.GeneralLinearGroup (Fin 14) (ZMod 3)) : Mat3) =
      M (genArr k))
    (hinv : ∀ k < 8, gens (Certificates.G2ThreeMax.invK k) = (gens k)⁻¹)
    (hψ : ∀ k < 8, ψ (gens k) = gens outerInput.sigma[k]!) :
    IsCoatom (MulAction.stabilizer G (⟨M (wordArr outerInput.base)⟩ : TwPt ρ ψ)) :=
  coatom_recs (σ := outerInput.sigma) hgen hρ hinv (fun k hk => by interval_cases k <;> decide)
    (fun k hk => by
      rw [hψ k hk]
      congr 1
      interval_cases k <;> decide)
    (by decide) ch5182o_c ch5182o_x0 (N := 2808) (nc := 6) (S := 512) (nh := 6) (m := 9)
    (hiS := 8) (hiR := 1) (hiT := 2) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (fun c hc => by
      interval_cases c
      exacts [ch5182o_cl0, ch5182o_cl1, ch5182o_cl2, ch5182o_cl3, ch5182o_cl4, ch5182o_cl5])
    (fun c hc => by
      interval_cases c
      exacts [ch5182o_fo0, ch5182o_fo1, ch5182o_fo2, ch5182o_fo3, ch5182o_fo4, ch5182o_fo5])
    ch5182o_h ch5182o_root ch5182o_tr ch5182o_nt

theorem inner_invol : M (wordArr innerInput.base) * M (wordArr innerInput.base) = 1 := by
  have h : Nat.beq (MUL (wA K7G innerInput.base) (wA K7G innerInput.base)) ONE = true := by
    quickRfl
  obtain ⟨c, e⟩ := wA_mat innerInput.base (by decide)
  rw [← e, ← (mat3_MUL c c).2, Nat.eq_of_beq_eq_true h, mat3_ONE]

end Inputs

end CFSG.KD.G2Three

end
