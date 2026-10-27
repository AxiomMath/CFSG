module

public import Certificates.Kernel.EaLat10506.All
public import Certificates.Kernel.EaLat10506.Extra
public import CFSG.Certificates.Kernel.EaLatGlue
public import CFSG.Certificates.Kernel.EaLatF2Sound
public import CFSG.Certificates.Kernel.CosetLat.MatEnc
public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporCo1Rep
import CFSG.Certificates.Kernel.LocalQTPermSound
import CFSG.Certificates.Kernel.Misc.F2BfsRec2Sound
import CFSG.Certificates.Kernel.E27Orth.Sound

public section

namespace CertificateChecks.KernelEaLat10506

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.EaLat CFSG.KC.Misc.Spec
open CFSG.KC.Misc.Clos (ClosEnc clos_card)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F10.Co1K CFSG.Sporadic.Co1.Cover
  CFSG.Sporadic.SmallF2 CFSG.KD.Co1K105
open scoped Matrix

@[expose] noncomputable def cA : ℕ := 332327598384389048651904009604433922

@[expose] noncomputable def cB : ℕ := 2362772229624717193438227940019027972

@[expose] noncomputable def wK (ca cb w len : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) one10 (fun k acc => M10 acc (Bool.rec ca cb (Nat.testBit w k)))
    len

theorem wK_succ (ca cb w len : ℕ) :
    wK ca cb w (len + 1) = M10 (wK ca cb w len) (Bool.rec ca cb (Nat.testBit w len)) := rfl

theorem GT_wK : ∀ j < 4, GT j = wK cA cB (t24Codes.getD j (0, 0)).2 (t24Codes.getD j (0, 0)).1 := by
  intro j hj
  interval_cases j <;> decide +kernel

theorem ordMat_eq_pkMat (X : ℕ) : CFSG.KS.Ord.ordMat 2 11 1 (11 * 1) X = pkMat 11 X := by
  ext i j
  simp only [CFSG.KS.Ord.ordMat, pkMat, Matrix.of_apply, Nat.testBit_eq_decide_div_mod_eq,
    Nat.mul_one, Nat.one_mul, pow_one]
  rcases Nat.mod_two_eq_zero_or_one (X / 2 ^ (11 * i.val + j.val)) with h | h <;> simp [h]

theorem one10_lt : one10 < 2 ^ (11 * 11) := by decide +kernel

theorem pkMat_of_cols {c : ℕ} {R : Array ℕ}
    (h : allN 11 (fun i => allN 11 fun j =>
      decide (c.testBit (11 * i + j) = (R[j]?.getD 0).testBit i)) = true) :
    pkMat 11 c = (rowsMatrix 11 R)ᵀ := by
  ext i j
  have e := of_decide_eq_true ((CFSG.KC.LQT.P.allN_iff _ _).1
    ((CFSG.KC.LQT.P.allN_iff _ _).1 h i i.isLt) j j.isLt)
  rw [Matrix.transpose_apply, rowsMatrix_apply, toVecD_apply]
  simp only [pkMat, Matrix.of_apply]
  rw [e]

section Enc

@[expose] noncomputable def matP (p : PM24) : Matrix (Fin 11) (Fin 11) (ZMod 2) :=
  (LinearMap.toMatrix' ((rho p : (Fin 11 → ZMod 2) ≃ₗ[ZMod 2] (Fin 11 → ZMod 2)) :
    (Fin 11 → ZMod 2) →ₗ[ZMod 2] (Fin 11 → ZMod 2)))ᵀ

theorem rho_eq_vecMul (p : PM24) (v : Fin 11 → ZMod 2) : rho p v = v ᵥ* matP p := by
  rw [matP, Matrix.vecMul_transpose, LinearMap.toMatrix'_mulVec]
  rfl

theorem matP_mul (p q : PM24) : matP (p * q) = matP q * matP p :=
  Matrix.ext_iff_vecMul.2 fun v => by
    rw [← rho_eq_vecMul, map_mul, LinearEquiv.mul_apply, rho_eq_vecMul q, rho_eq_vecMul p,
      Matrix.vecMul_vecMul]

theorem matP_one : matP 1 = 1 :=
  Matrix.ext_iff_vecMul.2 fun v => by
    rw [Matrix.vecMul_one, ← rho_eq_vecMul, map_one]
    rfl

@[expose] noncomputable def enc10 (p : PM24) : ℕ := CFSG.KC.CosetLat.matCode 2 11 1 (matP p)

theorem pkMat_enc10 (p : PM24) : pkMat 11 (enc10 p) = matP p := by
  rw [← ordMat_eq_pkMat]
  exact (CFSG.KC.CosetLat.ordMat_matCode (w := 1) (by norm_num) (matP p)).2

theorem enc10_lt (p : PM24) : enc10 p < 2 ^ (11 * 11) :=
  (CFSG.KC.CosetLat.ordMat_matCode (w := 1) (by norm_num) (matP p)).1.1

theorem matP_gen0 : matP (CFSG.Monster.Schur.M24.gen 0) = Amatᵀ :=
  Matrix.ext_iff_vecMul.2 fun v => by rw [← rho_eq_vecMul, rho_gen0, Matrix.vecMul_transpose]

theorem matP_gen1 : matP (CFSG.Monster.Schur.M24.gen 1) = Bmatᵀ :=
  Matrix.ext_iff_vecMul.2 fun v => by rw [← rho_eq_vecMul, rho_gen1, Matrix.vecMul_transpose]

theorem enc_gen0 : enc10 (CFSG.Monster.Schur.M24.gen 0) = cA := by
  refine CFSG.KD.E27Orth.pkMat_inj (enc10_lt _) (by decide +kernel) ?_
  rw [pkMat_enc10, matP_gen0, Amat, pkMat_of_cols (c := cA) (R := Aa) (by decide +kernel)]

theorem enc_gen1 : enc10 (CFSG.Monster.Schur.M24.gen 1) = cB := by
  refine CFSG.KD.E27Orth.pkMat_inj (enc10_lt _) (by decide +kernel) ?_
  rw [pkMat_enc10, matP_gen1, Bmat, pkMat_of_cols (c := cB) (R := Ba) (by decide +kernel)]

theorem enc10_closEnc : ClosEnc enc10 M10 one10 where
  enc_one := CFSG.KD.E27Orth.pkMat_inj (enc10_lt 1) one10_lt (by
    rw [pkMat_enc10, matP_one, one10, pkMat_oneF2])
  enc_mul a b := CFSG.KD.E27Orth.pkMat_inj (enc10_lt _) (CFSG.KC.F2BfsRec.mulF2_lt 11 _ _) (by
    rw [pkMat_enc10, matP_mul, M10, pkMat_mulF2, pkMat_enc10, pkMat_enc10])
  inj a b h := rho_injective (LinearEquiv.ext fun v => by
    rw [rho_eq_vecMul, rho_eq_vecMul, ← pkMat_enc10 a, ← pkMat_enc10 b, h])

theorem eltPos_snoc (l : List Bool) (c : Bool) :
    eltPos (CFSG.Monster.Schur.M24.gen 0) (CFSG.Monster.Schur.M24.gen 1) (l ++ [c]) =
      eltPos (CFSG.Monster.Schur.M24.gen 0) (CFSG.Monster.Schur.M24.gen 1) l *
        (if c then CFSG.Monster.Schur.M24.gen 1 else CFSG.Monster.Schur.M24.gen 0) := by
  simp [eltPos]

theorem enc_eltPos (w : ℕ) : ∀ len,
    enc10 (eltPos (CFSG.Monster.Schur.M24.gen 0) (CFSG.Monster.Schur.M24.gen 1) (wordOf len w)) =
      wK cA cB w len
  | 0 => by
    have h0 : eltPos (CFSG.Monster.Schur.M24.gen 0) (CFSG.Monster.Schur.M24.gen 1)
        (wordOf 0 w) = 1 := by simp [eltPos, wordOf]
    rw [h0, enc10_closEnc.enc_one]
    rfl
  | len + 1 => by
    have e : wordOf (len + 1) w = wordOf len w ++ [w.testBit len] := by
      simp [wordOf, List.range_succ]
    rw [e, eltPos_snoc, enc10_closEnc.enc_mul, enc_eltPos w len, wK_succ]
    cases w.testBit len
    · rw [if_neg Bool.false_ne_true, enc_gen0]
    · rw [if_pos rfl, enc_gen1]

theorem GT_eq (i : Fin 4) : GT i.val = enc10 (t24Gen i) := by
  exact (GT_wK i.val i.isLt).trans (enc_eltPos _ _).symm

@[expose] noncomputable def gensT : List PM24 := [t24Gen 0, t24Gen 1, t24Gen 2, t24Gen 3]

theorem gensT_closure : Subgroup.closure {g | g ∈ gensT} = t24 := by
  unfold t24
  congr 1
  ext g
  simp only [gensT, Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false, Set.mem_range]
  constructor
  · rintro (h | h | h | h)
    exacts [⟨0, h.symm⟩, ⟨1, h.symm⟩, ⟨2, h.symm⟩, ⟨3, h.symm⟩]
  · rintro ⟨⟨_ | _ | _ | _ | k, hk⟩, h⟩
    · exact Or.inl h.symm
    · exact Or.inr (Or.inl h.symm)
    · exact Or.inr (Or.inr (Or.inl h.symm))
    · exact Or.inr (Or.inr (Or.inr h.symm))
    · omega

theorem gensT_codes : ∀ j < gensT.length, GT j = enc10 (gensT.getD j 1) := by
  intro j hj
  change j < 4 at hj
  interval_cases j
  exacts [GT_eq 0, GT_eq 1, GT_eq 2, GT_eq 3]

theorem ncw11_sound : ∀ x y : PM24, ∀ w < 256,
    ncw11 (enc10 x) (enc10 y) w = true → x * y ≠ y * x := by
  intro x y w _ h hxy
  rw [ncw11, notB_iff, beq_iff] at h
  apply h
  rw [← enc10_closEnc.enc_mul, ← enc10_closEnc.enc_mul, hxy]

end Enc

theorem wit_lt : ∀ i < 191, ∀ j < i, bit (CM i) j = false → prb PR i j < 256 := by
  intro i _ j _ _
  unfold prb fld
  exact Nat.lt_succ_of_le Nat.and_le_right

theorem tag_all : ∀ e < 1024, TagOK M10 one10 191 V EC TG e := by
  intro e he
  have h := (list_all e he).2.2.2
  rw [tagAt, CFSG.KC.LQT.P.letB_eq, CFSG.KC.LQT.P.letB_eq] at h
  unfold TagOK
  cases ht : Nat.blt (TG e) 191
  · rw [ht] at h
    right
    rcases orB_iff.1 h with h | h
    · exact Or.inl (beq_iff.1 h)
    · exact Or.inr fun h' => (notB_iff.1 h) (beq_iff.2 h')
  · rw [ht] at h
    exact Or.inl ⟨blt_iff.1 ht, beq_iff.1 h⟩

theorem tagMask_bit : ∀ m i, (tagMask m).testBit i = true → ∃ e < m, TG e = i ∧ TG e < 191
  | 0, i, h => by
    change (0 : ℕ).testBit i = true at h
    simp at h
  | m + 1, i, h => by
    change (Nat.lor (tagMask m) (Bool.rec (motive := fun _ => Nat) (nat_lit 0)
      (Nat.shiftLeft (nat_lit 1) (TG m)) (Nat.blt (TG m) (nat_lit 191)))).testBit i = true at h
    rw [CFSG.KC.Benes.nlor, Nat.testBit_or, Bool.or_eq_true] at h
    rcases h with h | h
    · obtain ⟨e, he, h1⟩ := tagMask_bit m i h
      exact ⟨e, by omega, h1⟩
    · cases hb : Nat.blt (TG m) 191
      · rw [hb] at h
        change (0 : ℕ).testBit i = true at h
        simp at h
      · rw [hb] at h
        change (Nat.shiftLeft (nat_lit 1) (TG m)).testBit i = true at h
        rw [F2.shl1, Nat.testBit_two_pow] at h
        exact ⟨m, by omega, of_decide_eq_true h, blt_iff.1 hb⟩

theorem tag_cover : ∀ i < 191, ∃ e < 1024, TG e = i ∧ TG e < 191 := by
  intro i hi
  have hb : (tagMask 1024).testBit i = true := by
    rw [ch10506t_ok, Nat.testBit_two_pow_sub_one]
    exact decide_eq_true hi
  exact tagMask_bit 1024 i hb

theorem fvAt_pos {f : ℕ} (hf : 0 < f) (h : fvAt FV FX REC f = true) :
    FV f = FV (recP REC f) &&& FX (recK REC f) ∧ popK (FV f) * (recSz REC f + 1) ≤ 1024 := by
  unfold fvAt at h
  rw [CFSG.KC.LQT.P.letB_eq, CFSG.KC.LQT.P.letB_eq] at h
  cases hb : Nat.beq f 0
  · rw [hb] at h
    obtain ⟨h1, h2⟩ := andB_iff.1 h
    exact ⟨beq_iff.1 h1, Nat.le_of_ble_eq_true h2⟩
  · exact absurd (beq_iff.1 hb) (by omega)

theorem fv_zero : FV 0 = full2048 := by
  have h := fv_all 0 (by norm_num)
  unfold fvAt at h
  rw [CFSG.KC.LQT.P.letB_eq, CFSG.KC.LQT.P.letB_eq] at h
  exact beq_iff.1 h

section Main

open Classical in
@[expose] noncomputable def vI (i : ℕ) : PM24 :=
  if h : ∃ g : PM24, enc10 g = V i then h.choose else 1

theorem enc_vI {i : ℕ} (h : ∃ g : PM24, enc10 g = V i) : enc10 (vI i) = V i := by
  rw [vI, dif_pos h]
  exact h.choose_spec

theorem finite_PM24 : Finite PM24 :=
  Nat.finite_of_card_ne_zero (by rw [natCard_PM24]; norm_num)

theorem exists_V : ∀ i < 191, ∃ g : PM24, enc10 g = V i := by
  have := finite_PM24
  intro i hi
  obtain ⟨e, he, hte, htl⟩ := tag_cover i hi
  have h := (list_all e he).2.2.2
  rw [tagAt, CFSG.KC.LQT.P.letB_eq, CFSG.KC.LQT.P.letB_eq, blt_iff.2 htl] at h
  have hEC : EC e = V i := by rw [beq_iff.1 h, hte]
  obtain ⟨g, -, hg⟩ := (clos_card enc10_closEnc gensT gensT_codes (N := 1024) (by norm_num)
    (fun k hk => (list_all k hk).1) (fun k hk => (list_all k hk).2.1)).1 e he
  exact ⟨g, hg.trans hEC⟩

theorem enc_vI' : ∀ i < 191, enc10 (vI i) = V i := fun i hi => enc_vI (exists_V i hi)

set_option exponentiation.threshold 2048 in
theorem fv_fix [DecidableEq PM24]
    (hr : Recs 191 7507 vI (prb PR) (recS REC) (recC 191 REC) (recP REC) (recK REC) (recSz REC)) :
    ∀ f < 7507, FV f < 2 ^ 2048 ∧ ∀ x < 2048,
      (∀ i ∈ recS REC f, rho (vI i) (toVecD 11 x) = toVecD 11 x) → (FV f).testBit x = true := by
  intro f
  induction f using Nat.strong_induction_on with
  | _ f ih =>
    intro hf
    rcases Nat.eq_zero_or_pos f with rfl | hf0
    · rw [fv_zero, F2.full2048_eq]
      refine ⟨Nat.sub_lt (Nat.two_pow_pos 2048) Nat.one_pos, fun x hx _ => ?_⟩
      rw [Nat.testBit_two_pow_sub_one]
      exact decide_eq_true (by omega)
    · have e := fvAt_pos hf0 (fv_all f hf)
      have hp := hr.P_lt f hf0 hf
      have hk := hr.K_lt f hf0 hf
      have hS := hr.S_eq f hf0 hf
      obtain ⟨hlt, hfx⟩ := ih _ hp (by omega)
      refine ⟨?_, fun x hx hfix => ?_⟩
      · rw [e.1]
        exact lt_of_le_of_lt Nat.and_le_left hlt
      · rw [e.1, Nat.testBit_and, Bool.and_eq_true]
        refine ⟨hfx x hx fun i hi => hfix i (by
          rw [hS]
          exact Finset.mem_insert_of_mem (Finset.mem_union_left _ hi)), ?_⟩
        have hfxk := fx_all _ hk
        rw [fxAt, beq_iff] at hfxk
        rw [hfxk, ← enc_vI' _ hk, F2.fixK_iff _ _ hx, pkMat_enc10, ← rho_eq_vecMul]
        exact hfix _ (by
          rw [hS]
          exact Finset.mem_insert_self _ _)

theorem t24_facts_of_checks : Nat.card t24 = 2 ^ 10 ∧
    (∀ t ∈ t24, rho t (toVecD 11 3) = toVecD 11 3) ∧
    ∀ K : Subgroup PM24, K ≤ t24 → K ≠ ⊥ → (∀ x ∈ K, ∀ y ∈ K, x * y = y * x) →
      (∀ x ∈ K, x * x = 1) →
      Nat.card K * Nat.card {v : Fin 11 → ZMod 2 // ∀ p ∈ K, rho p v = v} ≤ 2 ^ 10 := by
  classical
  have := finite_PM24
  obtain ⟨hcard, hea⟩ := ea_of_checks enc10_closEnc gensT gensT_codes (N := 1024) (by norm_num)
    (fun k hk => (list_all k hk).1) (fun k hk => (list_all k hk).2.1)
    (fun k hk => (list_all k hk).2.2.1) (n := 191) (NF := 7507) (by norm_num) (by norm_num) vI
    enc_vI' ncw11_sound wit_lt tag_all uni_all base_ok gen_all cov_all
  obtain ⟨-, hcm⟩ := uni_of_checks (by norm_num) enc10_closEnc vI enc_vI' ncw11_sound wit_lt
    uni_all
  have hr := recs_of_checks (by norm_num) vI hcm base_ok gen_all cov_all
  rw [gensT_closure] at hcard hea
  refine ⟨by rw [hcard]; norm_num, fun t ht => ?_, fun K hKT hK hcomm hsq => ?_⟩
  · have hx3 : ∀ j < 4, (fixK (GT j)).testBit 3 = true := by
      intro j hj
      have h := ch10506x_ok
      rw [ch10506x, CFSG.KC.LQT.P.allN_iff] at h
      rw [← F2.bit_eq]
      exact h j hj
    unfold t24 at ht
    induction ht using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      rw [rho_eq_vecMul, ← pkMat_enc10, ← GT_eq i]
      exact (F2.fixK_iff _ 3 (by norm_num)).1 (hx3 i.val i.isLt)
    | one =>
      rw [map_one]
      rfl
    | mul x y _ _ hx hy => rw [map_mul, LinearEquiv.mul_apply, hy, hx]
    | inv x _ hx =>
      calc rho x⁻¹ (toVecD 11 3) = rho x⁻¹ (rho x (toVecD 11 3)) := by rw [hx]
        _ = toVecD 11 3 := by
          rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
          rfl
  · obtain ⟨f, hf, hfK⟩ := hea K hKT hcomm hsq
    have hf0 : 0 < f := by
      rcases Nat.eq_zero_or_pos f with rfl | h
      · refine absurd ((Subgroup.eq_bot_iff_forall K).2 fun x hx => ?_) hK
        rcases (hfK x).1 hx with h | ⟨i, hi, -⟩
        · exact h
        · rw [hr.S0] at hi
          exact absurd hi (Finset.notMem_empty i)
      · exact h
    obtain ⟨hlt, hfx⟩ := fv_fix hr f hf
    have hb := (fvAt_pos hf0 (fv_all f hf)).2
    have hcK : Nat.card K ≤ recSz REC f + 1 := by
      have e : (K : Set PM24) = ↑(aSet vI (recS REC f)) := by
        ext x
        rw [SetLike.mem_coe, hfK, Finset.mem_coe, mem_aSet]
      calc Nat.card K = Nat.card (K : Set PM24) := rfl
        _ = (aSet vI (recS REC f)).card := by rw [e, Nat.card_coe_set_eq, Set.ncard_coe_finset]
        _ ≤ ((recS REC f).image vI).card + 1 := Finset.card_insert_le _ _
        _ ≤ (recS REC f).card + 1 := Nat.add_le_add_right Finset.card_image_le _
        _ ≤ (Finset.range (recSz REC f)).card + 1 := Nat.add_le_add_right Finset.card_image_le _
        _ = recSz REC f + 1 := by rw [Finset.card_range]
    have hcF : Nat.card {v : Fin 11 → ZMod 2 // ∀ p ∈ K, rho p v = v} ≤ popK (FV f) := by
      choose sel hsel using exists_toVecD
      let S := (Finset.range 2048).filter fun q => (FV f).testBit q = true
      have hmem : ∀ v : {v : Fin 11 → ZMod 2 // ∀ p ∈ K, rho p v = v}, sel v.1 ∈ S := by
        rintro ⟨v, hv⟩
        have hl : sel v < 2048 := (hsel v).1
        simp only [S, Finset.mem_filter, Finset.mem_range]
        refine ⟨hl, hfx _ hl fun i hi => ?_⟩
        rw [(hsel v).2]
        exact hv _ ((hfK _).2 (Or.inr ⟨i, hi, rfl⟩))
      have hinj : Function.Injective fun v : {v : Fin 11 → ZMod 2 // ∀ p ∈ K, rho p v = v} =>
          (⟨sel v.1, hmem v⟩ : S) := by
        intro v w h
        apply Subtype.ext
        rw [← (hsel v.1).2, ← (hsel w.1).2]
        exact congrArg (toVecD 11) (congrArg Subtype.val h)
      calc _ ≤ Nat.card S := Nat.card_le_card_of_injective _ hinj
        _ = S.card := Nat.card_eq_finsetCard S
        _ = popK (FV f) := (F2.popK_eq hlt).symm
    calc Nat.card K * _ ≤ (recSz REC f + 1) * popK (FV f) := Nat.mul_le_mul hcK hcF
      _ = popK (FV f) * (recSz REC f + 1) := Nat.mul_comm _ _
      _ ≤ 1024 := hb
      _ = 2 ^ 10 := by norm_num

end Main

end CertificateChecks.KernelEaLat10506

end
