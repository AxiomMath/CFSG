module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.L37.ModelPointsDefs
public import Certificates.Kernel.Misc.ON.Rels
public import Certificates.Kernel.Misc.ON.BlkAll
public import Certificates.Kernel.Misc.ON.BlkMisc
public import CFSG.Certificates.Kernel.Misc.F7FastSound

public section

namespace CertificateChecks.KernelMisc.ON

open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.L37
open CFSG.KC.Misc.F7 CFSG.KC.Loop
open CFSG.RankThree.Native.ONTriple hiding ptMat

attribute [local irreducible] dotProduct

theorem ptOK_of {k : ℕ} (hk : k < nPt) : ptOK k = true := by
  rw [nPt_eq] at hk
  have h := blkB (k / 1023) (by omega)
  rw [ptsOK, allN_iff] at h
  have h1 := h (k % 1023) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (1023 * (k / 1023)) (k % 1023) = k := Nat.add_eq.trans (by omega)
  rwa [e] at h1

theorem ptOK_parts {k : ℕ} (hk : k < nPt) :
    f7Canon (ptCode k) (ptPw k) = true ∧ ordOK k = true ∧
      (k ≠ 0 → treeOK k (ptRec k) (widenF (ptCode k)) = true) := by
  have h := ptOK_of hk
  unfold ptOK at h
  rw [strictB_eq, strictB_eq, bAnd_eq, bAnd_eq] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, h2, fun hk0 => ?_⟩
  rw [bIf_true_eq] at h3
  rcases h3 with h3 | h3
  · exact absurd (Nat.eq_of_beq_eq_true h3) hk0
  · rwa [strictB_eq] at h3

theorem echelon_ptMat {k : ℕ} (hk : k < nPt) :
    ∃ p : Fin 8 → Fin 45, (∀ c, (p c : ℕ) = pvF (ptPw k) c) ∧ Echelon (ptMat k) p :=
  f7Canon_echelon (ptOK_parts hk).1

@[expose] noncomputable def ordPt (j : ℕ) : ℕ := rSig (ptRec j)

theorem ord_step {j : ℕ} (hj : j < nPt) :
    ordPt j < nPt ∧ (j + 1 < nPt → ptCode (ordPt j) < ptCode (ordPt (j + 1))) := by
  have h := (ptOK_parts hj).2.1
  unfold ordOK at h
  rw [strictB_eq, bAnd_eq, Nat.blt_eq, ifB_true_right] at h
  refine ⟨h.1, fun hj1 => ?_⟩
  have h2 := h.2 (by rw [Nat.blt_eq]; exact hj1)
  rw [strictB_eq, Nat.blt_eq] at h2
  exact h2

theorem ord_mono {a b : ℕ} (hab : a < b) (hb : b < nPt) :
    ptCode (ordPt a) < ptCode (ordPt b) := by
  induction b with
  | zero => omega
  | succ b ih =>
    have hs := (ord_step (j := b) (by omega)).2 hb
    rcases Nat.lt_succ_iff_lt_or_eq.1 hab with h | h
    · exact (ih h (by omega)).trans hs
    · rw [h]
      exact hs

theorem exists_ordPt {i : ℕ} (hi : i < nPt) : ∃ a < nPt, ordPt a = i := by
  let f : Fin nPt → Fin nPt := fun a => ⟨ordPt a, (ord_step a.isLt).1⟩
  have hf : Function.Injective f := by
    intro a b hab
    have e : ordPt a = ordPt b := congrArg Fin.val hab
    rcases lt_trichotomy a b with h | h | h
    · exact absurd (congrArg ptCode e) (ord_mono h b.isLt).ne
    · exact h
    · exact absurd (congrArg ptCode e) (ord_mono h a.isLt).ne'
  obtain ⟨a, ha⟩ := (Finite.injective_iff_surjective.1 hf) ⟨i, hi⟩
  exact ⟨a, a.isLt, congrArg Fin.val ha⟩

theorem ptCode_inj {i j : ℕ} (hi : i < nPt) (hj : j < nPt) (e : ptCode i = ptCode j) : i = j := by
  obtain ⟨a, ha, rfl⟩ := exists_ordPt hi
  obtain ⟨b, hb, rfl⟩ := exists_ordPt hj
  rcases lt_trichotomy a b with h | h | h
  · exact absurd e (ord_mono h hb).ne
  · rw [h]
  · exact absurd e (ord_mono h ha).ne'

theorem ptS_injK (i j : ℕ) (hi : i < nPt) (hj : j < nPt) (e : ptS i = ptS j) : i = j := by
  obtain ⟨p, -, hp⟩ := echelon_ptMat hi
  obtain ⟨q, -, hq⟩ := echelon_ptMat hj
  have hm := echelon_unique hp hq e
  exact ptCode_inj hi hj (f7Canon_inj (ptOK_parts hi).1 (ptOK_parts hj).1 hm)

theorem letRev_eq {s : ℕ} (hs : s < 16) :
    letRev s = revM (enc (((letU s)⁻¹ : Mat45ˣ) : Mat45)) := by
  have h := lrB s hs
  unfold lrOK at h
  rw [Nat.eq_of_beq_eq_true h, nIf_eq]
  have e1 : Nat.shiftRight s 1 = s / 2 := (Nat.shiftRight_eq_div_pow s 1).trans (by rw [pow_one])
  have e2 : Nat.land s 1 = s % 2 := Nat.and_one_is_mod s
  have h8 : s / 2 < 8 := by omega
  have hg := chkGensM_spec gensB ⟨s / 2, h8⟩
  rw [e1, e2, letU, dif_pos h8]
  by_cases hs2 : s % 2 = 0
  · rw [if_pos (by rw [hs2]; rfl), if_pos hs2, inv_inv]
    exact congrArg revM hg.1.1
  · rw [if_neg (by rw [Nat.beq_eq]; exact hs2), if_neg hs2]
    exact congrArg revM hg.1.2

theorem tree_stepK (k : ℕ) (hk : k < nPt) (h0 : k ≠ 0) :
    rPar (ptRec k) < k ∧ rLet (ptRec k) < 16 ∧
      (k ≠ startOf k → rLet (ptRec k) % 2 = 1 ∧ rLet (ptRec k) < 12 ∧
        startOf k ≤ rPar (ptRec k)) ∧
      ptS k = ptAct (letU (rLet (ptRec k))) (ptS (rPar (ptRec k))) := by
  have h := (ptOK_parts hk).2.2 h0
  unfold treeOK at h
  simp only [strictB_eq, bAnd_eq, Nat.blt_eq, Nat.ble_eq, Nat.beq_eq, bIf_true_eq] at h
  obtain ⟨hp, hs, hr, hspan⟩ := h
  refine ⟨hp, hs, fun hne => ?_, ?_⟩
  · rcases hr with hr | hr
    · exact absurd hr hne
    · rw [← Nat.and_one_is_mod]
      exact hr
  · have hpk : rPar (ptRec k) < nPt := hp.trans hk
    obtain ⟨pk, hpvk, hek⟩ := echelon_ptMat hk
    obtain ⟨pp, -, hep⟩ := echelon_ptMat hpk
    rw [letRev_eq hs, f7Img_eq (ptOK_parts hpk).1, widenF_eq] at hspan
    have hle : rowSpan (ptMat (rPar (ptRec k)) *
        (((letU (rLet (ptRec k)))⁻¹ : Mat45ˣ) : Mat45)) ≤ rowSpan (ptMat k) :=
      (inSpan8_iff hek.1 hpvk).1 hspan
    have heq : rowSpan (ptMat (rPar (ptRec k)) *
        (((letU (rLet (ptRec k)))⁻¹ : Mat45ˣ) : Mat45)) = rowSpan (ptMat k) :=
      rowSpan_mul_eq_of_le hep.1 hek.1 (Units.inv_mul (letU (rLet (ptRec k)))) hle
    rw [ptS_eq, ptS_eq, ← heq, ptAct_apply, rowSpan_mul]

theorem fixes_iff {k l : ℕ} (hk : k < nPt) (hl : l < 8)
    (h : fixesOK k l = true) : ptAct (gM ⟨l, hl⟩) (ptS k) = ptS k := by
  unfold fixesOK at h
  have hs : 2 * l + 1 < 16 := by omega
  have e : Nat.add (Nat.mul 2 l) 1 = 2 * l + 1 := rfl
  rw [e, letRev_eq hs, f7Img_eq (ptOK_parts hk).1, widenF_eq] at h
  obtain ⟨pk, hpvk, hek⟩ := echelon_ptMat hk
  have hle : rowSpan (ptMat k * (((letU (2 * l + 1))⁻¹ : Mat45ˣ) : Mat45)) ≤
      rowSpan (ptMat k) :=
    (inSpan8_iff hek.1 hpvk).1 h
  have heq : rowSpan (ptMat k * (((letU (2 * l + 1))⁻¹ : Mat45ˣ) : Mat45)) =
      rowSpan (ptMat k) :=
    rowSpan_mul_eq_of_le hek.1 hek.1 (Units.inv_mul (letU (2 * l + 1))) hle
  have hU : letU (2 * l + 1) = gM ⟨l, hl⟩ := by
    have h1 : (2 * l + 1) / 2 = l := by omega
    have h8 : (2 * l + 1) / 2 < 8 := by omega
    rw [letU, dif_pos h8, if_neg (by omega)]
    congr 1
    exact Fin.ext h1
  rw [hU] at heq
  conv_rhs => rw [ptS_eq, ← heq]
  rw [ptS_eq, ptAct_apply, rowSpan_mul]

theorem fixes_WK (l : Fin 6) : ptAct (gM l.castSucc.castSucc) (ptS 0) = ptS 0 :=
  fixes_iff (by rw [nPt_eq]; norm_num) (by omega) (fixWB l l.isLt)

theorem orbFix_partsK : ∀ o < 5, orbStart o ≤ fixP o ∧ fixP o < orbStart (o + 1) ∧
    ∃ hl : fixL o < 6, ptAct (gM ⟨fixL o, by omega⟩) (ptS (fixP o)) = ptS (fixP o) := by
  intro o ho
  have h := orbFixB o ho
  unfold orbFixOK at h
  rw [bAnd_eq, bAnd_eq, bAnd_eq, Nat.ble_eq, Nat.blt_eq, Nat.blt_eq] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hlt : fixP o < nPt := by
    have : orbStart (o + 1) ≤ nPt := by interval_cases o <;> decide
    exact lt_of_lt_of_le h2 this
  have h3' : fixL o < 6 := h3
  exact ⟨h1, h2, h3', fixes_iff hlt (by omega) h4⟩

theorem gM_seven_eqK : ((gM 7 : Mat45ˣ) : Mat45) = (2 : ZMod 7) • (1 : Mat45) := by
  have h : genM 7 = 2 * idM := Nat.eq_of_beq_eq_true zScalarB
  have hg : genM 7 = enc ((gM 7 : Mat45ˣ) : Mat45) := (chkGensM_spec gensB 7).1.1
  apply enc_inj
  rw [← hg, h, idM_eq, enc_two_smul_one]

theorem pivots_ptMat_zeroK : Pivots (ptMat 0) (Fin.castLE (by norm_num)) := by
  obtain ⟨p, hpv, hp⟩ := echelon_ptMat (k := 0) (by rw [nPt_eq]; norm_num)
  have hdet := detB 0 (by norm_num)
  unfold detOK at hdet
  rw [bAnd_eq, allN_iff] at hdet
  have hpe : p = Fin.castLE (by norm_num) := by
    funext c
    apply Fin.ext
    rw [hpv, Fin.coe_castLE]
    exact Nat.eq_of_beq_eq_true (hdet.1 c c.isLt)
  rw [← hpe]
  exact hp.1

theorem ifB_eq_ite (c t e : Bool) : ifB c t e = if c = true then t else e := by
  cases c <;> rfl

theorem prodN_eq (n : ℕ) (f : ℕ → ℕ) : prodN n f = ∏ i ∈ Finset.range n, f i := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Finset.prod_range_succ, ← ih]
    rfl

theorem lane_row_enc {A : Matrix (Fin 8) (Fin 45) (ZMod 7)} (i : Fin 8) (j : Fin 45) :
    lane (row (enc A) i) j = (A i j).val := by
  rw [row_enc A i, lane_encV, ev, dif_pos j.isLt]
  rfl

theorem swapN_eq {a b : ℕ} (ha : a < 8) (hb : b < 8) (i : Fin 8) :
    swapN a b i = (Equiv.swap (⟨a, ha⟩ : Fin 8) ⟨b, hb⟩ i : ℕ) := by
  rw [swapN, nIf_eq, nIf_eq, Equiv.swap_apply_def]
  simp only [Nat.beq_eq, Fin.ext_iff]
  split_ifs <;> rfl

theorem det_resW_gMK (l' : Fin 6) :
    (resW ((gM l'.castSucc.castSucc : Mat45ˣ) : Mat45)).det = -1 := by
  obtain ⟨l, hl⟩ := l'
  have hdet := detB l hl
  unfold detOK at hdet
  rw [bAnd_eq, strictB_eq] at hdet
  have hl8 : l < 8 := by omega
  change (resW ((gM ⟨l, hl8⟩ : Mat45ˣ) : Mat45)).det = -1
  set G : Mat45 := ((gM ⟨l, hl8⟩ : Mat45ˣ) : Mat45) with hG
  have hU : imgS (widenF (ptCode 0)) (genM l) = enc (ptMat 0 * G) := by
    have hg : genM l = enc G := (chkGensM_spec gensB ⟨l, hl8⟩).1.1
    rw [widenF_eq, hg, imgS_enc]
    rfl
  have h := hdet.2
  rw [hU] at h
  unfold luOK at h
  simp only [bAnd_eq, allN_iff, Nat.beq_eq, Nat.blt_eq, ifB_eq_ite] at h
  obtain ⟨hprod, htri, hdiag, hab, hb8⟩ := h
  set L := detL l
  set U' := detU l
  set a := nthN (detS l) 0
  set b := nthN (detS l) 1
  have ha8 : a < 8 := hab.trans hb8
  let Lm : Matrix (Fin 8) (Fin 8) (ZMod 7) := fun i j => (nthN L (8 * i + j) : ZMod 7)
  let Um : Matrix (Fin 8) (Fin 8) (ZMod 7) := fun i j => (nthN U' (8 * i + j) : ZMod 7)
  set R := resW G
  set σ := Equiv.swap (⟨a, ha8⟩ : Fin 8) ⟨b, hb8⟩
  have hR : R.submatrix σ id = Lm * Um := by
    ext i j
    have h1 := hprod i i.isLt j j.isLt
    rw [swapN_eq ha8 hb8 i] at h1
    have h2 : lane (row (enc (ptMat 0 * G)) (σ i)) j =
        ((ptMat 0 * G) (σ i) (Fin.castLE (by norm_num) j)).val :=
      lane_row_enc (σ i) (Fin.castLE (by norm_num) j)
    have hsum : (sumN 8 fun m => Nat.mul (nthN L (Nat.add (Nat.mul 8 i) m))
        (nthN U' (Nat.add (Nat.mul 8 m) j))) =
        ∑ m : Fin 8, nthN L (8 * i + m) * nthN U' (8 * m + j) := by
      rw [sumN_eq, ← Fin.sum_univ_eq_sum_range]
      rfl
    have hm : ∀ n : ℕ, ((Nat.mod n 7 : ℕ) : ZMod 7) = (n : ZMod 7) := fun n => ZMod.natCast_mod n 7
    rw [h2, hsum] at h1
    rw [Matrix.submatrix_apply, id, Matrix.mul_apply]
    change (ptMat 0 * G) (σ i) (Fin.castLE (by norm_num) j) = ∑ m, Lm i m * Um m j
    rw [← ZMod.natCast_zmod_val ((ptMat 0 * G) (σ i) (Fin.castLE (by norm_num) j)), ← h1,
      hm, Nat.cast_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Nat.cast_mul]
  have hL : Lm.det = 1 := by
    rw [Matrix.det_of_isLowerTriangular Lm ?_]
    · refine Finset.prod_eq_one fun i _ => ?_
      have h1 := htri i i.isLt i i.isLt
      rw [if_neg (lt_irrefl _), if_pos rfl] at h1
      have h2 : nthN L (8 * i + i) % 7 = 1 := Nat.eq_of_beq_eq_true h1
      change ((nthN L (8 * i + i) : ℕ) : ZMod 7) = 1
      rw [← ZMod.natCast_mod, h2, Nat.cast_one]
    · intro i j hij
      have h1 := htri i i.isLt j j.isLt
      have hij' : (i : ℕ) < j := hij
      rw [if_pos hij'] at h1
      have h2 : nthN L (8 * i + j) = 0 := Nat.eq_of_beq_eq_true h1
      change ((nthN L (8 * i + j) : ℕ) : ZMod 7) = 0
      rw [h2, Nat.cast_zero]
  have hUd : Um.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular ?_]
    · have hd : (∏ i ∈ Finset.range 8, nthN U' (8 * i + i)) % 7 = 1 := by
        rw [← prodN_eq]
        exact hdiag
      calc ∏ i, Um i i = ((∏ i : Fin 8, nthN U' (8 * i + i) : ℕ) : ZMod 7) := by
            rw [Nat.cast_prod]
        _ = ((∏ i ∈ Finset.range 8, nthN U' (8 * i + i) : ℕ) : ZMod 7) := by
            rw [Fin.prod_univ_eq_prod_range (fun i => nthN U' (8 * i + i))]
        _ = 1 := by rw [← ZMod.natCast_mod, hd, Nat.cast_one]
    · intro i j hij
      have h1 := htri i i.isLt j j.isLt
      have hji : (j : ℕ) < i := hij
      rw [if_neg (by omega), if_neg (by omega)] at h1
      have h2 : nthN U' (8 * i + j) % 7 = 0 := Nat.eq_of_beq_eq_true h1
      change ((nthN U' (8 * i + j) : ℕ) : ZMod 7) = 0
      rw [← ZMod.natCast_mod, h2, Nat.cast_zero]
  have hne : (⟨a, ha8⟩ : Fin 8) ≠ ⟨b, hb8⟩ := fun e => by
    have := congrArg Fin.val e
    simp only at this
    omega
  have hdR := Matrix.det_permute σ R
  have hs : (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ZMod 7) = -1 := by
    rw [Equiv.Perm.sign_swap hne]
    rfl
  rw [hR, Matrix.det_mul, hL, hUd, one_mul] at hdR
  have key : ∀ x y : ZMod 7, 1 = y * x → y = -1 → x = -1 := by decide
  exact key _ _ hdR hs

end CertificateChecks.KernelMisc.ON
