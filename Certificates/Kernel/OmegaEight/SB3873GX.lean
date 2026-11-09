module

public import Certificates.Kernel.OmegaEight.SB3873GS
public import Certificates.Kernel.OmegaEight.SB3873LD
public import Certificates.Kernel.OmegaEight.SB3872KC
public import CFSG.Certificates.Kernel.O8.SBExtGrp
public import CFSG.Certificates.Kernel.O8.SBRecSub
public import CFSG.Certificates.Kernel.Census.ConjFSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8.SB3873

open CFSG.KC.Enum CFSG.KC.SB CFSG.EvenSmallLie.OmegaEight.SpBranch CertificateChecks.KernelO8.SB3871
  CertificateChecks.KernelO8.SB3872 CertificateChecks.KernelO8 CFSG.KC.SBCen CFSG.KC.SBCenF
  CFSG.KC.SBExt CFSG.KC.SBLow CFSG.KC.SBCls CFSG.KC.SBCenL

@[expose] noncomputable def pkR (i : ℕ) : ℕ := Nat.land (Nat.shiftRight sClsPk (Nat.mul 32 i)) 131071

@[expose] noncomputable def pkS (i : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight sClsPk (Nat.add (Nat.mul 32 i) 17)) 255

theorem sClsPk_ok : ((List.range sClsLen).all fun i =>
    sClsLit.getD i (0, 0) == (pkR i, pkS i)) = true := by decide +kernel

theorem sClsLit_length : sClsLit.length = sClsLen := by decide +kernel

theorem pk_mem {i : ℕ} (hi : i < sClsLen) : (pkR i, pkS i) ∈ sClsLit := by
  have h := List.all_eq_true.1 sClsPk_ok i (List.mem_range.2 hi)
  rw [beq_iff_eq] at h
  rw [← h, List.getD_eq_getElem _ _ (sClsLit_length ▸ hi)]
  exact List.getElem_mem _

@[expose] noncomputable def lowAt (k m : ℕ) (r : ℕ × ℕ) (d : ℕ × ℕ × ℕ × ℕ) : Bool :=
  strictB (wLit.getD (16 * k + m - 16) 0) fun W => strictB (lLit.getD k 0) fun L =>
    Nat.blt r.1 65536 && Nat.blt d.1 65536 && Nat.blt d.2.1 65536 && !(Nat.beq r.1 0) &&
      Nat.beq (mulK r.1 r.1) 0 &&
      Nat.beq (rowFN mulK sNfRow W L r.1) (cconj mulK invK d.2.1 d.1) &&
      Nat.blt d.2.2.1 sClsLen && Nat.blt d.2.2.2 sClsLen &&
      Nat.beq (pkR d.2.2.1) r.1 && Nat.beq (pkR d.2.2.2) d.1 &&
      ((Nat.beq d.1 r.1 && Nat.beq r.2 (pkS d.2.2.1)) ||
        (Nat.blt r.1 d.1 && Nat.beq r.2 (Nat.add (pkS d.2.2.1) (pkS d.2.2.2)))) &&
      Nat.blt r.2 130

@[expose] def lowDOf (k m z : ℕ) : List (ℕ × ℕ × ℕ × ℕ) :=
  ((lowDLit.find? fun p => p.1 == (k, m, z)).map Prod.snd).getD []

@[expose] noncomputable def lowOK (k m z : ℕ) (D : List (ℕ × ℕ × ℕ × ℕ)) : Bool :=
  (((t1Cls k m z).take D.length).zip D).all fun p => lowAt k m p.1 p.2

theorem exists_of_zip_all {α β : Type} {f : α → β → Bool} {L : List α} {D : List β}
    (hl : L.length ≤ D.length) (h : (L.zip D).all (fun p => f p.1 p.2) = true) :
    ∀ a ∈ L, ∃ b, f a b = true := by
  intro a ha
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
  refine ⟨D[i]'(by omega), ?_⟩
  have hi' : i < (L.zip D).length := by rw [List.length_zip]; omega
  have hmem := List.getElem_mem hi'
  rw [List.getElem_zip] at hmem
  exact List.all_eq_true.1 h _ hmem

theorem clsAt_of_low {k m z : ℕ} (hH : homK k m z = true) (hz : z < 65536) (hFz : FK k m z = z)
    {r : ℕ × ℕ} {d : ℕ × ℕ × ℕ × ℕ} (h : lowAt k m r d = true) : clsAt k m z r = true := by
  unfold lowAt at h
  simp only [cen_strictB, FK_eqN, Bool.and_eq_true, Bool.or_eq_true, Nat.blt_eq, Nat.beq_eq,
    Bool.not_eq_true', Nat.add_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hr1, hd1⟩, hd2⟩, hr0⟩, hrr⟩, hF⟩, hi⟩, hj⟩, hpi⟩, hpj⟩, hcase⟩, hn⟩ := h
  have hr0' : r.1 ≠ 0 := Nat.ne_of_beq_eq_false hr0
  have ha : (r.1, pkS d.2.2.1) ∈ sClsLit := hpi ▸ pk_mem hi
  have hb : (d.1, pkS d.2.2.2) ∈ sClsLit := hpj ▸ pk_mem hj
  have hFlt : ∀ a < 65536, FK k m a < 65536 := fun a _ => mulK_lt _ _
  have hconj : ∀ y < 65536, mulK z y = mulK (FK k m (FK k m y)) z := fun y hy =>
    conj_of_homK hH hz hy
  have hE : ExtHyp ΦK (FK k m) z :=
    ⟨mulK_zero, fun _ => mulK_lt _ _, homK_mul hH, hz, hFz, hconj⟩
  obtain ⟨H, _, ⟨Φ₁⟩⟩ := exists_ext hE
  have hinv1 := FHom.invOK_ext_of_conj ΦK invOK_K hFlt hz hconj
  have hG₁ : Gen (extMul 65536 mulK (FK k m) z) t1Gens (2 * 65536) :=
    gen_ext' ΦK mulK_zero (FK k m) z sGens_lt genK
  have hg₁ : ∀ g ∈ t1Gens, g < 2 * 65536 := by decide
  obtain ⟨h1, h2, h3, h4⟩ := low_parts ΦK Φ₁ mulK_zero hFlt invOK_K sGens_lt genK hinv1 hg₁ hG₁
    cls_check ha hb hd2 hF hcase hn
  have hMK : MK k m z r.1 r.1 = mulK r.1 r.1 := by
    rw [MK, extMul, if_pos hr1, if_pos hr1]
  unfold clsAt
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, bne_iff_ne, ne_eq, List.all_eq_true]
  exact ⟨⟨⟨⟨⟨⟨by omega, by rw [hMK, hrr]⟩, hr0'⟩, h1⟩, h2⟩, h3⟩, h4⟩

@[expose] def g6 : List ℕ := [68, 69, 4096, 256, 34816, 65536]

@[expose] def wordsOf (k m z : ℕ) : List (List ℕ) :=
  ((wordsLit.find? fun p => p.1 == (k, m, z)).map Prod.snd).getD []

@[expose] noncomputable def wordsOK (k m z : ℕ) : Bool :=
  strictB (wLit.getD (16 * k + m - 16) 0) fun W => strictB (lLit.getD k 0) fun L =>
    Nat.beq (wordsOf k m z).length 10 &&
      (t1Gens.zip (wordsOf k m z)).all fun p => p.2.all (fun a => g6.contains a) &&
        Nat.beq (p.2.foldl (extMulF 65536 mulK (rowFN mulK sNfRow W L) z) 0) p.1

@[expose] noncomputable def clsAtU (k m z : ℕ) (r : ℕ × ℕ) : Bool :=
  strictB (wLit.getD (16 * k + m - 16) 0) fun W => strictB (lLit.getD k 0) fun L =>
    Nat.blt r.2 130 && clsChk (extMulF 65536 mulK (rowFN mulK sNfRow W L) z)
      (extInv 65536 mulK invK (rowFN mulK sNfRow W L) z) g6 131072 r

theorem clsAt_of_U {k m z : ℕ} (hH : homK k m z = true) (hz : z < 65536) (hFz : FK k m z = z)
    (hw : wordsOK k m z = true) {r : ℕ × ℕ} (h : clsAtU k m z r = true) : clsAt k m z r = true := by
  unfold clsAtU at h
  simp only [cen_strictB, MK_eqN, IK_eqN, Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨hn, hchk⟩ := h
  unfold wordsOK at hw
  simp only [cen_strictB, MK_eqN, Bool.and_eq_true, Nat.beq_eq] at hw
  obtain ⟨hw10, hwz⟩ := hw
  have hFlt : ∀ a < 65536, FK k m a < 65536 := fun a _ => mulK_lt _ _
  have hconj : ∀ y < 65536, mulK z y = mulK (FK k m (FK k m y)) z := fun y hy =>
    conj_of_homK hH hz hy
  have hE : ExtHyp ΦK (FK k m) z :=
    ⟨mulK_zero, fun _ => mulK_lt _ _, homK_mul hH, hz, hFz, hconj⟩
  obtain ⟨H, _, ⟨Φ₁⟩⟩ := exists_ext hE
  have hinv1 := FHom.invOK_ext_of_conj ΦK invOK_K hFlt hz hconj
  have hG₁ : Gen (extMul 65536 mulK (FK k m) z) t1Gens (2 * 65536) :=
    gen_ext' ΦK mulK_zero (FK k m) z sGens_lt genK
  have hg₁ : ∀ g ∈ t1Gens, g < 2 * 65536 := by decide
  have hg6 : ∀ g ∈ g6, g < 2 * 65536 := by decide
  have hG6 : Gen (extMul 65536 mulK (FK k m) z) g6 (2 * 65536) := by
    refine CFSG.KC.SBRec.gen_of_words Φ₁ (ext00 ΦK mulK_zero) hG₁ hg6 fun g hg => ?_
    have hl : t1Gens.length ≤ (wordsOf k m z).length := by rw [hw10]; rfl
    obtain ⟨w, hw⟩ := exists_of_zip_all (f := fun g w => (w.all fun a => g6.contains a) &&
      (List.foldl (MK k m z) 0 w).beq g) hl hwz g hg
    simp only [Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem, Nat.beq_eq] at hw
    exact ⟨w, hw.1, hw.2⟩
  have := CFSG.KC.SBRec.parts_of_sub Φ₁ (ext00 ΦK mulK_zero) hinv1 hg₁ hG₁ hg6 hG6 hchk hn
  unfold clsAt
  exact this

theorem clsBlk_of {k m z : ℕ} {D : List (ℕ × ℕ × ℕ × ℕ)} (hH : homK k m z = true) (hz : z < 65536)
    (hFz : Nat.beq (rowFN mulK sNfRow (wLit.getD (16 * k + m - 16) 0) (lLit.getD k 0) z) z = true)
    (hlow : lowOK k m z D = true) (hl128 : (t1Cls k m z).length ≤ 128)
    (hlen : (t1Cls k m z).length ≤ D.length + 3 * 8) (hw : wordsOK k m z = true)
    (hup : ∀ c < 3, (((t1Cls k m z).drop (D.length + c * 8)).take 8).all (clsAtU k m z) = true) :
    ∀ s < 16, ((chunks 8 16 (t1Cls k m z)).getD s []).all (clsAt k m z) = true := by
  rw [FK_eqN, Nat.beq_eq] at hFz
  have hall : (t1Cls k m z).all (clsAt k m z) = true := by
    rw [← List.take_append_drop D.length (t1Cls k m z), List.all_append, Bool.and_eq_true]
    refine ⟨List.all_eq_true.2 fun r hr => ?_, List.all_eq_true.2 fun r hr => ?_⟩
    · obtain ⟨d, hd⟩ := exists_of_zip_all (List.length_take_le _ _) hlow r hr
      exact clsAt_of_low hH hz hFz hd
    · exact clsAt_of_U hH hz hFz hw
        (List.all_eq_true.1 (CFSG.KC.Census.all_blocks hup hlen) r hr)
  intro s hs
  refine List.all_eq_true.2 fun r hr => List.all_eq_true.1 hall r ?_
  rw [← chunks_flatten 8 16 (t1Cls k m z) hl128]
  have hs' : s < (chunks 8 16 (t1Cls k m z)).length := by rw [chunks_length]; exact hs
  rw [List.getD_eq_getElem _ _ hs'] at hr
  exact List.mem_flatten.2 ⟨_, List.getElem_mem hs', hr⟩

theorem clsBlk_ofD {k m z : ℕ} (hH : homK k m z = true) (hz : z < 65536)
    (hFz : Nat.beq (rowFN mulK sNfRow (wLit.getD (16 * k + m - 16) 0) (lLit.getD k 0) z) z = true)
    (hlow : lowOK k m z (lowDOf k m z) = true) (hl128 : (t1Cls k m z).length ≤ 128)
    (hlen : (t1Cls k m z).length ≤ (lowDOf k m z).length + 3 * 8) (hw : wordsOK k m z = true)
    (hup : ∀ c < 3, (((t1Cls k m z).drop ((lowDOf k m z).length + c * 8)).take 8).all
      (clsAtU k m z) = true) :
    ∀ s < 16, ((chunks 8 16 (t1Cls k m z)).getD s []).all (clsAt k m z) = true :=
  clsBlk_of hH hz hFz hlow hl128 hlen hw hup

theorem packF_map_congr {α : Type} (L : List α) (f g : α → ℕ → Bool) (c : ℕ)
    (h : ∀ q ∈ L, f q c = g q c) : packF (L.map f) c = packF (L.map g) c := by
  induction L with
  | nil => rfl
  | cons q L ih =>
    rw [List.map_cons, List.map_cons, packF_cons, packF_cons, h q List.mem_cons_self,
      ih fun q' hq => h q' (List.mem_cons_of_mem _ hq)]

theorem cen_low (F : ℕ → ℕ) (z : ℕ) {Q U : List ℕ} (hQ : ∀ q ∈ Q, q < 65536)
    (hU : ∀ u ∈ U, u < 65536) {c : ℕ} (hc : c < 65536) :
    cen (extMulF 65536 mulK F z) Q U Q.length c = cen mulK Q U Q.length c := by
  have hm : ∀ a b, a < 65536 → b < 65536 → extMulF 65536 mulK F z a b = mulK a b :=
    fun a b ha hb => mulK_low F z a b ha hb
  have e1 := hm c c hc hc
  have hs : mulK c c < 65536 := mulK_lt _ _
  have e4 : extMulF 65536 mulK F z (extMulF 65536 mulK F z c c) (extMulF 65536 mulK F z c c) =
      mulK (mulK c c) (mulK c c) := by rw [e1]; exact hm _ _ hs hs
  rw [cen_eq, cen_eq]
  unfold cenPreds
  rw [packF_cons, packF_cons, packF_append, packF_append, List.length_map, List.length_map,
    packF_map_congr Q _ (fun q c => (mulK c c == 0 && c != 0) && (mulK c q == mulK q c)) c
      fun q hq => by rw [e1, hm c q hc (hQ q hq), hm q c (hQ q hq) hc],
    packF_map_congr U _ (fun u c => isOrd4 mulK c && (mulK c u == mulK u c)) c
      fun u hu => by unfold isOrd4; rw [e4, e1, hm c u hc (hU u hu), hm u c (hU u hu) hc]]
  simp only [e1]

theorem cenBlk_low (F : ℕ → ℕ) (z : ℕ) {Q U : List ℕ} (hQ : ∀ q ∈ Q, q < 65536)
    (hU : ∀ u ∈ U, u < 65536) {s : ℕ} (hs : s < 8) :
    cenBlk (extMulF 65536 mulK F z) Q U Q.length (8192 * s) = cenBlk mulK Q U Q.length (8192 * s) := by
  unfold cenBlk
  rw [sumBelow_list _ (by norm_num), sumBelow_list _ (by norm_num)]
  refine congrArg List.sum (List.map_congr_left fun i hi => ?_)
  have := List.mem_range.1 hi
  exact cen_low F z hQ hU (by rw [Nat.add_eq]; omega)

theorem cenW1_shared {k m z : ℕ} {Q B Q0 B0 : List ℕ} (hQ : (Q == Q0) = true)
    (hB : (B.take 8 == B0) = true) (hQ0 : (Q0.all fun q => Nat.blt q 65536) = true)
    (hg : ∀ s < 8, blkG mulK sActRow sMtRow Q0 [64, 75] Q0.length s = B0.getD s 0) :
    ∀ s < 8, (strictB (wLit.getD (16 * k + m - 16) 0) fun W => strictB (lLit.getD k 0) fun L =>
      strictB Q.length fun n =>
        Nat.beq (blkG (extMulF 65536 mulK (rowFN mulK sNfRow W L) z) sActRow sMtRow Q [64, 75] n s)
          (B.getD s 0)) = true := by
  intro s hs
  rw [beq_iff_eq] at hQ hB
  subst hQ hB
  simp only [cen_strictB, Nat.beq_eq]
  have hQl : ∀ q ∈ Q, q < 65536 := fun q hq => by
    have := List.all_eq_true.1 hQ0 q hq
    rwa [Nat.blt_eq] at this
  have hU : ∀ u ∈ [64, 75], u < 65536 := by decide
  rw [blk_eq (mulK_low _ _) sqFacts hU Q.length hs, cenBlk_low _ _ hQl hU hs,
    ← blk_eq (mul := mulK) (fun c d _ _ => rfl) sqFacts hU Q.length hs, hg s hs, List.getD_eq_getElem?_getD,
    List.getElem?_take_of_lt hs, ← List.getD_eq_getElem?_getD]

theorem globA : ∀ s < 8, blkG mulK sActRow sMtRow cenQA [64, 75] cenQA.length s = cenBA.getD s 0 := by
  intro s hs
  interval_cases s <;> decide +kernel

theorem globB : ∀ s < 8, blkG mulK sActRow sMtRow cenQB [64, 75] cenQB.length s = cenBB.getD s 0 := by
  intro s hs
  interval_cases s <;> decide +kernel

macro "t1cenS " Q:term ", " B:term : tactic => `(tactic| (
  refine t1KillC_of_cen (Q := $Q) (B := $B) ?_ ?_ ?_ ?_
  · refine ⟨conjOK_of_hom (by decide +kernel) (by decide), by decide +kernel, by decide +kernel, ?_,
      ?_, by decide, ?_⟩
    · simp only [chiWOK, chiS_get]
      decide +kernel
    · simp only [chiLOK, chiS_get]
      decide +kernel
    · rw [chiS_get]
      decide +kernel
  · refine ⟨clsBlk_ofD (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      fun c hc => ?_, by decide +kernel,
      by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
    interval_cases c <;> decide +kernel
  · refine CenB_of_F (CenBF_of_L (CenBL_of_W (by decide) (by decide +kernel) (by decide +kernel)
      ⟨?_, fun t ht => ?_⟩))
    · first
        | exact cenW1_shared (by decide +kernel) (by decide +kernel) (by decide +kernel) globA
        | exact cenW1_shared (by decide +kernel) (by decide +kernel) (by decide +kernel) globB
        | (intro s hs; interval_cases s <;> decide +kernel)
    · interval_cases t <;> decide +kernel
  · refine CenK_of_F ?_
    unfold CenKF
    simp only [sMarked, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨⟨by decide +kernel, by decide +kernel⟩, ⟨by decide +kernel, by decide +kernel⟩⟩))

end CertificateChecks.KernelO8.SB3873

end
