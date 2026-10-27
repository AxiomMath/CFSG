module

public import Certificates.Kernel.Misc.Sp6RefS.Facts

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMisc.Sp6RefS.Facts

open CFSG.KC.Misc.Sp6Transv CFSG.KC.Misc.Clos CFSG.KD.Sp62 CFSG.KC.Sp62
open CFSG.KD.Sp6RefS (addIdx elt commB recAt wordH letH abK)
open CFSG.KC.Misc.Sp6RefS
open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two CFSG.Quasithin.G2U
open CFSG.RankThree.PartTwo.Sec21.FF81.Sp6RefS (nGrp repSE repLE Sp6RefSAt Sp6RefSFacts sw01C
  c7Gen0 c7Gen1 c7Gen0Inv c7Gen1Inv r0Gen0 r0Gen1 r0Gen2 r2Gen0 r2Gen1 r4Gen0 r4Gen1)
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII
open CFSG.RankThree.PartTwo.Sec21.FF79 CFSG.RankThree.PartTwo.Sec21.FF81
open CertificateChecks.KernelMisc.Sp6RefS
open CertificateChecks.KernelMisc.Sp6Transv.Facts (emul eq_of_enc enc_one enc_ha enc_hb)
open CFSG.RankThree.PartTwo.Sec4.Item434Kit (vecElt)

variable {z : Fin 3 → H6} {t f0 f2 sw c0 c1 : H6}

theorem rpairs : pairCheck (r0Gen0, r0Gen0) = true ∧ pairCheck (r0Gen1, r0Gen1) = true ∧
    pairCheck (r0Gen2, r0Gen2) = true ∧ pairCheck (r2Gen0, r2Gen0) = true ∧
    pairCheck (r2Gen1, r2Gen1) = true ∧
    pairCheck (r4Gen0, mul6 r4Gen0 (mul6 r4Gen0 r4Gen0)) = true ∧
    pairCheck (r4Gen1, mul6 r4Gen1 (mul6 r4Gen1 r4Gen1)) = true ∧
    pairCheck (sw01C, sw01C) = true ∧ pairCheck (c7Gen0, c7Gen0Inv) = true ∧
    pairCheck (c7Gen1, c7Gen1Inv) = true :=
  ⟨pairCheck_of (by decide +kernel), pairCheck_of (by decide +kernel),
    pairCheck_of (by decide +kernel), pairCheck_of (by decide +kernel),
    pairCheck_of (by decide +kernel), pairCheck_of (by decide +kernel),
    pairCheck_of (by decide +kernel), pairCheck_of (by decide +kernel),
    pairCheck_of (by decide +kernel), pairCheck_of (by decide +kernel)⟩

@[expose] noncomputable def r00 : H6 := ofCode _ rpairs.1
@[expose] noncomputable def r01 : H6 := ofCode _ rpairs.2.1
@[expose] noncomputable def r02 : H6 := ofCode _ rpairs.2.2.1
@[expose] noncomputable def r20 : H6 := ofCode _ rpairs.2.2.2.1
@[expose] noncomputable def r21 : H6 := ofCode _ rpairs.2.2.2.2.1
@[expose] noncomputable def r40 : H6 := ofCode _ rpairs.2.2.2.2.2.1
@[expose] noncomputable def r41 : H6 := ofCode _ rpairs.2.2.2.2.2.2.1

theorem enc_ofCode1 {cc : List ℕ × List ℕ} (h : pairCheck cc = true) :
    enc6 (ofCode cc h) = pk cc.1 :=
  enc6_of (mat6_ofCode cc h) (pairCheck_spec h).1

theorem enc_r : enc6 r00 = RG0 0 ∧ enc6 r01 = RG0 1 ∧ enc6 r02 = RG0 2 ∧ enc6 r20 = RG2 0 ∧
    enc6 r21 = RG2 1 ∧ enc6 r40 = RG4 0 ∧ enc6 r41 = RG4 1 :=
  ⟨(enc_ofCode1 _).trans (by decide +kernel), (enc_ofCode1 _).trans (by decide +kernel),
    (enc_ofCode1 _).trans (by decide +kernel), (enc_ofCode1 _).trans (by decide +kernel),
    (enc_ofCode1 _).trans (by decide +kernel), (enc_ofCode1 _).trans (by decide +kernel),
    (enc_ofCode1 _).trans (by decide +kernel)⟩

theorem enc_aElt (j : Fin 5) : enc6 (aElt j) = REC (33 + (j : ℕ)) := by
  rw [aElt, enc6_of (mat6_vecElt _) (a_ok j).1, (a_ok j).2]

theorem Hyp.l_eq (H : Hyp z t f0 f2 sw c0 c1) :
    z 0 = aElt 0 ∧ z 0 * z 1 = aElt 3 ∧ z 2 = aElt 2 := by
  refine ⟨eq_of_enc ?_, eq_of_enc ?_, eq_of_enc ?_⟩
  · rw [H.ez0, enc_aElt]; decide +kernel
  · rw [emul, H.ez0, H.ez1, enc_aElt]; decide +kernel
  · rw [H.ez2, enc_aElt]; decide +kernel

theorem mem_closure_of_lt (l : List (List ℕ × List ℕ)) (h : l.all pairCheck = true)
    {n : ℕ} (hok : closureOK (l.map Prod.fst) (closureT (l.map Prod.fst)) n = true) {t : ℕ}
    (ht : t < (closureT (l.map Prod.fst)).size) :
    ∃ g ∈ Subgroup.closure (genSet l h), mat6 g = dec6 ((closureT (l.map Prod.fst)).getD t []) := by
  simp only [closureOK, Bool.and_eq_true, beq_iff_eq] at hok
  obtain ⟨⟨⟨-, hclosed⟩, -⟩, -⟩ := hok
  have himg := image_closure_eq dec6 one6 mul6 (l.map Prod.fst) mat6 dec6_one6 dec6_mul6
    (genSet l h) (image_genSet l h) _ hclosed
  have hmem : dec6 ((closureT (l.map Prod.fst)).getD t []) ∈
      mat6 '' (Subgroup.closure (genSet l h) : Set H6) := by
    rw [himg]
    exact ⟨t, ht, rfl⟩
  obtain ⟨g, hg, e⟩ := hmem
  exact ⟨g, hg, e⟩

theorem rec_table (j : Fin 5) {l : H6} (hl : l = aElt j) {o n hiT : ℕ} (ho : offC j = o)
    (hn : centOrder j = n) (hm : n ≤ 64 * hiT)
    (hsort : CFSG.KD.G2Three.sortK (recX REC o) (recF REC o 2) (recF REC o 3) n hiT = true) :
    (∀ g ∈ Cen l, ∃ p < n, enc6 g = recS o p) ∧ ∀ p < n, ∃ g ∈ Cen l, enc6 g = recS o p := by
  obtain ⟨hsr, hss⟩ := sortK_sound hm hsort
  obtain ⟨hok, hrec⟩ := clos_ok j
  have hsz : (closureT (gs j)).size = n := hn ▸ CFSG.KD.Sp6Two.size_of_closureOK hok
  have hC : Cen l = centSub j := by rw [hl, centSub_eq]
  refine ⟨fun g hg => ?_, fun p hp => ?_⟩
  · rw [hC] at hg
    obtain ⟨t, ht, e, hcan⟩ := exists_code_closure (centGens j) (pairs_spec.2.2.2 j) _ hok hg
    have ht' : t < n := hsz ▸ ht
    obtain ⟨p, hp, ep⟩ := hss t ht'
    refine ⟨p, hp, ?_⟩
    rw [enc6_of e.symm hcan, (hrec t (hn ▸ ht')).2, ho]
    change _ = recX REC o (recF REC o 2 p)
    rw [ep]
  · have htn := hsr p hp
    obtain ⟨g, hg, eg⟩ := mem_closure_of_lt (centGens j) (pairs_spec.2.2.2 j) hok
      (t := recF REC o 2 p) (hsz ▸ htn)
    refine ⟨g, hC ▸ hg, ?_⟩
    rw [enc6_of eg ((hrec _ (hn ▸ htn)).1), (hrec _ (hn ▸ htn)).2, ho]
    rfl

theorem sortC0 : CFSG.KD.G2Three.sortK (recX REC 38) (recF REC 38 2) (recF REC 38 3) 2160 34 = true := by
  have h := tabC0_ok
  simp only [tableK, Bool.and_eq_true] at h
  exact h.2.2

theorem sortC2 : CFSG.KD.G2Three.sortK (recX REC 4360) (recF REC 4360 2) (recF REC 4360 3) 2160 34 =
    true := by
  have h := tabC2_ok
  simp only [tableK, Bool.and_eq_true] at h
  exact h.2.2

theorem sortC3 : CFSG.KD.G2Three.sortK (recX REC 6521) (recF REC 6521 2) (recF REC 6521 3) 108 2 =
    true := by
  have h := tabC3_ok
  simp only [tableK, Bool.and_eq_true] at h
  exact h.2.2

theorem hRG0 : ∀ j < [r00, r01, r02].length, RG0 j = enc6 ([r00, r01, r02].getD j 1) := by
  intro j hj
  have hj' : j < 3 := by simpa using hj
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
  · exact enc_r.1.symm
  · exact enc_r.2.1.symm
  · exact enc_r.2.2.1.symm

theorem Hyp.hRG2 (H : Hyp z t f0 f2 sw c0 c1) :
    ∀ j < [r20, r21, sw].length, RG2 j = enc6 ([r20, r21, sw].getD j 1) := by
  intro j hj
  have hj' : j < 3 := by simpa using hj
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
  · exact enc_r.2.2.2.1.symm
  · exact enc_r.2.2.2.2.1.symm
  · exact (H.esw.trans (by decide +kernel)).symm

theorem hRG4 : ∀ j < [r40, r41].length, RG4 j = enc6 ([r40, r41].getD j 1) := by
  intro j hj
  have hj' : j < 2 := by simpa using hj
  rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
  · exact enc_r.2.2.2.2.2.1.symm
  · exact enc_r.2.2.2.2.2.2.symm

theorem hRG1 {x : H6} {c : ℕ} (hx : enc6 x = c) : ∀ j < [x].length, (fun _ => c) j = enc6 ([x].getD j 1) := by
  intro j hj
  have hj' : j = 0 := by simpa using hj
  subst hj'
  exact hx.symm

theorem Hyp.op0 (H : Hyp z t f0 f2 sw c0 c1) :
    Op 2 (Cen f2 ⊓ Cen (z 0)) = Subgroup.closure {g | g ∈ [r00, r01, r02]} ∧
      Nat.card (Subgroup.closure {g | g ∈ [r00, r01, r02]}) = 8 ∧
      ∀ g ∈ Subgroup.closure {g | g ∈ [r00, r01, r02]}, ∃ i < 8, enc6 g = rqX 0 i := by
  have el : enc6 (z 0) = AX (RI 0) := H.ez0.trans (by decide +kernel)
  obtain ⟨T1, T2⟩ := rec_table 0 H.l_eq.1 (o := 38) (n := 2160) (hiT := 34) rfl rfl (by decide)
    sortC0
  exact op_eq (e := 3) (hi := 34) hRG0 (by decide) (by decide) (by simp) rfl
    (by rw [H.ef2, el]; exact sp6refs_r0_ok) (by rw [H.ef2]; exact sp6refs_rep0_ok) (by decide) T1 T2

theorem Hyp.op1 (H : Hyp z t f0 f2 sw c0 c1) :
    Op 2 (Cen f2 ⊓ Cen (z 0 * z 1)) = Subgroup.closure {g | g ∈ [f2]} ∧
      Nat.card (Subgroup.closure {g | g ∈ [f2]}) = 2 ∧
      ∀ g ∈ Subgroup.closure {g | g ∈ [f2]}, ∃ i < 2, enc6 g = rqX 8 i := by
  have es : enc6 f2 = RS 1 := H.ef2.trans (by decide +kernel)
  have el : enc6 (z 0 * z 1) = AX (RI 1) := by rw [emul, H.ez0, H.ez1]; decide +kernel
  obtain ⟨T1, T2⟩ := rec_table 3 H.l_eq.2.1 (o := 6521) (n := 108) (hiT := 2) rfl rfl (by decide)
    sortC3
  exact op_eq (e := 1) (hi := 2) (hRG1 es) (by decide) (by decide) (by simp) rfl
    (by rw [es, el]; exact sp6refs_r1_ok) (by rw [es]; exact sp6refs_rep1_ok) (by decide) T1 T2

theorem Hyp.op2 (H : Hyp z t f0 f2 sw c0 c1) :
    Op 2 (Cen sw ⊓ Cen (z 2)) = Subgroup.closure {g | g ∈ [r20, r21, sw]} ∧
      Nat.card (Subgroup.closure {g | g ∈ [r20, r21, sw]}) = 8 ∧
      ∀ g ∈ Subgroup.closure {g | g ∈ [r20, r21, sw]}, ∃ i < 8, enc6 g = rqX 10 i := by
  have es : enc6 sw = RS 2 := H.esw.trans (by decide +kernel)
  have el : enc6 (z 2) = AX (RI 2) := H.ez2.trans (by decide +kernel)
  obtain ⟨T1, T2⟩ := rec_table 2 H.l_eq.2.2 (o := 4360) (n := 2160) (hiT := 34) rfl rfl
    (by decide) sortC2
  exact op_eq (e := 3) (hi := 34) H.hRG2 (by decide) (by decide) (by simp) rfl
    (by rw [es, el]; exact sp6refs_r2_ok) (by rw [es]; exact sp6refs_rep2_ok) (by decide) T1 T2

theorem Hyp.op3 (H : Hyp z t f0 f2 sw c0 c1) :
    Op 2 (Cen sw ⊓ Cen (z 0 * z 1)) = Subgroup.closure {g | g ∈ [sw]} ∧
      Nat.card (Subgroup.closure {g | g ∈ [sw]}) = 2 ∧
      ∀ g ∈ Subgroup.closure {g | g ∈ [sw]}, ∃ i < 2, enc6 g = rqX 18 i := by
  have es : enc6 sw = RS 3 := H.esw.trans (by decide +kernel)
  have el : enc6 (z 0 * z 1) = AX (RI 3) := by rw [emul, H.ez0, H.ez1]; decide +kernel
  obtain ⟨T1, T2⟩ := rec_table 3 H.l_eq.2.1 (o := 6521) (n := 108) (hiT := 2) rfl rfl (by decide)
    sortC3
  exact op_eq (e := 1) (hi := 2) (hRG1 es) (by decide) (by decide) (by simp) rfl
    (by rw [es, el]; exact sp6refs_r3_ok) (by rw [es]; exact sp6refs_rep3_ok) (by decide) T1 T2

theorem Hyp.op4 (H : Hyp z t f0 f2 sw c0 c1) :
    Op 2 (Cen sw ⊓ Cen (z 0 * z 1 * z 2)) = Subgroup.closure {g | g ∈ [r40, r41]} ∧
      Nat.card (Subgroup.closure {g | g ∈ [r40, r41]}) = 8 ∧
      ∀ g ∈ Subgroup.closure {g | g ∈ [r40, r41]}, ∃ i < 8, enc6 g = rqX 20 i := by
  have es : enc6 sw = RS 4 := H.esw.trans (by decide +kernel)
  have el : enc6 (z 0 * z 1 * z 2) = AX (RI 4) := H.ew7.trans (by decide +kernel)
  obtain ⟨T1, T2⟩ := H.c7_table
  exact op_eq (e := 3) (hi := 11) hRG4 (by decide) (by decide) (by simp) rfl
    (by rw [es, el]; exact sp6refs_r4_ok) (by rw [es]; exact sp6refs_rep4_ok) (by decide) T1 T2

theorem Hyp.card_op (H : Hyp z t f0 f2 sw c0 c1) (k : Fin 5) :
    Nat.card (Op 2 (Cen (repSE f2 sw k) ⊓ Cen (repLE z k))) = ![8, 2, 8, 2, 8] k := by
  fin_cases k
  · change Nat.card (Op 2 (Cen f2 ⊓ Cen (z 0))) = 8
    rw [H.op0.1]; exact H.op0.2.1
  · change Nat.card (Op 2 (Cen f2 ⊓ Cen (z 0 * z 1))) = 2
    rw [H.op1.1]; exact H.op1.2.1
  · change Nat.card (Op 2 (Cen sw ⊓ Cen (z 2))) = 8
    rw [H.op2.1]; exact H.op2.2.1
  · change Nat.card (Op 2 (Cen sw ⊓ Cen (z 0 * z 1))) = 2
    rw [H.op3.1]; exact H.op3.2.1
  · change Nat.card (Op 2 (Cen sw ⊓ Cen (z 0 * z 1 * z 2))) = 8
    rw [H.op4.1]; exact H.op4.2.1

theorem ab_parts : ((∀ i < 8, ∀ j < 8, commB (rqX 0 i) (rqX 0 j) = true) ∧
      ∀ i < 8, MULF (rqX 0 i) (rqX 0 i) = ONE) ∧
    ((∀ i < 8, ∀ j < 8, commB (rqX 10 i) (rqX 10 j) = true) ∧
      ∀ i < 8, MULF (rqX 10 i) (rqX 10 i) = ONE) ∧ commB (RG4 0) (RG4 1) = false := by
  have h := sp6refs_ab_ok
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  exact ⟨ab_sound (by decide) h.1.1, ab_sound (by decide) h.1.2, h.2⟩

theorem elem_ab {R : Subgroup H6} {RX : ℕ → ℕ} (hall : ∀ g ∈ R, ∃ i < 8, enc6 g = RX i)
    (h : (∀ i < 8, ∀ j < 8, commB (RX i) (RX j) = true) ∧ ∀ i < 8, MULF (RX i) (RX i) = ONE) :
    (∀ u ∈ R, ∀ v ∈ R, u * v = v * u) ∧ ∀ u ∈ R, u * u = 1 := by
  refine ⟨fun u hu v hv => ?_, fun u hu => ?_⟩
  · obtain ⟨i, hi, ei⟩ := hall u hu
    obtain ⟨j, hj, ej⟩ := hall v hv
    exact commB_enc.mp (by rw [ei, ej]; exact h.1 i hi j hj)
  · obtain ⟨i, hi, ei⟩ := hall u hu
    exact eq_of_enc (by rw [emul, ei, enc_one]; exact h.2 i hi)

theorem Hyp.op_ab (H : Hyp z t f0 f2 sw c0 c1) (k : Fin 5) (hk : k = 0 ∨ k = 2) :
    (∀ u ∈ Op 2 (Cen (repSE f2 sw k) ⊓ Cen (repLE z k)),
      ∀ v ∈ Op 2 (Cen (repSE f2 sw k) ⊓ Cen (repLE z k)), u * v = v * u) ∧
    ∀ u ∈ Op 2 (Cen (repSE f2 sw k) ⊓ Cen (repLE z k)), u * u = 1 := by
  rcases hk with rfl | rfl
  · change (∀ u ∈ Op 2 (Cen f2 ⊓ Cen (z 0)), ∀ v ∈ Op 2 (Cen f2 ⊓ Cen (z 0)), u * v = v * u) ∧
      ∀ u ∈ Op 2 (Cen f2 ⊓ Cen (z 0)), u * u = 1
    rw [H.op0.1]
    exact elem_ab H.op0.2.2 ab_parts.1
  · change (∀ u ∈ Op 2 (Cen sw ⊓ Cen (z 2)), ∀ v ∈ Op 2 (Cen sw ⊓ Cen (z 2)), u * v = v * u) ∧
      ∀ u ∈ Op 2 (Cen sw ⊓ Cen (z 2)), u * u = 1
    rw [H.op2.1]
    exact elem_ab H.op2.2.2 ab_parts.2.1

theorem Hyp.op_nonab (H : Hyp z t f0 f2 sw c0 c1) :
    ∃ u ∈ Op 2 (Cen (repSE f2 sw 4) ⊓ Cen (repLE z 4)),
      ∃ v ∈ Op 2 (Cen (repSE f2 sw 4) ⊓ Cen (repLE z 4)), u * v ≠ v * u := by
  change ∃ u ∈ Op 2 (Cen sw ⊓ Cen (z 0 * z 1 * z 2)),
    ∃ v ∈ Op 2 (Cen sw ⊓ Cen (z 0 * z 1 * z 2)), u * v ≠ v * u
  rw [H.op4.1]
  refine ⟨r40, Subgroup.subset_closure (by simp), r41, Subgroup.subset_closure (by simp),
    fun e => ?_⟩
  have h := commB_enc.mpr e
  rw [enc_r.2.2.2.2.2.1, enc_r.2.2.2.2.2.2, ab_parts.2.2] at h
  exact Bool.false_ne_true h

@[expose] def vIdx (x : Fin 3 → ZMod 3) : ℕ := 9 * (x 0).val + 3 * (x 1).val + (x 2).val

theorem Hyp.ax_vec (H : Hyp z t f0 f2 sw c0 c1) (x : Fin 3 → ZMod 3) :
    vIdx x < 27 ∧ AX (vIdx x) = enc6 (vecElt z x) := by
  have h0 := ZMod.val_lt (x 0)
  have h1 := ZMod.val_lt (x 1)
  have h2 := ZMod.val_lt (x 2)
  refine ⟨by unfold vIdx; omega, ?_⟩
  rw [H.encA (by unfold vIdx; omega)]
  congr 1
  simp only [aE, vecElt, vIdx]
  rw [show (9 * (x 0).val + 3 * (x 1).val + (x 2).val) / 9 = (x 0).val by omega,
    show (9 * (x 0).val + 3 * (x 1).val + (x 2).val) / 3 % 3 = (x 1).val by omega,
    show (9 * (x 0).val + 3 * (x 1).val + (x 2).val) % 3 = (x 2).val by omega]

set_option synthInstance.maxSize 2048 in
theorem idx_ne : ∀ x y : Fin 3 → ZMod 3, x ≠ 0 → (∀ c : ZMod 3, y ≠ c • x) →
    vIdx x ≠ 0 ∧ vIdx y ≠ 0 ∧ vIdx y ≠ vIdx x ∧ vIdx y ≠ addIdx (vIdx x) (vIdx x) := by
  decide +kernel

theorem wt_eq : ∀ i < 27,
    CFSG.KD.Sp6RefS.wtIdx i = CFSG.RankThree.PartTwo.Sec21.FF81.Sp6RefS.wtIdx i := by
  decide +kernel

theorem wt_idx (x : Fin 3 → ZMod 3) : CFSG.KD.Sp6RefS.wtIdx (vIdx x) = torWt x := by
  have h0 := ZMod.val_lt (x 0)
  have h1 := ZMod.val_lt (x 1)
  have h2 := ZMod.val_lt (x 2)
  have e0 : (9 * (x 0).val + 3 * (x 1).val + (x 2).val) / 9 = (x 0).val := by omega
  have e1 : (9 * (x 0).val + 3 * (x 1).val + (x 2).val) / 3 % 3 = (x 1).val := by omega
  have e2 : (9 * (x 0).val + 3 * (x 1).val + (x 2).val) % 3 = (x 2).val := by omega
  rw [wt_eq _ (by unfold vIdx; omega), vIdx, CFSG.RankThree.PartTwo.Sec21.FF81.Sp6RefS.wtIdx,
    e0, e1, e2, torWt]
  simp only [ZMod.val_eq_zero, ne_eq, ite_not]

theorem Hyp.enc_repS (H : Hyp z t f0 f2 sw c0 c1) {k : ℕ} (hk : k < 5) :
    enc6 (repSE f2 sw ⟨k, hk⟩) = RS k := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4) with rfl | rfl | rfl | rfl | rfl
  · exact H.ef2
  · exact H.ef2.trans (by decide +kernel)
  · exact H.esw.trans (by decide +kernel)
  · exact H.esw.trans (by decide +kernel)
  · exact H.esw.trans (by decide +kernel)

theorem Hyp.enc_repL (H : Hyp z t f0 f2 sw c0 c1) {k : ℕ} (hk : k < 5) :
    enc6 (repLE z ⟨k, hk⟩) = AX (RI k) := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4) with rfl | rfl | rfl | rfl | rfl
  · exact H.ez0.trans (by decide +kernel)
  · change enc6 (z 0 * z 1) = _
    rw [emul, H.ez0, H.ez1]; decide +kernel
  · exact H.ez2.trans (by decide +kernel)
  · change enc6 (z 0 * z 1) = _
    rw [emul, H.ez0, H.ez1]; decide +kernel
  · exact H.ew7.trans (by decide +kernel)

theorem repW_eq : ∀ k, ∀ hk : k < 5, (![1, 2, 1, 2, 3] : Fin 5 → ℕ) ⟨k, hk⟩ = RW k := by
  decide +kernel

theorem Hyp.conj_rep (H : Hyp z t f0 f2 sw c0 c1) :
    ∀ s ∈ nGrp z t f0 sw, orderOf s = 2 → ∀ x y : Fin 3 → ZMod 3, x ≠ 0 →
      (∀ c : ZMod 3, y ≠ c • x) → s * vecElt z x = vecElt z x * s →
        s * vecElt z y = vecElt z y * s → ∃ n : H6, ∃ k : Fin 5,
          n * repSE f2 sw k * n⁻¹ = s ∧ n * repLE z k * n⁻¹ = vecElt z x ∧
            ![1, 2, 1, 2, 3] k = torWt x := by
  intro s hs hs2 x y hx hy hsx hsy
  obtain ⟨n, hn, en⟩ := H.elt_all s hs
  have hsq : s * s = 1 := by
    have e := pow_orderOf_eq_one s
    rw [hs2, sq] at e
    exact e
  have hs1 : s ≠ 1 := fun e => by
    rw [e, orderOf_one] at hs2
    exact absurd hs2 (by decide)
  have hss : MULF (elt AX WX n) (elt AX WX n) = ONE := by rw [← en, ← emul, hsq, enc_one]
  have hs1' : elt AX WX n ≠ ONE := fun e => hs1 (eq_of_enc (by rw [en, e, enc_one]))
  obtain ⟨hix0, hiy0, hiyx, hiy2⟩ := idx_ne x y hx hy
  have hax := H.ax_vec x
  have hay := H.ax_vec y
  have hcx : commB (elt AX WX n) (AX (vIdx x)) = true := by
    rw [← en, hax.2]; exact commB_enc.mpr hsx
  have hcy : commB (elt AX WX n) (AX (vIdx y)) = true := by
    rw [← en, hay.2]; exact commB_enc.mpr hsy
  have hr := look_sound sp6refs_look_ok n hn hss hs1' _ hax.1 hix0 hcx
    ⟨_, hay.1, hiy0, hiyx, hiy2, hcy⟩
  simp only [recAt, Bool.and_eq_true] at hr
  obtain ⟨⟨⟨⟨hm, hk⟩, e1⟩, e2⟩, e3⟩ := hr
  obtain ⟨g, -, eg⟩ := H.elt_ex _ (Nat.blt_eq.mp hm)
  have hk' := Nat.blt_eq.mp hk
  refine ⟨g, ⟨_, hk'⟩, conj_of_mul (eq_of_enc ?_), conj_of_mul (eq_of_enc ?_), ?_⟩
  · rw [emul, emul, eg, en, H.enc_repS hk']
    exact Nat.eq_of_beq_eq_true e1
  · rw [emul, emul, eg, ← hax.2, H.enc_repL hk']
    exact Nat.eq_of_beq_eq_true e2
  · rw [← wt_idx x, ← Nat.eq_of_beq_eq_true e3]
    exact repW_eq _ hk'

theorem HG_ex (l : ℕ) : ∃ g : H6, HG l = enc6 g ∧ HI l = enc6 g⁻¹ := by
  rcases Nat.eq_zero_or_pos l with rfl | hl
  · exact ⟨CertificateChecks.KernelMisc.Sp6Transv.Facts.ha, (enc_ha.1.trans (by decide +kernel)).symm,
      (enc_ha.2.trans (by decide +kernel)).symm⟩
  · have hb0 : Nat.beq l 0 = false := by
      obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
      rfl
    have e1 : HG l = HG 1 := by unfold HG; rw [hb0]; rfl
    have e2 : HI l = HI 1 := by unfold HI; rw [hb0]; rfl
    exact ⟨CertificateChecks.KernelMisc.Sp6Transv.Facts.hb,
      e1.trans (enc_hb.1.trans (by decide +kernel)).symm,
      e2.trans (enc_hb.2.trans (by decide +kernel)).symm⟩

theorem letH_ex (l : ℕ) : ∃ g : H6, letH HG HI l = enc6 g := by
  unfold letH
  cases Nat.blt l 2
  · obtain ⟨g, -, e⟩ := HG_ex (Nat.sub l 2)
    exact ⟨g⁻¹, e⟩
  · obtain ⟨g, e, -⟩ := HG_ex l
    exact ⟨g, e⟩

theorem wordH_ex : ∀ n v, ∃ g : H6, wordH HG HI n v = enc6 g
  | 0, _ => ⟨1, by rw [enc_one]; rfl⟩
  | n + 1, v => by
    obtain ⟨g, eg⟩ := wordH_ex n v
    obtain ⟨g', eg'⟩ := letH_ex (Nat.land (Nat.shiftRight v (Nat.mul 2 n)) 3)
    exact ⟨g * g', by rw [emul, ← eg, ← eg']; rfl⟩

theorem Hyp.conj_t (H : Hyp z t f0 f2 sw c0 c1) : ∃ g : H6, t = g * (z 0 * z 1) * g⁻¹ := by
  obtain ⟨g, eg⟩ := wordH_ex 8 44097
  have h := sl_sound sp6refs_sl_ok
  refine ⟨g, (conj_of_mul (eq_of_enc ?_)).symm⟩
  rw [emul, emul, emul, ← eg, H.ez0, H.ez1, H.et,
    show MULF (ZG 0) (ZG 1) = AX 12 by decide +kernel]
  exact h

theorem sp6RefSFacts_kernel : Sp6RefSFacts := by
  refine ⟨⟨⟨_, mat6_ofCode _ rpairs.2.2.2.2.2.2.2.1⟩, ⟨_, mat6_ofCode _ rpairs.2.2.2.2.2.2.2.2.1⟩,
    ⟨_, mat6_ofCode _ rpairs.2.2.2.2.2.2.2.2.2⟩⟩, ?_, CFSG.KD.Sp6A2.c7_799751.1⟩
  intro z t f0 f2 sw c0 c1 hz ht hf0 hf2 hsw hc0 hc1
  have H : Hyp z t f0 f2 sw c0 c1 := ⟨hz, ht, hf0, hf2, hsw, hc0, hc1⟩
  exact ⟨H.frames, H.c7_facts.1, H.card_op, H.op_ab, H.op_nonab, H.conj_rep, H.conj_t⟩

end CertificateChecks.KernelMisc.Sp6RefS.Facts

end
