module

public import Certificates.Kernel.Misc.Sp6SR.FactsC
import CFSG.Certificates.Kernel.Misc.PermClosProof

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMisc.Sp6SR.Facts

open CFSG.KC.Misc.Sp6Transv CFSG.KC.Misc.Clos CFSG.KD.Sp62 CFSG.KC.Sp62 CFSG.KC.Misc.Sp6SR
open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two CFSG.Quasithin.G2U
open CFSG.RankThree.PartTwo.Sec21.FF79
open CFSG.RankThree.PartTwo.Sec21.FF81.Sp6SR CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII
open CertificateChecks.KernelMisc.Sp6SR
open CertificateChecks.KernelMisc.Sp6Transv.Facts (orB_true commF_iff)
open CFSG.KC.LQT.P (letB)
open CFSG.KC.Ord (andB orB)

variable {z : Fin 3 → H6} {s : H6}

theorem idx_complete {n : ℕ} {f : ℕ → Bool} {L : ℕ → ℕ}
    (hL : ∀ m < 8, L m < n ∧ f (L m) = true ∧ (m < 7 → L m < L (m + 1))) (hc : cntR n f = 8) :
    ∀ i < n, f i = true → ∃ m < 8, L m = i := by
  have hmono : ∀ a b, a < b → b < 8 → L a < L b := by
    intro a b hab hb
    induction b with
    | zero => omega
    | succ b ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hab with h | rfl
      · exact (ih h (by omega)).trans ((hL b (by omega)).2.2 (by omega))
      · exact (hL a (by omega)).2.2 (by omega)
  have hinj : Set.InjOn L (Finset.range 8 : Set ℕ) := by
    intro a ha b hb e
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    rcases Nat.lt_trichotomy a b with h | h | h
    · exact absurd e (hmono a b h hb).ne
    · exact h
    · exact absurd e.symm (hmono b a h ha).ne
  have hsub : (Finset.range 8).image L ⊆ (Finset.range n).filter fun i => f i = true := by
    intro i hi
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hi
    have hm' := Finset.mem_range.1 hm
    exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (hL m hm').1, (hL m hm').2.1⟩
  have hcard : ((Finset.range 8).image L).card = ((Finset.range n).filter fun i => f i = true).card := by
    rw [Finset.card_image_of_injOn hinj, ← cntR_eq, hc, Finset.card_range]
  have heq := Finset.eq_of_subset_of_card_le hsub hcard.ge
  intro i hi hf
  have hmem : i ∈ (Finset.range 8).image L := by
    rw [heq]
    exact Finset.mem_filter.2 ⟨Finset.mem_range.2 hi, hf⟩
  obtain ⟨m, hm, e⟩ := Finset.mem_image.1 hmem
  exact ⟨m, Finset.mem_range.1 hm, e⟩

theorem idxOK_parts {L : ℕ → ℕ} {x : ℕ} (h : idxOK L x = true) :
    (∀ m < 8, L m < 128 ∧ commF (rt 2 (L m)) x = true) ∧
    ∀ i < 128, commF (rt 2 i) x = true → ∃ m < 8, L m = i := by
  unfold idxOK at h
  obtain ⟨h1, h2⟩ := andB_eq_true h
  have hL : ∀ m < 8, L m < 128 ∧ commF (rt 2 (L m)) x = true ∧ (m < 7 → L m < L (m + 1)) := by
    intro m hm
    obtain ⟨e1, e⟩ := andB_eq_true ((allN_iff _ _).1 h1 m hm)
    obtain ⟨e2, e3⟩ := andB_eq_true e
    exact ⟨Nat.blt_eq.mp e1, e2, fun hm7 => Nat.blt_eq.mp (impB_eq_true e3 (Nat.blt_eq.mpr hm7))⟩
  have hc : cntR 128 (fun i => commF (rt 2 i) x) = 8 := by
    have e128 : Nat.sub (RO (Nat.succ 2)) (RO 2) = 128 := by decide +kernel
    have e : cntT 2 x = cntR 128 (fun i => commF (rt 2 i) x) := by
      unfold cntT
      rw [e128]
    rw [← e]
    exact Nat.eq_of_beq_eq_true h2
  exact ⟨fun m hm => ⟨(hL m hm).1, (hL m hm).2.1⟩, idx_complete hL hc⟩

theorem iz_parts :
    idxOK IZ (KY 1) = true ∧ idxOK I2 (KY 6) = true ∧ idxOK I3 (KY 7) = true ∧
    (∀ a < 8, MULF (rt 2 (IZ a)) (rt 2 (IZ a)) = ONE ∧
      ∀ b < 8, commF (rt 2 (IZ a)) (rt 2 (IZ b)) = true) ∧
    (∀ a < 8, ∀ b < 8, commF (rt 2 (I2 a)) (rt 2 (IZ b)) = true) ∧
    (∀ a < 8, ∀ b < 8, commF (rt 2 (I3 a)) (rt 2 (IZ b)) = true) ∧
    (∀ a < 8, ∀ b < 8, commF (rt 2 (I3 a)) (rt 2 (I2 b)) = true) := by
  have h : izB 0 = true := chIz.all 0 (by norm_num)
  unfold izB at h
  obtain ⟨h1, h⟩ := andB_eq_true h
  obtain ⟨h2, h⟩ := andB_eq_true h
  obtain ⟨h3, h⟩ := andB_eq_true h
  obtain ⟨h4, h⟩ := andB_eq_true h
  obtain ⟨h5, h⟩ := andB_eq_true h
  obtain ⟨h6, h7⟩ := andB_eq_true h
  refine ⟨h1, h2, h3, fun a ha => ?_, fun a ha => (allN_iff _ _).1 ((allN_iff _ _).1 h5 a ha),
    fun a ha => (allN_iff _ _).1 ((allN_iff _ _).1 h6 a ha),
    fun a ha => (allN_iff _ _).1 ((allN_iff _ _).1 h7 a ha)⟩
  obtain ⟨e1, e2⟩ := andB_eq_true ((allN_iff _ _).1 h4 a ha)
  exact ⟨Nat.eq_of_beq_eq_true e1, (allN_iff _ _).1 e2⟩

theorem Hyp.code_idx (H : Hyp z s) {L : ℕ → ℕ} {m : ℕ} (hL : idxOK L (KY m) = true) {y : H6}
    (ey : enc6 y = KY m) {x : H6} (hx : x ∈ RSub 2 ⊓ Cen y) : ∃ a < 8, enc6 x = rt 2 (L a) := by
  obtain ⟨-, -, r3, -⟩ := H.R_facts 2 (by norm_num)
  obtain ⟨i, hi, ei⟩ := r3 x hx.1
  have e : RO (2 + 1) - RO 2 = 128 := by decide +kernel
  rw [e] at hi
  have hc : commF (rt 2 i) (KY m) = true := by
    rw [← ei, ← ey, commF_iff]
    exact hx.2
  obtain ⟨a, ha, ea⟩ := (idxOK_parts hL).2 i hi hc
  exact ⟨a, ha, by rw [ei, ea]⟩

theorem Hyp.idx_mem (H : Hyp z s) {L : ℕ → ℕ} {m : ℕ} (hL : idxOK L (KY m) = true) {y : H6}
    (ey : enc6 y = KY m) {a : ℕ} (ha : a < 8) {x : H6} (ex : enc6 x = rt 2 (L a)) :
    x ∈ RSub 2 ⊓ Cen y := by
  obtain ⟨h1, h2⟩ := (idxOK_parts hL).1 a ha
  have e : RO (2 + 1) - RO 2 = 128 := by decide +kernel
  refine ⟨H.mem_R_of (t := 2) (by norm_num) (by rw [e]; exact h1) ex, ?_⟩
  change x ∈ Subgroup.centralizer ({y} : Set H6)
  rw [← commF_iff, ex, ey]
  exact h2

theorem Hyp.idx_ex (H : Hyp z s) {L : ℕ → ℕ} {m : ℕ} (hL : idxOK L (KY m) = true) {a : ℕ}
    (ha : a < 8) : ∃ g : H6, enc6 g = rt 2 (L a) := by
  have e : RO (2 + 1) - RO 2 = 128 := by decide +kernel
  obtain ⟨g, -, eg⟩ := (H.R_facts 2 (by norm_num)).1 (L a) (by rw [e]; exact ((idxOK_parts hL).1 a ha).1)
  exact ⟨g, eg⟩

theorem le_cenS_of {A B : Subgroup H6} (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) : A ≤ CenS B :=
  fun a ha => Subgroup.mem_centralizer_iff.mpr fun b hb => (h a ha b hb).symm

theorem isElemAb_of {A : Subgroup H6} (hc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hs : ∀ a ∈ A, a * a = 1) (h8 : Nat.card A = 8) : IsElemAb 2 3 A :=
  ⟨{ is_comm := ⟨fun a b => Subtype.ext (hc a a.2 b b.2)⟩
     exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a =>
       Subtype.ext (by rw [Subgroup.coe_pow, pow_two]; exact hs a a.2) }, h8.trans (by norm_num)⟩

theorem Hyp.r3_z0_elemAb (H : Hyp z s) : IsElemAb 2 3 (RSub 2 ⊓ Cen (z 0)) := by
  obtain ⟨hz, -, -, hsq, -⟩ := iz_parts
  have hc : Nat.card ↥(RSub 2 ⊓ Cen (z 0)) = 8 := by
    have e := H.card_cnt (t := 2) (by norm_num) H.ez0
    rw [cnt_parts.2.2.2.2.2.2.1] at e
    exact e
  refine isElemAb_of (fun a ha b hb => ?_) (fun a ha => ?_) hc
  · obtain ⟨i, hi, ei⟩ := H.code_idx hz H.ez0 ha
    obtain ⟨j, hj, ej⟩ := H.code_idx hz H.ez0 hb
    refine comm_of_commF ?_
    rw [ei, ej]
    exact (hsq i hi).2 j hj
  · obtain ⟨i, hi, ei⟩ := H.code_idx hz H.ez0 ha
    exact eq_of_enc (by rw [emul, ei, enc_one]; exact (hsq i hi).1)

theorem Hyp.r3_cenS_facts (H : Hyp z s) :
    RSub 2 ⊓ Cen (z 0 * (z 1 * z 2)) ≤ CenS (RSub 2 ⊓ Cen (z 0)) ∧
    RSub 2 ⊓ Cen ((z 0)⁻¹ * (z 1 * z 2)) ≤ CenS (RSub 2 ⊓ Cen (z 0)) ∧
    RSub 2 ⊓ Cen ((z 0)⁻¹ * (z 1 * z 2)) ≤ CenS (RSub 2 ⊓ Cen (z 0 * (z 1 * z 2))) := by
  obtain ⟨hz, h2, h3, -, c2z, c3z, c32⟩ := iz_parts
  refine ⟨le_cenS_of fun a ha b hb => ?_, le_cenS_of fun a ha b hb => ?_,
    le_cenS_of fun a ha b hb => ?_⟩
  · obtain ⟨i, hi, ei⟩ := H.code_idx h2 H.ex2 ha
    obtain ⟨j, hj, ej⟩ := H.code_idx hz H.ez0 hb
    refine comm_of_commF ?_
    rw [ei, ej]
    exact c2z i hi j hj
  · obtain ⟨i, hi, ei⟩ := H.code_idx h3 H.ex3 ha
    obtain ⟨j, hj, ej⟩ := H.code_idx hz H.ez0 hb
    refine comm_of_commF ?_
    rw [ei, ej]
    exact c3z i hi j hj
  · obtain ⟨i, hi, ei⟩ := H.code_idx h3 H.ex3 ha
    obtain ⟨j, hj, ej⟩ := H.code_idx h2 H.ex2 hb
    refine comm_of_commF ?_
    rw [ei, ej]
    exact c32 i hi j hj

theorem xg_lo {l : ℕ} (hl : l < 8) : xg l = rt 2 (I2 l) := by
  unfold xg
  rw [Nat.blt_eq.mpr hl]

theorem xg_hi {l : ℕ} (hl : ¬ l < 8) : xg l = rt 2 (I3 (l - 8)) := by
  have h : Nat.blt l 8 = false := by
    cases e : Nat.blt l 8
    · rfl
    · exact absurd (Nat.blt_eq.mp e) hl
  change rt 2 (Bool.rec (motive := fun _ => Nat) (I3 (l - 8)) (I2 l) (Nat.blt l 8)) = _
  rw [h]

theorem Hyp.xg_ex (H : Hyp z s) : ∀ l < 16, ∃ g : H6, enc6 g = xg l := by
  obtain ⟨-, h2, h3, -⟩ := iz_parts
  intro l hl
  by_cases h : l < 8
  · rw [xg_lo h]
    exact H.idx_ex h2 h
  · rw [xg_hi h]
    exact H.idx_ex h3 (by omega)

@[expose] noncomputable def xgens : List H6 := (List.range 16).map fun l => eltOf (xg l)

@[expose] noncomputable def XSub : Subgroup H6 := Subgroup.closure {g | g ∈ xgens}

theorem x_parts :
    (∀ k < 32, treeAt MULF ONE xg 16 XA XAP k = true) ∧ (∀ i < 32, sortAt 32 XA XAS i = true) ∧
    (∀ k < 32, closedAt MULF xg 16 32 XA XAC k = true) ∧
    (∀ q < 32, XA q = ONE ∨ XA q = KY 0 ∨ witNC XA 32 (XA q) (XZ q) = true) ∧
    (∀ q < 32, MULF (XA q) (XA q) = ONE ∨ MULF (XA q) (XA q) = KY 0) ∧
    (∀ q < 32, ∀ y < 32, commOrS (KY 0) (XA q) (XA y) = true) := by
  have h : xB 0 = true := chX.all 0 (by norm_num)
  unfold xB at h
  rw [letB_eq] at h
  obtain ⟨h1, h⟩ := andB_eq_true h
  obtain ⟨h2, h⟩ := andB_eq_true h
  obtain ⟨h3, h⟩ := andB_eq_true h
  obtain ⟨h4, h⟩ := andB_eq_true h
  obtain ⟨h5, h6⟩ := andB_eq_true h
  refine ⟨rall h1, rall h2, rall h3, fun q hq => ?_, fun q hq => ?_,
    fun q hq => (allN_iff _ _).1 ((allN_iff _ _).1 h6 q hq)⟩
  · have e := (allN_iff _ _).1 h4 q hq
    simp only [letB_eq] at e
    rcases orB_true e with e | e
    · exact Or.inl (Nat.eq_of_beq_eq_true e)
    rcases orB_true e with e | e
    · exact Or.inr (Or.inl (Nat.eq_of_beq_eq_true e))
    · exact Or.inr (Or.inr e)
  · have e := (allN_iff _ _).1 h5 q hq
    simp only [letB_eq] at e
    rcases orB_true e with e | e
    · exact Or.inl (Nat.eq_of_beq_eq_true e)
    · exact Or.inr (Nat.eq_of_beq_eq_true e)

theorem Hyp.X_facts (H : Hyp z s) :
    (∀ k < 32, ∃ g ∈ XSub, enc6 g = XA k) ∧ Nat.card XSub = 32 ∧
      ∀ g ∈ XSub, ∃ k < 32, enc6 g = XA k := by
  have hG : ∀ j < xgens.length, xg j = enc6 (xgens.getD j 1) := by
    intro j hj
    have hj' : j < 16 := by simpa [xgens] using hj
    have e : xgens.getD j 1 = eltOf (xg j) := getD_map_range _ hj'
    rw [e, enc_eltOf (H.xg_ex j hj')]
  have hl : xgens.length = 16 := by simp [xgens]
  obtain ⟨h1, h2, h3, -⟩ := x_parts
  rw [← hl] at h1 h3
  obtain ⟨e1, -, e3⟩ := clos_card_proved enc6_enc xgens hG (by norm_num) h1 h2
  obtain ⟨e4, e5⟩ := e3 h3
  exact ⟨e1, e4, e5⟩

theorem Hyp.sup_eq_X (H : Hyp z s) :
    RSub 2 ⊓ Cen (z 0 * (z 1 * z 2)) ⊔ RSub 2 ⊓ Cen ((z 0)⁻¹ * (z 1 * z 2)) = XSub := by
  obtain ⟨-, h2, h3, -⟩ := iz_parts
  have gen_mem : ∀ {l : ℕ}, l < 16 → ∀ {g : H6}, enc6 g = xg l → g ∈ XSub := by
    intro l hl g eg
    rw [← eltOf_eq eg]
    exact Subgroup.subset_closure (List.mem_map.2 ⟨l, List.mem_range.2 hl, rfl⟩)
  apply le_antisymm
  · refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · obtain ⟨a, ha, ea⟩ := H.code_idx h2 H.ex2 hx
      exact gen_mem (l := a) (by omega) (by rw [ea, xg_lo ha])
    · obtain ⟨a, ha, ea⟩ := H.code_idx h3 H.ex3 hx
      refine gen_mem (l := a + 8) (by omega) ?_
      rw [ea, xg_hi (l := a + 8) (by omega), Nat.add_sub_cancel]
  · rw [XSub, Subgroup.closure_le]
    intro g hg
    simp only [xgens, Set.mem_setOf_eq, List.mem_map, List.mem_range] at hg
    obtain ⟨l, hl, rfl⟩ := hg
    have eg := enc_eltOf (H.xg_ex l hl)
    rw [SetLike.mem_coe]
    by_cases h : l < 8
    · exact Subgroup.mem_sup_left (H.idx_mem h2 H.ex2 h (eg.trans (xg_lo h)))
    · exact Subgroup.mem_sup_right (H.idx_mem h3 H.ex3 (by omega) (eg.trans (xg_hi h)))

theorem a_parts : (∀ l < 3, AG l < 32) ∧
    (∀ k < 8, treeAt MULF ONE (fun l => XA (AG l)) 3 AE AP k = true) ∧
    (∀ i < 8, sortAt 8 AE AS i = true) ∧
    (∀ k < 8, closedAt MULF (fun l => XA (AG l)) 3 8 AE AC k = true) ∧
    (∀ a < 8, MULF (AE a) (AE a) = ONE ∧ ∀ b < 8, commF (AE a) (AE b) = true) ∧
    AI 0 < 8 ∧ AE (AI 0) = KY 0 := by
  have h : aB 0 = true := chA.all 0 (by norm_num)
  unfold aB at h
  obtain ⟨h1, h⟩ := andB_eq_true h
  obtain ⟨h2, h⟩ := andB_eq_true h
  obtain ⟨h3, h⟩ := andB_eq_true h
  obtain ⟨h4, h⟩ := andB_eq_true h
  obtain ⟨h5, h⟩ := andB_eq_true h
  obtain ⟨h6, h7⟩ := andB_eq_true h
  refine ⟨fun l hl => Nat.blt_eq.mp ((allN_iff _ _).1 h1 l hl), rall h2, rall h3, rall h4,
    fun a ha => ?_, Nat.blt_eq.mp h6, Nat.eq_of_beq_eq_true h7⟩
  obtain ⟨e1, e2⟩ := andB_eq_true ((allN_iff _ _).1 h5 a ha)
  exact ⟨Nat.eq_of_beq_eq_true e1, (allN_iff _ _).1 e2⟩

theorem commOrS_spec {q y : H6} (h : commOrS (enc6 s) (enc6 q) (enc6 y) = true) :
    q * y * q⁻¹ * y⁻¹ = 1 ∨ q * y * q⁻¹ * y⁻¹ = s := by
  unfold commOrS at h
  simp only [letB_eq] at h
  rcases orB_true h with e | e
  · have e' : q * y = y * q := eq_of_enc (by rw [emul, emul]; exact Nat.eq_of_beq_eq_true e)
    left
    rw [e']
    group
  · have e' : q * y = s * (y * q) :=
      eq_of_enc (by rw [emul, emul, emul]; exact Nat.eq_of_beq_eq_true e)
    right
    rw [e']
    group

theorem Hyp.x_facts (H : Hyp z s) : Nat.card XSub = 32 ∧
    (∀ q ∈ XSub, (∀ y ∈ XSub, q * y = y * q) → q = 1 ∨ q = s) ∧
    (∀ q ∈ XSub, q * q = 1 ∨ q * q = s) ∧
    (∀ q ∈ XSub, ∀ y ∈ XSub, q * y * q⁻¹ * y⁻¹ = 1 ∨ q * y * q⁻¹ * y⁻¹ = s) ∧
    ∃ A : Subgroup H6, A ≤ XSub ∧ IsElemAb 2 3 A ∧ s ∈ A := by
  obtain ⟨x1, x2, x3⟩ := H.X_facts
  obtain ⟨-, -, -, hcen, hsq, hcomm⟩ := x_parts
  obtain ⟨ag, at1, at2, at3, aab, ai1, ai2⟩ := a_parts
  refine ⟨x2, fun q hq hc => ?_, fun q hq => ?_, fun q hq y hy => ?_, ?_⟩
  · obtain ⟨i, hi, ei⟩ := x3 q hq
    rcases hcen i hi with e | e | e
    · exact Or.inl (eq_of_enc (by rw [ei, e, enc_one]))
    · exact Or.inr (eq_of_enc (by rw [ei, e, H.es]))
    · unfold witNC at e
      obtain ⟨e1, e2⟩ := andB_eq_true e
      obtain ⟨y, hy, ey⟩ := x1 _ (Nat.blt_eq.mp e1)
      have hc' := commF_of_comm (hc y hy).symm
      rw [ey, ei] at hc'
      rw [hc'] at e2
      exact absurd e2 (by decide)
  · obtain ⟨i, hi, ei⟩ := x3 q hq
    rcases hsq i hi with e | e
    · exact Or.inl (eq_of_enc (by rw [emul, ei, e, enc_one]))
    · exact Or.inr (eq_of_enc (by rw [emul, ei, e, H.es]))
  · obtain ⟨i, hi, ei⟩ := x3 q hq
    obtain ⟨j, hj, ej⟩ := x3 y hy
    have h := hcomm i hi j hj
    rw [← ei, ← ej, ← H.es] at h
    exact commOrS_spec h
  · set agens : List H6 := (List.range 3).map fun l => eltOf (XA (AG l)) with hag
    have hex : ∀ l < 3, ∃ g ∈ XSub, enc6 g = XA (AG l) := fun l hl => x1 _ (ag l hl)
    have hG : ∀ j < agens.length, XA (AG j) = enc6 (agens.getD j 1) := by
      intro j hj
      have hj' : j < 3 := by simpa [hag] using hj
      have e : agens.getD j 1 = eltOf (XA (AG j)) := getD_map_range _ hj'
      obtain ⟨g, -, eg⟩ := hex j hj'
      rw [e, enc_eltOf ⟨g, eg⟩]
    have hl : agens.length = 3 := by simp [hag]
    rw [← hl] at at1 at3
    obtain ⟨a1, -, a3⟩ := clos_card_proved enc6_enc agens hG (by norm_num) at1 at2
    obtain ⟨a4, a5⟩ := a3 at3
    refine ⟨Subgroup.closure {g | g ∈ agens}, ?_, isElemAb_of (fun a ha b hb => ?_)
      (fun a ha => ?_) a4, ?_⟩
    · rw [Subgroup.closure_le]
      intro g hg
      simp only [hag, Set.mem_setOf_eq, List.mem_map, List.mem_range] at hg
      obtain ⟨l, hl', rfl⟩ := hg
      obtain ⟨g, hg, eg⟩ := hex l hl'
      rw [SetLike.mem_coe, eltOf_eq eg]
      exact hg
    · obtain ⟨i, hi, ei⟩ := a5 a ha
      obtain ⟨j, hj, ej⟩ := a5 b hb
      refine comm_of_commF ?_
      rw [ei, ej]
      exact (aab i hi).2 j hj
    · obtain ⟨i, hi, ei⟩ := a5 a ha
      exact eq_of_enc (by rw [emul, ei, enc_one]; exact (aab i hi).1)
    · obtain ⟨g, hg, eg⟩ := a1 _ ai1
      rwa [eq_of_enc (eg.trans (ai2.trans H.es.symm))] at hg

end CertificateChecks.KernelMisc.Sp6SR.Facts

end
