module

public import Certificates.Kernel.LyGlue.Facts9
public import Certificates.Kernel.LyGlue.Facts5
public import Certificates.Kernel.LyGlue.Facts6
public import Certificates.Kernel.LyGlue.Facts8

set_option maxRecDepth 100000

public section

namespace CertificateChecks.KernelLy

open CFSG.KC.Enum CFSG.KS CFSG.KC.LyGlue CFSG.Sporadic.Recognition.LyonsSims Equiv Subgroup
  CFSG.Sporadic.Recognition CFSG.Certificates.Kernel.PkCV CFSG.Sporadic.Th

@[expose] noncomputable def imgCV {Φ : ↥Ly0.UYperm ≃* ↥Ly1080.Y0}
    (hc : ∀ (x : Perm (Fin Ly0.deg)) (hx : x ∈ Ly0.UYperm), ∀ a ∈ OY,
      x a ∈ OY ∧ fY (x a) = (Φ ⟨x, hx⟩ : Perm (Fin 1080)) (fY a))
    (x : Perm (Fin Ly0.deg)) (hx : x ∈ Ly0.UYperm) (f : Nat → Nat)
    (hf : ∀ j : Fin 1080, f j = FY (x ⟨SY j, (fY_SY j).1⟩)) : CV 1080 :=
  cvOf (pmk 1080 11 f) (Φ ⟨x, hx⟩)
    (by
      rw [wC1080]
      refine pmk_shr (by norm_num) (by norm_num) fun y hy => ?_
      rw [hf ⟨y, hy⟩]
      have := FY_lt (phi_pt hc x hx ⟨y, hy⟩).2
      omega)
    (fun i hi => by
      rw [wC1080]
      have hlt : ∀ y < 1080, f y < 2 ^ 11 := by
        intro y hy
        rw [hf ⟨y, hy⟩]
        have := FY_lt (phi_pt hc x hx ⟨y, hy⟩).2
        omega
      rw [pg_pmk (by norm_num) hlt hi, hf ⟨i, hi⟩, (phi_pt hc x hx ⟨i, hi⟩).1])

theorem imgCV_val {Φ : ↥Ly0.UYperm ≃* ↥Ly1080.Y0} {hc} {x} {hx} {f} {hf} :
    (imgCV (Φ := Φ) hc x hx f hf).1 = pmk 1080 11 f := rfl

theorem ev_imgCV {Φ : ↥Ly0.UYperm ≃* ↥Ly1080.Y0} {hc} {x} {hx} {f} {hf} :
    ev (imgCV (Φ := Φ) hc x hx f hf) = Φ ⟨x, hx⟩ := ev_cvOf _ _ _ _

theorem ptY (hM : Ly0.ModelChecks) (j : Fin 1080) :
    FY (cdPt 256 (encW Ly0.wordY) (SY j)) = FY (Ly0.y0G ⟨SY j, (fY_SY j).1⟩) := by
  rw [← wordY_len, Ly0.y0G_def]
  exact congrArg FY (cdPt_eq hM.tab _ (fun l hl => Ly0.decodeWord_mem _ l hl) ⟨SY j, _⟩)

theorem ptX (hM : Ly0.ModelChecks) (j : Fin 1080) :
    FY (cdPt 36 (encW Ly0.wordX) (SY j)) = FY (Ly0.xG ⟨SY j, (fY_SY j).1⟩) := by
  rw [← wordX_len, xG_eq_word hM]
  exact congrArg FY (cdPt_eq hM.tab _ (fun l hl => Ly0.decodeWord_mem _ l hl) ⟨SY j, _⟩)

theorem yIso (hM : Ly0.ModelChecks) (hY : Ly1080.YOK)
    (hcY : Nat.card Ly0.Y0 ≤ 349920) :
    ∃ Φy : ↥Ly0.UYperm ≃* ↥Ly1080.Y0,
      (∀ k (hk : k < 4) (hmem : Ly0.uG k ∈ Ly0.UYperm),
        (Φy ⟨Ly0.uG k, hmem⟩ : Perm (Fin 1080)) = Ly1080.ug k) ∧
      (∀ (l : ℕ) (_ : l < 5) (hmem : Glue.txyBp l ∈ Ly0.UYperm),
        (Φy ⟨Glue.txyBp l, hmem⟩ : Perm (Fin 1080)) = Ly1080.txyG l) ∧
      Nat.card ↥Ly0.UYperm = 349920 ∧
      Ly0.UYperm.subgroupOf Ly0.B0 = Ly0.Y0 ∧
      Ly0.y0G = Yu ∧ Ly0.xG = Xu ∧ Ly0.w0G = Wu ∧
      (∀ j < 5, ∀ x ∈ ({Ly0.xG, Ly0.y0G, Ly0.w0G} : Set (Perm (Fin Ly0.deg))),
        Glue.txyBp j * x * (Glue.txyBp j)⁻¹ = x ∨ Glue.txyBp j * x * (Glue.txyBp j)⁻¹ = x⁻¹) := by
  obtain ⟨Φ, hgen, hc, hcard⟩ := exists_Phiy hM hY hcY
  have hle : Ly0.UYperm.subgroupOf Ly0.B0 ≤ Ly0.Y0 := Ly0.UY_le_Y0 hM.tab hM.struct hM.cp1 hM.inv
  have eY : Ly0.UYperm.subgroupOf Ly0.B0 = Ly0.Y0 := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe Ly0.UYperm_le_B0).toEquiv, hcard]
    exact hcY
  have memU : ∀ b : Ly0.B0, b ∈ Ly0.Y0 → (b : Perm (Fin Ly0.deg)) ∈ Ly0.UYperm := by
    intro b hb
    rw [← eY] at hb
    exact hb
  obtain ⟨-, h3, -⟩ := Ly0.cp1_facts hM.tab hM.struct hM.cp1
  obtain ⟨hcx, -⟩ := Ly0.cp1_facts hM.tab hM.struct hM.cp1
  have hyU : Ly0.y0G ∈ Ly0.UYperm := memU Ly0.yB (Subgroup.le_normalizer (mem_zpowers _))
  obtain ⟨hYuU, hYu⟩ := phi_word hgen (ws := yU) (fun l hl => by have := yU_range l hl; omega)
  have hy1 : (Φ ⟨Ly0.y0G, hyU⟩ : Perm (Fin 1080)) = wordG (wordLetter Ly1080.ug) yU :=
    phi_eq_of_img hc hY Ly0.y0G hyU (f := fun j => FY (cdPt 256 (encW Ly0.wordY) (SY j)))
      (ptY hM) (fun l hl => by have := yU_range l hl; omega) img_parts.1
  have hyeq : Ly0.y0G = Yu :=
    congrArg Subtype.val (Φ.injective (Subtype.ext (hy1.trans hYu.symm)))
  have hxY0 : Ly0.xB ∈ Ly0.Y0 := by
    refine mem_normalizer_zpowers_of_conj ?_
    have : Ly0.xB * Ly0.yB * Ly0.xB⁻¹ = Ly0.yB := by
      apply Subtype.ext
      change Ly0.xG * Ly0.y0G * Ly0.xG⁻¹ = Ly0.y0G
      rw [← hcx]
      group
    rw [this]
    exact mem_zpowers _
  have hxU : Ly0.xG ∈ Ly0.UYperm := memU Ly0.xB hxY0
  obtain ⟨hXuU, hXu⟩ := phi_word hgen (ws := xU) (fun l hl => by have := xU_range l hl; omega)
  have hx1 : (Φ ⟨Ly0.xG, hxU⟩ : Perm (Fin 1080)) = wordG (wordLetter Ly1080.ug) xU :=
    phi_eq_of_img hc hY Ly0.xG hxU (f := fun j => FY (cdPt 36 (encW Ly0.wordX) (SY j)))
      (ptX hM) (fun l hl => by have := xU_range l hl; omega) img_parts.2.1
  have hxeq : Ly0.xG = Xu :=
    congrArg Subtype.val (Φ.injective (Subtype.ext (hx1.trans hXu.symm)))
  have hyi : Ly0.y0G⁻¹ = Ly0.y0G * Ly0.y0G :=
    inv_eq_of_mul_eq_one_right (by rw [← pow_three]; exact h3)
  have hweq : Ly0.w0G = Wu := by
    rw [Ly0.w0G_eq, hyi, hyeq]
    rfl
  have hWY : Wu * Yu = Yu * Wu :=
    conj_perm hM.tab (j := 0) (by norm_num) (tl_w hM.tab) (tl_y hM.tab) (tl_y hM.tab) (tl_w hM.tab)
  have hwY0 : Ly0.wB ∈ Ly0.Y0 := by
    refine mem_normalizer_zpowers_of_conj ?_
    have : Ly0.wB * Ly0.yB * Ly0.wB⁻¹ = Ly0.yB := by
      apply Subtype.ext
      change Ly0.w0G * Ly0.y0G * Ly0.w0G⁻¹ = Ly0.y0G
      rw [hweq, hyeq, hWY]
      group
    rw [this]
    exact mem_zpowers _
  have hwU : Ly0.w0G ∈ Ly0.UYperm := memU Ly0.wB hwY0
  have htxy : ∀ j < 5, ∃ hmem : Glue.txyBp j ∈ Ly0.UYperm,
      (Φ ⟨Glue.txyBp j, hmem⟩ : Perm (Fin 1080)) = Ly1080.txyG j := by
    intro j hj
    have hr : ∀ l ∈ Ly1080.txyWords[j]!, l ≠ 0 ∧ l.natAbs ≤ 4 := fun l hl =>
      Ly1080.words_range₄ hY _ (List.mem_append_right _ (Ly1080.txyWords_get_mem hY hj)) l hl
    obtain ⟨hm, he⟩ := phi_word hgen hr
    exact ⟨hm, he⟩
  refine ⟨Φ, hgen, fun l hl hmem => (htxy l hl).2, hcard, eY, hyeq, hxeq, hweq, ?_⟩
  intro j hj x hx
  obtain ⟨hmT, hT⟩ := htxy j hj
  have hr : ∀ l ∈ Ly1080.txyWords.getD j [], l ≠ 0 ∧ l.natAbs ≤ 4 := by
    rw [← txyWords_getD hj]
    exact fun l hl =>
      Ly1080.words_range₄ hY _ (List.mem_append_right _ (Ly1080.txyWords_get_mem hY hj)) l hl
  set T : CV 1080 := wordC (wordLetter (ucv hY)) (Ly1080.txyWords.getD j []) with hTdef
  have hTv : T.1 = uWord1080 (Ly1080.txyWords.getD j []) := (uWord1080_eq hY hr).symm
  have hTe : ev T = (Φ ⟨Glue.txyBp j, hmT⟩ : Perm (Fin 1080)) := by
    rw [hT, hTdef, ev_wordC_letter (ucv hY) Ly1080.ug (m := 4) (fun k hk => ev_ucv hY hk) hr,
      ← txyWords_getD hj]
    rfl
  obtain ⟨hlx, hly, hlw⟩ := img_parts.2.2 j hj
  rcases hx with rfl | rfl | rfl
  · let A := imgCV hc Ly0.xG hxU (fun j => FY (cdPt 36 (encW Ly0.wordX) (SY j))) (ptX hM)
    have h := lineK_spec (T := T) (A := A) (by rw [hTv, imgCV_val]; exact hlx)
    rw [hTe, ev_imgCV] at h
    exact line_of_phi hxU hmT h
  · let A := imgCV hc Ly0.y0G hyU (fun j => FY (cdPt 256 (encW Ly0.wordY) (SY j))) (ptY hM)
    have h := lineK_spec (T := T) (A := A) (by rw [hTv, imgCV_val]; exact hly)
    rw [hTe, ev_imgCV] at h
    exact line_of_phi hyU hmT h
  · let A := imgCV hc Ly0.w0G hwU (fun j => FY (tl (tIdx 8) (SY j)))
      (fun j => by rw [tl_w hM.tab ⟨SY j, (fY_SY j).1⟩, hweq])
    have h := lineK_spec (T := T) (A := A) (by rw [hTv, imgCV_val]; exact hlw)
    rw [hTe, ev_imgCV] at h
    exact line_of_phi hwU hmT h

end CertificateChecks.KernelLy

end
