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

theorem yx_eq_u (hM : Ly0.ModelChecks) : Ly0.y0G = Yu ∧ Ly0.xG = Xu := by
  have h : bAnd(lyBase3 yShort (uE yU), lyBase3 (cdE Ly0.wordX) (uE xU)) = true := k_img
  obtain ⟨hy, hx⟩ := (bAnd_iff (lyBase3 yShort (uE yU)) (lyBase3 (cdE Ly0.wordX) (uE xU))).1 h
  refine ⟨?_, ?_⟩
  · rw [← prodP_yShort hM, lyBase3_spec hM hy]
    exact prodP_uE hM.tab yU yU_range
  · rw [xG_eq_word hM, ← prodP_cdE hM.tab Ly0.wordX (fun l hl => Ly0.decodeWord_mem _ l hl),
      lyBase3_spec hM hx]
    exact prodP_uE hM.tab xU xU_range

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
  obtain ⟨Φ, hgen, -, hcard⟩ := exists_Phiy hM hY hcY
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
  obtain ⟨hyeq, hxeq⟩ := yx_eq_u hM
  have hyi : Ly0.y0G⁻¹ = Ly0.y0G * Ly0.y0G :=
    inv_eq_of_mul_eq_one_right (by rw [← pow_three]; exact h3)
  have hweq : Ly0.w0G = Wu := by
    rw [Ly0.w0G_eq, hyi, hyeq]
    rfl
  have htxy : ∀ j < 5, ∃ hmem : Glue.txyBp j ∈ Ly0.UYperm,
      (Φ ⟨Glue.txyBp j, hmem⟩ : Perm (Fin 1080)) = Ly1080.txyG j := by
    intro j hj
    have hr : ∀ l ∈ Ly1080.txyWords[j]!, l ≠ 0 ∧ l.natAbs ≤ 4 := fun l hl =>
      Ly1080.words_range₄ hY _ (List.mem_append_right _ (Ly1080.txyWords_get_mem hY hj)) l hl
    obtain ⟨hm, he⟩ := phi_word hgen hr
    exact ⟨hm, he⟩
  refine ⟨Φ, hgen, fun l hl hmem => (htxy l hl).2, hcard, eY, hyeq, hxeq, hweq, ?_⟩
  intro j hj x hx
  have hr : ∀ l ∈ Ly1080.txyWords.getD j [], l ≠ 0 ∧ l.natAbs ≤ 4 := by
    rw [← txyWords_getD hj]
    exact fun l hl =>
      Ly1080.words_range₄ hY _ (List.mem_append_right _ (Ly1080.txyWords_get_mem hY hj)) l hl
  have hT : prodP baseP (uEs (Ly1080.txyWords.getD j [])) = Glue.txyBp j := by
    rw [prodP_uEs hM.tab _ hr, Glue.txyBp, txyWords_getD hj]
  have hk : lyConjK (uEs (Ly1080.txyWords.getD j [])) (cdE Ly0.wordX) = true ∧
      lyConjK (uEs (Ly1080.txyWords.getD j [])) yShort = true ∧
      lyConjK (uEs (Ly1080.txyWords.getD j [])) wShort = true := by
    have h := allN_spec (n := 5) k_txyConj j hj
    obtain ⟨a1, a2⟩ := (bAnd_iff _ _).1 h
    obtain ⟨a3, a4⟩ := (bAnd_iff _ _).1 a2
    exact ⟨a1, a3, a4⟩
  rcases hx with rfl | rfl | rfl
  · have h := lyConjK_spec hM hk.1
    rwa [hT, prodP_cdE hM.tab Ly0.wordX (fun l hl => Ly0.decodeWord_mem _ l hl),
      ← xG_eq_word hM] at h
  · have h := lyConjK_spec hM hk.2.1
    rwa [hT, prodP_yShort hM] at h
  · have h := lyConjK_spec hM hk.2.2
    rwa [hT, prodP_wShort hM, ← hweq] at h

end CertificateChecks.KernelLy

end
