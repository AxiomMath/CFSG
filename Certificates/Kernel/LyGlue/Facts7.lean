module

public import Certificates.Kernel.LyGlue.Facts2

set_option maxRecDepth 100000

public section

namespace CertificateChecks.KernelLy

open CFSG.KC.Enum CFSG.KS CFSG.KC.LyGlue CFSG.Sporadic.Recognition.LyonsSims Equiv Subgroup
  CFSG.Sporadic.Recognition CFSG.Certificates.Kernel.PkCV CFSG.Sporadic.Th

theorem fY_val {a : Fin Ly0.deg} (ha : a ∈ OY) : (fY a : Nat) = FY a := by
  obtain ⟨h1, -⟩ := yBlk_spec a a.2 ha
  simp [fY, Nat.mod_eq_of_lt h1]

theorem FY_lt {a : Fin Ly0.deg} (ha : a ∈ OY) : FY a < 1080 := (yBlk_spec a a.2 ha).1

theorem mem_Txy_of_lines {g : Perm (Fin Ly0.deg)} (hg : g ∈ Ly0.B0)
    (c1 : g * Ly0.xG * g⁻¹ = Ly0.xG ∨ g * Ly0.xG * g⁻¹ = Ly0.xG⁻¹)
    (c2 : g * Ly0.y0G * g⁻¹ = Ly0.y0G ∨ g * Ly0.y0G * g⁻¹ = Ly0.y0G⁻¹)
    (c3 : g * Ly0.w0G * g⁻¹ = Ly0.w0G ∨ g * Ly0.w0G * g⁻¹ = Ly0.w0G⁻¹) :
    (⟨g, hg⟩ : Ly0.B0) ∈ Ly0.Txy := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · refine mem_normalizer_zpowers_of_conj ?_
    rcases c1 with e | e
    · have : (⟨g, hg⟩ : Ly0.B0) * Ly0.xB * (⟨g, hg⟩ : Ly0.B0)⁻¹ = Ly0.xB := Subtype.ext e
      rw [this]; exact mem_zpowers _
    · have : (⟨g, hg⟩ : Ly0.B0) * Ly0.xB * (⟨g, hg⟩ : Ly0.B0)⁻¹ = Ly0.xB⁻¹ := Subtype.ext e
      rw [this]; exact inv_mem (mem_zpowers _)
  · refine mem_normalizer_zpowers_of_conj ?_
    rcases c2 with e | e
    · have : (⟨g, hg⟩ : Ly0.B0) * Ly0.yB * (⟨g, hg⟩ : Ly0.B0)⁻¹ = Ly0.yB := Subtype.ext e
      rw [this]; exact mem_zpowers _
    · have : (⟨g, hg⟩ : Ly0.B0) * Ly0.yB * (⟨g, hg⟩ : Ly0.B0)⁻¹ = Ly0.yB⁻¹ := Subtype.ext e
      rw [this]; exact inv_mem (mem_zpowers _)
  · refine mem_normalizer_zpowers_of_conj ?_
    rcases c3 with e | e
    · have : (⟨g, hg⟩ : Ly0.B0) * Ly0.wB * (⟨g, hg⟩ : Ly0.B0)⁻¹ = Ly0.wB := Subtype.ext e
      rw [this]; exact mem_zpowers _
    · have : (⟨g, hg⟩ : Ly0.B0) * Ly0.wB * (⟨g, hg⟩ : Ly0.B0)⁻¹ = Ly0.wB⁻¹ := Subtype.ext e
      rw [this]; exact inv_mem (mem_zpowers _)

theorem imgK_spec {ax ay aw : Nat} (h : imgK ax ay aw = true) :
    ay = uWord1080 yU ∧ ax = uWord1080 xU ∧
    ∀ j < 5, lineK (uWord1080 (Ly1080.txyWords.getD j [])) ax = true ∧
      lineK (uWord1080 (Ly1080.txyWords.getD j [])) ay = true ∧
      lineK (uWord1080 (Ly1080.txyWords.getD j [])) aw = true := by
  unfold imgK at h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h3, h4⟩ := (bAnd_iff _ _).1 h2
  refine ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h3, fun j hj => ?_⟩
  have h5 := allN_spec h4 j hj
  rw [CFSG.KS.PF.strictB_eqP] at h5
  obtain ⟨a1, a2⟩ := (bAnd_iff _ _).1 h5
  obtain ⟨a3, a4⟩ := (bAnd_iff _ _).1 a2
  exact ⟨a1, a3, a4⟩

theorem strict3 (a b c : Nat) (k : Nat → Nat → Nat → Bool) :
    (strictB a fun x => strictB b fun y => strictB c fun z => k x y z) = k a b c := by
  rw [CFSG.KS.PF.strictB_eqP, CFSG.KS.PF.strictB_eqP, CFSG.KS.PF.strictB_eqP]

theorem img_parts : imgW 256 (encW Ly0.wordY) = uWord1080 yU ∧
    imgW 36 (encW Ly0.wordX) = uWord1080 xU ∧
    ∀ j < 5, lineK (uWord1080 (Ly1080.txyWords.getD j [])) (imgW 36 (encW Ly0.wordX)) = true ∧
      lineK (uWord1080 (Ly1080.txyWords.getD j [])) (imgW 256 (encW Ly0.wordY)) = true ∧
      lineK (uWord1080 (Ly1080.txyWords.getD j [])) (imgY 8) = true :=
  imgK_spec ((strict3 _ _ _ imgK).symm.trans k_img)

end CertificateChecks.KernelLy

end
