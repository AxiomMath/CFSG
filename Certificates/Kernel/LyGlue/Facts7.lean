module

public import Certificates.Kernel.LyGlue.Facts2

set_option maxRecDepth 100000

public section

namespace CertificateChecks.KernelLy

open CFSG.KC.Enum CFSG.KS CFSG.KC.LyGlue CFSG.Sporadic.Recognition.LyonsSims Equiv Subgroup
  CFSG.Sporadic.Recognition CFSG.Certificates.Kernel.PkCV CFSG.Sporadic.Th

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

end CertificateChecks.KernelLy

end
