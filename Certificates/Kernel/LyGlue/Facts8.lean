module

public import Certificates.Kernel.LyGlue.Facts7
public import Certificates.Kernel.LyGlue.Facts4

set_option maxRecDepth 100000

public section

namespace CertificateChecks.KernelLy

open CFSG.KC.Enum CFSG.KS CFSG.KC.LyGlue CFSG.Sporadic.Recognition.LyonsSims Equiv Subgroup
  CFSG.Sporadic.Recognition CFSG.Certificates.Kernel.PkCV CFSG.Sporadic.Th

section

variable {Φ : ↥Ly0.UYperm ≃* ↥Ly1080.Y0}
  (hgen : ∀ k (hk : k < 4) (hmem : Ly0.uG k ∈ Ly0.UYperm),
    (Φ ⟨Ly0.uG k, hmem⟩ : Perm (Fin 1080)) = Ly1080.ug k)

include hgen in
theorem phi_word {ws : List Int} (hws : ∀ l ∈ ws, l ≠ 0 ∧ l.natAbs ≤ 4) :
    ∃ hmem : wordG (wordLetter Ly0.uG) ws ∈ Ly0.UYperm,
      (Φ ⟨_, hmem⟩ : Perm (Fin 1080)) = wordG (wordLetter Ly1080.ug) ws := by
  have hu : ∀ i, i < 4 → ∃ h : Ly0.uG i ∈ Ly0.UYperm,
      ((Ly1080.Y0.subtype.comp Φ.toMonoidHom) ⟨Ly0.uG i, h⟩) = Ly1080.ug i :=
    fun i hi => ⟨subset_closure ⟨⟨i, hi⟩, rfl⟩, hgen i hi _⟩
  exact wordG_hom Ly0.UYperm (Ly1080.Y0.subtype.comp Φ.toMonoidHom) _ _ ws
    (fun l hl => wordLetter_hom Ly0.UYperm _ Ly0.uG Ly1080.ug hu (hws l hl))

end

end CertificateChecks.KernelLy

end
