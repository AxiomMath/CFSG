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
  (hc : ∀ (x : Perm (Fin Ly0.deg)) (hx : x ∈ Ly0.UYperm), ∀ a ∈ OY,
    x a ∈ OY ∧ fY (x a) = (Φ ⟨x, hx⟩ : Perm (Fin 1080)) (fY a))

include hc in
theorem phi_pt (x : Perm (Fin Ly0.deg)) (hx : x ∈ Ly0.UYperm) (j : Fin 1080) :
    (((Φ ⟨x, hx⟩ : Perm (Fin 1080)) j : Fin 1080) : Nat) = FY (x ⟨SY j, (fY_SY j).1⟩) ∧
      x ⟨SY j, (fY_SY j).1⟩ ∈ OY := by
  obtain ⟨hs, hj, hO⟩ := fY_SY j
  obtain ⟨h1, h2⟩ := hc x hx _ hO
  rw [hj] at h2
  exact ⟨by rw [← h2, fY_val h1], h1⟩

include hgen in
theorem phi_word {ws : List Int} (hws : ∀ l ∈ ws, l ≠ 0 ∧ l.natAbs ≤ 4) :
    ∃ hmem : wordG (wordLetter Ly0.uG) ws ∈ Ly0.UYperm,
      (Φ ⟨_, hmem⟩ : Perm (Fin 1080)) = wordG (wordLetter Ly1080.ug) ws := by
  have hu : ∀ i, i < 4 → ∃ h : Ly0.uG i ∈ Ly0.UYperm,
      ((Ly1080.Y0.subtype.comp Φ.toMonoidHom) ⟨Ly0.uG i, h⟩) = Ly1080.ug i :=
    fun i hi => ⟨subset_closure ⟨⟨i, hi⟩, rfl⟩, hgen i hi _⟩
  exact wordG_hom Ly0.UYperm (Ly1080.Y0.subtype.comp Φ.toMonoidHom) _ _ ws
    (fun l hl => wordLetter_hom Ly0.UYperm _ Ly0.uG Ly1080.ug hu (hws l hl))

include hc in
theorem phi_eq_of_img (hY : Ly1080.YOK) (x : Perm (Fin Ly0.deg))
    (hx : x ∈ Ly0.UYperm) {f : Nat → Nat} (hf : ∀ j : Fin 1080, f j = FY (x ⟨SY j, (fY_SY j).1⟩))
    {ws : List Int} (hws : ∀ l ∈ ws, l ≠ 0 ∧ l.natAbs ≤ 4)
    (hA : pmk 1080 11 f = uWord1080 ws) :
    (Φ ⟨x, hx⟩ : Perm (Fin 1080)) = wordG (wordLetter Ly1080.ug) ws := by
  ext j
  have hlt : ∀ y < 1080, f y < 2 ^ 11 := by
    intro y hy
    rw [hf ⟨y, hy⟩]
    have := FY_lt (phi_pt hc x hx ⟨y, hy⟩).2
    omega
  have e1 := pg_pmk (n := 1080) (by norm_num) hlt j.2
  rw [hA, uWord1080_eq hY hws, hf j] at e1
  rw [(phi_pt hc x hx j).1, ← e1]
  have e2 := congrArg (fun σ : Perm (Fin 1080) => (σ j : Nat))
    (ev_wordC_letter (ucv hY) Ly1080.ug (m := 4) (fun k hk => ev_ucv hY hk) hws)
  rw [← e2, ev_apply]
  change _ = pg (wC 1080) (mask (wC 1080)) _ _
  rw [wC1080]

end

end CertificateChecks.KernelLy

end
