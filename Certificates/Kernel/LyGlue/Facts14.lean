module

public import Certificates.Kernel.LyGlue.Facts13
public import Certificates.Kernel.LyGlue.Facts11
public import Certificates.Kernel.LyGlue.Facts12
public import Certificates.Kernel.LyGlue.Facts9

set_option maxRecDepth 100000

public section

namespace CertificateChecks.KernelLy

open CFSG.KC.Enum CFSG.KS CFSG.KC.LyGlue CFSG.Sporadic.Recognition.LyonsSims Equiv Subgroup
  CFSG.Sporadic.Recognition CFSG.Certificates.Kernel.PkCV CFSG.Sporadic.Th

theorem xIso (hM : Ly0.ModelChecks) (hY : Ly1080.YOK) (hT : Ly243.trCheck = true)
    (hcT : Nat.card Ly0.Tx ≤ 7776) (hxeq : Ly0.xG = Xu) (hyeq : Ly0.y0G = Yu)
    (hweq : Ly0.w0G = Wu) :
    ∃ Φx : ↥(closure (Glue.txG '' {k | k < 4})) ≃* ↥Ly243.Tx0,
      (∀ (k : ℕ) (_ : k < 4) (hmem : Glue.txG k ∈ closure (Glue.txG '' {k | k < 4})),
        (Φx ⟨Glue.txG k, hmem⟩ : Perm (Fin Ly243.deg)) = Ly243.gg k) ∧
      (∀ (l : ℕ) (_ : l < 5) (hmem : Glue.txyBp l ∈ closure (Glue.txG '' {k | k < 4})),
        (Φx ⟨Glue.txyBp l, hmem⟩ : Perm (Fin Ly243.deg)) = Ly243.txyG l) ∧
      Nat.card ↥(closure (Glue.txG '' {k | k < 4})) = 7776 := by
  obtain ⟨φ, hsurj, hgen, -⟩ := exists_phiT hM.tab hT
  have eT : closure (Ly243.gg '' {k | k < 4}) = Ly243.Tx0 :=
    le_antisymm ((closure_le _).2 (by rintro _ ⟨k, hk, rfl⟩; exact Ly243.gg_mem_Tx0 hT hk))
      (Glue.Tx0_le_closure243 hT)
  have hcP : Nat.card ↥(closure (Glue.txG '' {k | k < 4})) ≤ 7776 := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe Glue.Pxp_le_B0).toEquiv]
    exact (Subgroup.card_le_of_le (Pxp_sub_le_Tx' hM hxeq hyeq hweq)).trans hcT
  have hle1 := Nat.card_le_card_of_surjective φ hsurj
  have hge : 7776 ≤ Nat.card ↥(closure (Ly243.gg '' {k | k < 4})) := by
    rw [eT]
    exact card_Tx0_ge hT
  have hbij : Function.Bijective φ := hsurj.bijective_of_nat_card_le (by omega)
  let Φx := (MulEquiv.ofBijective φ hbij).trans (MulEquiv.subgroupCongr eT)
  refine ⟨Φx, fun k hk hmem => hgen k hk, fun l hl hmem => ?_, by omega⟩
  have hr4 : ∀ l' ∈ Ly1080.txyWords.getD l [], l' ≠ 0 ∧ l'.natAbs ≤ 4 := by
    rw [← txyWords_getD hl]
    exact fun l' hl' =>
      Ly1080.words_range₄ hY _ (List.mem_append_right _ (Ly1080.txyWords_get_mem hY hl)) l' hl'
  have h4 : ∀ l' ∈ Ly243.txyWords.getD l [], l' ≠ 0 ∧ l'.natAbs ≤ 4 := by
    interval_cases l <;> decide
  let ψ := Ly243.Tx0.subtype.comp Φx.toMonoidHom
  obtain ⟨h, hψ⟩ := wordG_hom _ ψ (wordLetter Glue.txG) (wordLetter Ly243.gg) _
    fun l' hl' => wordLetter_hom _ ψ Glue.txG Ly243.gg (n := 4)
      (fun i hi => ⟨subset_closure ⟨i, hi, rfl⟩, hgen i hi⟩) (h4 l' hl')
  have e : (⟨Glue.txyBp l, hmem⟩ : ↥(closure (Glue.txG '' {k | k < 4}))) = ⟨_, h⟩ := by
    apply Subtype.ext
    change wordG (wordLetter Ly0.uG) Ly1080.txyWords[l]! = _
    rw [txyWords_getD hl]
    exact txyBp_txG hM hl hr4 h4
  rw [e]
  change ψ _ = _
  rw [hψ]
  have he : Ly243.txyWords.getD l [] = Ly243.txyWords[l]! := by
    interval_cases l <;> rfl
  rw [he]
  rfl

end CertificateChecks.KernelLy

end
