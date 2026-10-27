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
  obtain ⟨φ, hsurj, hgen, hcomp⟩ := exists_phiT hM.tab hT
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
  refine ⟨(MulEquiv.ofBijective φ hbij).trans (MulEquiv.subgroupCongr eT),
    fun k hk hmem => hgen k hk, fun l hl hmem => ?_, by omega⟩
  ext i
  obtain ⟨hs, hi, hO⟩ := fT_ST i
  obtain ⟨h1, h2⟩ := hcomp ⟨Glue.txyBp l, hmem⟩ _ hO
  rw [hi] at h2
  change ((φ ⟨Glue.txyBp l, hmem⟩ : Perm (Fin 243)) i : Nat) = _
  rw [← h2, (fT_val h1).1]
  have hr4 : ∀ l' ∈ Ly1080.txyWords.getD l [], l' ≠ 0 ∧ l'.natAbs ≤ 4 := by
    rw [← txyWords_getD hl]
    exact fun l' hl' =>
      Ly1080.words_range₄ hY _ (List.mem_append_right _ (Ly1080.txyWords_get_mem hY hl)) l' hl'
  have hpt := uwPt_eq hM.tab _ hr4 ⟨ST i, hs⟩
  rw [← txyWords_getD hl] at hpt
  change FT (Glue.txyBp l ⟨ST i, hs⟩ : Nat) = _
  unfold Glue.txyBp
  rw [← hpt, txyWords_getD hl, agree_spec l hl i i.2]
  have hr5 : ∀ l' ∈ Ly243.txyWords.getD l [], l' ≠ 0 ∧ l'.natAbs ≤ 5 := by
    have he : Ly243.txyWords.getD l [] = Ly243.txyWords[l]! := by
      interval_cases l <;> rfl
    rw [he]
    exact fun l' hl' => by
      have := (Ly243.words_range_tr hT).1 _ (Ly243.txyWords_get_mem hT hl) l' hl'
      omega
  rw [ghWord_eq hT hr5]
  have e2 := congrArg (fun σ : Perm (Fin 243) => (σ i : Nat))
    (ev_wordC_letter (gcv hT) Ly243.gg (m := 5) (fun k hk => ev_gcv hT hk) hr5)
  rw [show (pg 8 (mask 8) (wordC (wordLetter (gcv hT)) (Ly243.txyWords.getD l [])).1 i : Nat) =
    (ev (wordC (wordLetter (gcv hT)) (Ly243.txyWords.getD l [])) i : Nat) by
      rw [ev_apply]; change _ = pg (wC 243) (mask (wC 243)) _ _; rw [wC243], e2]
  have he : Ly243.txyWords.getD l [] = Ly243.txyWords[l]! := by
    interval_cases l <;> rfl
  rw [he]
  rfl

end CertificateChecks.KernelLy

end
