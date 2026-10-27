
module

public import Certificates.Kernel.LyModel.Range
public import Certificates.Kernel.LyBenes.Facts
public import Certificates.Kernel.LyGlue.Bind
public import CFSG.Certificates.Kernel.LyModel.RangeSound
public import CFSG.Certificates.Kernel.SporSch.TblSound

public section

namespace CertificateChecks.KernelLyModel

open Equiv CFSG.KC CFSG.KC.Benes CFSG.KC.LyBenes CFSG.KC.LyModel CertificateChecks.KernelLy
  CertificateChecks.KernelLyB CFSG.Sporadic.Recognition.LyonsSims CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native

section Net

variable {N : Nat} (hv : StagesValid 17 N) (h : rangeOK 66825 N = true)
include hv h

@[expose] noncomputable def netFin : Fin Ly0.deg → Fin Ly0.deg :=
  fun a => ⟨benesPerm 17 N a, rangeOK_sound (by norm_num) hv h a a.2⟩

theorem netFin_injective : Function.Injective (netFin hv h) := by
  intro a b e
  have e' := congrArg (fun x : Fin Ly0.deg => benesInv 17 N x) e
  simp only [netFin] at e'
  rw [benesInv_benesPerm hv, benesInv_benesPerm hv] at e'
  exact Fin.ext e'

@[expose] noncomputable def netPerm : Perm (Fin Ly0.deg) :=
  Equiv.ofBijective (netFin hv h) (Finite.injective_iff_bijective.1 (netFin_injective hv h))

theorem netPerm_apply (a : Fin Ly0.deg) : (netPerm hv h a : Nat) = benesPerm 17 N a := rfl

end Net

theorem rep_cT : Rep Ly0.deg Ly0.cT (netPerm (valid_all 0 (by decide)) ly6110_range0) := by
  intro i hi
  rw [idx_of_lt _ hi, Perm.smul_def, netPerm_apply]
  unfold ap
  rw [cT_get hi]
  exact ((bindOK_sound bind0).2 i hi).symm

theorem rep_dT : Rep Ly0.deg Ly0.dT (netPerm (valid_all 1 (by decide)) ly6110_range1) := by
  intro i hi
  rw [idx_of_lt _ hi, Perm.smul_def, netPerm_apply]
  unfold ap
  rw [dT_get hi]
  exact ((bindOK_sound bind1).2 i hi).symm

theorem cT_size : Ly0.cT.size = Ly0.deg := by
  unfold Ly0.cT Ly0.tabOfHex
  simp

theorem dT_size : Ly0.dT.size = Ly0.deg := by
  unfold Ly0.dT Ly0.tabOfHex
  simp

theorem permOK_invT {T : Table} {g : Perm (Fin Ly0.deg)} (hs : T.size = Ly0.deg)
    (hT : Rep Ly0.deg T g) : Ly0.permOK Ly0.deg T (invT Ly0.deg T) = true := by
  have hR := CFSG.KS.Tbl.invT_rep Ly0.deg_lt hT
  unfold Ly0.permOK
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨hs, CFSG.KS.Tbl.invT_size _ _⟩, allIn_eq_true.2 fun i _ hi => ?_⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  rw [hT i hi, hR i hi, hR _ (idx_lt g hi), hT _ (idx_lt g⁻¹ hi)]
  exact ⟨⟨⟨idx_lt g hi, idx_lt g⁻¹ hi⟩, idx_inv_idx g i⟩, idx_idx_inv g i⟩

theorem permOK_c : Ly0.permOK Ly0.deg Ly0.cT Ly0.invs0[0]! = true := by
  rw [Ly0.invs0_get (by decide), Ly0.tabs0_zero]
  exact permOK_invT cT_size rep_cT

theorem permOK_d : Ly0.permOK Ly0.deg Ly0.dT Ly0.invs0[1]! = true := by
  rw [Ly0.invs0_get (by decide), Ly0.tabs0_one]
  exact permOK_invT dT_size rep_dT

theorem rep_gens0' : ∀ k < 2, Rep Ly0.deg Ly0.tabs0[k]! (Ly0.gens0 k) := by
  intro k hk
  interval_cases k
  · rw [Ly0.tabs0_zero, Ly0.gens0_zero, Ly0.cG_def]
    exact Ly0.rep_permOfTab permOK_c
  · rw [Ly0.tabs0_one, Ly0.gens0_one, Ly0.dG_def]
    exact Ly0.rep_permOfTab permOK_d

theorem invOK_level0' : ∀ k < 2, invOK Ly0.deg Ly0.tabs0[k]! Ly0.invs0[k]! = true := by
  intro k hk
  rw [Ly0.invs0_get hk]
  exact CFSG.KS.Tbl.invOK_invT Ly0.deg_lt (rep_gens0' k hk)

theorem rep_gens1' : ∀ k < 2, Rep Ly0.deg Ly0.tabs1[k]! (Ly0.gens1 k) := by
  have hw := Ly0.rep_wT (invs := Ly0.invs0) rep_gens0' invOK_level0'
  intro k hk
  interval_cases k
  · rw [Ly0.tabs1_zero, Ly0.gens1_zero, Ly0.AG_def]
    exact hw Ly0.wordA (fun l hl => by simpa using Ly0.decodeWord_mem _ l hl)
  · rw [Ly0.tabs1_one, Ly0.gens1_one, Ly0.BG_def]
    exact hw Ly0.wordB (fun l hl => by simpa using Ly0.decodeWord_mem _ l hl)

theorem invOK_level1' : ∀ k < 2, invOK Ly0.deg Ly0.tabs1[k]! Ly0.invs1[k]! = true := by
  intro k hk
  rw [Ly0.invs1_get hk]
  exact CFSG.KS.Tbl.invOK_invT Ly0.deg_lt (rep_gens1' k hk)

theorem rep_yG' : ∀ k < 6, Rep Ly0.deg Ly0.tabs2[k]! (Ly0.yG k) := by
  have hw := Ly0.rep_wT (invs := Ly0.invs1) rep_gens1' invOK_level1'
  intro k hk
  rw [Ly0.tabs2_get hk, Ly0.yG_def]
  refine hw (CFSG.Sporadic.Recognition.McLMultiplier.mclGenWord k) ?_
  intro l hl
  interval_cases k <;> simp [CFSG.Sporadic.Recognition.McLMultiplier.mclGenWord] at hl <;> omega

theorem invOK_level2' : ∀ k < 6, invOK Ly0.deg Ly0.tabs2[k]! Ly0.invs2[k]! = true := by
  intro k hk
  rw [Ly0.invs2_get hk]
  exact CFSG.KS.Tbl.invOK_invT Ly0.deg_lt (rep_yG' k hk)

theorem tabCheck_true : Ly0.tabCheck = true := by
  unfold Ly0.tabCheck
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range]
  exact ⟨⟨⟨permOK_c, permOK_d⟩, invOK_level1'⟩, invOK_level2'⟩

theorem cL_eq_cG (a : Fin Ly0.deg) : cL a = (Ly0.cG a : Nat) := cL_eq tabCheck_true a

theorem dL_eq_dG (a : Fin Ly0.deg) : dL a = (Ly0.dG a : Nat) := dL_eq tabCheck_true a

end CertificateChecks.KernelLyModel

end
