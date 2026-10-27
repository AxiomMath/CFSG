module

public import Certificates.Kernel.Q16L34.Checks
public import Certificates.Kernel.Census.L34
public import CFSG.Certificates.Kernel.Q16Q16KSound
public import CFSG.Certificates.Kernel.Census.E16Sound

public section

namespace CertificateChecks.KernelQ16L34

open CFSG.KC.Q16Q16K CFSG.KC.Census CFSG.ComponentClassification.RankTwoL3Four.HypII
open CFSG.ComponentClassification.RankTwoSporadic.Cert CFSG.RankThree.Native
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf
open CertificateChecks.KernelCensus.L34K

@[expose] noncomputable def l34S : Subgroup (Equiv.Perm (Fin 42)) :=
  Subgroup.closure (permsA 42 (l34SG.map (unpackP 42 6)))

theorem q16L34_canon : l34SG.toList.all (canon1 42 6) = true ∧
    l34CS.pts.toList.all (canon1 42 6) = true := by
  have h := kCanon
  simp only [canonP, Bool.and_eq_true] at h
  exact ⟨h.1.1.1, h.1.2⟩

theorem q16L34_free : q16L34R.all (chkX 42 6 q16L34R) = true := by
  have h := all_drop_chunk (a := 0) (B := 32) (allL_eq_all _ _ ▸ q16L34F0)
    (all_drop_chunk (a := 32) (B := 32) (allL_eq_all _ _ ▸ q16L34F1)
    (all_drop_chunk (a := 64) (B := 32) (allL_eq_all _ _ ▸ q16L34F2)
    (all_drop_chunk (a := 96) (B := 32) (allL_eq_all _ _ ▸ q16L34F3)
    (all_drop_chunk (a := 128) (B := 32) (allL_eq_all _ _ ▸ q16L34F4)
    (all_drop_chunk (a := 160) (B := 32) (allL_eq_all _ _ ▸ q16L34F5)
    (all_drop_chunk (a := 192) (B := 32) (allL_eq_all _ _ ▸ q16L34F6)
      (allL_eq_all _ _ ▸ q16L34F7)))))))
  rw [List.drop_zero] at h
  exact h

theorem q16L34_card_noQ16Q16 : Nat.card ↥l34S = 2 ^ 8 ∧ NoQ16Q16 ↥l34S := by
  obtain ⟨hg, hc⟩ := q16L34_canon
  have hpts : l34CS.pts.toList = q16L34R.map Prod.fst := by
    rw [q16L34R, List.map_map]
    exact ((List.map_congr_left fun _ _ => rfl).trans (List.map_id _)).symm
  have hrec : q16L34R.all (recOK 42 6) = true := by
    rw [q16L34R, List.all_map, List.all_eq_true]
    intro x hx
    exact recOK_mkRec (List.all_eq_true.1 hc x hx)
  obtain ⟨h1, h2⟩ := q16K_sound (by norm_num) (by norm_num) l34PS_lt hg hpts hrec kS q16L34_free
  refine ⟨?_, h2⟩
  unfold l34S
  rw [h1, q16L34R, List.length_map, Array.length_toList]
  decide +kernel

theorem q16L34_le_R : l34S ≤ CFSG.ComponentClassification.PSL3Four.R := by
  have h := l34CheckWII_eq_true
  unfold l34CheckWII at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨-, hslp⟩, -⟩, hin⟩, -⟩ := h
  have hW : Subgroup.closure (permsA 42 l34GensR) ≤ CFSG.ComponentClassification.PSL3Four.R := by
    rw [Subgroup.closure_le]
    rintro _ ⟨l, hl, rfl⟩
    obtain ⟨a, ha, hT⟩ := CFSG.ComponentClassification.PSL3Four.gTabs_tabs l hl
    change permOfArr 42 CFSG.PSL3Four.Native.gTabs[l]! ∈ _
    rw [permOfArr_eq_of_rep fun x => hT.2 x]
    exact Subgroup.subset_closure ha
  refine le_trans ?_ hW
  rw [l34S, Subgroup.closure_le]
  rintro _ ⟨k, hk, rfl⟩
  have hk' : k < l34SG.size := by simpa using hk
  have hv : validA 42 (l34SG.map (unpackP 42 6))[k]! = true := by
    rw [SP.map_get _ _ hk', SP.validA_unpack (by norm_num)
      (List.all_eq_true.1 q16L34_canon.1 _ (by
        rw [getElem!_pos l34SG k hk']
        exact Array.getElem_mem_toList hk'))]
    have hS := kS
    unfold penumOK at hS
    simp only [Bool.and_eq_true] at hS
    exact List.all_eq_true.1 hS.1 k (List.mem_range.2 hk')
  exact mem_closure_of_inRegsL hslp hv (allLt_spec hin hk)

end CertificateChecks.KernelQ16L34
