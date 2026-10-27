module

public import Certificates.Kernel.HNDce2.RelsGlue
public import Certificates.Kernel.HNDce2.Glue
public import CFSG.Certificates.Kernel.Misc.Coset.TableFactSub
public import Certificates.Kernel.HNDce2.TabsA

public section

namespace CFSG.KD.HNDce2

open CFSG.Sporadic.Recognition.HNMultiplier CFSG.CosetTable CFSG.KC.MiscCoset CFSG.Certificates
  CFSG.LieType.Multipliers CFSG.Sporadic.Recognition.CoverRecipe

theorem l3_eq : hnL3.map encW = CFSG.KBRoute.F24321c.rels := by decide +kernel

@[expose] def decodeW (k : ℕ) (ws : List (List (ℕ × Bool))) : List (List (Fin k × Bool)) :=
  ws.map fun w => w.filterMap fun l => if h : l.1 < k then some (⟨l.1, h⟩, l.2) else none

@[expose] def hnL2t : List (List (Fin hnS1L.length × Bool)) :=
  decodeW hnS1L.length CFSG.KBRoute.F24321d.rels

@[expose] def hnL1t : List (List (Fin hnS2L.length × Bool)) :=
  decodeW hnS2L.length CFSG.KBRoute.F24321e.rels

theorem l2_eq : hnL2t.map encW = CFSG.KBRoute.F24321d.rels := by decide +kernel

theorem l1_eq : hnL1t.map encW = CFSG.KBRoute.F24321e.rels := by decide +kernel

@[expose] def hnL2u : List (List (Fin hnS1L.length × Bool)) :=
  restrictWords hnS1L (restrictWords hnTL (coverWords hnRelsMid hnCommWord ++ squareWords hnRelsMid))

@[expose] def hnL1u : List (List (Fin hnS2L.length × Bool)) :=
  restrictWords hnS2L (restrictWords hnS1L
    (restrictWords hnTL (coverWords hnRels2 hnCommWord ++ squareWords hnRels2)))

theorem hnL2t_u : ∀ w ∈ hnL2t, w ∈ hnL2u := by decide +kernel

theorem hnL1t_u : ∀ w ∈ hnL1t, w ∈ hnL1u := by decide +kernel

theorem hnL2t_mem : ∀ w ∈ hnL2t, w ∈ hnL2 := fun _ hw =>
  mem_restrictWords_of_subset (fun _ hv => mem_restrictWords_of_subset
    (fun _ hu => mem_cover₂Words.2 (List.mem_append.1 hu)) hv) (hnL2t_u _ hw)

theorem hnL1t_mem : ∀ w ∈ hnL1t, w ∈ hnL1 := fun _ hw =>
  mem_restrictWords_of_subset (fun _ hv => mem_restrictWords_of_subset
    (fun _ hu => mem_restrictWords_of_subset
      (fun _ hx => mem_cover₂Words.2 (List.mem_append.1 hx)) hu) hv) (hnL1t_u _ hw)

theorem fact3 : KB.TableFact hnTL.length (hnL3.map encW)
    ((subsetOf hnTL.length [0, 1, 2, 3, 4]).map fun x => [(x.val, true)]) 2 := by
  rw [l3_eq]
  exact CFSG.KBFact.F24321c

theorem fact2 : KB.TableFact hnS1L.length (hnL2t.map encW)
    (hnS2L.map fun x => [(x.val, true)]) 704 := by
  rw [l2_eq]
  exact CFSG.KBFact.F24321d

theorem fact1 : KB.TableFact hnS2L.length (hnL1t.map encW) [] 126000 := by
  rw [l1_eq]
  exact CFSG.KBFact.F24321e

theorem card_hnPR_le_tf : Finite hnPR ∧ Nat.card hnPR ≤ 177408000 := by
  obtain ⟨f, c⟩ := card_PG_le_chain₃_tf (ws := hnR) (S₁ := [0, 1, 2, 3, 4]) (S₂ := [0, 1])
    (by decide) (by decide) (by decide) hnL3_sub (fun w hw => hnL2_sub w (hnL2t_mem w hw))
    (fun w hw => hnL1_sub w (hnL1t_mem w hw)) fact3 fact2 fact1
  exact ⟨f, c.trans (by norm_num)⟩

end CFSG.KD.HNDce2

namespace CertificateChecks.KernelHNMult

open CFSG.Sporadic.Recognition.HNMultiplier CFSG.CosetTable CFSG.KC.MiscCoset
  CFSG.LieType.Multipliers CFSG.Sporadic.Recognition.CoverRecipe
  CFSG.Sporadic.Recognition.CoverTransfer CFSG.Sporadic.Recognition.CoverBootstrap

theorem card_PC1_le_tf : Finite PC1 ∧ Nat.card PC1 ≤ 704 * 126000 :=
  card_PG_le_chain₂_tf (S := [0, 1]) (by decide) (by decide)
    (fun w hw => hnL2_mem w (CFSG.KD.HNDce2.hnL2t_mem w hw))
    (fun w hw => hnL1_mem w (CFSG.KD.HNDce2.hnL1t_mem w hw))
    CFSG.KD.HNDce2.fact2 CFSG.KD.HNDce2.fact1

theorem hnPsi_injective_gf_tf : Function.Injective (hnPsi hnGens_gf) := by
  obtain ⟨hfin, hle⟩ := card_PC1_le_tf
  have := hfin
  refine injective_of_card_le (hnPsi hnGens_gf) ?_
  rw [range_hnPsi hnGens_gf, closure_sigma_eq]
  exact hle.trans (le_trans (by norm_num) card_closure_ge)

end CertificateChecks.KernelHNMult

end
