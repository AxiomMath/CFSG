module

public import CFSG.Sporadic.Recognition.HNMultiplier
public import CFSG.Sporadic.Recognition.CoverChainSub
public import Certificates.Kernel.HNMult.ChainCard
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Sporadic.HN
public import CFSG.Sporadic.HN.CertificateBase
public import CFSG.Sporadic.Recognition.HNMultiplierTables

public section

namespace CFSG.Sporadic.Recognition.HNMultiplier

open CFSG.CosetTable CFSG.LieType.Multipliers CFSG.Sporadic.Recognition.CoverRecipe
  CFSG.Sporadic.Recognition.CoverTransfer CFSG.Sporadic.Recognition.CoverBootstrap Subgroup

noncomputable abbrev hnHP : Subgroup (PG 7 hnCoverPlus) :=
  genSub {r : FreeGroup (Fin 7) | r ∈ hnCoverPlus.map FreeGroup.mk} hnTL

end CFSG.Sporadic.Recognition.HNMultiplier

namespace CertificateChecks.KernelHNMult

open CFSG.Sporadic.Recognition.HNMultiplier CFSG.CosetTable

theorem hnGens_gf : HNGens (fun i : Fin 7 => gf i.val) :=
  ⟨facts.1, facts.2.1, facts.2.2⟩

theorem closure_sigma_eq :
    Subgroup.closure (Set.range fun j => (fun i : Fin 7 => gf i.val) (hnSigma j)) = H5 := by
  congr 1
  ext y
  simp only [Set.mem_range]
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨⟨j.val, by have := j.2; have h5 := hnS1L_length; omega⟩, by
      simp only [hnSigma_val]⟩
  · rintro ⟨i, rfl⟩
    exact ⟨⟨i.val, by have := i.2; have h5 := hnS1L_length; omega⟩, by
      simp only [hnSigma_val]⟩

end CertificateChecks.KernelHNMult

end
