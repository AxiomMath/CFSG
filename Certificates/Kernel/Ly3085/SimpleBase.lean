
module

public import Certificates.Kernel.Ly3085.CardBase
public import Certificates.Kernel.Ly3085.Alg
public import CFSG.Sporadic.Ly.Setup
public import CFSG.Certificates.CosetTableShort
public import CFSG.Sporadic.Bridge.LyData
public import CFSG.Sporadic.Bridge.TableSurj
public import CFSG.Sporadic.HN.LevelChainSpec
public import CFSG.Sporadic.Ly.ActionBase
public import CFSG.Sporadic.Ly.CertificateBase
public import CFSG.Sporadic.Ly.FaithSpec
public import CFSG.Sporadic.Ly.FiveFacts
public import CFSG.Sporadic.Ly.OrbitSpec
public import CFSG.Sporadic.Ly.PrimitiveBase
public import CFSG.Sporadic.Ly.WordFacts
public import CFSG.Sporadic.LyBase
public import CFSG.Sporadic.Presentation.Common
public import CFSG.Sporadic.Presentation.Ly
public import CFSG.Sporadic.Schreier.LyChain11
public import Certificates.Kernel.Ly3085.Ord

@[expose] public section

namespace CertificateChecks.KernelLy

open CFSG.Sporadic.Ly

theorem J_eq_JS [LySeed] : J = JS := by
  change Subgroup.closure {gA, gB} = Subgroup.closure _
  congr 1
  ext g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq]
  constructor
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (h | h)
    · exact Or.inl (Units.ext h)
    · exact Or.inr (Units.ext h)

end CertificateChecks.KernelLy

end
