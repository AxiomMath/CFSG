
module

public import Certificates.Kernel.Th3.ZOne
public import Certificates.Kernel.Bounds.Family
public import CFSG.Certificates.Kernel.Misc.Coset.TableFactSub
public import CFSG.Sporadic.Recognition.CoverIndex

public section

namespace CertificateChecks.KernelTh3.Z

open CFSG.CosetTable CFSG.SectionRank.Native CFSG.KC.MiscCoset CFSG.LieType.Multipliers
  CFSG.Sporadic.Recognition.CoverRecipe CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary
  CFSG.Certificates CFSG.Sporadic.Recognition.CoverIndex

local instance : NeZero CFSG.SectionRank.Native.thMax6Cover3.m := ⟨by decide⟩

set_option maxRecDepth 200000

end CertificateChecks.KernelTh3.Z

end
