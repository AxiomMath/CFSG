
module

public import CFSG.Certificates.Kernel.Bounds.Load
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.Cover3Sound
public import Certificates.Data.CFSGNative.ComponentPrimary.Cover3Ly
public import Certificates.Data.Kernel.Misc.Coset.Act

public section

namespace CertificateChecks.KernelLy3.Card

open CFSG.CosetTable CFSG.KC.MiscCoset CFSG.Certificates CFSG.SectionRank.Native
  CFSG.LieType.Multipliers CFSG.Sporadic.Recognition.CoverRecipe
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary

local instance : NeZero CFSG.SectionRank.Native.lyMax7Cover3.m := ⟨by decide⟩

set_option maxRecDepth 200000

end CertificateChecks.KernelLy3.Card

end
