
module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.Cover3
public import Certificates.Data.CFSGNative.ComponentPrimary.Cover3Ly
public import Certificates.Kernel.Bounds.Family
public import CFSG.Certificates.Kernel.Misc.Coset.TableFact
public import CFSG.Certificates.Kernel.Misc.Coset.ActRegular
public import Certificates.Kernel.Misc.Coset.ActBlocks
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.NativeSchreierCard
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF2
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF3
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsFp
public import CFSG.Sporadic.Recognition.CoverCubeTransfer

public section

namespace CertificateChecks.KernelLy3.Q

open CFSG.CosetTable CFSG.KC.MiscCoset CFSG.Certificates CFSG.Certificates.CosetEnumeration
  CFSG.SectionRank.Native CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary
  CFSG.LieType.Multipliers CFSG.Sporadic.Recognition.CoverRecipe

set_option maxRecDepth 200000

local instance : NeZero lyMax7Cover3.m := ⟨by decide⟩

end CertificateChecks.KernelLy3.Q

end
