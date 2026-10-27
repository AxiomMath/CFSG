
module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.Cover3
public import Certificates.Data.CFSGNative.ComponentPrimary.Cover3Ly
public import Certificates.Kernel.Bounds.Family
public import Certificates.Kernel.Bounds.AssembleZ
import CFSG.Certificates.Kernel.Bounds.LoadGz
import CFSG.Certificates.Kernel.Common.Repo
public import CFSG.Certificates.Kernel.Misc.Coset.TableZSound
public import CFSG.Certificates.CosetTableShort
public import CFSG.Certificates.NativeSchreierCard
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF2
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF3
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsFp
public import CFSG.Sporadic.Recognition.CoverCubeTransfer

public section

namespace CertificateChecks.KernelLy3.Z

open CFSG.CosetTable CFSG.SectionRank.Native CFSG.KC.MiscCoset CFSG.LieType.Multipliers
  CFSG.Sporadic.Recognition.CoverRecipe CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary
  CFSG.Certificates

set_option maxRecDepth 200000

local instance : NeZero lyMax7Cover3.m := ⟨by decide⟩

end CertificateChecks.KernelLy3.Z

end
