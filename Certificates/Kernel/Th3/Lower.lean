module

public import Certificates.Data.Kernel.LaneChain
public import Certificates.Data.Kernel.OpsRenL
public import Certificates.Kernel.Th3.Snaps
public import Certificates.Kernel.LocalComp.LaySnapsFrom
public import CFSG.Certificates.Kernel.Common.Each
public import CFSG.Certificates.Kernel.Common.ForallTree
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
public import Certificates.Data.Kernel.LocalQT.Sec
public import CFSG.Certificates.Kernel.LaneChainSound
public import CFSG.Certificates.Kernel.OpsRenLSound
public import CFSG.Certificates.Kernel.OpsLayMcertSound
public import CFSG.Certificates.Kernel.LocalQTSecLemmas
public import CFSG.Certificates.Kernel.OpsLayKSndP
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsFp
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.Cover3Sound
import CFSG.Certificates.Kernel.Spor.OrdCanon
import all CFSG.Blueprint.NativeSporadic
public import CFSG.Certificates.CosetTableShort
public import CFSG.Certificates.NativeSchreierCard
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF2
public import CFSG.Open.Defs

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelTh3

open CFSG.KC.LQT CFSG.KC.OpsLayK CFSG.KC.OpsLayK.Snd CFSG.KS.Ord CFSG.SectionRank CFSG.SectionRank.Native CFSG.SectionRank.LocalWitness CertificateChecks.KernelTh3.L CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary

local instance : NeZero thMax6Cover3.m := ⟨by decide⟩

local notation "Mx" => ordMat lay.p lay.d lay.w lay.S

end CertificateChecks.KernelTh3

end
