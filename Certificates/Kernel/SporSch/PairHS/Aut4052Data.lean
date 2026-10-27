module

public import Certificates.Kernel.SporSch.GenPerms
public import Certificates.Kernel.Sporadic.RawGen
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporAutHSInputs
meta import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporAutHSInputs
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
public import CFSG.Foundations
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporAutLocal
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.Sporadic.Schreier.PairHSPairs
meta import CFSG.Foundations
meta import CFSG.GroupTheory.LocalCores.Fitting
meta import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
meta import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
meta import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
meta import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
meta import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
meta import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
meta import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporAutLocal
meta import CFSG.LocalAnalysis.SectionRank.PRank
meta import CFSG.LocalAnalysis.SectionRank.SQT
meta import CFSG.Sporadic.Schreier.PairHSPairs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch

meta def s0M : Array (Array Nat) :=
  #[CFSG.QuasithinUnique.Ch1.SporAutHS.s0Arr 0, CFSG.QuasithinUnique.Ch1.SporAutHS.s0Arr 1,
    CFSG.QuasithinUnique.Ch1.SporAutHS.s0Arr 2]

end CertificateChecks.KernelSporSch

#kss_perms CertificateChecks.KernelSporSch.PS0 12 CertificateChecks.KernelSporSch.s0M

#ks_chars CertificateChecks.KernelSporSch.PS0T CFSG.QuasithinUnique.Ch1.SporAutHS.s0Hex

#kc_repo #kc_json_gz CertificateChecks.KernelSporSch.PA4 "Certificates/Kernel/SporSch/PairHS/data/aut4052.json.gz" 188 1013053207000899405
  (nfg : List Nat) (d : Nat) (di : List Nat) (sw : List (List Nat)) (V : List Nat)

end
