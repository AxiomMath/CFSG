module

public import Certificates.Kernel.SporSch.Ru.Gens
public import Certificates.Data.Kernel.LocalQT.Tc
public import CFSG.Certificates.Kernel.BfsPinSound
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42RuCheckInputs
meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42RuCheckInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.BfsPinUnpack
public import CFSG.Foundations
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42RuData
public import CFSG.LocalAnalysis.SectionRank.SQT
meta import CFSG.Foundations
meta import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
meta import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
meta import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
meta import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
meta import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
meta import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42RuData
meta import CFSG.LocalAnalysis.SectionRank.SQT

public section

set_option maxRecDepth 400000

#ks_perm CertificateChecks.KD.LQT.C4036.Zt 12 CFSG.QuasithinUnique.Bridge.RuExcl.ruZtArr

namespace CertificateChecks.KD.LQT.C4036

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KC.LQT.TC
  CFSG.Sporadic.RuSchreier CFSG.Monster.B.Co2.Native CFSG.QuasithinUnique.Setup.X1
  CFSG.QuasithinUnique.Bridge.RuExcl CertificateChecks.KernelSporSch.RuG

theorem hA : tcK 4060 12 [A0, A1] [A0I, A1I] A0 A0I ruAWords ruAProg [A0, A1] = true := by
  quickRfl

theorem hZ : tcK 4060 12 [A0, A1] [A0I, A1I] Zt Zt ruZWords ruZProg [A0, A1] = true := by
  quickRfl

theorem cA1 : canonK 4060 12 (mask 12) (4060 * 12) A1 = true := by quickRfl
theorem eZ : Nat.beq (pcomp 4060 12 (mask 12) A1 A1) Zt = true := by quickRfl

theorem gens_eq : [ruA0P, ruA1P] = ([A0, A1].zip [A0I, A1I]).map
    (fun p => (unpack 4060 12 p.1, unpack 4060 12 p.2)) := by
  unfold ruA0P ruA1P
  rw [(inv_of a0_eq pA0).1, (inv_of a1_eq pA1).1, a0_eq, a1_eq]
  rfl

theorem a0p_eq : ruA0P = (unpack 4060 12 A0, unpack 4060 12 A0I) := by
  unfold ruA0P
  rw [(inv_of a0_eq pA0).1, a0_eq]

theorem zt_eq : ruZtP = (unpack 4060 12 Zt, unpack 4060 12 Zt) := by
  unfold ruZtP ruZtArr
  rw [a1_eq, compA_unpack cA1 cA1, Nat.eq_of_beq_eq_true eZ]

theorem targ_eq : [ruA0A, ruA1A] = [A0, A1].map (unpack 4060 12) := by
  rw [a0_eq, a1_eq]
  rfl

end CertificateChecks.KD.LQT.C4036

end
