module

public import Certificates.Kernel.Sporadic.Fi22.X2069Final
public import Certificates.Kernel.Sporadic.Fi22.E2067T
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Data.Kernel.Misc.HexFlat
public import Certificates.Data.Kernel.Spor.CommBase
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Fi22CenterInputs
meta import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Fi22CenterInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Rows
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
public import CFSG.Walter.JRFacts
meta import CFSG.GroupTheory.Fitting.CharacteristicP
meta import CFSG.GroupTheory.LocalCores.Components
meta import CFSG.GroupTheory.LocalCores.Fitting
meta import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
meta import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
meta import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
meta import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
meta import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
meta import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
meta import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Rows
meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
meta import CFSG.Walter.JRFacts

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSpor.Fi22Um CFSG.EvenSporadicStandard.Solomon78.fi22UmovHex
#kmisc_hexflat CertificateChecks.KernelSpor.Fi22Um CFSG.EvenSporadicStandard.Solomon78.fi22UmovHex 3
  3510 12 18

public section

set_option maxHeartbeats 0
set_option Elab.async false

namespace CertificateChecks.KernelSpor.Fi22Um

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KC.CommBase

@[expose] noncomputable def umovK (L T T' : Nat) : Bool :=
  bAnd(Fi22X.cn L, bAnd(Fi22X.cn (Fi22X.inv L),
  bAnd(permOK 3510 12 (mask 12) (3510 * 12) L (Fi22X.inv L),
  bAnd(Fi22X.siftP L,
  bAnd(Fi22X.cn T, bAnd(permOK 3510 12 (mask 12) (3510 * 12) T (Fi22X.inv T),
  bAnd(Fi22X.cn T', bAnd(permOK 3510 12 (mask 12) (3510 * 12) T' (Fi22X.inv T'),
  strictB (Fi22X.c (Fi22X.c L T) (Fi22X.inv L)) fun C =>
    Nat.beq (Fi22X.c C T') (Fi22X.c T' C)))))))))

theorem umAll : allN 3 (fun i => allN 6 fun j =>
    umovK (F (6 * i + j)) (Fi22ExtT.L (21 + i)) (Fi22ExtT.L (21 + j))) = true := by
  quickRfl

theorem negUm1 : notB (umovK (F 1) (Fi22ExtT.L 21) (Fi22ExtT.L 26)) = true := by quickRfl

theorem negUmOuter : notB (umovK (Fi22X.c (F 1) Fi22X.GO) (Fi22ExtT.L 21) (Fi22ExtT.L 22)) =
    true := by
  quickRfl

end CertificateChecks.KernelSpor.Fi22Um

end
