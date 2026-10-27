module

public import Certificates.Kernel.Sporadic.OddCore.J3HypSyl
public import Certificates.Kernel.Misc.Perm.HexCmd
meta import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.J3Inputs
meta import Certificates.Data.CFSGNative.PSL3Four.Basic
import CFSG.Certificates.Kernel.Common.Harness
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
public import CFSG.Certificates.Kernel.Bounds.Core3
import CFSG.Certificates.Kernel.Bounds.Load

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0

namespace CertificateChecks.KernelSpor.J3Tab

open CFSG.EvenSporadicStandard.HypOne.J3 CFSG.Sporadic.SmallOddCore.Native CFSG.PSL3Four.Native
open CertificateChecks.KernelSpor.J3HypSyl

meta def eM : Enum := bfs (fun j t => conjTab 6156 idM sM[j]! t) 3 idM 128

meta def rM : Array (Array Nat) :=
  let idx := indexOf eM.tabs
  eM.tabs.map fun t => (Array.range 3).map fun j => (idx[conjTab 6156 idM sM[j]! t]?).getD 0

meta def mM : Array (Array Nat) :=
  (Array.range 128).map fun a => (List.range 127).foldl
    (fun row c => row.push ((rM[row[eM.par[c + 1]!]!]!)[eM.lab[c + 1]!]!)) #[a]

meta def tM : Array (Array Nat) := #[#[((indexOf eM.tabs)[natArr t0]?).getD 0]]

end CertificateChecks.KernelSpor.J3Tab

#kc_items CertificateChecks.KernelSpor.J3MT include_bytes "data/J3TabK.J3MT.items" 14848 3017136000806174028
#kc_items CertificateChecks.KernelSpor.J3TI include_bytes "data/J3TabK.J3TI.items" 5 7782985730899408063

namespace CertificateChecks.KernelSpor.J3Tab

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum

@[expose] noncomputable def mK (a b : Nat) : Nat := pg 7 (mask 7) (J3MT a) b

@[expose] noncomputable def mF (a b : Nat) : Nat :=
  nIf(Nat.blt a 128, nIf(Nat.blt b 128, mK a b, 0), 0)

@[expose] noncomputable def tI : Nat := J3TI 0

theorem rec_ok : allN 128 (fun a => bAnd(Nat.beq (mK a 0) a, allN 127 (fun c =>
    bAnd(Nat.blt (mK a (Nat.succ c)) 128, Nat.beq (mK a (Nat.succ c))
      (r32 J3HS.POS (Nat.add (Nat.mul (mK a (parOf J3HS.PL (Nat.succ c))) 3)
        (labOf J3HS.PL (Nat.succ c)))))))) = true := by
  quickRfl

theorem t_ok : bAnd(Nat.blt tI 128, bAnd(Nat.beq (J3HS.T tI) (J3CentP 9),
    Nat.beq (J3HS.T 0) (pidn 6156 13))) = true := by
  quickRfl

theorem rec_neg : Nat.beq (mK 1 1) (r32 J3HS.POS (Nat.add (Nat.mul (mK 1 (parOf J3HS.PL 1)) 3)
    (Nat.mod (Nat.add (labOf J3HS.PL 1) 1) 3))) = false := by
  decide +kernel

end CertificateChecks.KernelSpor.J3Tab

end
