module

public import Certificates.Kernel.Sporadic.Fi22.X2069Final
public import Certificates.Kernel.Sporadic.Fi22.E2067T
public import Certificates.Kernel.Misc.Perm.HexDropCmd
public import Certificates.Data.Kernel.Spor.CommBase
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Fi22Inputs
public meta import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Fi22Inputs
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Harness
public meta import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.GroupTheory.Fitting.CharacteristicP
public meta import CFSG.GroupTheory.LocalCores.Components
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.GroupTheory.LocalCores.Fitting
public meta import CFSG.GroupTheory.LocalCores.Fitting
public meta import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public meta import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public meta import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public meta import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public meta import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public meta import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Rows
public meta import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Rows
public meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
public meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
public meta import CFSG.Walter.JRFacts
public import CFSG.Walter.JRFacts

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSpor.Fi22HypT CFSG.EvenSporadicStandard.HypOne.Fi22.hypHex

#kmisc_hexflat_drop CertificateChecks.KernelSpor.Fi22HypG CertificateChecks.KernelSpor.Fi22HypT
  CFSG.EvenSporadicStandard.HypOne.Fi22.hypHex 115830 3 3510 12 2

namespace CertificateChecks.KernelSpor.Fi22R1

open CFSG.EvenSporadicStandard.HypOne.Fi22

meta def compM (p q : Array Nat) : Array Nat := q.map fun i => p[i]!

meta def invM (p : Array Nat) : Array Nat := Id.run do
  let mut r := Array.replicate p.size 0
  for i in [0:p.size] do
    r := r.set! p[i]! i
  return r

meta def g1M : Array Nat := (hypTbl 11).map (·.toNat)

meta def h1M : Array Nat := compM ((hypTbl 12).map (·.toNat)) ((hypTbl 12).map (·.toNat))

meta def h2M : Array Nat := compM g1M (compM h1M (invM g1M))

meta def lettersM : Array (Array Nat) :=
  #[h1M, h2M, CFSG.Sporadic.FischerOddCore.fi22ExtArr 22, invM h1M, invM h2M]

end CertificateChecks.KernelSpor.Fi22R1

#kmisc_packarrs CertificateChecks.KernelSpor.Fi22R1L CertificateChecks.KernelSpor.Fi22R1.lettersM 12

#kc_repo #kc_json_gz CertificateChecks.KernelSpor.Fi22R1D
  "Certificates/Kernel/Sporadic/Fi22/data/hypr1.json.gz" 38451 10511349992612205010
  (B : List CFSG.KC.CommBase.BaseRec) (PF : Nat) (ZF : Nat) (DF : Nat)

namespace CertificateChecks.KernelSpor.Fi22R1

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.CommBase

@[expose] noncomputable def G1 : Nat := Fi22HypG.F 0

@[expose] noncomputable def G2 : Nat := Fi22HypG.F 1

@[expose] noncomputable def T : Nat := Fi22ExtT.L 22

@[expose] noncomputable def L (z : Nat) : Nat := Fi22R1L z

@[expose] noncomputable def pow5 (p : Nat) : Nat := Fi22X.c p (Fi22X.c p (Fi22X.c p (Fi22X.c p p)))

@[expose] noncomputable def gensOK (a b t : Nat) : Bool :=
  bAnd(Fi22X.cn a, bAnd(Fi22X.cn b, bAnd(Fi22X.cn t,
  bAnd(permOK 3510 12 (mask 12) (3510 * 12) b (Fi22X.inv b),
  bAnd(permOK 3510 12 (mask 12) (3510 * 12) t t,
  bAnd(permOK 3510 12 (mask 12) (3510 * 12) a (Fi22X.inv a), bAnd(Fi22X.cn (Fi22X.inv a),
  bAnd(Fi22X.siftP a, bAnd(Fi22X.siftP b,
  bAnd(Nat.beq (Fi22X.c a t) (Fi22X.c t a), Nat.beq (Fi22X.c b t) (Fi22X.c t b)))))))))))

@[expose] noncomputable def lettersOK (M : Nat → Nat) (a b t : Nat) : Bool :=
  bAnd(allN 5 (fun z => Fi22X.cn (M z)),
  bAnd(Nat.beq (M 0) (Fi22X.c b b),
  bAnd(Nat.beq (M 1) (Fi22X.c a (Fi22X.c (M 0) (Fi22X.inv a))),
  bAnd(Nat.beq (M 2) t,
  bAnd(permOK 3510 12 (mask 12) (3510 * 12) (M 0) (M 3),
  bAnd(permOK 3510 12 (mask 12) (3510 * 12) (M 1) (M 4),
  bAnd(Nat.beq (pow5 (M 0)) (pidn 3510 12), Nat.beq (pow5 (M 1)) (pidn 3510 12))))))))

@[expose] noncomputable def baseChk (B : List BaseRec) (PF ZF DF : Nat) : Bool :=
  commBaseOK 3510 12 (mask 12) L 5 B PF ZF DF

theorem gensAll : gensOK G1 G2 T = true := by quickRfl

theorem lettersAll : lettersOK L G1 G2 T = true := by quickRfl

theorem baseAll : baseChk Fi22R1D.B Fi22R1D.PF Fi22R1D.ZF Fi22R1D.DF = true := by quickRfl

end CertificateChecks.KernelSpor.Fi22R1

end
