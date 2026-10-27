module

public import Certificates.Kernel.Sporadic.OddCore.F1K27811
public import Certificates.Kernel.Sporadic.OddCore.MulHCmd
public import Certificates.Data.Kernel.Spor.RawOrbOut
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RYData
meta import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RYData
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Each
meta import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
meta import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
meta import CFSG.Walter.JRFacts

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.S16J3

open CFSG.EvenSporadicStandard.Fin76b.S16
open CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Th.Native CFSG.PSL3Four.Native
open CFSG.Sporadic.SmallOddCore

meta def idM : Array Nat := idTab 6156
meta def tbM (k : Nat) : Table := j3Tb k
meta def tM (k : Nat) : Array Nat := natArr (j3Tb k)
meta def cmM (x y : Table) : Array Nat := natArr (compT 6156 x y)

meta def csM : Array (Array Nat) := #[cmM (tbM 7) (tbM 0), tM 8, tM 9, cmM (tbM 10) (tbM 0)]

meta def ids4M : Array (Array Nat) := Array.replicate 4 idM

meta def invA (a : Array Nat) : Array Nat := CFSG.Monster.B.Co2.Native.invCand 6156 a
meta def recOf (gs : Array (Array Nat)) : Array (Array Nat) :=
  (bfs (fun j t => conjTab 6156 idM gs[j]! t) gs.size idM 40).tabs

meta def cRecM : Array (Array Nat) := recOf csM
meta def cIM : Array (Array Nat) := csM.map invA
meta def cAM : Array (Array Nat) := cRecM.map invA

end CertificateChecks.KernelSpor.S16J3

open CertificateChecks.KernelSpor.S16J3 in
#kmulh CertificateChecks.KernelSpor.S16J3C 6156 13 ids4M csM idM 40
open CertificateChecks.KernelSpor.S16J3 in
#kmisc_packarrs CertificateChecks.KernelSpor.S16J3CI cIM 13
open CertificateChecks.KernelSpor.S16J3 in
#kmisc_packarrs CertificateChecks.KernelSpor.S16J3CA cAM 13

namespace CertificateChecks.KernelSpor.S16J3

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH
open CertificateChecks.KernelSpor CertificateChecks.KernelSporSch

@[expose] noncomputable def pc (p q : Nat) : Nat := pcomp 6156 13 (mask 13) p q

@[expose] noncomputable def idK : Nat := pidn 6156 13

@[expose] noncomputable def cK (p : Nat) : Bool := canonK 6156 13 (mask 13) (6156 * 13) p

@[expose] noncomputable def iK (p q : Nat) : Bool := invEqK 6156 13 (mask 13) (6156 * 13) p q

@[expose] noncomputable def S (k : Nat) : Nat := TS16J3P k

@[expose] noncomputable def tK : Nat := J3CentP 9
@[expose] noncomputable def rK : Nat := S 0
@[expose] noncomputable def xK : Nat := S 2

@[expose] noncomputable def quadK (y : Nat) : Bool :=
  Nat.beq y idK || Nat.beq y tK || Nat.beq y xK || Nat.beq y (pc tK xK)

@[expose] def rOut : List Int := [-2, -2, -4, -2, -3, -1, -2, -1, -2]

@[expose] noncomputable def outJ3 (iw : List Int) (X : Nat) : Bool :=
  outK 6156 13 (mask 13) (6156 * 13) (pidn 6156 13) PJ3.S PJ3.SI 5 PJ3.BP 1 (PJ3.LR 1) iw X

theorem k_rout : bAnd(cK rK, bAnd(iK rK rK, outJ3 rOut rK)) = true := by
  quickRfl

theorem k_rout_neg : outJ3 [] (PJ3.S 0) = false := by
  decide +kernel

@[expose] noncomputable def s16j3q (i : Nat) : Bool :=
  bAnd(cK (S16J3CA i), bAnd(iK (S16J3C.T i) (S16J3CA i),
    bAnd(quadK (pc (S16J3C.T i) (S16J3C.T i)),
    allN 32 (fun j => quadK (pc (pc (S16J3C.T i) (S16J3C.T j)) (pc (S16J3CA i) (S16J3CA j)))))))

theorem s16j3q_neg : quadK rK = false := by
  decide +kernel

end CertificateChecks.KernelSpor.S16J3

#kc_each CertificateChecks.KernelSpor.S16J3.s16j3q 0 32

end
