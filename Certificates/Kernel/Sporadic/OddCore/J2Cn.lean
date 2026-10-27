
module

public import Certificates.Kernel.Sporadic.OddCore.J2Loc
public import Certificates.Kernel.Sporadic.OddCore.RowsCmd
public import Certificates.Kernel.Sporadic.OddCore.J2PChain
public import CFSG.Sporadic.SmallOddCore.J2CheckInputs
meta import CFSG.Sporadic.SmallOddCore.J2CheckInputs
meta import Certificates.Kernel.Sporadic.OddCore.J2Loc
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.J2Cn

open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.PSL3Four.Native
open CFSG.Sporadic.Th.Native

meta def idM : Array Nat := idTab 315
meta def idsM (k : Nat) : Array (Array Nat) := Array.replicate k idM
meta def cM (k : Nat) : Array Nat := natArr (j2CentTbl k)
meta def ciM (k : Nat) : Array Nat := CFSG.Monster.B.Co2.Native.invCand 315 (cM k)
meta def gsM (ks : List Nat) : Array (Array Nat) := ks.toArray.map cM
meta def gsiM (ks : List Nat) : Array (Array Nat) := ks.toArray.map ciM
meta def pgM : Array (Array Nat) :=
  #[(CFSG.Sporadic.Schreier.PairNative.j2StrongArrs ())[0]!,
    (CFSG.Sporadic.Schreier.PairNative.j2StrongArrs ())[1]!]
meta def pgiM : Array (Array Nat) := pgM.map (CFSG.Monster.B.Co2.Native.invCand 315)
meta def conjRec (gs gis : Array (Array Nat)) (x : Array Nat) : Array (Array Nat) :=
  (bfs (fun j t => conjTab 315 gs[j]! gis[j]! t) gs.size x 3000).tabs
meta def mulRec (gs : Array (Array Nat)) : Array (Array Nat) :=
  (bfs (fun j t => conjTab 315 idM gs[j]! t) gs.size idM 3000).tabs

meta def r9M : Array Nat := cM 9
meta def r17M : Array Nat := cM 17
meta def r31M : Array Nat := cM 31
meta def syM : Array (Array Nat) := gsM [1, 2, 3, 4, 5, 6, 7, 8]
meta def syiM : Array (Array Nat) := gsiM [1, 2, 3, 4, 5, 6, 7, 8]
meta def k1M : Array (Array Nat) := gsM [10, 11, 12]
meta def k1iM : Array (Array Nat) := gsiM [10, 11, 12]
meta def k2M : Array (Array Nat) := gsM [18, 19, 20, 21, 22]
meta def k2iM : Array (Array Nat) := gsiM [18, 19, 20, 21, 22]
meta def k3M : Array (Array Nat) := gsM [32, 33, 34, 35]
meta def k3iM : Array (Array Nat) := gsiM [32, 33, 34, 35]
meta def e2aM : Array (Array Nat) := gsM [24, 25]
meta def e2bM : Array (Array Nat) := gsM [27, 28]
meta def q13M : Array Nat := cM 13
meta def q15M : Array Nat := cM 15
meta def q23M : Array Nat := cM 23
meta def q26M : Array Nat := cM 26
meta def q29M : Array Nat := cM 29
meta def q36M : Array Nat := cM 36
meta def q38M : Array Nat := cM 38
meta def q40M : Array Nat := cM 40
meta def ids2M : Array (Array Nat) := idsM 2
meta def ids3M : Array (Array Nat) := idsM 3
meta def ids8M : Array (Array Nat) := idsM 8

meta def o1R : Array (Array Nat) := conjRec pgM pgiM r9M
meta def o2R : Array (Array Nat) := conjRec pgM pgiM r17M
meta def o3R : Array (Array Nat) := conjRec pgM pgiM r31M
meta def syR : Array (Array Nat) := mulRec syM
meta def k1R : Array (Array Nat) := mulRec k1M
meta def q1aR : Array (Array Nat) := conjRec k1M k1iM q13M
meta def q1bR : Array (Array Nat) := conjRec k1M k1iM q15M
meta def q2aR : Array (Array Nat) := conjRec k2M k2iM q23M
meta def q2bR : Array (Array Nat) := conjRec k2M k2iM q26M
meta def q2cR : Array (Array Nat) := conjRec k2M k2iM q29M
meta def q3aR : Array (Array Nat) := conjRec k3M k3iM q36M
meta def q3bR : Array (Array Nat) := conjRec k3M k3iM q38M
meta def q3cR : Array (Array Nat) := conjRec k3M k3iM q40M
meta def e2aR : Array (Array Nat) := mulRec e2aM
meta def e2bR : Array (Array Nat) := mulRec e2bM

meta def syClM : Array (Array Nat) :=
  (syR.map fun x => (syM ++ syiM).map fun g => comp 315 x g).flatten
meta def uqM : Array (Array Nat) :=
  #[conjTab 315 (cM 0) (ciM 0) r9M, conjTab 315 (cM 0) (ciM 0) r17M,
    conjTab 315 (cM 0) (ciM 0) r31M]
meta def isInvM (x : Array Nat) : Bool := comp 315 x x == idM && x != idM
meta def einvM : Array Nat :=
  #[((List.range e2aR.size).find? fun i => isInvM e2aR[i]!).getD 0,
    ((List.range e2bR.size).find? fun i => isInvM e2bR[i]!).getD 0]

#kmulh CertificateChecks.KernelSpor.J2R1 315 9 pgM pgiM r9M 3000
#kmulh CertificateChecks.KernelSpor.J2R2 315 9 pgM pgiM r17M 3000
#kmulh CertificateChecks.KernelSpor.J2R3 315 9 pgM pgiM r31M 3000
#kmulh CertificateChecks.KernelSpor.J2SY 315 9 ids8M syM idM 3000
#kmulh CertificateChecks.KernelSpor.J2K1 315 9 ids3M k1M idM 3000
#kmulh CertificateChecks.KernelSpor.J2Q1a 315 9 k1M k1iM q13M 3000
#kmulh CertificateChecks.KernelSpor.J2Q1b 315 9 k1M k1iM q15M 3000
#kmulh CertificateChecks.KernelSpor.J2Q2a 315 9 k2M k2iM q23M 3000
#kmulh CertificateChecks.KernelSpor.J2Q2b 315 9 k2M k2iM q26M 3000
#kmulh CertificateChecks.KernelSpor.J2Q2c 315 9 k2M k2iM q29M 3000
#kmulh CertificateChecks.KernelSpor.J2Q3a 315 9 k3M k3iM q36M 3000
#kmulh CertificateChecks.KernelSpor.J2Q3b 315 9 k3M k3iM q38M 3000
#kmulh CertificateChecks.KernelSpor.J2Q3c 315 9 k3M k3iM q40M 3000
#kmulh CertificateChecks.KernelSpor.J2E2a 315 9 ids2M e2aM idM 3000
#kmulh CertificateChecks.KernelSpor.J2E2b 315 9 ids2M e2bM idM 3000

#kfind CertificateChecks.KernelSpor.J2SYCl syR syClM
#kfind CertificateChecks.KernelSpor.J2SYin1 o1R syR
#kfind CertificateChecks.KernelSpor.J2SYin2 o2R syR
#kfind CertificateChecks.KernelSpor.J2SYin3 o3R syR
#kfind CertificateChecks.KernelSpor.J2Uin1 o1R uqM
#kfind CertificateChecks.KernelSpor.J2Uin2 o2R uqM
#kfind CertificateChecks.KernelSpor.J2Uin3 o3R uqM
#kfind CertificateChecks.KernelSpor.J2Nin2a q2aR e2aM
#kfind CertificateChecks.KernelSpor.J2Nin2b q2bR e2bM
#kfind CertificateChecks.KernelSpor.J2K1in1a q1aR k1R
#kfind CertificateChecks.KernelSpor.J2K1in1b q1bR k1R
#kfind CertificateChecks.KernelSpor.J2C1in2a q2aR CertificateChecks.KernelSpor.J2Loc.c1RecM
#kfind CertificateChecks.KernelSpor.J2C1in2b q2bR CertificateChecks.KernelSpor.J2Loc.c1RecM
#kfind CertificateChecks.KernelSpor.J2C1in2c q2cR CertificateChecks.KernelSpor.J2Loc.c1RecM
#kfind CertificateChecks.KernelSpor.J2C2in3a q3aR CertificateChecks.KernelSpor.J2Loc.c2RecM
#kfind CertificateChecks.KernelSpor.J2C2in3b q3bR CertificateChecks.KernelSpor.J2Loc.c2RecM
#kfind CertificateChecks.KernelSpor.J2C2in3c q3cR CertificateChecks.KernelSpor.J2Loc.c2RecM
#krows CertificateChecks.KernelSpor.J2EInv einvM

end CertificateChecks.KernelSpor.J2Cn

end
