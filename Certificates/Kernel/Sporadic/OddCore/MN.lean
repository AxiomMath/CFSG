module

public import Certificates.Kernel.Sporadic.OddCore.McLL
public import Certificates.Kernel.Sporadic.OddCore.MulHCmd
public import Certificates.Kernel.Sporadic.OddCore.RowsCmd
public import Certificates.Kernel.Census.McLN
public import CFSG.Sporadic.SmallOddCore.McLCheckInputs
meta import CFSG.Sporadic.SmallOddCore.McLCheckInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.MNd

open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.PSL3Four.Native
open CFSG.Sporadic.Th.Native

meta def idM : Array Nat := idTab 275
meta def idsM (k : Nat) : Array (Array Nat) := Array.replicate k idM
meta def cM (k : Nat) : Array Nat := natArr (mclCentTbl k)
meta def ciM (k : Nat) : Array Nat := CFSG.Monster.B.Co2.Native.invCand 275 (cM k)
meta def gsM (ks : List Nat) : Array (Array Nat) := ks.toArray.map cM
meta def gsiM (ks : List Nat) : Array (Array Nat) := ks.toArray.map ciM
meta def allInvM : Array (Array Nat) := (List.range 30).toArray.map ciM
meta def pgM : Array (Array Nat) := #[CFSG.Sporadic.Schreier.mclStrongArrs[0]!,
  CFSG.Sporadic.Schreier.mclStrongArrs[1]!]
meta def pgiM : Array (Array Nat) := pgM.map (CFSG.Monster.B.Co2.Native.invCand 275)
meta def conjRec (gs gis : Array (Array Nat)) (x : Array Nat) : Array (Array Nat) :=
  (bfs (fun j t => conjTab 275 gs[j]! gis[j]! t) gs.size x 200000).tabs
meta def mulRec (gs : Array (Array Nat)) : Array (Array Nat) :=
  (bfs (fun j t => conjTab 275 idM gs[j]! t) gs.size idM 200000).tabs

meta def syM : Array (Array Nat) := gsM [1, 2, 3]
meta def syiM : Array (Array Nat) := gsiM [1, 2, 3]
meta def k1M : Array (Array Nat) := gsM [5, 6]
meta def k1iM : Array (Array Nat) := gsiM [5, 6]
meta def k2M : Array (Array Nat) := gsM [18, 19, 20, 21]
meta def k2iM : Array (Array Nat) := gsiM [18, 19, 20, 21]
meta def ids3M : Array (Array Nat) := idsM 3
meta def ids4M : Array (Array Nat) := idsM 4
meta def q7M : Array Nat := cM 7
meta def q9M : Array Nat := cM 9
meta def q11M : Array Nat := cM 11
meta def q13M : Array Nat := cM 13
meta def q15M : Array Nat := cM 15
meta def q22M : Array Nat := cM 22
meta def q24M : Array Nat := cM 24
meta def q26M : Array Nat := cM 26
meta def q28M : Array Nat := cM 28

meta def syR : Array (Array Nat) := mulRec syM
meta def k2R : Array (Array Nat) := mulRec k2M
meta def q2aR : Array (Array Nat) := conjRec k2M k2iM q22M
meta def q2bR : Array (Array Nat) := conjRec k2M k2iM q24M
meta def q2cR : Array (Array Nat) := conjRec k2M k2iM q26M
meta def q2dR : Array (Array Nat) := conjRec k2M k2iM q28M
meta def uqM : Array (Array Nat) :=
  #[conjTab 275 (cM 0) (ciM 0) (cM 4), conjTab 275 (cM 0) (ciM 0) (cM 17)]
meta def syClM : Array (Array Nat) :=
  (syR.map fun x => (syM ++ syiM).map fun g => comp 275 x g).flatten

#kmisc_packarrs CertificateChecks.KernelSpor.MNI allInvM 9
#kmulh CertificateChecks.KernelSpor.MN.SY 275 9 ids3M syM idM 120000
#kmulh CertificateChecks.KernelSpor.MN.K2 275 9 ids4M k2M idM 120000
#kmulh CertificateChecks.KernelSpor.MN.Q1a 275 9 k1M k1iM q7M 120000
#kmulh CertificateChecks.KernelSpor.MN.Q1b 275 9 k1M k1iM q9M 120000
#kmulh CertificateChecks.KernelSpor.MN.Q1c 275 9 k1M k1iM q11M 120000
#kmulh CertificateChecks.KernelSpor.MN.Q1d 275 9 k1M k1iM q13M 120000
#kmulh CertificateChecks.KernelSpor.MN.Q1e 275 9 k1M k1iM q15M 120000
#kmulh CertificateChecks.KernelSpor.MN.Q2a 275 9 k2M k2iM q22M 120000
#kmulh CertificateChecks.KernelSpor.MN.Q2b 275 9 k2M k2iM q24M 120000
#kmulh CertificateChecks.KernelSpor.MN.Q2c 275 9 k2M k2iM q26M 120000
#kmulh CertificateChecks.KernelSpor.MN.Q2d 275 9 k2M k2iM q28M 120000
#kfind CertificateChecks.KernelSpor.MN.SYCl syR syClM
#kfind CertificateChecks.KernelSpor.MN.K2in2a q2aR k2R
#kfind CertificateChecks.KernelSpor.MN.K2in2b q2bR k2R
#kfind CertificateChecks.KernelSpor.MN.K2in2c q2cR k2R
#kfind CertificateChecks.KernelSpor.MN.K2in2d q2dR k2R

end CertificateChecks.KernelSpor.MNd

end
