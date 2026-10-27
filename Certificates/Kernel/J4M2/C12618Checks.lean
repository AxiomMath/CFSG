module

public import Certificates.Kernel.J4M2.Base
public import Certificates.Kernel.J4M2.KDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4CentCEData
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness
public import CFSG.Open.Defs
public import CFSG.Sporadic.Th.F2Spec

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4M2

open CFSG.KC.J4Q CFSG.KD.J4Q

@[expose] noncomputable def invK : Nat :=
  CFSG.AGLEmbeddingD2.Wilson.NormalizerAction.invWord.foldl (fun acc n => mulJ c rm acc (gmK n)) one

theorem c12618inv : Nat.beq (mulJ c rm invK cK) (mulJ c rm (mulJ c rm cK cK) invK) = true := by
  quickRfl

theorem c12618zc : Nat.beq (mulJ c rm ZM cK) (mulJ c rm cK ZM) = true := by quickRfl

theorem c12618zz : Nat.beq (mulJ c rm ZM ZM) one = true := by quickRfl

end CertificateChecks.KernelJ4M2

end
