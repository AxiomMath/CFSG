module

public import Certificates.Kernel.Sporadic.ONLine.Data
public import Certificates.Kernel.Sporadic.OrbRecGen
public meta import Certificates.Kernel.Sporadic.ON.Gen
public meta import CFSG.LocalAnalysis.RankThreeTheoremC.ONPair.ModelData

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ONNQ

open CFSG.ONSchreier.Native CFSG.LocalAnalysis.RankThreeTheoremC.ONPair

meta def nqWordsM : Array (List Int) :=
  let tw := fun (w : List Int) => w.map fun l => if l == 1 then 6 else if l == -1 then -6 else l
  #[[], [], h1Word, h2Word, [-2, 1, 2, -1, 1, 2, -2, 1, -1, -2, 2, -1, 2, 1, 2, 1],
    [5, 5, 5, 5, 5], tw h1Word, tw h2Word]

meta def nqAllM : Array (Array Nat) := Id.run do
  let U := CertificateChecks.KernelSpor.ONLine.lineM
  let mut T : Array (Array Nat) := #[natTab U.alpha, natTab U.beta]
  for j in [2:8] do
    T := T.push (pword 122760 T (pinvs 122760 T) nqWordsM[j]!)
  return T

meta def nqTabsM : Array (Array Nat) :=
  let T := nqAllM
  let I := pinvs 122760 T
  #[I[1]!, T[2]!, T[3]!, I[3]!, T[4]!, I[4]!, T[5]!, T[6]!, T[7]!, I[7]!]

meta def nqWCM : Array Nat := nqWordsM.map CFSG.KS.ONGen.encW

meta def nqWLM : Array Nat := nqWordsM.map List.length

end CertificateChecks.KernelSpor.ONNQ

#kon_tables CertificateChecks.KernelSpor.ONNQ.nqTabsM CertificateChecks.KernelSpor.ONQ.D1I
  CertificateChecks.KernelSpor.ONQ.H1 CertificateChecks.KernelSpor.ONQ.H2
  CertificateChecks.KernelSpor.ONQ.H2I CertificateChecks.KernelSpor.ONQ.W
  CertificateChecks.KernelSpor.ONQ.WI CertificateChecks.KernelSpor.ONQ.AP
  CertificateChecks.KernelSpor.ONQ.HA1 CertificateChecks.KernelSpor.ONQ.HA2
  CertificateChecks.KernelSpor.ONQ.HA2I

#kc_nattree CertificateChecks.KernelSpor.ONQ.WC CertificateChecks.KernelSpor.ONNQ.nqWCM

#kc_nattree CertificateChecks.KernelSpor.ONQ.WL CertificateChecks.KernelSpor.ONNQ.nqWLM

namespace CertificateChecks.KernelSpor.ONNQ

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON

@[expose] noncomputable def TT (h i : Nat) : Nat :=
  nIf(Nat.beq h 0, tab ONL.A i, nIf(Nat.beq h 1, tab ONL.B i, nIf(Nat.beq h 2, tab ONQ.H1 i,
    nIf(Nat.beq h 3, tab ONQ.H2 i, nIf(Nat.beq h 4, tab ONQ.W i, nIf(Nat.beq h 5, tab ONQ.AP i,
      nIf(Nat.beq h 6, tab ONQ.HA1 i, tab ONQ.HA2 i)))))))

@[expose] noncomputable def UU (h i : Nat) : Nat :=
  nIf(Nat.beq h 0, tab ONL.A i, nIf(Nat.beq h 1, tab ONQ.D1I i, nIf(Nat.beq h 2, tab ONQ.H1 i,
    nIf(Nat.beq h 3, tab ONQ.H2I i, nIf(Nat.beq h 4, tab ONQ.WI i, nIf(Nat.beq h 5, tab ONQ.AP i,
      nIf(Nat.beq h 6, tab ONQ.HA1 i, tab ONQ.HA2I i)))))))

@[expose] noncomputable def nqTrS (s : Nat) : Bool :=
  trRange TT UU ONQ.WC ONQ.WL (nat_lit 122760) (nat_lit 8) (nat_lit 2) (Nat.mul s (nat_lit 120))
    (nat_lit 120)

end CertificateChecks.KernelSpor.ONNQ

end
