module

public import Certificates.Kernel.LocalComp.L34Idx.Data
public import Certificates.Data.Kernel.L34Scan2
public import CFSG.Open.LocalVocabulary
public import Certificates.Kernel.LocalComp.L34Para.Data

public section

namespace CertificateChecks.KernelLC.L34Idx

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K CFSG.KC.L34Scan
open CFSG.KC.L34Scan2
open CFSG.KLie.CT (andB orB notB)

@[expose] noncomputable def idxPt (nY z5 z51 e x : Nat) : Bool :=
  orB (notB (andB (commPt 42 6 x z5) (commPt 42 6 x z51)))
    (orB (notB (Nat.beq (ppowK x 4) e)) (orB (memL 64 L34PT.T x) (memL nY L34IX.Y x)))

@[expose] noncomputable def idx22970 (s : Nat) : Bool :=
  strictB (pidn 42 6) fun e => strictB (L34PT.T 5) fun z5 => strictB (L34PT.T 51) fun z51 =>
    scanSl (idxPt 48 z5 z51 e) L34R.T 1344 s

@[expose] noncomputable def pairPt (q q' w : Nat) : Bool :=
  strictB (pcomp 42 6 (mask 6) (L34IX.Y q) (L34IX.YI q')) fun p =>
    orB (notB (Nat.beq (ppowK p 4) (pidn 42 6)))
      (andB (Nat.blt w 20160) (Nat.beq (L34S.T w) p))

@[expose] noncomputable def pairRows (lo n : Nat) : Bool :=
  allN n fun t => strictB (Nat.add lo t) fun q =>
    allN 48 fun q' => pairPt q q' (L34IX.W (Nat.add (Nat.mul 48 q) q'))

end CertificateChecks.KernelLC.L34Idx

end
