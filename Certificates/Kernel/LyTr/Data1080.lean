module

public import Certificates.Kernel.LyTr.Data
public import CFSG.Sporadic.Recognition.LyonsAmalgamYInputs
meta import CFSG.Sporadic.Recognition.LyonsAmalgamYInputs
meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelLyTr.SH CFSG.Sporadic.Recognition.LyonsSims.Ly1080.sigmaHex
#kmisc_hexflat CertificateChecks.KernelLyTr.SH CFSG.Sporadic.Recognition.LyonsSims.Ly1080.sigmaHex
  3 1080 11 1

namespace CertificateChecks.KernelLyTr

open CFSG.Sporadic.SmallOddCore.Native CFSG.PSL3Four.Native
open CFSG.Sporadic.Recognition.LyonsSims

meta def id1080N : Array Nat := idTab 1080
meta def g1080N : Array (Array Nat) := Ly1080.txyTabs.map natArr
meta def gi1080N : Array (Array Nat) := g1080N.map (CFSG.Monster.B.Co2.Native.invCand 1080)
meta def rec1080N : Array (Array Nat) :=
  (bfs (fun j t => conjTab 1080 id1080N g1080N[j]! t) 5 id1080N 5000).tabs
meta def cl1080N : Array (Array Nat) :=
  (rec1080N.map fun x => (g1080N ++ gi1080N).map fun g => comp 1080 x g).flatten

end CertificateChecks.KernelLyTr

#kmisc_packarrs CertificateChecks.KernelLyTr.R1I CertificateChecks.KernelLyTr.gi1080N 11
#kfind CertificateChecks.KernelLyTr.R1Cl CertificateChecks.KernelLyTr.rec1080N
  CertificateChecks.KernelLyTr.cl1080N
