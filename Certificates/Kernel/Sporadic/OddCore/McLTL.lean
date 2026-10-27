module

public import Certificates.Kernel.Sporadic.OddCore.MulHCmd
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Kernel.Census.McLChain
public import Certificates.Data.Kernel.Spor.MulHQ
public import Certificates.Data.Kernel.Spor.MulHAbs
public import CFSG.Sporadic.Recognition.McLASThreeLocalInputs
public meta import CFSG.Sporadic.Recognition.McLASThreeLocalInputs
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSpor.McLTh CFSG.Sporadic.Recognition.McLAS.threeHex
#kmisc_hexflat CertificateChecks.KernelSpor.McLTh CFSG.Sporadic.Recognition.McLAS.threeHex 3 275 9 11
#ks_chars CertificateChecks.KernelSpor.McLTl CFSG.Sporadic.Recognition.McLAS.tlHex
#kmisc_hexflat CertificateChecks.KernelSpor.McLTl CFSG.Sporadic.Recognition.McLAS.tlHex 3 275 9 15

namespace CertificateChecks.KernelSpor.McLTL

open CFSG.Sporadic.Recognition.McLAS CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open CFSG.PSL3Four.Native

meta def idM : Array Nat := idTab 275

meta def invM (a : Array Nat) : Array Nat := CFSG.Monster.B.Co2.Native.invCand 275 a

meta def thM : Array (Array Nat) := (List.range 11).toArray.map fun k => natArr (threeTbl k)

meta def tlM : Array (Array Nat) := (List.range 15).toArray.map fun k => natArr (tlTbl k)

meta def thIM : Array (Array Nat) := thM.map invM

meta def tlIM : Array (Array Nat) := tlM.map invM

meta def outIM : Array (Array Nat) := #[invM (natArr mclOuterTbl)]

meta def ids (k : Nat) : Array (Array Nat) := Array.replicate k idM

meta def ids5M : Array (Array Nat) := ids 5

meta def ids4M : Array (Array Nat) := ids 4

meta def tgM : Array (Array Nat) := (List.range 5).toArray.map fun i => thM[i + 6]!
meta def rgM : Array (Array Nat) := (List.range 5).toArray.map fun i => tlM[i + 2]!
meta def agM : Array (Array Nat) := (List.range 4).toArray.map fun i => tlM[i + 7]!

meta def mulRec (gs : Array (Array Nat)) (cap : Nat) : Array (Array Nat) :=
  (bfs (fun j t => conjTab 275 idM gs[j]! t) gs.size idM cap).tabs

meta def recT : Array (Array Nat) := mulRec tgM 800
meta def recR : Array (Array Nat) := mulRec rgM 300
meta def recA : Array (Array Nat) := mulRec agM 200

meta def clOf (rec gs : Array (Array Nat)) : Array (Array Nat) :=
  (rec.map fun x => (gs ++ gs.map invM).map fun g => comp 275 x g).flatten

meta def clT : Array (Array Nat) := clOf recT tgM
meta def clR : Array (Array Nat) := clOf recR rgM
meta def clA : Array (Array Nat) := clOf recA agM

meta def rIM : Array (Array Nat) := recR.map invM

meta def hkM (t : Array Nat) : Nat := (hkey 275 (t.map UInt32.ofNat)).toNat

meta def hsM (rec : Array (Array Nat)) : Array Nat := (rec.map hkM).qsort (· < ·)

meta def lowerM (s : Array Nat) (v : Nat) : Nat := Id.run do
  let mut lo := 0
  let mut hi := s.size
  for _ in [0:64] do
    if lo < hi then
      let mid := (lo + hi) / 2
      if s[mid]! < v then lo := mid + 1 else hi := mid
  return lo

meta def pbM (rec : Array (Array Nat)) (hs : Array Nat) (q : Array Nat) : Array Nat :=
  #[(indexOf rec).getD q rec.size, lowerM hs (hkM q)]

meta def nrM : Array (Array Nat) :=
  (#[thM[0]!, thM[1]!, thM[2]!, tlM[0]!].map fun c => rgM.map fun r =>
    comp 275 (comp 275 c r) (invM c)).flatten

meta def xabM : Array (Array Nat) := #[thM[0]!, tlM[12]!, tlM[13]!]

meta def tsM : Array (Array Nat) :=
  let hs := hsM recT
  let g := tlM[11]!
  recT.map fun e => #[(indexOf recR).getD e recR.size,
    lowerM hs (hkM (comp 275 (comp 275 (invM g) e) g))]

meta def traM : Array (Array Nat) :=
  let ia := indexOf recA
  recT.map fun e => Id.run do
    for r in [0:recR.size] do
      let q := comp 275 (invM recR[r]!) e
      match ia[q]? with
      | some p => return #[r, p]
      | none => pure ()
    return #[recR.size, recA.size]

meta def toM : Array (Array Nat) :=
  let ir := indexOf recR
  let ia := indexOf recA
  recT.map fun e => #[ir.getD e recR.size, ia.getD e recA.size]

meta def arM : Array (Array Nat) := recA.map (pbM recR (hsM recR))

end CertificateChecks.KernelSpor.McLTL

#kmisc_packarrs CertificateChecks.KernelSpor.McLThI CertificateChecks.KernelSpor.McLTL.thIM 9
#kmisc_packarrs CertificateChecks.KernelSpor.McLTlI CertificateChecks.KernelSpor.McLTL.tlIM 9
#kmisc_packarrs CertificateChecks.KernelSpor.McLTO CertificateChecks.KernelSpor.McLTL.outIM 9
#kmulh CertificateChecks.KernelSpor.McLTT 275 9 CertificateChecks.KernelSpor.McLTL.ids5M
  CertificateChecks.KernelSpor.McLTL.tgM CertificateChecks.KernelSpor.McLTL.idM 800
#kmulh CertificateChecks.KernelSpor.McLTR 275 9 CertificateChecks.KernelSpor.McLTL.ids5M
  CertificateChecks.KernelSpor.McLTL.rgM CertificateChecks.KernelSpor.McLTL.idM 300
#kmulh CertificateChecks.KernelSpor.McLTA 275 9 CertificateChecks.KernelSpor.McLTL.ids4M
  CertificateChecks.KernelSpor.McLTL.agM CertificateChecks.KernelSpor.McLTL.idM 200
#kfind CertificateChecks.KernelSpor.McLTClT CertificateChecks.KernelSpor.McLTL.recT
  CertificateChecks.KernelSpor.McLTL.clT
#kfind CertificateChecks.KernelSpor.McLTClR CertificateChecks.KernelSpor.McLTL.recR
  CertificateChecks.KernelSpor.McLTL.clR
#kfind CertificateChecks.KernelSpor.McLTClA CertificateChecks.KernelSpor.McLTL.recA
  CertificateChecks.KernelSpor.McLTL.clA
#kmisc_packarrs CertificateChecks.KernelSpor.McLTRI CertificateChecks.KernelSpor.McLTL.rIM 9
#kfind CertificateChecks.KernelSpor.McLTQRT CertificateChecks.KernelSpor.McLTL.recT
  CertificateChecks.KernelSpor.McLTL.recR
#kfind CertificateChecks.KernelSpor.McLTQAT CertificateChecks.KernelSpor.McLTL.recT
  CertificateChecks.KernelSpor.McLTL.recA
#kfind CertificateChecks.KernelSpor.McLTQNR CertificateChecks.KernelSpor.McLTL.recR
  CertificateChecks.KernelSpor.McLTL.nrM
#kfind CertificateChecks.KernelSpor.McLTQX CertificateChecks.KernelSpor.McLTL.recR
  CertificateChecks.KernelSpor.McLTL.xabM
#kmisc_packarrs CertificateChecks.KernelSpor.McLTQS CertificateChecks.KernelSpor.McLTL.tsM 32
#kmisc_packarrs CertificateChecks.KernelSpor.McLTQRA CertificateChecks.KernelSpor.McLTL.traM 32
#kmisc_packarrs CertificateChecks.KernelSpor.McLTQO CertificateChecks.KernelSpor.McLTL.toM 32
#kmisc_packarrs CertificateChecks.KernelSpor.McLTQAR CertificateChecks.KernelSpor.McLTL.arM 32

end
