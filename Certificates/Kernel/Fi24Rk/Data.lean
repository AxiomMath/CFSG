module

public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Kernel.Sporadic.HexNumsGen
public import Certificates.Kernel.LocalComp.Fi24Pl.Data
public import Certificates.Data.Fi24Rank.KData
meta import Certificates.Data.Fi24Rank.KCheck

namespace CertificateChecks.KernelFi24Rk.E

open CFSG.LocalAnalysis.GLTheoremA.H1017.Fi24RankNative

meta def sing (a : Array Nat) : Array (Array Nat) := a.map fun x => #[x]

meta def comp (t u : Array Nat) : Array Nat := Array.ofFn (n := u.size) fun i => t[u[i.val]!]!

meta def idn (n : Nat) : Array Nat := Array.ofFn (n := n) fun i => i.val

meta def key (b : Nat) (a : Array Nat) : Nat := a.foldr (fun x acc => x + (acc <<< b)) 0

meta def A : Array (Array Nat) := kRA ()

meta def G : Array (Array Nat) := kRG ()

meta def M : Array (Array Nat) := kRMu ()

meta def pw : Array (Array Nat) := Id.run do
  let mut out := #[]
  for k in [0:5] do
    let a := A[k]!
    out := out.push (idn 504)
    out := out.push (comp a (idn 504))
    out := out.push (comp a (comp a (idn 504)))
  return out

meta def layer (k : Nat) (J' : Array (Array Nat)) : Array (Array Nat) :=
  Array.ofFn (n := 3 * J'.size) fun i => comp pw[3 * k + i.val % 3]! J'[i.val / 3]!

meta def j3 : Array (Array Nat) := layer 3 #[pw[12]!, pw[13]!, pw[14]!]
meta def j2 : Array (Array Nat) := layer 2 j3
meta def j1 : Array (Array Nat) := layer 1 j2
meta def iot : Array (Array Nat) := layer 0 j1

meta def so : Array Nat := (Array.range 243).qsort fun a b => iot[a]![kRP0]! < iot[b]![kRP0]!

meta def pb : Array (Array Nat) × Array Nat × Array Nat := pbBFS M

meta def L : Array (Array Nat) := pb.1

meta def lidx (x : Array Nat) : Nat := (L.findIdx? fun y => y == x).getD 127

meta def edges : Array Nat := (Array.range L.size).map fun q =>
  lidx (comp L[q]! M[0]!) ||| (lidx (comp L[q]! M[1]!) <<< 7)

meta def pls : Array Nat := (Array.range L.size).map fun k => pb.2.1[k]! ||| (pb.2.2[k]! <<< 7)

meta def sl : Array Nat := (Array.range L.size).qsort fun a b => key 8 L[a]! < key 8 L[b]!

meta def mts : Array Nat := (Array.range L.size).map fun k =>
  (List.range L.size).foldr (fun l acc => lidx (comp L[k]! L[l]!) ||| (acc <<< 7)) 0

meta def fms : Array Nat := L.map fun p =>
  (List.range 243).foldl (fun acc v => if p[v]! == v then acc ||| (1 <<< v) else acc) 0

meta def sms : Array Nat := (Array.range 504).map fun q =>
  (List.range 243).foldl (fun acc i => if iot[i]![q]! == q then acc ||| (1 <<< i) else acc) 0

meta def cms : Array Nat := (sms.qsort (· < ·)).foldl
  (fun acc m => if acc.back? == some m then acc else acc.push m) #[]

meta def cls : Array Nat := sms.map fun m => (cms.findIdx? (· == m)).getD 0

meta def po : Array Nat :=
  (Array.range 504).qsort fun a b => cls[a]! < cls[b]! || (cls[a]! == cls[b]! && a < b)

meta def poi : Array Nat := Id.run do
  let mut r := Array.replicate 504 0
  for s in [0:504] do
    r := r.set! po[s]! s
  return r

meta def st : Array Nat := (Array.range (cms.size + 1)).map fun c =>
  (List.range 504).foldl (fun acc s => if cls[po[s]!]! < c then acc + 1 else acc) 0

meta def ws : Array Nat := (Array.range 504).map fun q =>
  let c := cls[q]!
  let img := (List.range 243).foldl (fun (r : Array Nat) i => r.set! iot[i]![q]! i)
    (Array.replicate 504 0)
  (List.range (st[c + 1]! - st[c]!)).foldr (fun t acc =>
    img[po[st[c]! + t]!]! ||| (acc <<< 8)) 0

meta def soR : Array (Array Nat) := sing so
meta def lR : Array (Array Nat) := L
meta def edgesR : Array (Array Nat) := sing edges
meta def plsR : Array (Array Nat) := sing pls
meta def slR : Array (Array Nat) := sing sl
meta def mtsR : Array (Array Nat) := sing mts
meta def fmsR : Array (Array Nat) := sing fms
meta def smsR : Array (Array Nat) := sing sms
meta def clsR : Array (Array Nat) := sing cls
meta def cmsR : Array (Array Nat) := sing cms
meta def poR : Array (Array Nat) := sing po
meta def poiR : Array (Array Nat) := sing poi
meta def stR : Array (Array Nat) := sing st
meta def wsR : Array (Array Nat) := sing ws

end CertificateChecks.KernelFi24Rk.E

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelFi24Rk.T.G CFSG.LocalAnalysis.GLTheoremA.H1017.Fi24RankNative.kRGText
#ks_hexnums CertificateChecks.KernelFi24Rk.T.G
  CFSG.LocalAnalysis.GLTheoremA.H1017.Fi24RankNative.kRGText 3 9
#ks_chars CertificateChecks.KernelFi24Rk.T.M
  CFSG.LocalAnalysis.GLTheoremA.H1017.Fi24RankNative.kRMuText
#ks_hexnums CertificateChecks.KernelFi24Rk.T.M
  CFSG.LocalAnalysis.GLTheoremA.H1017.Fi24RankNative.kRMuText 2 8

#kmisc_packarrs CertificateChecks.KernelFi24Rk.D.AK CertificateChecks.KernelFi24Rk.E.A 9
#kmisc_packarrs CertificateChecks.KernelFi24Rk.D.GK CertificateChecks.KernelFi24Rk.E.G 9
#kmisc_packarrs CertificateChecks.KernelFi24Rk.D.MUK CertificateChecks.KernelFi24Rk.E.M 8
#kmisc_packarrs CertificateChecks.KernelFi24Rk.D.PW CertificateChecks.KernelFi24Rk.E.pw 9
#kmisc_packarrs CertificateChecks.KernelFi24Rk.D.J3 CertificateChecks.KernelFi24Rk.E.j3 9
#kmisc_packarrs CertificateChecks.KernelFi24Rk.D.J2 CertificateChecks.KernelFi24Rk.E.j2 9
#kmisc_packarrs CertificateChecks.KernelFi24Rk.D.J1 CertificateChecks.KernelFi24Rk.E.j1 9
#kmisc_packarrs CertificateChecks.KernelFi24Rk.D.IK CertificateChecks.KernelFi24Rk.E.iot 9
#kmisc_packarrs CertificateChecks.KernelFi24Rk.D.SO CertificateChecks.KernelFi24Rk.E.soR 16
#kmisc_packarrs CertificateChecks.KernelFi24Rk.D.LK CertificateChecks.KernelFi24Rk.E.lR 8
#kmisc_packarrs CertificateChecks.KernelFi24Rk.D.EK CertificateChecks.KernelFi24Rk.E.edgesR 16
#kmisc_packarrs CertificateChecks.KernelFi24Rk.D.PLK CertificateChecks.KernelFi24Rk.E.plsR 16
#kmisc_packarrs CertificateChecks.KernelFi24Rk.D.SL CertificateChecks.KernelFi24Rk.E.slR 16
#kmisc_packarrs CertificateChecks.KernelFi24Rk.D.MTK CertificateChecks.KernelFi24Rk.E.mtsR 1024
#kmisc_packarrs CertificateChecks.KernelFi24Rk.D.FMK CertificateChecks.KernelFi24Rk.E.fmsR 256
#kmisc_packarrs CertificateChecks.KernelFi24Rk.D.SMK CertificateChecks.KernelFi24Rk.E.smsR 256
#kmisc_packarrs CertificateChecks.KernelFi24Rk.D.CLK CertificateChecks.KernelFi24Rk.E.clsR 16
#kmisc_packarrs CertificateChecks.KernelFi24Rk.D.CMK CertificateChecks.KernelFi24Rk.E.cmsR 256
#kmisc_packarrs CertificateChecks.KernelFi24Rk.D.POK CertificateChecks.KernelFi24Rk.E.poR 16
#kmisc_packarrs CertificateChecks.KernelFi24Rk.D.POIK CertificateChecks.KernelFi24Rk.E.poiR 16
#kmisc_packarrs CertificateChecks.KernelFi24Rk.D.STK CertificateChecks.KernelFi24Rk.E.stR 16
#kmisc_packarrs CertificateChecks.KernelFi24Rk.D.WK CertificateChecks.KernelFi24Rk.E.wsR 2048

end
