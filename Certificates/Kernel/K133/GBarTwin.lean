module

public import Certificates.Kernel.K133.GBarData
public import Certificates.Kernel.Misc.Perm.HexCmd
meta import Certificates.Kernel.K133.GBarData
meta import Certificates.Kernel.LocalComp.BfsGen
import CFSG.Certificates.Kernel.Common.Harness

namespace CertificateChecks.KernelK133.GBarE

meta def ptsM : Array (Array Nat) := (CFSG.KC.BfsGen.search 256 9 gens.toArray).1

meta def compM (t u : Array Nat) : Array Nat := u.map fun i => t[i]!

meta def idM : Array Nat := Array.range 256

meta def powM (x : Array Nat) : Nat → Array Nat
  | 0 => idM
  | k + 1 => compM x (powM x k)

meta def movedM (x : Array Nat) (e : Nat) : Nat :=
  let y := powM x e
  ((List.range 256).find? fun p => y[p]! != p).getD 0

meta def isOrd (x : Array Nat) (e : Nat) : Bool := powM x e == idM && x != idM

meta def fiveM : Array Nat := (Array.range ptsM.size).filter fun i => isOrd ptsM[i]! 5
meta def twoM : Array Nat := (Array.range ptsM.size).filter fun i => isOrd ptsM[i]! 2

meta def posM (L : Array Nat) : List Nat := Id.run do
  let mut r := Array.replicate ptsM.size 0
  for k in [0:L.size] do
    r := r.set! L[k]! k
  return r.toList

meta def fiL : List Nat := fiveM.toList
meta def wiL : List Nat := twoM.toList
meta def p5L : List Nat := posM fiveM
meta def p2L : List Nat := posM twoM
meta def q5L : List Nat := (List.range ptsM.size).map fun i => movedM ptsM[i]! 5
meta def q2L : List Nat := (List.range ptsM.size).map fun i => movedM ptsM[i]! 2

meta def powsM (e : Nat) : Array (Array Nat) := fiveM.map fun i => powM ptsM[i]! e
meta def l2M : Array (Array Nat) := powsM 2
meta def l3M : Array (Array Nat) := powsM 3
meta def l4M : Array (Array Nat) := powsM 4

meta def fuM (u : Array Nat) : List Nat :=
  (List.range fiveM.size).filter fun k =>
    let a := ptsM[fiveM[k]!]!
    compM u a == compM a u

meta def fusM : List (List Nat) := twoM.toList.map fun j => fuM ptsM[j]!

meta def uvL : List Nat := fusM.flatten
meta def uoL : List Nat := (fusM.foldl (fun (acc : List Nat × Nat) l => (acc.1 ++ [acc.2], acc.2 + l.length))
  ([], 0)).1 ++ [uvL.length]

end CertificateChecks.KernelK133.GBarE

public section

set_option maxRecDepth 400000

#kss_natlist CertificateChecks.KernelK133.GB.FI CertificateChecks.KernelK133.GBarE.fiL
#kss_natlist CertificateChecks.KernelK133.GB.WI CertificateChecks.KernelK133.GBarE.wiL
#kss_natlist CertificateChecks.KernelK133.GB.P5 CertificateChecks.KernelK133.GBarE.p5L
#kss_natlist CertificateChecks.KernelK133.GB.P2 CertificateChecks.KernelK133.GBarE.p2L
#kss_natlist CertificateChecks.KernelK133.GB.Q5 CertificateChecks.KernelK133.GBarE.q5L
#kss_natlist CertificateChecks.KernelK133.GB.Q2 CertificateChecks.KernelK133.GBarE.q2L
#kmisc_packarrs CertificateChecks.KernelK133.GB.L2 CertificateChecks.KernelK133.GBarE.l2M 9
#kmisc_packarrs CertificateChecks.KernelK133.GB.L3 CertificateChecks.KernelK133.GBarE.l3M 9
#kmisc_packarrs CertificateChecks.KernelK133.GB.L4 CertificateChecks.KernelK133.GBarE.l4M 9
#kss_natlist CertificateChecks.KernelK133.GB.UV CertificateChecks.KernelK133.GBarE.uvL
#kss_natlist CertificateChecks.KernelK133.GB.UO CertificateChecks.KernelK133.GBarE.uoL

end
