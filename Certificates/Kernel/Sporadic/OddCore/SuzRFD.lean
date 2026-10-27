module

public import Certificates.Kernel.Sporadic.OddCore.PEnumCmd
public import Certificates.Kernel.Misc.Perm.HexCmd
meta import CFSG.Sporadic.SuzRecog.LocalRFusionGenTests
import CFSG.Open.LocalVocabulary

namespace CertificateChecks.KernelSpor.SuzRF

open CFSG.Sporadic.SuzRecog.LocalR CFSG.PSL3Four.Native CFSG.KS.PEnumGen CFSG.Sporadic.SuzOddCore
  CFSG.ComponentClassification.AS81.SuzB0

meta def oG : Array (Array Nat) := orbGens
meta def oGI : Array (Array Nat) := orbInvs

meta def r0 : Array Nat := lambdaTab 0
meta def r1 : Array Nat := lambdaTab 1
meta def r2 : Array Nat := lambdaTab 2
meta def r3 : Array Nat := lambdaTab 3

meta def sG : Array (Array Nat) := s1Gens
meta def idR : Array Nat := idTab 1782

meta def sT : Array (Array Nat) := (enumBFS 1782 s1Gens 8192).tabs

meta def orbIdx : Std.HashMap (Array Nat) Nat := Id.run do
  let mut m : Std.HashMap (Array Nat) Nat := {}
  for i in [0:4] do
    let T := (orbitBFS 1782 orbGens orbInvs (lambdaTab i) lambdaSizes[i]!).tabs
    for q in [0:T.size] do
      m := m.insert T[q]! (8192 * i + q)
  return m

meta def diffAt (x y : Array Nat) : Nat :=
  ((List.range 1782).find? fun p => !(x[p]! == y[p]!)).map (· + 1) |>.getD 0

meta def coverCode (x : Array Nat) : Nat :=
  if x == idTab 1782 then 0 else
    let d := diffAt (comp 1782 x x) (idTab 1782)
    if d != 0 then d else 2048 + orbIdx.getD x 0

meta def commCode (x : Array Nat) : Nat :=
  diffAt (comp 1782 x (lambdaTab 3)) (comp 1782 (lambdaTab 3) x)

meta def rowsOf (a : Array Nat) : Array (Array Nat) :=
  (List.range ((a.size + 31) / 32)).toArray.map fun r =>
    (List.range 32).toArray.map fun t => a.getD (32 * r + t) 0

meta def wCR : Array (Array Nat) := rowsOf (sT.map coverCode)
meta def wVR : Array (Array Nat) := rowsOf (sT.map commCode)

meta def v0L : List Nat := (List.range sT.size).filter fun k => commCode sT[k]! == 0

meta def anyL : List Nat :=
  ((List.range v0L.length).find? fun j => pow4Tab sT[v0L[j]!]! == tTab).toList

end CertificateChecks.KernelSpor.SuzRF

public section

set_option maxRecDepth 400000

#kpenum CertificateChecks.KernelSpor.SuzRFO0 1782 11 true CertificateChecks.KernelSpor.SuzRF.oG
  CertificateChecks.KernelSpor.SuzRF.oGI CertificateChecks.KernelSpor.SuzRF.r0 1
#kpenum CertificateChecks.KernelSpor.SuzRFO1 1782 11 true CertificateChecks.KernelSpor.SuzRF.oG
  CertificateChecks.KernelSpor.SuzRF.oGI CertificateChecks.KernelSpor.SuzRF.r1 54
#kpenum CertificateChecks.KernelSpor.SuzRFO2 1782 11 true CertificateChecks.KernelSpor.SuzRF.oG
  CertificateChecks.KernelSpor.SuzRF.oGI CertificateChecks.KernelSpor.SuzRF.r2 360
#kpenum CertificateChecks.KernelSpor.SuzRFO3 1782 11 true CertificateChecks.KernelSpor.SuzRF.oG
  CertificateChecks.KernelSpor.SuzRF.oGI CertificateChecks.KernelSpor.SuzRF.r3 6480
#kpenum CertificateChecks.KernelSpor.SuzRFS 1782 11 false CertificateChecks.KernelSpor.SuzRF.sG
  CertificateChecks.KernelSpor.SuzRF.sG CertificateChecks.KernelSpor.SuzRF.idR 8192

#kmisc_packarrs CertificateChecks.KernelSpor.SuzRFWC CertificateChecks.KernelSpor.SuzRF.wCR 32
#kmisc_packarrs CertificateChecks.KernelSpor.SuzRFWV CertificateChecks.KernelSpor.SuzRF.wVR 32

#knatlist CertificateChecks.KernelSpor.SuzRFV CertificateChecks.KernelSpor.SuzRF.v0L
#knatlist CertificateChecks.KernelSpor.SuzRFA CertificateChecks.KernelSpor.SuzRF.anyL

end
