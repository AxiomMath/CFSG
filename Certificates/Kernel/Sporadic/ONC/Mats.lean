module

public import Certificates.Data.CFSGNative.ON.Certificate
public import Certificates.Kernel.SporSch.HN.GenNTree
public meta import Certificates.Data.CFSGNative.ON.Certificate

public section

namespace CertificateChecks.KernelSpor.ONC

open CFSG.F3.Native CFSG.Sporadic.ON.Native CFSG.Sporadic.Th.Native

meta def laneOf (X : Array V) : Nat := Id.run do
  let mut acc := 0
  for r in [0:154] do
    let mut row := 0
    for c in [0:154] do
      row := row ||| (X[r]!.get c <<< (11 * c))
    acc := acc ||| (row <<< (1694 * r))
  return acc

meta def slpM : Array (Array V) × Array (Array V) := Id.run do
  let A := rowsA ()
  let B := rowsB ()
  let mut R : Array (Array V) := #[A, mul 154 (mul 154 B A) B] ++ Array.replicate 24 (idM 154)
  let mut invs : Array (Array V) := #[]
  for ins in prog do
    match ins with
    | .mu i j k => R := R.set! k (mul 154 R[i]! R[j]!)
    | .pwr e i k => R := R.set! k (powM 154 R[i]! e)
    | .iv i k =>
      let X := invV 154 R[i]!
      invs := invs.push X
      R := R.set! k X
  return (R, invs)

meta def mlM : List Nat := sel.toList.map fun s => laneOf slpM.1[s]!
meta def mvM : List Nat := slpM.2.toList.map laneOf

end CertificateChecks.KernelSpor.ONC

#kss_ntree CertificateChecks.KernelSpor.ONC.ML CertificateChecks.KernelSpor.ONC.mlM
#kss_ntree CertificateChecks.KernelSpor.ONC.MV CertificateChecks.KernelSpor.ONC.mvM

end
