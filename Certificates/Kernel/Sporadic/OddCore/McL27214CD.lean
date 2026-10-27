module

public import Certificates.Kernel.LocalQT.PEnumD
public meta import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.McLInvData

namespace CertificateChecks.KernelSpor.M27214

open CFSG.PSL3Four.Native CFSG.EvenSporadicStandard.McLInv CFSG.Sporadic.McL.Native

meta def commM (x r : Tab) : Bool := Id.run do
  for p in [0:275] do
    if x[r[p]!]! != r[x[p]!]! then return false
  return true

meta def centPosM : Array (Array Nat) :=
  let gJ := gensJ (orbitData ())
  let I := (orbitBFS 275 gJ (gJ.map (invTab 275)) gJ[0]! 22275).tabs
  (repsOf (enumBFS 275 (gensR (orbitData ())) 729)).map fun r =>
    ((List.range I.size).filter fun i => commM I[i]! r).toArray

meta def cWM : Array Nat := centPosM.flatten

meta def cOM : Array Nat := Id.run do
  let mut a : Array Nat := #[0]
  for c in centPosM do
    a := a.push (a.back! + c.size)
  return a

end CertificateChecks.KernelSpor.M27214

public section

set_option maxRecDepth 400000

#krows32 CertificateChecks.KernelSpor.MLCW CertificateChecks.KernelSpor.M27214.cWM

#krows32 CertificateChecks.KernelSpor.MLCO CertificateChecks.KernelSpor.M27214.cOM

end
