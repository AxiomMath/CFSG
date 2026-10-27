module

public import Certificates.Kernel.Sporadic.ON.GenLv
public import Certificates.Kernel.Sporadic.ON.GenTab
public meta import CFSG.Sporadic.Schreier.ONOuterData
public meta import Mathlib.Init

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ON3

meta def pslSM : Array (Array Nat) := CFSG.ONSchreier.Data.PSL120Chain.strongGenerators

meta def pslBM : Array Nat := CFSG.ONSchreier.Data.PSL120Chain.base

meta def inv120 (t : Array Nat) : Array Nat := Id.run do
  let mut r := Array.replicate 120 0
  for i in [0:120] do
    r := r.set! t[i]! i
  return r

meta def pslFM : Array Nat := pslSM.foldl (fun acc t => acc ++ t) #[]

meta def pslIM : Array Nat := pslSM.foldl (fun acc t => acc ++ inv120 t) #[]

meta def uIM : Array Nat := inv120 CFSG.ONSchreier.Data.quotientConjugator

end CertificateChecks.KernelSpor.ON3

#kon_levels CertificateChecks.KernelSpor.ON3LP CertificateChecks.KernelSpor.ON3.pslSM
  CertificateChecks.KernelSpor.ON3.pslBM 3

#kon_table CertificateChecks.KernelSpor.ON3P.FW CertificateChecks.KernelSpor.ON3.pslFM
#kon_table CertificateChecks.KernelSpor.ON3P.INV CertificateChecks.KernelSpor.ON3.pslIM
#kon_table CertificateChecks.KernelSpor.ON3P.UI CertificateChecks.KernelSpor.ON3.uIM
