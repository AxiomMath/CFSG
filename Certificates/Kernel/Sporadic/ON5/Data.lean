module

public import Certificates.Kernel.Sporadic.OddCore.PEnumCmd
public import Certificates.Kernel.Sporadic.ON.GenTab
public import Certificates.Kernel.Sporadic.ON.GenLv
public meta import CFSG.Sporadic.Schreier.ONCheckSmallAuxInputs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ON5

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.PSL3Four.Native

meta def m120G : Array (Array Nat) := Data.M120Chain.generators

meta def id120 : Array Nat := idTab 120

meta def dSelM : List Nat :=
  (List.range m120Enum.tabs.size).filter fun i =>
    Data.D120Generators.all fun g => comp 120 m120Enum.tabs[i]! g == comp 120 g m120Enum.tabs[i]!

meta def tSelM : List Nat :=
  (List.range t32Enum.tabs.size).filter fun i =>
    Data.T32Chain.generators.all fun g => comp 32 t32Enum.tabs[i]! g == comp 32 g t32Enum.tabs[i]!

meta def invM (n : Nat) (t : Array Nat) : Array Nat := Id.run do
  let mut r := Array.replicate n 0
  for i in [0:n] do
    r := r.set! t[i]! i
  return r

meta def dIM : Array Nat := Data.D120Generators.foldl (fun acc t => acc ++ invM 120 t) #[]

meta def sIM : Array Nat :=
  Data.M120Chain.strongGenerators.foldl (fun acc t => acc ++ invM 120 t) #[]

meta def zIM : Array Nat := invM 32 Data.T32z

meta def m120S : Array (Array Nat) := Data.M120Chain.strongGenerators

meta def m120B : Array Nat := Data.M120Chain.base

meta def dFM : Array Nat := Data.D120Generators.foldl (fun acc t => acc ++ t) #[]

meta def sFM : Array Nat := Data.M120Chain.strongGenerators.foldl (fun acc t => acc ++ t) #[]

meta def dPackM : List Nat := Data.D120Generators.toList.map (CFSG.KS.RawGen.pack 7)

meta def idx0M : List Nat := levIdx Data.M120Chain.strongGenerators Data.M120Chain.base 0
meta def idx1M : List Nat := levIdx Data.M120Chain.strongGenerators Data.M120Chain.base 1
meta def idx2M : List Nat := levIdx Data.M120Chain.strongGenerators Data.M120Chain.base 2

end CertificateChecks.KernelSpor.ON5

#knatlist CertificateChecks.KernelSpor.ON5.dPack CertificateChecks.KernelSpor.ON5.dPackM
#knatlist CertificateChecks.KernelSpor.ON5.idx0 CertificateChecks.KernelSpor.ON5.idx0M
#knatlist CertificateChecks.KernelSpor.ON5.idx1 CertificateChecks.KernelSpor.ON5.idx1M
#knatlist CertificateChecks.KernelSpor.ON5.idx2 CertificateChecks.KernelSpor.ON5.idx2M

#kon_table CertificateChecks.KernelSpor.ON5T.DF CertificateChecks.KernelSpor.ON5.dFM
#kon_table CertificateChecks.KernelSpor.ON5T.SF CertificateChecks.KernelSpor.ON5.sFM

#kpenum CertificateChecks.KernelSpor.ON5M 120 7 false CertificateChecks.KernelSpor.ON5.m120G
  CertificateChecks.KernelSpor.ON5.m120G CertificateChecks.KernelSpor.ON5.id120 50000

#knatlist CertificateChecks.KernelSpor.ON5.dSel CertificateChecks.KernelSpor.ON5.dSelM
#knatlist CertificateChecks.KernelSpor.ON5.tSel CertificateChecks.KernelSpor.ON5.tSelM

#kon_table CertificateChecks.KernelSpor.ON5T.DI CertificateChecks.KernelSpor.ON5.dIM
#kon_table CertificateChecks.KernelSpor.ON5T.SI CertificateChecks.KernelSpor.ON5.sIM
#kon_table CertificateChecks.KernelSpor.ON5T.ZI CertificateChecks.KernelSpor.ON5.zIM

#kon_levels CertificateChecks.KernelSpor.ON5LM CertificateChecks.KernelSpor.ON5.m120S
  CertificateChecks.KernelSpor.ON5.m120B 3
