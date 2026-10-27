module

public import Certificates.Kernel.Sporadic.OddCore.PEnumCmd
public import Certificates.Kernel.Sporadic.ON.GenTab
public import Certificates.Kernel.Sporadic.ON.GenLv
public import CFSG.Sporadic.Schreier.ONOuterData
public meta import CFSG.Sporadic.Schreier.ONOuterData
public meta import Mathlib.Init
public import Mathlib.Init

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ON6

open CFSG.ONSchreier CFSG.ONSchreier.Native

meta def invM (n : Nat) (t : Array Nat) : Array Nat := Id.run do
  let mut r := Array.replicate n 0
  for i in [0:n] do
    r := r.set! t[i]! i
  return r

meta def flatF (c : Data.SmallChain) : Array Nat := c.strongGenerators.foldl (· ++ ·) #[]
meta def flatI (c : Data.SmallChain) : Array Nat :=
  c.strongGenerators.foldl (fun acc t => acc ++ invM c.degree t) #[]
meta def idxM (c : Data.SmallChain) (i : Nat) : List Nat := levIdx c.strongGenerators c.base i

meta def tF : Array Nat := flatF Data.T32Chain
meta def tI : Array Nat := flatI Data.T32Chain
meta def tS : Array (Array Nat) := Data.T32Chain.strongGenerators
meta def tB : Array Nat := Data.T32Chain.base
meta def tX0 : List Nat := idxM Data.T32Chain 0
meta def tX1 : List Nat := idxM Data.T32Chain 1
meta def tX2 : List Nat := idxM Data.T32Chain 2

meta def mF : Array Nat := flatF Data.M120Chain
meta def mI : Array Nat := flatI Data.M120Chain
meta def mS : Array (Array Nat) := Data.M120Chain.strongGenerators
meta def mB : Array Nat := Data.M120Chain.base
meta def mX0 : List Nat := idxM Data.M120Chain 0
meta def mX1 : List Nat := idxM Data.M120Chain 1
meta def mX2 : List Nat := idxM Data.M120Chain 2

meta def lF : Array Nat := flatF Data.L120Chain
meta def lI : Array Nat := flatI Data.L120Chain
meta def lS : Array (Array Nat) := Data.L120Chain.strongGenerators
meta def lB : Array Nat := Data.L120Chain.base
meta def lX0 : List Nat := idxM Data.L120Chain 0
meta def lX1 : List Nat := idxM Data.L120Chain 1
meta def lX2 : List Nat := idxM Data.L120Chain 2

meta def pF : Array Nat := flatF Data.PSL21Chain
meta def pI : Array Nat := flatI Data.PSL21Chain
meta def pS : Array (Array Nat) := Data.PSL21Chain.strongGenerators
meta def pB : Array Nat := Data.PSL21Chain.base
meta def pX0 : List Nat := idxM Data.PSL21Chain 0
meta def pX1 : List Nat := idxM Data.PSL21Chain 1
meta def pX2 : List Nat := idxM Data.PSL21Chain 2
meta def pX3 : List Nat := idxM Data.PSL21Chain 3

meta def qF : Array Nat := flatF Data.PSL120Chain
meta def qI : Array Nat := flatI Data.PSL120Chain
meta def qS : Array (Array Nat) := Data.PSL120Chain.strongGenerators
meta def qB : Array Nat := Data.PSL120Chain.base
meta def qX0 : List Nat := idxM Data.PSL120Chain 0
meta def qX1 : List Nat := idxM Data.PSL120Chain 1
meta def qX2 : List Nat := idxM Data.PSL120Chain 2

end CertificateChecks.KernelSpor.ON6

#kon_table CertificateChecks.KernelSpor.ON6T.TF CertificateChecks.KernelSpor.ON6.tF
#kon_table CertificateChecks.KernelSpor.ON6T.TI CertificateChecks.KernelSpor.ON6.tI
#kon_levels CertificateChecks.KernelSpor.ON6TL CertificateChecks.KernelSpor.ON6.tS
  CertificateChecks.KernelSpor.ON6.tB 3
#knatlist CertificateChecks.KernelSpor.ON6.TX0 CertificateChecks.KernelSpor.ON6.tX0
#knatlist CertificateChecks.KernelSpor.ON6.TX1 CertificateChecks.KernelSpor.ON6.tX1
#knatlist CertificateChecks.KernelSpor.ON6.TX2 CertificateChecks.KernelSpor.ON6.tX2

#kon_table CertificateChecks.KernelSpor.ON6T.MF CertificateChecks.KernelSpor.ON6.mF
#kon_table CertificateChecks.KernelSpor.ON6T.MI CertificateChecks.KernelSpor.ON6.mI
#kon_levels CertificateChecks.KernelSpor.ON6ML CertificateChecks.KernelSpor.ON6.mS
  CertificateChecks.KernelSpor.ON6.mB 3
#knatlist CertificateChecks.KernelSpor.ON6.MX0 CertificateChecks.KernelSpor.ON6.mX0
#knatlist CertificateChecks.KernelSpor.ON6.MX1 CertificateChecks.KernelSpor.ON6.mX1
#knatlist CertificateChecks.KernelSpor.ON6.MX2 CertificateChecks.KernelSpor.ON6.mX2

#kon_table CertificateChecks.KernelSpor.ON6T.LF CertificateChecks.KernelSpor.ON6.lF
#kon_table CertificateChecks.KernelSpor.ON6T.LI CertificateChecks.KernelSpor.ON6.lI
#kon_levels CertificateChecks.KernelSpor.ON6LL CertificateChecks.KernelSpor.ON6.lS
  CertificateChecks.KernelSpor.ON6.lB 3
#knatlist CertificateChecks.KernelSpor.ON6.LX0 CertificateChecks.KernelSpor.ON6.lX0
#knatlist CertificateChecks.KernelSpor.ON6.LX1 CertificateChecks.KernelSpor.ON6.lX1
#knatlist CertificateChecks.KernelSpor.ON6.LX2 CertificateChecks.KernelSpor.ON6.lX2

#kon_table CertificateChecks.KernelSpor.ON6T.PF CertificateChecks.KernelSpor.ON6.pF
#kon_table CertificateChecks.KernelSpor.ON6T.PI CertificateChecks.KernelSpor.ON6.pI
#kon_levels CertificateChecks.KernelSpor.ON6PL CertificateChecks.KernelSpor.ON6.pS
  CertificateChecks.KernelSpor.ON6.pB 4
#knatlist CertificateChecks.KernelSpor.ON6.PX0 CertificateChecks.KernelSpor.ON6.pX0
#knatlist CertificateChecks.KernelSpor.ON6.PX1 CertificateChecks.KernelSpor.ON6.pX1
#knatlist CertificateChecks.KernelSpor.ON6.PX2 CertificateChecks.KernelSpor.ON6.pX2
#knatlist CertificateChecks.KernelSpor.ON6.PX3 CertificateChecks.KernelSpor.ON6.pX3

#kon_table CertificateChecks.KernelSpor.ON6T.QF CertificateChecks.KernelSpor.ON6.qF
#kon_table CertificateChecks.KernelSpor.ON6T.QI CertificateChecks.KernelSpor.ON6.qI
#kon_levels CertificateChecks.KernelSpor.ON6QL CertificateChecks.KernelSpor.ON6.qS
  CertificateChecks.KernelSpor.ON6.qB 3
#knatlist CertificateChecks.KernelSpor.ON6.QX0 CertificateChecks.KernelSpor.ON6.qX0
#knatlist CertificateChecks.KernelSpor.ON6.QX1 CertificateChecks.KernelSpor.ON6.qX1
#knatlist CertificateChecks.KernelSpor.ON6.QX2 CertificateChecks.KernelSpor.ON6.qX2

end
