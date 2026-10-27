module

public import Certificates.Kernel.Sporadic.ConjTreeGen
public import Certificates.Kernel.Sporadic.ON.Gen
public import Certificates.Kernel.Sporadic.Fi24K.K2077
public import Certificates.Kernel.Sporadic.Fi24K.P2077
public meta import CFSG.Sporadic.FischerOddCore.Fi24R2KCheckInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Fi24R

meta def gM : Array (Array Nat) := CFSG.Sporadic.FischerOddCore.fi24KStrong.extract 0 2

end CertificateChecks.KernelSpor.Fi24R

#ks_conjtree CertificateChecks.KernelSpor.Fi24ST 504 9 2 64 CertificateChecks.KernelSpor.Fi24R.gM
  CFSG.Sporadic.FischerOddCore.fi24S0 CFSG.Sporadic.FischerOddCore.fi24STree
  CertificateChecks.KernelSpor.Fi24KC.S CertificateChecks.KernelSpor.Fi24KC.SI
  CertificateChecks.KernelSpor.Fi24T.Tree.F 10 CertificateChecks.KernelSpor.Fi24PC.S 9

namespace CertificateChecks.KernelSpor.Fi24ST

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

@[expose] noncomputable def siftSl (s : Nat) : Bool := allN 63 (fun d =>
  siftK 504 9 (mask 9) (504 * 9) (pidn 504 9) Fi24KC.LR Fi24KC.TRI Fi24KC.BP 7 0
    (T (Nat.add (s * 63) d)))

@[expose] noncomputable def baseCommRow (j : Nat) : Bool := strictB (T j) (fun a => allN j (fun k =>
  strictB (T k) (fun b => allN 7 (fun t => strictB (pg 9 (mask 9) Fi24KC.BP t) (fun p =>
    Nat.beq (pg 9 (mask 9) a (pg 9 (mask 9) b p)) (pg 9 (mask 9) b (pg 9 (mask 9) a p)))))))

end CertificateChecks.KernelSpor.Fi24ST

#kon_slices CertificateChecks.KernelSpor.Fi24ST.siftSl 0 6
#kon_join CertificateChecks.KernelSpor.Fi24ST.siftAll CertificateChecks.KernelSpor.Fi24ST.siftSl 6

#kon_slices CertificateChecks.KernelSpor.Fi24ST.baseCommRow 0 378
#kon_join CertificateChecks.KernelSpor.Fi24ST.baseCommAll
  CertificateChecks.KernelSpor.Fi24ST.baseCommRow 378

end
