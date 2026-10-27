module

public import Certificates.Kernel.Sporadic.Fi22.Pair214032D
public import Certificates.Kernel.Sporadic.Fi22.Pump36908K
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Pair214032

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Fi22Pump CFSG.KC.PtOrb
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.Pump36908
open CertificateChecks.KernelFi22Reps (xT)

@[expose] noncomputable def Z (j : Nat) : Nat := Fi22PairT.F j

theorem zY : strictB S (fun s => strictB (Fi22X.inv s) fun si => strictB (xT 3) fun t =>
    allN 2 fun j => strictB (Z j) fun y => chkY s si t y) = true := by quickRfl

theorem zO : strictB (Z 0) (fun y0 => strictB (Z 1) fun y1 => orbC (gY y0 y1) 2 12 1 405) =
    true := by quickRfl

end CertificateChecks.KernelSpor.Pair214032

end
