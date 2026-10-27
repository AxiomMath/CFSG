module

public import Certificates.Kernel.Sporadic.ONOrd.Glue
public import Certificates.Kernel.Sporadic.ONOrd.Defs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Sporadic.ONOddCore.SeedOrdersCheckInputs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ONOrd

open CFSG.KS.ONLin CFSG.ONSchreier.Native CFSG.Sporadic.ON.Native CFSG.Sporadic.ONOddCore
open CertificateChecks.KernelSpor.ON8

theorem peq_id {t : Array Nat} {F : Nat → Nat} (ht : Rd (nPts ()) t F) (hF : L F)
    (h : onP F (fun x => x) = true) : peq (nPts ()) t (pid (nPts ())) = true :=
  peq_true ht rd_pid (id_of_onP hF h)

theorem peq_ne {t : Array Nat} {F : Nat → Nat} (ht : Rd (nPts ()) t F)
    (h : (!onP F fun x => x) = true) : peq (nPts ()) t (pid (nPts ())) = false := by
  obtain ⟨x, hx, hne⟩ := moved_of_onP h
  exact peq_false ht rd_pid hx hne

end CertificateChecks.KernelSpor.ONOrd

end
