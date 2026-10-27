
module

public import Certificates.Kernel.L34W.Outer
public import Certificates.Kernel.L34W.Glue
public import CFSG.Certificates.Kernel.L34W.OuterSound

public section

namespace CertificateChecks.KernelL34W

open CFSG.KC.Enum CFSG.KS CFSG.KC.L34W
open CFSG.ComponentClassification.GrSLit.L34Facts.Real CFSG.ComponentClassification.GrSLit.L34Facts.Real.WIso

theorem out_mem {t i : ℕ} (ht : t < 64) (hi : i < 36) (hS : repInS.contains i = false)
    (h2 : yPerm t i * yPerm t i = 1) : ∃ j < 144, OT j = 64 * i + t :=
  outer_mem gensG y_k out_k ht hi hS h2

theorem cm_iff {j j' : ℕ} (hj : j < 144) (hj' : j' < 144) :
    hasBit (CM j) j' = true ↔
      yPerm (OT j % 64) (OT j / 64) * yPerm (OT j' % 64) (OT j' / 64) =
        yPerm (OT j' % 64) (OT j' / 64) * yPerm (OT j % 64) (OT j / 64) :=
  comm_iff gensG y_k out_k comm_k hj hj'

theorem bt_dec {j k : ℕ} (hj : j < 144) (hk : k < 64) :
    pg 10 (mask 10) (BT j) k < 1024 ∧
      dec (pg 10 (mask 10) (BT j) k) = betaYM (OT j % 64) (OT j / 64) (k, 0, 0) :=
  bt_spec t1Of alOf bounds_k (fun _ hj => ot_lt out_k hj) beta_k hj hk

theorem kv_iff' {j k : ℕ} (hj : j < 144) (hk : k < 64) :
    kvK T1X.F BT j k = true ↔ k = 0 ∨ ((mulM (k, 0, 0) (k, 0, 0)).1 = 0 ∧
      (betaYM (OT j % 64) (OT j / 64) (k, 0, 0)).1 = k) :=
  kv_iff t1Of alOf bounds_k (fun _ hj => ot_lt out_k hj) beta_k hj hk

end CertificateChecks.KernelL34W

end
