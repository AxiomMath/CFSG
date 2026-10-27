module

public import Certificates.Kernel.KDenseP.Axis.Mono
public import Certificates.Kernel.KDenseP.Axis.Tags
public import CFSG.Certificates.Kernel.KDenseP.Axis.C6016T0
public import CFSG.Certificates.Kernel.KDenseP.Axis.C6016T1
public import CFSG.Certificates.Kernel.KDenseP.Axis.C6016T2

public section

namespace CertificateChecks.KernelKDenseP.Axis

open CFSG.KC CFSG.KC.KDense CFSG.KC.KDenseP CFSG.KC.KDenseP.Axis CFSG.Monster.AxisCount

set_option maxRecDepth 100000

theorem items6016 : ∀ x ∈ recTag HS.recShard_6, TagEq x :=
  eq_items data_okP (T := recTag HS.recShard_6) (recTag_fst _).symm CFSG.KD.AX.c6016.weq
    (WL := CFSG.KD.AX.c6016.WL) (fun _ => rfl)
    (S := rlS CFSG.KD.AX.c6016.rn CFSG.KD.AX.c6016.CH CFSG.KD.AX.c6016.PRf CFSG.KD.AX.c6016.S0 3)
    (CH := CFSG.KD.AX.c6016.CH) (IXf := CFSG.KD.AX.c6016.IXf) (CHI := CFSG.KD.AX.c6016.CHI)
    (fun _ => rfl) (nch := kd_count% CFSG.KD.AX.c6016 CH) (nIX := kd_count% CFSG.KD.AX.c6016 IX)
    (IT := CFSG.KD.AX.c6016.IT) (kd_axC% CFSG.KD.AX.c6016) (by decide +kernel) (by quickRfl)
    (rlS_init (by norm_num) (by quickRfl)) (rlS_init (by norm_num) (by quickRfl)) (rlS_wit2 rfl)
    (by quickRfl) (by decide +kernel)

theorem c6016 :
    ∀ s ∈ HS.recShard_6, ∀ r, s.2.1 ≤ r → r < s.2.2 → ∀ ε, HS.RecSpec s.1 r ε :=
  rec_body items6016 (by quickRfl)

end CertificateChecks.KernelKDenseP.Axis

end
