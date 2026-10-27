module

public import Certificates.Kernel.KDenseP.Axis.Mono
public import Certificates.Kernel.KDenseP.Axis.Tags
public import CFSG.Certificates.Kernel.KDenseP.Axis.C6013T0
public import CFSG.Certificates.Kernel.KDenseP.Axis.C6013T1
public import CFSG.Certificates.Kernel.KDenseP.Axis.C6013T2
public import CFSG.Certificates.Kernel.KDenseP.Axis.C6013T3

public section

namespace CertificateChecks.KernelKDenseP.Axis

open CFSG.KC CFSG.KC.KDense CFSG.KC.KDenseP CFSG.KC.KDenseP.Axis CFSG.Monster.AxisCount

set_option maxRecDepth 100000

theorem items6013 : ∀ x ∈ recTag HS.recShard_3, TagEq x :=
  eq_items data_okP (T := recTag HS.recShard_3) (recTag_fst _).symm CFSG.KD.AX.c6013.weq
    (WL := CFSG.KD.AX.c6013.WL) (fun _ => rfl)
    (S := rlS CFSG.KD.AX.c6013.rn CFSG.KD.AX.c6013.CH CFSG.KD.AX.c6013.PRf CFSG.KD.AX.c6013.S0 3)
    (CH := CFSG.KD.AX.c6013.CH) (IXf := CFSG.KD.AX.c6013.IXf) (CHI := CFSG.KD.AX.c6013.CHI)
    (fun _ => rfl) (nch := kd_count% CFSG.KD.AX.c6013 CH) (nIX := kd_count% CFSG.KD.AX.c6013 IX)
    (IT := CFSG.KD.AX.c6013.IT) (kd_axC% CFSG.KD.AX.c6013) (by decide +kernel) (by quickRfl)
    (rlS_init (by norm_num) (by quickRfl)) (rlS_init (by norm_num) (by quickRfl)) (rlS_wit2 rfl)
    (by quickRfl) (by decide +kernel)

theorem c6013 :
    ∀ s ∈ HS.recShard_3, ∀ r, s.2.1 ≤ r → r < s.2.2 → ∀ ε, HS.RecSpec s.1 r ε :=
  rec_body items6013 (by quickRfl)

end CertificateChecks.KernelKDenseP.Axis

end
