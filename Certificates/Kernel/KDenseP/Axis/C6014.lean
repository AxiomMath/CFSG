module

public import Certificates.Kernel.KDenseP.Axis.Mono
public import Certificates.Kernel.KDenseP.Axis.Tags
public import CFSG.Certificates.Kernel.KDenseP.Axis.C6014T0
public import CFSG.Certificates.Kernel.KDenseP.Axis.C6014T1
public import CFSG.Certificates.Kernel.KDenseP.Axis.C6014T2
public import CFSG.Certificates.Kernel.KDenseP.Axis.C6014T3

public section

namespace CertificateChecks.KernelKDenseP.Axis

open CFSG.KC CFSG.KC.KDense CFSG.KC.KDenseP CFSG.KC.KDenseP.Axis CFSG.Monster.AxisCount

set_option maxRecDepth 100000

theorem items6014 : ∀ x ∈ recTag HS.recShard_4, TagEq x :=
  eq_items data_okP (T := recTag HS.recShard_4) (recTag_fst _).symm CFSG.KD.AX.c6014.weq
    (WL := CFSG.KD.AX.c6014.WL) (fun _ => rfl)
    (S := rlS CFSG.KD.AX.c6014.rn CFSG.KD.AX.c6014.CH CFSG.KD.AX.c6014.PRf CFSG.KD.AX.c6014.S0 3)
    (CH := CFSG.KD.AX.c6014.CH) (IXf := CFSG.KD.AX.c6014.IXf) (CHI := CFSG.KD.AX.c6014.CHI)
    (fun _ => rfl) (nch := kd_count% CFSG.KD.AX.c6014 CH) (nIX := kd_count% CFSG.KD.AX.c6014 IX)
    (IT := CFSG.KD.AX.c6014.IT) (kd_axC% CFSG.KD.AX.c6014) (by decide +kernel) (by quickRfl)
    (rlS_init (by norm_num) (by quickRfl)) (rlS_init (by norm_num) (by quickRfl)) (rlS_wit2 rfl)
    (by quickRfl) (by decide +kernel)

theorem c6014 :
    ∀ s ∈ HS.recShard_4, ∀ r, s.2.1 ≤ r → r < s.2.2 → ∀ ε, HS.RecSpec s.1 r ε :=
  rec_body items6014 (by quickRfl)

end CertificateChecks.KernelKDenseP.Axis

end
