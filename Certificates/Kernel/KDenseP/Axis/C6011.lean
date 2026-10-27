module

public import Certificates.Kernel.KDenseP.Axis.Mono
public import Certificates.Kernel.KDenseP.Axis.Tags
public import CFSG.Certificates.Kernel.KDenseP.Axis.C6011T0
public import CFSG.Certificates.Kernel.KDenseP.Axis.C6011T1
public import CFSG.Certificates.Kernel.KDenseP.Axis.C6011T2

public section

namespace CertificateChecks.KernelKDenseP.Axis

open CFSG.KC CFSG.KC.KDense CFSG.KC.KDenseP CFSG.KC.KDenseP.Axis CFSG.Monster.AxisCount

set_option maxRecDepth 100000

theorem items6011 : ∀ x ∈ recTag HS.recShard_1, TagEq x :=
  eq_items data_okP (T := recTag HS.recShard_1) (recTag_fst _).symm CFSG.KD.AX.c6011.weq
    (WL := CFSG.KD.AX.c6011.WL) (fun _ => rfl)
    (S := rlS CFSG.KD.AX.c6011.rn CFSG.KD.AX.c6011.CH CFSG.KD.AX.c6011.PRf CFSG.KD.AX.c6011.S0 3)
    (CH := CFSG.KD.AX.c6011.CH) (IXf := CFSG.KD.AX.c6011.IXf) (CHI := CFSG.KD.AX.c6011.CHI)
    (fun _ => rfl) (nch := kd_count% CFSG.KD.AX.c6011 CH) (nIX := kd_count% CFSG.KD.AX.c6011 IX)
    (IT := CFSG.KD.AX.c6011.IT) (kd_axC% CFSG.KD.AX.c6011) (by decide +kernel) (by quickRfl)
    (rlS_init (by norm_num) (by quickRfl)) (rlS_init (by norm_num) (by quickRfl)) (rlS_wit2 rfl)
    (by quickRfl) (by decide +kernel)

theorem c6011 :
    ∀ s ∈ HS.recShard_1, ∀ r, s.2.1 ≤ r → r < s.2.2 → ∀ ε, HS.RecSpec s.1 r ε :=
  rec_body items6011 (by quickRfl)

end CertificateChecks.KernelKDenseP.Axis

end
