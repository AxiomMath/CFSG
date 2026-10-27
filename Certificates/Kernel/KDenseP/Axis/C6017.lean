module

public import Certificates.Kernel.KDenseP.Axis.Mono
public import Certificates.Kernel.KDenseP.Axis.Tags
public import CFSG.Certificates.Kernel.KDenseP.Axis.C6017All

public section

namespace CertificateChecks.KernelKDenseP.Axis

open CFSG.KC CFSG.KC.KDense CFSG.KC.KDenseP CFSG.KC.KDenseP.Axis CFSG.Monster.AxisCount

set_option maxRecDepth 100000

theorem items6017 : ∀ x ∈ recTag HS.recShard_7, TagEq x :=
  eq_items data_okP (T := recTag HS.recShard_7) (recTag_fst _).symm CFSG.KD.AX.c6017.weq
    (WL := CFSG.KD.AX.c6017.WL) (fun _ => rfl)
    (S := rlS CFSG.KD.AX.c6017.rn CFSG.KD.AX.c6017.CH CFSG.KD.AX.c6017.PRf CFSG.KD.AX.c6017.S0 3)
    (CH := CFSG.KD.AX.c6017.CH) (IXf := CFSG.KD.AX.c6017.IXf) (CHI := CFSG.KD.AX.c6017.CHI)
    (fun _ => rfl) (nch := kd_count% CFSG.KD.AX.c6017 CH) (nIX := kd_count% CFSG.KD.AX.c6017 IX)
    (IT := CFSG.KD.AX.c6017.IT) (kd_axC% CFSG.KD.AX.c6017) (by decide +kernel) (by quickRfl)
    (rlS_init (by norm_num) (by quickRfl)) (rlS_init (by norm_num) (by quickRfl)) (rlS_wit2 rfl)
    (by quickRfl) (by decide +kernel)

theorem neg_grp6017 : notB (grpL CFSG.KD.AX.c6017.rn CFSG.KD.AX.c6017.ck
    (fun k => CFSG.KD.AX.c6017.CH k + 2 ^ 80) CFSG.KD.AX.c6017.PRf CFSG.KD.AX.c6017.Gf
    CFSG.KD.AX.c6017.S0 3 0) = true := by
  decide +kernel

theorem c6017 :
    ∀ s ∈ HS.recShard_7, ∀ r, s.2.1 ≤ r → r < s.2.2 → ∀ ε, HS.RecSpec s.1 r ε :=
  rec_body items6017 (by quickRfl)

end CertificateChecks.KernelKDenseP.Axis

end
