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
    (S := rlS CFSG.KD.AX.c6013.rn CFSG.KD.AX.c6013.CH CFSG.KD.AX.c6013.PRf CFSG.KD.AX.c6013.S0 202)
    (CH := CFSG.KD.AX.c6013.CH) (IXf := CFSG.KD.AX.c6013.IXf) (CHI := CFSG.KD.AX.c6013.CHI)
    (fun _ => rfl) (nch := kd_count% CFSG.KD.AX.c6013 CH) (nIX := kd_count% CFSG.KD.AX.c6013 IX)
    (IT := CFSG.KD.AX.c6013.IT)
    (replay_sound (run := CFSG.KD.AX.c6013.rn) (chk := CFSG.KD.AX.c6013.ck)
      (fun S S' c h3 h4 => chunkOKN_loc S S' c h3 h4) (fun S c h => chunkOKN_prod S c h)
      (CH := CFSG.KD.AX.c6013.CH) (PR := CFSG.KD.AX.c6013.PRf) (GK := CFSG.KD.AX.c6013.GKf)
      (G := CFSG.KD.AX.c6013.Gf) (S0 := CFSG.KD.AX.c6013.S0) (w := 202)
      (ng := kd_count% CFSG.KD.AX.c6013 u) (nch := kd_count% CFSG.KD.AX.c6013 CH)
      (by kd_allE CFSG.KD.AX.c6013 u) (by quickRfl))
    (by decide +kernel) (by quickRfl)
    (by rw [rlS_lt (by norm_num)] <;> quickRfl) (by rw [rlS_lt (by norm_num)] <;> quickRfl)
    (by rw [rlS_lt (by norm_num), rlS_lt (by norm_num)] <;> rfl)
    (by quickRfl) (by decide +kernel)

theorem c6013 :
    ∀ s ∈ HS.recShard_3, ∀ r, s.2.1 ≤ r → r < s.2.2 → ∀ ε, HS.RecSpec s.1 r ε :=
  rec_body items6013 (by quickRfl)

end CertificateChecks.KernelKDenseP.Axis

end
