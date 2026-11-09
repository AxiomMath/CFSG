module

public import Certificates.Kernel.KDenseP.Axis.Mono
public import Certificates.Kernel.KDenseP.Axis.Tags
public import CFSG.Certificates.Kernel.KDenseP.Axis.C6015T0
public import CFSG.Certificates.Kernel.KDenseP.Axis.C6015T1
public import CFSG.Certificates.Kernel.KDenseP.Axis.C6015T2
public import CFSG.Certificates.Kernel.KDenseP.Axis.C6015T3

public section

namespace CertificateChecks.KernelKDenseP.Axis

open CFSG.KC CFSG.KC.KDense CFSG.KC.KDenseP CFSG.KC.KDenseP.Axis CFSG.Monster.AxisCount

set_option maxRecDepth 100000

theorem items6015 : ∀ x ∈ recTag HS.recShard_5, TagEq x :=
  eq_items data_okP (T := recTag HS.recShard_5) (recTag_fst _).symm CFSG.KD.AX.c6015.weq
    (WL := CFSG.KD.AX.c6015.WL) (fun _ => rfl)
    (S := rlS CFSG.KD.AX.c6015.rn CFSG.KD.AX.c6015.CH CFSG.KD.AX.c6015.PRf CFSG.KD.AX.c6015.S0 157)
    (CH := CFSG.KD.AX.c6015.CH) (IXf := CFSG.KD.AX.c6015.IXf) (CHI := CFSG.KD.AX.c6015.CHI)
    (fun _ => rfl) (nch := kd_count% CFSG.KD.AX.c6015 CH) (nIX := kd_count% CFSG.KD.AX.c6015 IX)
    (IT := CFSG.KD.AX.c6015.IT)
    (replay_sound (run := CFSG.KD.AX.c6015.rn) (chk := CFSG.KD.AX.c6015.ck)
      (fun S S' c h3 h4 => chunkOKN_loc S S' c h3 h4) (fun S c h => chunkOKN_prod S c h)
      (CH := CFSG.KD.AX.c6015.CH) (PR := CFSG.KD.AX.c6015.PRf) (GK := CFSG.KD.AX.c6015.GKf)
      (G := CFSG.KD.AX.c6015.Gf) (S0 := CFSG.KD.AX.c6015.S0) (w := 157)
      (ng := kd_count% CFSG.KD.AX.c6015 u) (nch := kd_count% CFSG.KD.AX.c6015 CH)
      (by kd_allE CFSG.KD.AX.c6015 u) (by quickRfl))
    (by decide +kernel) (by quickRfl)
    (by rw [rlS_lt (by norm_num)] <;> quickRfl) (by rw [rlS_lt (by norm_num)] <;> quickRfl)
    (by rw [rlS_lt (by norm_num), rlS_lt (by norm_num)] <;> rfl)
    (by quickRfl) (by decide +kernel)

theorem c6015 :
    ∀ s ∈ HS.recShard_5, ∀ r, s.2.1 ≤ r → r < s.2.2 → ∀ ε, HS.RecSpec s.1 r ε :=
  rec_body items6015 (by quickRfl)

end CertificateChecks.KernelKDenseP.Axis

end
