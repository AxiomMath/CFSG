module

public import Certificates.Kernel.KDenseP.Axis.Mono
public import Certificates.Kernel.KDenseP.Axis.Tags
public import CFSG.Certificates.Kernel.KDenseP.Axis.C6003All

public section

namespace CertificateChecks.KernelKDenseP.Axis

open CFSG.KC CFSG.KC.KDense CFSG.KC.KDenseP CFSG.KC.KDenseP.Axis CFSG.Monster.AxisCount

set_option maxRecDepth 100000

theorem tag6003_fst : (babyTag 3 ++ babyTag 6 ++ babyTag 8).map Prod.fst = p6003 := by
  rw [List.map_append, List.map_append, babyTag_fst, babyTag_fst, babyTag_fst]
  rfl

theorem items6003 :
    ∀ x ∈ babyTag 3 ++ babyTag 6 ++ babyTag 8, TagEq x :=
  eq_items data_okP (T := babyTag 3 ++ babyTag 6 ++ babyTag 8) tag6003_fst.symm
    CFSG.KD.AX.c6003.weq
    (WL := CFSG.KD.AX.c6003.WL) (fun _ => rfl) (S := CFSG.KD.AX.c6003.S)
    (CH := CFSG.KD.AX.c6003.CH) (IXf := CFSG.KD.AX.c6003.IXf) (CHI := CFSG.KD.AX.c6003.CHI)
    (fun _ => rfl) (nch := kd_count% CFSG.KD.AX.c6003 t) (nIX := kd_count% CFSG.KD.AX.c6003 IX)
    (IT := CFSG.KD.AX.c6003.IT) (by kd_allE CFSG.KD.AX.c6003 t) (by decide +kernel) (by quickRfl)
    (by quickRfl) (by quickRfl) rfl (by quickRfl) (by decide +kernel)

theorem c6003 : BabyBody 3 ∧ BabyBody 6 ∧ BabyBody 8 :=
  have h := tagEq_append items6003
  have h' := tagEq_append h.1
  ⟨baby_body h'.1 (by quickRfl), baby_body h'.2 (by quickRfl), baby_body h.2 (by quickRfl)⟩

end CertificateChecks.KernelKDenseP.Axis

end
