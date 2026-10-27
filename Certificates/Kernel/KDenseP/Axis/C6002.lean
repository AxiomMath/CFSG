module

public import Certificates.Kernel.KDenseP.Axis.Mono
public import Certificates.Kernel.KDenseP.Axis.Tags
public import CFSG.Certificates.Kernel.KDenseP.Axis.C6002All

public section

namespace CertificateChecks.KernelKDenseP.Axis

open CFSG.KC CFSG.KC.KDense CFSG.KC.KDenseP CFSG.KC.KDenseP.Axis CFSG.Monster.AxisCount

set_option maxRecDepth 100000

theorem tag6002_fst : (babyTag 4 ++ babyTag 5).map Prod.fst = p6002 := by
  rw [List.map_append, babyTag_fst, babyTag_fst]
  rfl

theorem items6002 : ∀ x ∈ babyTag 4 ++ babyTag 5, TagEq x :=
  eq_items data_okP (T := babyTag 4 ++ babyTag 5) tag6002_fst.symm CFSG.KD.AX.c6002.weq
    (WL := CFSG.KD.AX.c6002.WL) (fun _ => rfl) (S := CFSG.KD.AX.c6002.S)
    (CH := CFSG.KD.AX.c6002.CH) (IXf := CFSG.KD.AX.c6002.IXf) (CHI := CFSG.KD.AX.c6002.CHI)
    (fun _ => rfl) (nch := kd_count% CFSG.KD.AX.c6002 t) (nIX := kd_count% CFSG.KD.AX.c6002 IX)
    (IT := CFSG.KD.AX.c6002.IT) (by kd_allE CFSG.KD.AX.c6002 t) (by decide +kernel) (by quickRfl)
    (by quickRfl) (by quickRfl) rfl (by quickRfl) (by decide +kernel)

theorem c6002 : BabyBody 4 ∧ BabyBody 5 :=
  have h := tagEq_append items6002
  ⟨baby_body h.1 (by quickRfl), baby_body h.2 (by quickRfl)⟩

end CertificateChecks.KernelKDenseP.Axis

end
