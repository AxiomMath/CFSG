module

public import Certificates.Kernel.KDenseP.Axis.Mono
public import Certificates.Kernel.KDenseP.Axis.Tags
public import CFSG.Certificates.Kernel.KDenseP.Axis.C6004All

public section

namespace CertificateChecks.KernelKDenseP.Axis

open CFSG.KC CFSG.KC.KDense CFSG.KC.KDenseP CFSG.KC.KDenseP.Axis CFSG.Monster.AxisCount

set_option maxRecDepth 100000

theorem tag6004_fst :
    (babyTag 0 ++ babyTag 1 ++ babyTag 2 ++ babyTag 7 ++ babyTag 9).map Prod.fst = p6004 := by
  rw [List.map_append, List.map_append, List.map_append, List.map_append, babyTag_fst,
    babyTag_fst, babyTag_fst, babyTag_fst, babyTag_fst]
  rfl

theorem items6004 :
    ∀ x ∈ babyTag 0 ++ babyTag 1 ++ babyTag 2 ++ babyTag 7 ++ babyTag 9, TagEq x :=
  eq_items data_okP (T := babyTag 0 ++ babyTag 1 ++ babyTag 2 ++ babyTag 7 ++ babyTag 9)
    tag6004_fst.symm CFSG.KD.AX.c6004.weq
    (WL := CFSG.KD.AX.c6004.WL) (fun _ => rfl) (S := CFSG.KD.AX.c6004.S)
    (CH := CFSG.KD.AX.c6004.CH) (IXf := CFSG.KD.AX.c6004.IXf) (CHI := CFSG.KD.AX.c6004.CHI)
    (fun _ => rfl) (nch := kd_count% CFSG.KD.AX.c6004 t) (nIX := kd_count% CFSG.KD.AX.c6004 IX)
    (IT := CFSG.KD.AX.c6004.IT) (by kd_allE CFSG.KD.AX.c6004 t) (by decide +kernel) (by quickRfl)
    (by quickRfl) (by quickRfl) rfl (by quickRfl) (by decide +kernel)

theorem c6004 :
    BabyBody 0 ∧ BabyBody 1 ∧ BabyBody 2 ∧ BabyBody 7 ∧ BabyBody 9 :=
  have h4 := tagEq_append items6004
  have h3 := tagEq_append h4.1
  have h2 := tagEq_append h3.1
  have h1 := tagEq_append h2.1
  ⟨baby_body h1.1 (by quickRfl), baby_body h1.2 (by quickRfl), baby_body h2.2 (by quickRfl),
    baby_body h3.2 (by quickRfl), baby_body h4.2 (by quickRfl)⟩

end CertificateChecks.KernelKDenseP.Axis

end
