module

public import Certificates.Kernel.KDenseP.Axis.Mono
public import Certificates.Kernel.KDenseP.Axis.Tags
public import CFSG.Certificates.Kernel.KDenseP.Axis.C6009All

public section

namespace CertificateChecks.KernelKDenseP.Axis

open CFSG.KC CFSG.KC.KDense CFSG.KC.KDenseP CFSG.KC.KDenseP.Axis CFSG.Monster.AxisCount
  CFSG.Monster.B.Short

set_option maxRecDepth 100000

theorem items6009 : ∀ x ∈ tag6009, TagEq x :=
  eq_items data_okP (T := tag6009) tag6009_fst.symm CFSG.KD.AX.c6009.weq
    (WL := CFSG.KD.AX.c6009.WL) (fun _ => rfl) (S := CFSG.KD.AX.c6009.S)
    (CH := CFSG.KD.AX.c6009.CH) (IXf := CFSG.KD.AX.c6009.IXf) (CHI := CFSG.KD.AX.c6009.CHI)
    (fun _ => rfl) (nch := kd_count% CFSG.KD.AX.c6009 t) (nIX := kd_count% CFSG.KD.AX.c6009 IX)
    (IT := CFSG.KD.AX.c6009.IT) (by kd_allE CFSG.KD.AX.c6009 t) (by decide +kernel) (by quickRfl)
    (by quickRfl) (by quickRfl) rfl (by quickRfl) (by decide +kernel)

theorem c6009 : ∀ j, j < 10 → ∀ b ∈ HS.babyBlocks[j]!,
    (∀ g ∈ b, g ≠ Native.Gen.tau) ∧ wordLin b aStar = aStar :=
  fix_body items6009 (by quickRfl)

end CertificateChecks.KernelKDenseP.Axis

end
