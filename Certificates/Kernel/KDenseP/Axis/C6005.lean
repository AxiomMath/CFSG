module

public import Certificates.Kernel.KDenseP.Axis.Mono
public import Certificates.Kernel.KDenseP.Axis.Tags
public import CFSG.Certificates.Kernel.KDenseP.Axis.C6005vAll

public section

namespace CertificateChecks.KernelKDenseP.Axis

open CFSG.KC CFSG.KC.KDense CFSG.KC.KDenseP CFSG.KC.KDenseP.Axis CFSG.Monster.AxisCount

set_option maxRecDepth 100000

theorem vals6005 (t : ℕ) (ht : t < tag6005v.length) :
    DyRes 7 (trA2 (wordLin tag6005v[t].1.1 (wv tag6005v[t].2)))
        (trOf 7 (endSt CFSG.KD.AX.c6005v.S CFSG.KD.AX.c6005v.CHI CFSG.KD.AX.c6005v.IT t)) ∧
      DyRes 7 (Baby.xStarCoord (wordLin tag6005v[t].1.1 (wv tag6005v[t].2)))
        (xOf 7 (endSt CFSG.KD.AX.c6005v.S CFSG.KD.AX.c6005v.CHI CFSG.KD.AX.c6005v.IT t)) :=
  val_items data_okP (T := tag6005v) tag6005v_fst.symm CFSG.KD.AX.c6005v.weq
    (WL := CFSG.KD.AX.c6005v.WL) (fun _ => rfl) (S := CFSG.KD.AX.c6005v.S)
    (CH := CFSG.KD.AX.c6005v.CH) (IXf := CFSG.KD.AX.c6005v.IXf) (CHI := CFSG.KD.AX.c6005v.CHI)
    (fun _ => rfl) (nch := kd_count% CFSG.KD.AX.c6005v t)
    (nIX := kd_count% CFSG.KD.AX.c6005v IX) (IT := CFSG.KD.AX.c6005v.IT)
    (by kd_allE CFSG.KD.AX.c6005v t) (by decide +kernel) (by quickRfl) (by quickRfl) (by quickRfl)
    rfl (by quickRfl) (by decide +kernel) (nV := kd_count% CFSG.KD.AX.c6005v v)
    (by decide +kernel) (by kd_allE CFSG.KD.AX.c6005v v) t ht

theorem c6005 :
    Function.Injective fun j : Fin 10 => (Baby.xStarCoord (Baby.vv j), trA2 (Baby.vv j)) :=
  baby_inj (R := fun t => trOf 7 (endSt CFSG.KD.AX.c6005v.S CFSG.KD.AX.c6005v.CHI
      CFSG.KD.AX.c6005v.IT t))
    (X := fun t => xOf 7 (endSt CFSG.KD.AX.c6005v.S CFSG.KD.AX.c6005v.CHI CFSG.KD.AX.c6005v.IT t))
    vals6005 (fun _ => trOf_lt _ _ (by norm_num)) (fun _ => xOf_lt _ _ (by norm_num))
    (by decide +kernel)

end CertificateChecks.KernelKDenseP.Axis

end
