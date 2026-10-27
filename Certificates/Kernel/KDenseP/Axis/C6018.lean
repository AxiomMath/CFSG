module

public import Certificates.Kernel.KDenseP.Axis.Mono
public import Certificates.Kernel.KDenseP.Axis.Tags
public import CFSG.Certificates.Kernel.KDenseP.Axis.C6018All
public import CFSG.Certificates.Kernel.KDenseP.Axis.C6018vAll

public section

namespace CertificateChecks.KernelKDenseP.Axis

open CFSG.KC CFSG.KC.KDense CFSG.KC.KDenseP CFSG.KC.KDenseP.Axis CFSG.Monster.AxisCount
  CFSG.Monster.B.Short

set_option maxRecDepth 100000

theorem items6018 : ∀ x ∈ tag6018, TagEq x :=
  eq_items data_okP (T := tag6018) tag6018_fst.symm CFSG.KD.AX.c6018.weq
    (WL := CFSG.KD.AX.c6018.WL) (fun _ => rfl)
    (S := rlS CFSG.KD.AX.c6018.rn CFSG.KD.AX.c6018.CH CFSG.KD.AX.c6018.PRf CFSG.KD.AX.c6018.S0 3)
    (CH := CFSG.KD.AX.c6018.CH) (IXf := CFSG.KD.AX.c6018.IXf) (CHI := CFSG.KD.AX.c6018.CHI)
    (fun _ => rfl) (nch := kd_count% CFSG.KD.AX.c6018 CH) (nIX := kd_count% CFSG.KD.AX.c6018 IX)
    (IT := CFSG.KD.AX.c6018.IT) (kd_axC% CFSG.KD.AX.c6018) (by decide +kernel) (by quickRfl)
    (rlS_init (by norm_num) (by quickRfl)) (rlS_init (by norm_num) (by quickRfl)) (rlS_wit2 rfl)
    (by quickRfl) (by decide +kernel)

theorem vals6018 (t : ℕ) (ht : t < tag6018v.length) :
    DyRes 7 (trA2 (wordLin tag6018v[t].1.1 (wv tag6018v[t].2)))
        (trOf 7 (endSt CFSG.KD.AX.c6018v.S CFSG.KD.AX.c6018v.CHI CFSG.KD.AX.c6018v.IT t)) ∧
      DyRes 7 (Baby.xStarCoord (wordLin tag6018v[t].1.1 (wv tag6018v[t].2)))
        (xOf 7 (endSt CFSG.KD.AX.c6018v.S CFSG.KD.AX.c6018v.CHI CFSG.KD.AX.c6018v.IT t)) :=
  val_items data_okP (T := tag6018v) tag6018v_fst.symm CFSG.KD.AX.c6018v.weq
    (WL := CFSG.KD.AX.c6018v.WL) (fun _ => rfl) (S := CFSG.KD.AX.c6018v.S)
    (CH := CFSG.KD.AX.c6018v.CH) (IXf := CFSG.KD.AX.c6018v.IXf) (CHI := CFSG.KD.AX.c6018v.CHI)
    (fun _ => rfl) (nch := kd_count% CFSG.KD.AX.c6018v t)
    (nIX := kd_count% CFSG.KD.AX.c6018v IX) (IT := CFSG.KD.AX.c6018v.IT)
    (by kd_allE CFSG.KD.AX.c6018v t) (by decide +kernel) (by quickRfl) (by quickRfl) (by quickRfl)
    rfl (by quickRfl) (by decide +kernel) (nV := kd_count% CFSG.KD.AX.c6018v v)
    (by decide +kernel) (by kd_allE CFSG.KD.AX.c6018v v) t ht

theorem c6018 :
    (∀ (i : Fin 12), ∀ k, k < 2 → wordLin (HS.uW i k) (HS.vv i) = HS.vv i) ∧
    (Function.Injective fun i : Fin 12 => trA2 (HS.vv i)) ∧
    (∀ (i : Fin 12), ∀ k, k < 2 → HS.bbU i k < 10 ∧
      wordLin (HS.uW i k) (wordLin (Cert.gammaW i) aStarMinus) =
        wordLin (HS.hppU i k ++ Cert.gammaW i) (wordLin (HS.babyW (HS.bbU i k)) aStarMinus)) ∧
    (∀ (i : Fin 12), ∀ k, k < 2 → wordLin (HS.hppU i k) aStar = aStar) :=
  have h := stab_body items6018 (by quickRfl)
  ⟨h.1, trace_inj (R := fun t => trOf 7 (endSt CFSG.KD.AX.c6018v.S CFSG.KD.AX.c6018v.CHI
      CFSG.KD.AX.c6018v.IT t))
    (X := fun t => xOf 7 (endSt CFSG.KD.AX.c6018v.S CFSG.KD.AX.c6018v.CHI CFSG.KD.AX.c6018v.IT t))
    vals6018 (fun _ => trOf_lt _ _ (by norm_num)) (by decide +kernel), h.2.1, h.2.2⟩

end CertificateChecks.KernelKDenseP.Axis

end
