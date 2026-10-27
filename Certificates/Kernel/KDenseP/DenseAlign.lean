module

public import Certificates.Kernel.KDenseP.AgreeB
public import Certificates.Kernel.KDense.Basic
public import Certificates.Kernel.KDenseP.Axis.Base
public import CFSG.Certificates.Kernel.KDense.Data.Checks
public import CFSG.Certificates.Kernel.KDenseP.DenseAlign.MonoEChk
public import CFSG.Certificates.Kernel.KDenseP.DenseAlign.C17594
import Certificates.Kernel.KDenseP.MonoTabL
public import CFSG.YGroups.Y443.Native.EdgeNoncomm

public section

namespace CertificateChecks.KernelKDenseP.DenseAlign

open CFSG.KC CFSG.KC.KDense CFSG.KC.KDenseP CFSG.KC.KDenseP.HeSeven CFSG.KC.KDenseP.DenseAlign
  CertificateChecks.KernelKDenseP.Axis CertificateChecks.KernelKDenseP.TwoPoint
  CFSG.Monster CFSG.Monster.AxisCount CFSG.AGLEmbedding.Norton.MON5_7 CFSG.YGroups.Y443
  CFSG.YGroups.Y443Native CFSG.HardMathSupport.Dickson.I271.TabMThreeA

set_option maxRecDepth 100000

theorem monoTab_ok : monoTabOK CFSG.KD.KDF.F CFSG.KD.DA7M.MT = true := by
  kd_monoTabL CFSG.KD.DA7ME t

theorem data_ok : dataOKP CFSG.KD.KDF.F CFSG.KD.DA7M.MT CFSG.KD.KDF.KT CFSG.KD.KDF.TH
    CFSG.KD.KDF.OCT CFSG.KD.KDF.DU1 = true :=
  andB_true CFSG.KD.KDF.th_ok (andB_true CFSG.KD.KDF.oct_ok (andB_true CFSG.KD.KDF.du1_ok
    (andB_true CFSG.KD.KDF.keys_ok (andB_true CFSG.KD.KDF.keyPlanes_ok (andB_true CFSG.KD.KDF.fix_ok
      monoTab_ok)))))

theorem agreeAll_17594 : agreeAll e17594 = true :=
  (tp3B_sound data_ok e17594 [] (by quickRfl) (S := CFSG.KD.DA7.c17594.S)
    (fun x hx => by interval_cases x <;> rfl) (CH := CFSG.KD.DA7.c17594.CH)
    (nch := kd_count% CFSG.KD.DA7.c17594 t) (IT := CFSG.KD.DA7.c17594.IT)
    (by kd_allE CFSG.KD.DA7.c17594 t) (by quickRfl) (by quickRfl)).1

theorem denseAlign_abw : denseAlignCheck (aV ()) = true ∧ denseAlignCheck (bV ()) = true ∧
    denseAlignCheck (wV ()) = true := by
  have h := agreeAll_17594
  unfold agreeAll e17594 at h
  simp only [List.all_cons, List.all_nil, Bool.and_true] at h
  unfold agree Native.evalWord at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, ha⟩, hb⟩, hw⟩ := h
  unfold denseAlignCheck eqWords
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨h1, h2⟩, ha⟩, ⟨⟨h1, h2⟩, hb⟩, ⟨⟨h1, h2⟩, hw⟩⟩

end CertificateChecks.KernelKDenseP.DenseAlign

end
