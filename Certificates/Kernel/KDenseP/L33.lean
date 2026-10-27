
module

public import Certificates.Kernel.KDenseP.AgreeB
public import Certificates.Kernel.KDense.Basic
public import Certificates.Kernel.KDenseP.Axis.Base
public import CFSG.Certificates.Kernel.KDense.Data.Checks
public import CFSG.Certificates.Kernel.KDenseP.L33.MonoEChk
public import CFSG.Certificates.Kernel.KDenseP.L33.C17632
public import Certificates.Certificate16959
public import CFSG.HardMathSupport.Dickson.BMRows.M13L33Base
import Certificates.Kernel.KDenseP.MonoTabL
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteen

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CertificateChecks.KernelKDenseP.L33

open CFSG.KC CFSG.KC.KDense CFSG.KC.KDenseP CFSG.KC.KDenseP.HeSeven CFSG.KC.KDenseP.L33
  CertificateChecks.KernelKDenseP.Axis CertificateChecks.KernelKDenseP.TwoPoint
  CFSG.Monster CFSG.Monster.AxisCount CFSG.AGLEmbedding.Norton.MON5_7
  CFSG.AGLEmbedding.Norton.MON11_13 CFSG.YGroups.Y443 CFSG.YGroups.Y443Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteen
  CFSG.HardMathSupport.Dickson.BMRows.M13L33

set_option maxRecDepth 100000

theorem monoTab_ok : monoTabOK CFSG.KD.KDF.F CFSG.KD.L33M.MT = true := by
  kd_monoTabL CFSG.KD.L33ME t

theorem data_ok : dataOKP CFSG.KD.KDF.F CFSG.KD.L33M.MT CFSG.KD.KDF.KT CFSG.KD.KDF.TH
    CFSG.KD.KDF.OCT CFSG.KD.KDF.DU1 = true :=
  andB_true CFSG.KD.KDF.th_ok (andB_true CFSG.KD.KDF.oct_ok (andB_true CFSG.KD.KDF.du1_ok
    (andB_true CFSG.KD.KDF.keys_ok (andB_true CFSG.KD.KDF.keyPlanes_ok (andB_true CFSG.KD.KDF.fix_ok
      monoTab_ok)))))

theorem agree_17632 : agreeAll e17632 = true :=
  (tp3B_sound data_ok e17632 [] (by quickRfl) (S := CFSG.KD.L33.c17632.S)
    (fun x hx => by interval_cases x <;> rfl) (CH := CFSG.KD.L33.c17632.CH)
    (nch := kd_count% CFSG.KD.L33.c17632 t) (IT := CFSG.KD.L33.c17632.IT)
    (by kd_allE CFSG.KD.L33.c17632 t) (by quickRfl) (by quickRfl)).1

theorem facts17632 :
    (∀ r ∈ l33Rels, evalRel l33Gen r = 1) ∧
      gw yW * gw thirteenX = gw thirteenX * gw yW ∧
      gw j1W * gw thirteenX = gw thirteenX * gw j1W ∧ gw j1W ≠ 1 := by
  have hp := agreeAll_sound agree_17632
  obtain ⟨hjj, -, -, hj, -, -, -, -, hj1, -⟩ := Certificates.certificate16959
  have hI : gw yIW = (gw yW)⁻¹ := by
    have := hp (yW ++ yIW, []) (List.mem_append_left _ List.mem_cons_self)
    rw [gw_append, gw_nil] at this
    exact eq_inv_of_mul_eq_one_left this
  have hy : gw yW * gw thirteenX = gw thirteenX * gw yW := by
    have := hp (thirteenX ++ yW, yW ++ thirteenX)
      (List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self))
    rwa [gw_append, gw_append] at this
  refine ⟨fun r hr => ?_, hy, hj, hj1⟩
  have := hp (relW r, []) (List.mem_append_right _ (List.mem_map_of_mem hr))
  rw [gw_nil] at this
  rw [← gw_relW hI (inv_eq_of_mul_eq_one_right hjj) r]
  exact this

end CertificateChecks.KernelKDenseP.L33

end
