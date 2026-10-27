module

public import Certificates.Kernel.KDenseP.AgreeB
public import Certificates.Kernel.KDenseP.SepAt
public import Certificates.Kernel.KDense.Basic
public import Certificates.Kernel.KDenseP.Axis.Base
public import CFSG.Certificates.Kernel.KDense.Data.Checks
public import CFSG.Certificates.Kernel.KDenseP.CM12.MonoEChk
public import CFSG.Certificates.Kernel.KDenseP.CM12.C17702
import Certificates.Kernel.KDenseP.MonoTabL

public section

namespace CertificateChecks.KernelKDenseP.CM12

open CFSG.KC CFSG.KC.KDense CFSG.KC.KDenseP CFSG.KC.KDenseP.MonThreeB CFSG.KC.KDenseP.CM12
  CFSG.KC.KDenseP.TwoPoint
  CertificateChecks.KernelKDenseP.Axis CertificateChecks.KernelKDenseP.TwoPoint
  CFSG.Monster.AxisCount CFSG.AGLEmbedding.Norton.MON5_7 CFSG.YGroups.Y443 CFSG.YGroups.Y443Native
  CFSG.HardMathSupport.Dickson.BMRows.M11

set_option maxRecDepth 100000

theorem monoTab_ok : monoTabOK CFSG.KD.KDF.F CFSG.KD.CM12M.MT = true := by
  kd_monoTabL CFSG.KD.CM12ME t

theorem data_ok : dataOKP CFSG.KD.KDF.F CFSG.KD.CM12M.MT CFSG.KD.KDF.KT CFSG.KD.KDF.TH
    CFSG.KD.KDF.OCT CFSG.KD.KDF.DU1 = true :=
  andB_true CFSG.KD.KDF.th_ok (andB_true CFSG.KD.KDF.oct_ok (andB_true CFSG.KD.KDF.du1_ok
    (andB_true CFSG.KD.KDF.keys_ok (andB_true CFSG.KD.KDF.keyPlanes_ok (andB_true CFSG.KD.KDF.fix_ok
      monoTab_ok)))))

open Lean in
macro "kd_cm12% " pre:ident eqs:term:max nes:term:max : term => do
  let n := fun (s : String) => mkIdentFrom pre (pre.getId ++ Name.mkSimple s)
  `(tp3B_sound CertificateChecks.KernelKDenseP.CM12.data_ok $eqs $nes (by quickRfl)
      (S := $(n "S")) (fun x hx => by interval_cases x <;> rfl) (CH := $(n "CH"))
      (nch := kd_count% $pre $(mkIdent `t)) (IT := $(n "IT")) (by kd_allE $pre $(mkIdent `t))
      (by quickRfl) (by quickRfl))

theorem c17702 : m12Check () = true := by
  obtain ⟨he, hn⟩ := kd_cm12% CFSG.KD.CM12.c17702 m12Pairs n17702
  unfold m12Check
  simp only [he, moveCheck_of_sepL (hn (m12aW, []) (by simp [n17702])), Bool.and_self]

end CertificateChecks.KernelKDenseP.CM12

end
