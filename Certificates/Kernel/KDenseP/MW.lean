module

public import Certificates.Kernel.KDenseP.AgreeB
public import Certificates.Kernel.KDense.Basic
public import Certificates.Kernel.KDenseP.Axis.Base
public import CFSG.Certificates.Kernel.KDense.Data.Checks
public import CFSG.Certificates.Kernel.KDenseP.MW.MonoEChk
public import CFSG.Certificates.Kernel.KDenseP.MW.C17421
import Certificates.Kernel.KDenseP.MonoTabL

public section

namespace CertificateChecks.KernelKDenseP.MW

open CFSG.KC CFSG.KC.KDense CFSG.KC.KDenseP CFSG.KC.KDenseP.MonThreeB
  CertificateChecks.KernelKDenseP.Axis CertificateChecks.KernelKDenseP.TwoPoint
  CFSG.Monster.AxisCount CFSG.AGLEmbedding.Norton.MON5_7 CFSG.YGroups.Y443 CFSG.YGroups.Y443Native
  CFSG.HardMathSupport.Dickson.I271

set_option maxRecDepth 100000

theorem monoTab_ok : monoTabOK CFSG.KD.KDF.F CFSG.KD.MWM.MT = true := by
  kd_monoTabL CFSG.KD.MWME t

theorem data_ok : dataOKP CFSG.KD.KDF.F CFSG.KD.MWM.MT CFSG.KD.KDF.KT CFSG.KD.KDF.TH
    CFSG.KD.KDF.OCT CFSG.KD.KDF.DU1 = true :=
  andB_true CFSG.KD.KDF.th_ok (andB_true CFSG.KD.KDF.oct_ok (andB_true CFSG.KD.KDF.du1_ok
    (andB_true CFSG.KD.KDF.keys_ok (andB_true CFSG.KD.KDF.keyPlanes_ok (andB_true CFSG.KD.KDF.fix_ok
      monoTab_ok)))))

open Lean in
macro "kd_mw% " pre:ident eqs:term:max nes:term:max : term => do
  let n := fun (s : String) => mkIdentFrom pre (pre.getId ++ Name.mkSimple s)
  `(tp3B_sound CertificateChecks.KernelKDenseP.MW.data_ok $eqs $nes (by quickRfl)
      (S := $(n "S")) (fun x hx => by interval_cases x <;> rfl) (CH := $(n "CH"))
      (nch := kd_count% $pre $(mkIdent `t)) (IT := $(n "IT")) (by kd_allE $pre $(mkIdent `t))
      (by quickRfl) (by quickRfl))

theorem c17421 : m13Check () = true := by
  unfold m13Check
  exact (kd_mw% CFSG.KD.MW.c17421 m13Pairs []).1

end CertificateChecks.KernelKDenseP.MW

end
