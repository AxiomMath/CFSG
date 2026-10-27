module

public import Certificates.Kernel.SporSch.Mathieu.M11H1Checks
public import Certificates.Kernel.SporSch.Mathieu.M11Facts
public import Certificates.Kernel.LocalComp.M12Cent.Facts

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.M11H1

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.Monster.B.Mathieu CFSG.ComponentClassification.M12Cover
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.M11 CFSG.KS.SporSch.MOC
open CFSG.KS.SporSch.CodesImg CFSG.KC.Child3
open CFSG.EvenSporadicStandard.HypOne CFSG.EvenSporadicStandard.M11Std
open CertificateChecks.KernelSporSch.M11OC CertificateChecks.KernelLC.M12Cent

theorem imgG : ∀ j < centGens1.length,
    imageList (centGens1.getD j 1) = (unpack 11 4 (M11C1.S j)).toList :=
  chainC1.2.2.2.1

theorem cnt : (cosetOrderTables m11CentQ1 1 4).length = M11H1R.N :=
  (chainK_cosetCount (by decide) (by decide) chainC1 imgOne cOne (by norm_num) (by norm_num)
    (by decide) M11H1X.hc).trans (by decide)

theorem fourData_eq : fourData = true := by
  have hri := reps_img szOK' imgG kP imgOne kW
  obtain ⟨h1, h2⟩ := repsOK_of_img (cap := 400) (X := cosetOrderTables m11CentQ1 1 4)
    (by decide : centGens1.length = 4) imgG (fun j hj => allN_spec kP j hj)
    (fun j hj => and_of_bAnd (allN_spec kC j hj))
    (by decide : (fourWords1.map (evalCodes centGens1)).length = M11H1R.CS.length)
    (fun i hi => hri i (lt_of_lt_of_eq hi (by decide))) kOff kPos cnt
    (fun j hj => allN_spec kR j hj)
  have h3 := ord_all szOK' (reps := fourWords1.map (evalCodes centGens1)) (e := 4) (by decide)
    (fun i hi => hri i hi) kO (by norm_num)
  unfold fourData fourCheck listTables
  rw [h1, h2, h3]
  decide

end CertificateChecks.KernelSporSch.M11H1

end
