module

public import Certificates.Kernel.SporSch.Mathieu.M23H1Checks
public import Certificates.Kernel.SporSch.Mathieu.M23Facts
public import Certificates.Kernel.LocalComp.M12Cent.Facts
public import CFSG.Certificates.Kernel.SporSch.TblSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.M23H1

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.Monster.B.Mathieu CFSG.ComponentClassification.M12Cover
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.M11 CFSG.KS.SporSch.MOC
open CFSG.KS.SporSch.CodesImg CFSG.KC.Child3
open CFSG.EvenSporadicStandard.HypOne CFSG.EvenSporadicStandard.HypOne.M23
open CertificateChecks.KernelSporSch.M23OC CertificateChecks.KernelLC.M12Cent

theorem one23 : imageList (1 : Equiv.Perm (Fin 23)) = (unpack 23 5 (pidn 23 5)).toList := by
  decide

theorem imgG : ∀ j < centGens1.length,
    imageList (centGens1.getD j 1) = (unpack 23 5 (M23C1.S j)).toList :=
  chainC1.2.2.2.1

theorem cnt : (cosetOrderTables m23CentQ1 1 4).length = M23H1R.N :=
  (chainK_cosetCount (by decide) (by decide) chainC1 one23 cOne23 (by norm_num) (by norm_num)
    (by decide) M23H1X.hc).trans (by decide)

theorem fourData_eq : fourData = true := by
  have hri := reps_img szOK' imgG kP one23 kW
  obtain ⟨h1, h2⟩ := repsOK_of_img (cap := 4000) (X := cosetOrderTables m23CentQ1 1 4)
    (by decide : centGens1.length = 4) imgG (fun j hj => allN_spec kP j hj)
    (fun j hj => and_of_bAnd (allN_spec kC j hj))
    (by decide : (fourWords1.map (evalCodes centGens1)).length = M23H1R.CS.length)
    (fun i hi => hri i (lt_of_lt_of_eq hi (by decide))) kOff kPos cnt
    (fun j hj => allN_spec kR j hj)
  have h3 := ord_all szOK' (reps := fourWords1.map (evalCodes centGens1)) (e := 4) (by decide)
    (fun i hi => hri i hi) kO (by norm_num)
  unfold fourData fourCheck listTables
  rw [h1, h2, h3]
  decide

theorem img_e {wd : List ℤ} (hw : abOK wd = true) : imageList (evalCodes gens wd) =
    (unpack 23 5 (abWordK 23 5 (mask 5) (pidn 23 5) (M23Q.S 0) (M23Q.SI 0) (M23Q.S 1) (M23Q.SI 1)
      wd)).toList :=
  abWordK_rep szOK' imgA imgB pA pB hw

theorem ord_of {g : Equiv.Perm (Fin 23)} {P : Nat} (hg : imageList g = (unpack 23 5 P).toList)
    (h : inv2K P = true) : ordTest 23 2 (toTable g) = true := by
  obtain ⟨hc, ho⟩ := and_of_bAnd h
  exact ordTest_of_ordIs szOK' hg hc (by norm_num) ho

theorem compT_toTable (g h : Equiv.Perm (Fin 23)) :
    compT 23 (toTable g) (toTable h) = toTable (g * h) :=
  CFSG.KS.Tbl.compT_eq_toTable (by norm_num) (rep_toTable (by norm_num) g)
    (rep_toTable (by norm_num) h)

theorem e8Data_eq : e8Data = true := by
  have i1 : imageList e1 = (unpack 23 5 E1P).toList := img_e kA1
  have i2 : imageList e2 = (unpack 23 5 E2P).toList := img_e kA2
  have i3 : imageList e3 = (unpack 23 5 E3P).toList := img_e kA3
  have i12 := mulK_rep szOK' i1 i2
  have i13 := mulK_rep szOK' i1 i3
  have i23 := mulK_rep szOK' i2 i3
  have i123 := mulK_rep szOK' i12 i3
  unfold e8Data e8Check
  simp only [compT_toTable]
  rw [commT_of_commK i1 i2 kC12, commT_of_commK i1 i3 kC13, commT_of_commK i2 i3 kC23,
    ord_of i1 kO1, ord_of i2 kO2, ord_of i3 kO3, ord_of i12 kO12, ord_of i13 kO13,
    ord_of i23 kO23, ord_of i123 kO123]
  rfl

theorem facts : (fourData = true) ∧ (e8Data = true) := ⟨fourData_eq, e8Data_eq⟩

end CertificateChecks.KernelSporSch.M23H1

end
