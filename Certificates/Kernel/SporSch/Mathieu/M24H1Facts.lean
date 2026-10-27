module

public import Certificates.Kernel.SporSch.Mathieu.M24H1Checks
public import Certificates.Kernel.SporSch.Mathieu.M24Facts
public import Certificates.Kernel.LocalComp.M12Cent.Facts
public import CFSG.Certificates.Kernel.SporSch.TblSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.M24H1

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.Monster.B.Mathieu CFSG.ComponentClassification.M12Cover
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.M11 CFSG.KS.SporSch.MOC
open CFSG.KS.SporSch.CodesImg CFSG.KC.Child3
open CFSG.EvenSporadicStandard.HypOne CFSG.EvenSporadicStandard.HypOne.M24
open CertificateChecks.KernelSporSch.M24OC CertificateChecks.KernelLC.M12Cent

theorem one24 : imageList (1 : Equiv.Perm (Fin 24)) = (unpack 24 5 (pidn 24 5)).toList := by
  decide

theorem imgG1 : ∀ j < centGens1.length,
    imageList (centGens1.getD j 1) = (unpack 24 5 (M24C1.S j)).toList :=
  chainC1.2.2.2.1

theorem imgG2 : ∀ j < centGens2.length,
    imageList (centGens2.getD j 1) = (unpack 24 5 (M24C2.S j)).toList :=
  chainC2.2.2.2.1

theorem cnt1 : (cosetOrderTables m24CentQ1 1 4).length = M24H1R1.N :=
  (chainK_cosetCount (by decide) (by decide) chainC1 one24 cOne24 (by norm_num) (by norm_num)
    (by decide) M24H1X1.hc).trans (by decide)

theorem cnt2 : (cosetOrderTables m24CentQ2 1 4).length = M24H1R2.N :=
  (chainK_cosetCount (by decide) (by decide) chainC2 one24 cOne24 (by norm_num) (by norm_num)
    (by decide) M24H1X2.hc).trans (by decide)

theorem four1 : fourCheck 24 m24CentQ1 centGens1 fourWords1 4000 = true := by
  have hri := reps_img szOK' imgG1 kP1 one24 kW1
  obtain ⟨h1, h2⟩ := repsOK_of_img (cap := 4000) (X := cosetOrderTables m24CentQ1 1 4)
    (by decide : centGens1.length = 3) imgG1 (fun j hj => allN_spec kP1 j hj)
    (fun j hj => and_of_bAnd (allN_spec kC1 j hj))
    (by decide : (fourWords1.map (evalCodes centGens1)).length = M24H1R1.CS.length)
    (fun i hi => hri i (lt_of_lt_of_eq hi (by decide))) kOff1 kPos1 cnt1
    (fun j hj => allN_spec kR1 j hj)
  have h3 := ord_all szOK' (reps := fourWords1.map (evalCodes centGens1)) (e := 4) (by decide)
    (fun i hi => hri i hi) kO1 (by norm_num)
  unfold fourCheck listTables
  rw [h1, h2, h3]
  decide

theorem four2 : fourCheck 24 m24CentQ2 centGens2 fourWords2 4000 = true := by
  have hri := reps_img szOK' imgG2 kP2 one24 kW2
  obtain ⟨h1, h2⟩ := repsOK_of_img (cap := 4000) (X := cosetOrderTables m24CentQ2 1 4)
    (by decide : centGens2.length = 2) imgG2 (fun j hj => allN_spec kP2 j hj)
    (fun j hj => and_of_bAnd (allN_spec kC2 j hj))
    (by decide : (fourWords2.map (evalCodes centGens2)).length = M24H1R2.CS.length)
    (fun i hi => hri i (lt_of_lt_of_eq hi (by decide))) kOff2 kPos2 cnt2
    (fun j hj => allN_spec kR2 j hj)
  have h3 := ord_all szOK' (reps := fourWords2.map (evalCodes centGens2)) (e := 4) (by decide)
    (fun i hi => hri i hi) kO2 (by norm_num)
  unfold fourCheck listTables
  rw [h1, h2, h3]
  decide

theorem fourData_eq : fourData = true := by
  unfold fourData
  rw [four1, four2]
  rfl

theorem img_e {wd : List ℤ} (hw : abOK wd = true) : imageList (evalCodes gens wd) =
    (unpack 24 5 (abWordK 24 5 (mask 5) (pidn 24 5) (M24Q.S 0) (M24Q.SI 0) (M24Q.S 1) (M24Q.SI 1)
      wd)).toList :=
  abWordK_rep szOK' imgA imgB pA pB hw

theorem ord_of {g : Equiv.Perm (Fin 24)} {P : Nat} (hg : imageList g = (unpack 24 5 P).toList)
    (h : inv2K P = true) : ordTest 24 2 (toTable g) = true := by
  obtain ⟨hc, ho⟩ := and_of_bAnd h
  exact ordTest_of_ordIs szOK' hg hc (by norm_num) ho

theorem compT_toTable (g h : Equiv.Perm (Fin 24)) :
    compT 24 (toTable g) (toTable h) = toTable (g * h) :=
  CFSG.KS.Tbl.compT_eq_toTable (by norm_num) (rep_toTable (by norm_num) g)
    (rep_toTable (by norm_num) h)

theorem e8Data_eq : e8Data = true := by
  have i1 : imageList e1 = (unpack 24 5 E1P).toList := img_e kA1
  have i2 : imageList e2 = (unpack 24 5 E2P).toList := img_e kA2
  have i3 : imageList e3 = (unpack 24 5 E3P).toList := img_e kA3
  have i12 := mulK_rep szOK' i1 i2
  have i13 := mulK_rep szOK' i1 i3
  have i23 := mulK_rep szOK' i2 i3
  have i123 := mulK_rep szOK' i12 i3
  unfold e8Data e8Check
  simp only [compT_toTable]
  rw [commT_of_commK i1 i2 kC12, commT_of_commK i1 i3 kC13, commT_of_commK i2 i3 kC23,
    ord_of i1 kE1, ord_of i2 kE2, ord_of i3 kE3, ord_of i12 kE12, ord_of i13 kE13,
    ord_of i23 kE23, ord_of i123 kE123]
  rfl

theorem facts : (fourData = true) ∧ (e8Data = true) := ⟨fourData_eq, e8Data_eq⟩

end CertificateChecks.KernelSporSch.M24H1

end
