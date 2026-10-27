module

public import Certificates.Kernel.SporSch.Mathieu.M22H1Facts
public import CFSG.Certificates.Kernel.SporSch.TblSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.M22H1

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.Monster.B.Mathieu CFSG.ComponentClassification.M12Cover CFSG.Sporadic.Mathieu
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.M11 CFSG.KS.SporSch.MOC
open CFSG.KS.SporSch.CodesImg CFSG.KC.Child3 CFSG.Certificates
open CFSG.EvenSporadicStandard.HypOne CFSG.EvenSporadicStandard.HypOne.M22
open CertificateChecks.KernelSporSch.M22OC CertificateChecks.KernelLC.M12Cent

theorem fourA : fourCheck 22 kChainA kGensA kFourWordsA 4000 = true := by
  have hl := lenKA
  have hP : ∀ j < kGensA.length, permOK 22 5 (mask 5) (22 * 5) (M22KA.S j) (M22KA.SI j) =
      true := fun j hj => (trip (allN_spec kPA j (by rw [← hl]; exact hj))).1
  have hW : allN kFourWordsA.length (fun i => bAnd(lettersK kGensA.length
      (kFourWordsA.getD i []), Nat.beq (wordK 22 5 (mask 5) (pidn 22 5) M22KA.S M22KA.SI
        (kFourWordsA.getD i [])) (M22H1RA.E (lget M22H1RA.OFF i)))) = true := by
    rw [hl]
    exact kWA
  have hri := reps_img szOK' imgKA (allN_of_forall hP) one22 hW
  have cnt : (cosetOrderTables kChainA 1 4).length = M22H1RA.N :=
    (chainK_cosetCount (by decide) (by decide) chainKA one22 cOne22 (by norm_num) (by norm_num)
      (by decide) M22H1XA.hc).trans (by decide)
  obtain ⟨h1, h2⟩ := repsOK_of_img (cap := 4000) (X := cosetOrderTables kChainA 1 4) hl
    (fun j hj => by rw [← hl] at hj; exact imgKA j hj)
    (fun j hj => by rw [← hl] at hj; exact hP j hj)
    (fun j hj => (trip (allN_spec kPA j hj)).2)
    (by decide : (kFourWordsA.map (evalCodes kGensA)).length = M22H1RA.CS.length)
    (fun i hi => hri i (lt_of_lt_of_eq hi (by decide))) kOffA kPosA cnt
    (fun j hj => allN_spec kRA j hj)
  have h3 := ord_all szOK' (reps := kFourWordsA.map (evalCodes kGensA)) (e := 4) (by decide)
    (fun i hi => hri i hi) kOA (by norm_num)
  unfold fourCheck listTables
  rw [h1, h2, h3]
  decide

theorem fourO1 : fourCheck 22 kChainO1 kGensO1 kFourWordsO1 4000 = true := by
  have hl := lenKO1
  have hP : ∀ j < kGensO1.length, permOK 22 5 (mask 5) (22 * 5) (M22KO1.S j) (M22KO1.SI j) =
      true := fun j hj => (trip (allN_spec kPO1 j (by rw [← hl]; exact hj))).1
  have hW : allN kFourWordsO1.length (fun i => bAnd(lettersK kGensO1.length
      (kFourWordsO1.getD i []), Nat.beq (wordK 22 5 (mask 5) (pidn 22 5) M22KO1.S M22KO1.SI
        (kFourWordsO1.getD i [])) (M22H1RO1.E (lget M22H1RO1.OFF i)))) = true := by
    rw [hl]
    exact kWO1
  have hri := reps_img szOK' imgKO1 (allN_of_forall hP) one22 hW
  have cnt : (cosetOrderTables kChainO1 1 4).length = M22H1RO1.N :=
    (chainK_cosetCount (by decide) (by decide) chainKO1 one22 cOne22 (by norm_num) (by norm_num)
      (by decide) M22H1XO1.hc).trans (by decide)
  obtain ⟨h1, h2⟩ := repsOK_of_img (cap := 4000) (X := cosetOrderTables kChainO1 1 4) hl
    (fun j hj => by rw [← hl] at hj; exact imgKO1 j hj)
    (fun j hj => by rw [← hl] at hj; exact hP j hj)
    (fun j hj => (trip (allN_spec kPO1 j hj)).2)
    (by decide : (kFourWordsO1.map (evalCodes kGensO1)).length = M22H1RO1.CS.length)
    (fun i hi => hri i (lt_of_lt_of_eq hi (by decide))) kOffO1 kPosO1 cnt
    (fun j hj => allN_spec kRO1 j hj)
  have h3 := ord_all szOK' (reps := kFourWordsO1.map (evalCodes kGensO1)) (e := 4) (by decide)
    (fun i hi => hri i hi) kOO1 (by norm_num)
  unfold fourCheck listTables
  rw [h1, h2, h3]
  decide

theorem fourO2 : fourCheck 22 kChainO2 kGensO2 kFourWordsO2 4000 = true := by
  have hl := lenKO2
  have hP : ∀ j < kGensO2.length, permOK 22 5 (mask 5) (22 * 5) (M22KO2.S j) (M22KO2.SI j) =
      true := fun j hj => (trip (allN_spec kPO2 j (by rw [← hl]; exact hj))).1
  have hW : allN kFourWordsO2.length (fun i => bAnd(lettersK kGensO2.length
      (kFourWordsO2.getD i []), Nat.beq (wordK 22 5 (mask 5) (pidn 22 5) M22KO2.S M22KO2.SI
        (kFourWordsO2.getD i [])) (M22H1RO2.E (lget M22H1RO2.OFF i)))) = true := by
    rw [hl]
    exact kWO2
  have hri := reps_img szOK' imgKO2 (allN_of_forall hP) one22 hW
  have cnt : (cosetOrderTables kChainO2 1 4).length = M22H1RO2.N :=
    (chainK_cosetCount (by decide) (by decide) chainKO2 one22 cOne22 (by norm_num) (by norm_num)
      (by decide) M22H1XO2.hc).trans (by decide)
  obtain ⟨h1, h2⟩ := repsOK_of_img (cap := 4000) (X := cosetOrderTables kChainO2 1 4) hl
    (fun j hj => by rw [← hl] at hj; exact imgKO2 j hj)
    (fun j hj => by rw [← hl] at hj; exact hP j hj)
    (fun j hj => (trip (allN_spec kPO2 j hj)).2)
    (by decide : (kFourWordsO2.map (evalCodes kGensO2)).length = M22H1RO2.CS.length)
    (fun i hi => hri i (lt_of_lt_of_eq hi (by decide))) kOffO2 kPosO2 cnt
    (fun j hj => allN_spec kRO2 j hj)
  have h3 := ord_all szOK' (reps := kFourWordsO2.map (evalCodes kGensO2)) (e := 4) (by decide)
    (fun i hi => hri i hi) kOO2 (by norm_num)
  unfold fourCheck listTables
  rw [h1, h2, h3]
  decide

theorem autData_eq : autData = true := by
  have hA : kChainA.check = true := (chainK_check (by decide) (by decide) chainKA).1
  have hO1 : kChainO1.check = true := (chainK_check (by decide) (by decide) chainKO1).1
  have hO2 : kChainO2.check = true := (chainK_check (by decide) (by decide) chainKO2).1
  have hc := commT_of_commK imgZ imgA kZcomm
  have hs : m22Certificate.sift (evalCodes gensA zWordA) 0 = false := by
    rw [m22Certificate, chainK_sift_eq (by decide) (by decide) chainQ imgZ kZcn]
    simpa using kZsift
  unfold autData
  rw [hA, hO1, hO2, hc, hs, fourA, fourO1, fourO2]
  rfl

theorem img_ab {wd : List ℤ} (hw : abOK wd = true) :
    imageList (evalCodes gensM wd) = (unpack 22 5 (ab wd)).toList :=
  abWordK_rep szOK' imgA imgB pA pB hw

theorem ord_of {g : Equiv.Perm (Fin 22)} {P : Nat} (hg : imageList g = (unpack 22 5 P).toList)
    (h : inv2K P = true) : ordTest 22 2 (toTable g) = true := by
  obtain ⟨hc, ho⟩ := and_of_bAnd h
  exact ordTest_of_ordIs szOK' hg hc (by norm_num) ho

theorem compT_toTable (g h : Equiv.Perm (Fin 22)) :
    compT 22 (toTable g) (toTable h) = toTable (g * h) :=
  CFSG.KS.Tbl.compT_eq_toTable (by norm_num) (rep_toTable (by norm_num) g)
    (rep_toTable (by norm_num) h)

theorem e8Data_eq : e8Data = true := by
  have i1 : imageList e1 = (unpack 22 5 (ab wordE1)).toList := img_ab kA1
  have i2 : imageList e2 = (unpack 22 5 (ab wordE2)).toList := img_ab kA2
  have i3 : imageList e3 = (unpack 22 5 (ab wordE3)).toList := img_ab kA3
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

theorem foursData_eq : foursData = true := by
  have il1 : imageList l1 = (unpack 22 5 (ab wordL1)).toList := img_ab kAL1
  have il2 : imageList l2 = (unpack 22 5 (ab wordL2)).toList := img_ab kAL2
  have c1 := mulK_rep szOK' (mulK_rep szOK' (mulK_rep szOK' il1 imgRO0) (invK_rep il1 kPL1))
    (invK_rep imgRO0 kPR0)
  have c2 := mulK_rep szOK' (mulK_rep szOK' (mulK_rep szOK' il2 imgRO1) (invK_rep il2 kPL2))
    (invK_rep imgRO1 kPR1)
  unfold foursData
  rw [ord_of c1 kF1, ord_of c2 kF2]
  rfl

theorem facts : innerData = true ∧ autData = true ∧ e8Data = true ∧ foursData = true :=
  ⟨innerData_eq, autData_eq, e8Data_eq, foursData_eq⟩

end CertificateChecks.KernelSporSch.M22H1

end
