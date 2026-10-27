module

public import Certificates.Kernel.LocalComp.M12Cent.Cover
public import Certificates.Kernel.LocalComp.M12Cent.Facts
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.SporSch.ConjClosureSpec

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.M12Cent

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Certificates CFSG.Sporadic.Mathieu
open CFSG.Sporadic.Schreier.Native CFSG.Monster.B.Mathieu CFSG.ComponentClassification.M12Cover
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.M11 CFSG.KS.MEnum CFSG.KS.SporSch.MOC
open CFSG.KS.SporSch.CodesImg CFSG.KC.Child3 CFSG.ClassicalInvolution.Q3.TL4.E3S3M12

theorem kRw0 : abOK (m12InvRepWords.getD 0 []) = true := by quickRfl
theorem kRw1 : abOK (m12InvRepWords.getD 1 []) = true := by quickRfl

theorem kRb1 : Nat.beq (abWordK 12 4 (mask 4) (pidn 12 4) PA (pinvS 12 4 (mask 4) PA) PB
    (pinvS 12 4 (mask 4) PB) (m12InvRepWords.getD 0 [])) (T1.E (lget T1.OFF 0)) = true := by
  quickRfl
theorem kRb3 : Nat.beq (abWordK 12 4 (mask 4) (pidn 12 4) PA (pinvS 12 4 (mask 4) PA) PB
    (pinvS 12 4 (mask 4) PB) (m12InvRepWords.getD 1 [])) (T3.E (lget T3.OFF 0)) = true := by
  quickRfl

theorem kWs1 : allN (gen1Data.map GenDatum.sw).length (fun i =>
    bAnd(lettersK k1Gens.length ((gen1Data.map GenDatum.sw).getD i []),
      Nat.beq (wordK 12 4 (mask 4) (pidn 12 4) C1.S C1.SI ((gen1Data.map GenDatum.sw).getD i []))
        (T1.E (lget T1.OFF (i + 1))))) = true := by quickRfl
theorem kWs3 : allN (gen2Data.map GenDatum.sw).length (fun i =>
    bAnd(lettersK k3Gens.length ((gen2Data.map GenDatum.sw).getD i []),
      Nat.beq (wordK 12 4 (mask 4) (pidn 12 4) C3.S C3.SI ((gen2Data.map GenDatum.sw).getD i []))
        (T3.E (lget T3.OFF (i + 1))))) = true := by quickRfl

theorem kTOff1 : offOK T1.CS T1.OFF T1.N = true := by quickRfl
theorem kTOff3 : offOK T3.CS T3.OFF T3.N = true := by quickRfl

theorem kTPos1 : CFSG.KC.J2Cover.allL (fun c => Nat.blt 0 c) T1.CS = true := by quickRfl
theorem kTPos3 : CFSG.KC.J2Cover.allL (fun c => Nat.blt 0 c) T3.CS = true := by quickRfl

theorem kT1 : allN T1.N (repK 12 4 C1.S C1.SI 4 T1.CS T1.OFF T1.CI T1.E T1.P T1.L T1.K T1.S
    T1.SI T1.N 1000) = true := by quickRfl
theorem kT3 : allN T3.N (repK 12 4 C3.S C3.SI 3 T3.CS T3.OFF T3.CI T3.E T3.P T3.L T3.K T3.S
    T3.SI T3.N 1000) = true := by quickRfl

theorem kOs1 : allN (gen1Data.map GenDatum.sw).length (fun i =>
    bAnd(canonK 12 4 (mask 4) (12 * 4) (T1.E (lget T1.OFF (i + 1))),
      ordIs 12 4 (mask 4) (pidn 12 4) (T1.E (lget T1.OFF (i + 1))) (2 - 1))) = true := by
  quickRfl
theorem kOs3 : allN (gen2Data.map GenDatum.sw).length (fun i =>
    bAnd(canonK 12 4 (mask 4) (12 * 4) (T3.E (lget T3.OFF (i + 1))),
      ordIs 12 4 (mask 4) (pidn 12 4) (T3.E (lget T3.OFF (i + 1))) (2 - 1))) = true := by
  quickRfl

@[expose] noncomputable def xK (d : GenDatum) : Nat :=
  abWordK 12 4 (mask 4) (pidn 12 4) PA (pinvS 12 4 (mask 4) PA) PB (pinvS 12 4 (mask 4) PB) d.xw

@[expose] noncomputable def extP (S : Nat → Nat) (g X : Nat) (j : Nat) : Nat := if j < g then S j else X

@[expose] noncomputable def genK (S SI : Nat → Nat) (g : Nat) (d : GenDatum) : Bool :=
  abOK d.xw && lettersK g d.sw &&
    commK 12 4 (mask 4) (12 * 4) (xK d) (wordK 12 4 (mask 4) (pidn 12 4) S SI d.sw) &&
    permOK 12 4 (mask 4) (12 * 4) (xK d) (pinvS 12 4 (mask 4) (xK d)) &&
    lettersK (g + 1) d.aw && lettersK (g + 1) d.bw &&
    Nat.beq (wordK 12 4 (mask 4) (pidn 12 4) (extP S g (xK d))
      (extP SI g (pinvS 12 4 (mask 4) (xK d))) d.aw) PA &&
    Nat.beq (wordK 12 4 (mask 4) (pidn 12 4) (extP S g (xK d))
      (extP SI g (pinvS 12 4 (mask 4) (xK d))) d.bw) PB

theorem kGen1 : gen1Data.all (genK C1.S C1.SI 4) = true := by quickRfl
theorem kGen3 : gen2Data.all (genK C3.S C3.SI 3) = true := by quickRfl

theorem genOK_of_genK {gs : List (Equiv.Perm (Fin 12))} {S SI : Nat → Nat} {g : Nat}
    (hgl : gs.length = g)
    (hg : ∀ j < gs.length, imageList (gs.getD j 1) = (unpack 12 4 (S j)).toList)
    (hp : ∀ j < gs.length, permOK 12 4 (mask 4) (12 * 4) (S j) (SI j) = true)
    {d : GenDatum} (h : genK S SI g d = true) : genOK gs d = true := by
  simp only [genK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hxw, hsw⟩, hcm⟩, hpx⟩, haw⟩, hbw⟩, ha⟩, hb⟩ := h
  have hx := abWordK_rep sz12 imgA imgB pA pB hxw
  have hs := evalCodes_img sz12 hg hp one12 (hgl ▸ hsw)
  have hg' : ∀ j < (gs ++ [evalCodes [m12gA, m12gB] d.xw]).length,
      imageList ((gs ++ [evalCodes [m12gA, m12gB] d.xw]).getD j 1) =
        (unpack 12 4 (extP S g (xK d) j)).toList := by
    intro j hj
    simp only [List.length_append, List.length_singleton] at hj
    unfold extP
    rcases Nat.lt_or_ge j gs.length with hl | hl
    · rw [List.getD_append _ _ _ _ hl, if_pos (hgl ▸ hl)]
      exact hg j hl
    · have e : j = gs.length := by omega
      subst e
      rw [List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self, if_neg (by omega)]
      exact hx
  have hp' : ∀ j < (gs ++ [evalCodes [m12gA, m12gB] d.xw]).length,
      permOK 12 4 (mask 4) (12 * 4) (extP S g (xK d) j)
        (extP SI g (pinvS 12 4 (mask 4) (xK d)) j) = true := by
    intro j hj
    simp only [List.length_append, List.length_singleton] at hj
    unfold extP
    by_cases hl : j < g
    · rw [if_pos hl, if_pos hl]
      exact hp j (hgl ▸ hl)
    · rw [if_neg hl, if_neg hl]
      exact hpx
  have hl' : (gs ++ [evalCodes [m12gA, m12gB] d.xw]).length = g + 1 := by simp [hgl]
  have hA := evalCodes_img sz12 hg' hp' one12 (hl' ▸ haw)
  have hB := evalCodes_img sz12 hg' hp' one12 (hl' ▸ hbw)
  rw [Nat.eq_of_beq_eq_true ha] at hA
  rw [Nat.eq_of_beq_eq_true hb] at hB
  unfold genOK
  simp only
  rw [commT_of_commK hx hs hcm, toTable_eq_arrTable_of_img hA, toTable_eq_arrTable_of_img imgA,
    toTable_eq_arrTable_of_img hB, toTable_eq_arrTable_of_img imgB,
    CFSG.KS.SporSch.ClsSpec.tblEq_self, CFSG.KS.SporSch.ClsSpec.tblEq_self]
  rfl

theorem chkGen1_eq : chkGen1 () = true := by
  unfold chkGen1
  rw [List.all_eq_true]
  intro d hd
  exact genOK_of_genK (by decide) img1 (fun j hj => allN_spec kP1 j hj)
    (List.all_eq_true.1 kGen1 d hd)

theorem chkGen2_eq : chkGen2 () = true := by
  unfold chkGen2
  rw [List.all_eq_true]
  intro d hd
  exact genOK_of_genK (by decide) img3 (fun j hj => allN_spec kP3 j hj)
    (List.all_eq_true.1 kGen3 d hd)

theorem ord_data {gs : List (Equiv.Perm (Fin 12))} {S SI : Nat → Nat} {D : List GenDatum}
    {E : Nat → Nat} {OFF : List Nat}
    (hg : ∀ j < gs.length, imageList (gs.getD j 1) = (unpack 12 4 (S j)).toList)
    (hp : allN gs.length (fun j => permOK 12 4 (mask 4) (12 * 4) (S j) (SI j)) = true)
    (hk : allN (D.map GenDatum.sw).length (fun i =>
      bAnd(lettersK gs.length ((D.map GenDatum.sw).getD i []),
        Nat.beq (wordK 12 4 (mask 4) (pidn 12 4) S SI ((D.map GenDatum.sw).getD i []))
          (E (lget OFF (i + 1))))) = true)
    (ho : allN (D.map GenDatum.sw).length (fun i =>
      bAnd(canonK 12 4 (mask 4) (12 * 4) (E (lget OFF (i + 1))),
        ordIs 12 4 (mask 4) (pidn 12 4) (E (lget OFF (i + 1))) (2 - 1))) = true) :
    (D.all fun d => ordTest 12 2 (toTable (evalCodes gs d.sw))) = true := by
  have h := ord_all sz12 (reps := (D.map GenDatum.sw).map (evalCodes gs)) (e := 2)
    (Ps := fun i => E (lget OFF (i + 1))) (by simp) (reps_img sz12 hg hp one12 hk) ho
    (by norm_num)
  simpa [List.all_map, Function.comp_def] using h

theorem cntY1 : (cosetOrderTables m12CentQ1 1 2).length = T1.N :=
  (chainK_cosetCount (by decide) (by decide) chain1 one12 cOne12 (by norm_num) (by norm_num)
    (by decide) Y1.hc).trans (by decide)

theorem cntY3 : (cosetOrderTables m12CentQ2 1 2).length = T3.N :=
  (chainK_cosetCount (by decide) (by decide) chain3 one12 cOne12 (by norm_num) (by norm_num)
    (by decide) Y3.hc).trans (by decide)

theorem cover_img {gs : List (Equiv.Perm (Fin 12))} {S SI : Nat → Nat} {D : List GenDatum}
    {wr : List Int} {E : Nat → Nat} {OFF : List Nat}
    (hg : ∀ j < gs.length, imageList (gs.getD j 1) = (unpack 12 4 (S j)).toList)
    (hp : allN gs.length (fun j => permOK 12 4 (mask 4) (12 * 4) (S j) (SI j)) = true)
    (hw : abOK wr = true)
    (hr : Nat.beq (abWordK 12 4 (mask 4) (pidn 12 4) PA (pinvS 12 4 (mask 4) PA) PB
      (pinvS 12 4 (mask 4) PB) wr) (E (lget OFF 0)) = true)
    (hk : allN (D.map GenDatum.sw).length (fun i =>
      bAnd(lettersK gs.length ((D.map GenDatum.sw).getD i []),
        Nat.beq (wordK 12 4 (mask 4) (pidn 12 4) S SI ((D.map GenDatum.sw).getD i []))
          (E (lget OFF (i + 1))))) = true) :
    ∀ i < (coverReps gs (evalCodes [m12gA, m12gB] wr) D).length,
      imageList ((coverReps gs (evalCodes [m12gA, m12gB] wr) D).getD i 1) =
        (unpack 12 4 (E (lget OFF i))).toList := by
  intro i hi
  have hri := reps_img sz12 hg hp one12 hk
  have e : coverReps gs (evalCodes [m12gA, m12gB] wr) D =
      evalCodes [m12gA, m12gB] wr :: (D.map GenDatum.sw).map (evalCodes gs) := by
    simp [coverReps, List.map_map, Function.comp_def]
  rw [e] at hi ⊢
  rcases i with _ | i
  · rw [List.getD_cons_zero, abWordK_rep sz12 imgA imgB pA pB hw, Nat.eq_of_beq_eq_true hr]
  · rw [List.getD_cons_succ]
    exact hri i (by simpa using hi)

theorem m12InvReps_getD (j : Nat) (hj : j < 2) :
    m12InvReps.getD j 1 = evalCodes [m12gA, m12gB] (m12InvRepWords.getD j []) :=
  getD_map_of_lt _ [] 1 (by simpa [m12InvRepWords] using hj)

theorem chkCover1_eq : chkCover1 () = true := by
  have himg := cover_img (D := gen1Data) img1 kP1 kRw0 kRb1 kWs1
  rw [← m12InvReps_getD 0 (by norm_num)] at himg
  obtain ⟨h1, -⟩ := repsOK_of_img (cap := 1000) (X := cosetOrderTables m12CentQ1 1 2)
    (by decide : k1Gens.length = 4) img1 (fun j hj => allN_spec kP1 j hj)
    (fun j hj => and_of_bAnd (allN_spec kC1 j hj))
    (by decide : (coverReps k1Gens (m12InvReps.getD 0 1) gen1Data).length = T1.CS.length)
    (fun i hi => himg i (lt_of_lt_of_eq hi (by decide))) kTOff1 kTPos1 cntY1
    (fun j hj => allN_spec kT1 j hj)
  unfold chkCover1 coverOK listTables
  rw [h1, Bool.true_and]
  exact ord_data img1 kP1 kWs1 kOs1

theorem chkCover2_eq : chkCover2 () = true := by
  have himg := cover_img (D := gen2Data) img3 kP3 kRw1 kRb3 kWs3
  rw [← m12InvReps_getD 1 (by norm_num)] at himg
  obtain ⟨h1, -⟩ := repsOK_of_img (cap := 1000) (X := cosetOrderTables m12CentQ2 1 2)
    (by decide : k3Gens.length = 3) img3 (fun j hj => allN_spec kP3 j hj)
    (fun j hj => and_of_bAnd (allN_spec kC3 j hj))
    (by decide : (coverReps k3Gens (m12InvReps.getD 1 1) gen2Data).length = T3.CS.length)
    (fun i hi => himg i (lt_of_lt_of_eq hi (by decide))) kTOff3 kTPos3 cntY3
    (fun j hj => allN_spec kT3 j hj)
  unfold chkCover2 coverOK listTables
  rw [h1, Bool.true_and]
  exact ord_data img3 kP3 kWs3 kOs3

theorem coverFacts : chkCover1 () = true ∧ chkGen1 () = true ∧ chkCover2 () = true ∧
    chkGen2 () = true :=
  ⟨chkCover1_eq, chkGen1_eq, chkCover2_eq, chkGen2_eq⟩

end CertificateChecks.KernelLC.M12Cent

end
