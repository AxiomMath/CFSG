module

public import Certificates.Kernel.SporSch.Mathieu.M22H1Checks
public import Certificates.Kernel.SporSch.Mathieu.M22OFacts
public import Certificates.Kernel.LocalComp.M12Cent.Facts
public import CFSG.Certificates.Kernel.Spor.SiftEq
public import CFSG.Certificates.Kernel.Spor.RawSiftK

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.M22H1

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.Monster.B.Mathieu CFSG.ComponentClassification.M12Cover CFSG.Sporadic.Mathieu
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.M11 CFSG.KS.SporSch.MOC
open CFSG.KS.SporSch.CodesImg CFSG.KC.Child3 CFSG.Certificates
open CFSG.EvenSporadicStandard.HypOne CFSG.EvenSporadicStandard.HypOne.M22
open CertificateChecks.KernelSporSch.M22OC CertificateChecks.KernelLC.M12Cent

theorem chainK_sift_eq {n w : Nat} {gens : List (Equiv.Perm (Fin n))} {words : List (List Int)}
    {k : Nat} {bv : Vector (Fin n) k} {PS PSI LR TR TRI : Nat → Nat} {kS BP NS CH : Nat}
    (hn : 1 ≤ n) (hbs : bv.toList.Nodup)
    (hQ : ChainK n w gens words bv PS PSI LR TR TRI kS BP NS CH) {g : Equiv.Perm (Fin n)} {G : Nat}
    (hg : imageList g = (unpack n w G).toList)
    (hG : CFSG.KS.Prim.canonK n w (mask w) (n * w) G = true) :
    (certificate hn gens words bv hbs).sift g 0 =
      siftK n w (mask w) (n * w) (pidn n w) LR TRI BP k 0 G := by
  obtain ⟨hA, hraw⟩ := chainK_arrays hn hbs hQ
  have hb := binds_of hQ
  have hp := (Orb.head_facts hQ.2.2.2.2.2.1).1
  have hF := chainCheckFacts hraw
  have e := hA.siftA_eq hF k 0 (by simp [certificate]) (unpack n w G) g (rep_of_imageList hg)
  obtain ⟨-, -, h3, -⟩ := CFSG.KS.PF.canon_facts hG
  exact e.symm.trans (siftK_eq hb hp hQ.2.2.2.2.2.2.1 rfl h3 (range_of_canonK hG))

theorem trip {a b c : Bool} (h : bAnd(a, bAnd(b, c)) = true) : a = true ∧ b = true ∧ c = true := by
  obtain ⟨h1, h2⟩ := and_of_bAnd h
  obtain ⟨h2, h3⟩ := and_of_bAnd h2
  exact ⟨h1, h2, h3⟩

theorem lenA : gensA.length = 3 := rfl

theorem lenC1 : centGens1.length = 3 := rfl

theorem lenO1 : (m22OutCentWords1.map (evalCodes gensM)).length = 3 := rfl

theorem lenO2 : (m22OutCentWords2.map (evalCodes gensM)).length = 3 := rfl

theorem lenKA : kGensA.length = 4 := rfl

theorem lenKO1 : kGensO1.length = 4 := rfl

theorem lenKO2 : kGensO2.length = 4 := rfl

theorem imgGA3 : ∀ j < gensA.length, imageList (gensA.getD j 1) = (unpack 22 5 (GA3 j)).toList := by
  intro j hj
  rw [lenA] at hj
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
  · exact imgA
  · exact imgB
  · exact imgD

theorem imgZ : imageList (evalCodes gensA zWordA) = (unpack 22 5 (M22KA.S 3)).toList := by
  have h1 := kZ1
  have h2 := kZ2
  have hp : ∀ j < gensA.length, permOK 22 5 (mask 5) (22 * 5) (GA3 j) (GA3I j) = true := by
    intro j hj
    rw [lenA] at hj
    exact (trip (allN_spec kGA3 j hj)).1
  have h1' : lettersK gensA.length zWordA = true := by
    rw [lenA]
    exact h1
  rw [evalCodes_img szOK' imgGA3 hp imgOne h1', Nat.eq_of_beq_eq_true h2]

theorem imgC1 : ∀ j < centGens1.length,
    imageList (centGens1.getD j 1) = (unpack 22 5 (M22C1.S j)).toList :=
  chainC1.2.2.2.1

theorem getD_append_lt {α : Type} {l : List α} {a d : α} {j : Nat} (hj : j < l.length) :
    (l ++ [a]).getD j d = l.getD j d := by
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ hj,
    List.getElem_append_left hj]

theorem getD_append_eq {α : Type} {l : List α} {a d : α} : (l ++ [a]).getD l.length d = a := by
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (by omega)]
  simp

theorem imgKA : ∀ j < kGensA.length,
    imageList (kGensA.getD j 1) = (unpack 22 5 (M22KA.S j)).toList := by
  intro j hj
  have hl := lenC1
  rw [lenKA] at hj
  by_cases h3 : j < 3
  · rw [kGensA, getD_append_lt (by rw [hl]; exact h3), imgC1 j (by rw [hl]; exact h3),
      Nat.eq_of_beq_eq_true (allN_spec kGenA j h3)]
  · have e : j = centGens1.length := by omega
    subst e
    rw [kGensA, getD_append_eq, imgZ, hl]

theorem imgOC1 : ∀ j < (m22OutCentWords1.map (evalCodes gensM)).length,
    imageList ((m22OutCentWords1.map (evalCodes gensM)).getD j 1) =
      (unpack 22 5 (M22OC1.S j)).toList :=
  chainO1.2.2.2.1

theorem imgOC2 : ∀ j < (m22OutCentWords2.map (evalCodes gensM)).length,
    imageList ((m22OutCentWords2.map (evalCodes gensM)).getD j 1) =
      (unpack 22 5 (M22OC2.S j)).toList :=
  chainO2.2.2.2.1

theorem imgKO1 : ∀ j < kGensO1.length,
    imageList (kGensO1.getD j 1) = (unpack 22 5 (M22KO1.S j)).toList := by
  intro j hj
  have hl := lenO1
  rw [lenKO1] at hj
  have g1 := kGenO1
  have g2 := kGenO1r
  by_cases h3 : j < 3
  · rw [kGensO1, getD_append_lt (by rw [hl]; exact h3), imgOC1 j (by rw [hl]; exact h3),
      Nat.eq_of_beq_eq_true (allN_spec g1 j h3)]
  · have e : j = (m22OutCentWords1.map (evalCodes gensM)).length := by omega
    subst e
    rw [kGensO1, getD_append_eq, imgRO0, hl, Nat.eq_of_beq_eq_true g2]

theorem imgKO2 : ∀ j < kGensO2.length,
    imageList (kGensO2.getD j 1) = (unpack 22 5 (M22KO2.S j)).toList := by
  intro j hj
  have hl := lenO2
  rw [lenKO2] at hj
  have g1 := kGenO2
  have g2 := kGenO2r
  by_cases h3 : j < 3
  · rw [kGensO2, getD_append_lt (by rw [hl]; exact h3), imgOC2 j (by rw [hl]; exact h3),
      Nat.eq_of_beq_eq_true (allN_spec g1 j h3)]
  · have e : j = (m22OutCentWords2.map (evalCodes gensM)).length := by omega
    subst e
    rw [kGensO2, getD_append_eq, imgRO1, hl, Nat.eq_of_beq_eq_true g2]

theorem chainKA : ChainK 22 5 kGensA kChainWordsA (#v[0, 1, 3, 2] : Vector (Fin 22) 4) M22KA.S
    M22KA.SI M22KA.LR M22KA.TR M22KA.TRI 6 M22KA.BP 2 16 :=
  ⟨by norm_num, by norm_num, by norm_num, imgKA, by decide, M22KA.head, M22KA.hl, by norm_num,
    M22KA.hs⟩

theorem chainKO1 : ChainK 22 5 kGensO1 kChainWordsO1 (#v[0, 1, 2] : Vector (Fin 22) 3) M22KO1.S
    M22KO1.SI M22KO1.LR M22KO1.TR M22KO1.TRI 8 M22KO1.BP 2 16 :=
  ⟨by norm_num, by norm_num, by norm_num, imgKO1, by decide, M22KO1.head, M22KO1.hl, by norm_num,
    M22KO1.hs⟩

theorem chainKO2 : ChainK 22 5 kGensO2 kChainWordsO2 (#v[0, 1, 2, 3] : Vector (Fin 22) 4)
    M22KO2.S M22KO2.SI M22KO2.LR M22KO2.TR M22KO2.TRI 7 M22KO2.BP 2 16 :=
  ⟨by norm_num, by norm_num, by norm_num, imgKO2, by decide, M22KO2.head, M22KO2.hl, by norm_num,
    M22KO2.hs⟩

theorem one22 : imageList (1 : Equiv.Perm (Fin 22)) = (unpack 22 5 (pidn 22 5)).toList := by
  decide

theorem cOne22 : canonK 22 5 (mask 5) (22 * 5) One22 = true := by quickRfl

theorem innerData_eq : innerData = true := by
  have hl := lenC1
  have hP : ∀ j < centGens1.length, permOK 22 5 (mask 5) (22 * 5) (M22C1.S j) (M22C1.SI j) =
      true := fun j hj => (trip (allN_spec kPI j (by rw [← hl]; exact hj))).1
  have hW : allN innerFourWords.length (fun i => bAnd(lettersK centGens1.length
      (innerFourWords.getD i []), Nat.beq (wordK 22 5 (mask 5) (pidn 22 5) M22C1.S M22C1.SI
        (innerFourWords.getD i [])) (M22H1RI.E (lget M22H1RI.OFF i)))) = true := by
    rw [hl]
    exact kWI
  have hri := reps_img szOK' imgC1 (allN_of_forall hP) one22 hW
  have cnt : (cosetOrderTables m22CentQ1 1 4).length = M22H1RI.N :=
    (chainK_cosetCount (by decide) (by decide) chainC1 one22 cOne22 (by norm_num) (by norm_num)
      (by decide) M22H1XI.hc).trans (by decide)
  obtain ⟨h1, h2⟩ := repsOK_of_img (cap := 4000) (X := cosetOrderTables m22CentQ1 1 4) hl
    (fun j hj => by rw [← hl] at hj; exact imgC1 j hj)
    (fun j hj => by rw [← hl] at hj; exact hP j hj)
    (fun j hj => (trip (allN_spec kPI j hj)).2)
    (by decide : (innerFourWords.map (evalCodes centGens1)).length = M22H1RI.CS.length)
    (fun i hi => hri i (lt_of_lt_of_eq hi (by decide))) kOffI kPosI cnt
    (fun j hj => allN_spec kRI j hj)
  have h3 := ord_all szOK' (reps := innerFourWords.map (evalCodes centGens1)) (e := 4) (by decide)
    (fun i hi => hri i hi) kOI (by norm_num)
  unfold innerData fourCheck listTables
  rw [h1, h2, h3]
  decide

end CertificateChecks.KernelSporSch.M22H1

end
