module

public import Certificates.Kernel.LocalComp.Sp6J.Checks
public import Certificates.Kernel.LocalComp.Sp6J.Slice0
public import Certificates.Kernel.LocalComp.Sp6J.Slice1
public import Certificates.Kernel.LocalComp.ExcGlue
public import CFSG.Certificates.Kernel.SporSch.MathieuOCSound
public import CFSG.Certificates.Kernel.SporSch.ChainKSlice
public import CFSG.Certificates.Kernel.Spor.SiftRSound
public import CFSG.LocalAnalysis.EvenSmallLie.Sp6JConditionInputs
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.Kernel.BfsPinSound
public import CFSG.Certificates.Kernel.BfsPinUnpack
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutCheckBase

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.Sp6J

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Certificates CFSG.Sporadic.Schreier.Co3
open CFSG.Sporadic.Schreier.Native CFSG.Monster.B.Mathieu CFSG.ComponentClassification.M12Cover
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch.MOC CFSG.KS.SporSch.MBT
open CFSG.KS.SporSch.CodesImg CFSG.KC.Child3 CFSG.KS.M11 CFSG.EvenSmallLie.Sp6
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CertificateChecks.KernelSpor CertificateChecks.KernelLC.ExcGlue

theorem one36 : imageList (1 : Equiv.Perm (Fin 36)) = (unpack 36 6 (pidn 36 6)).toList :=
  one_img kId

theorem imgX : ∀ j < sp6Gens.length, imageList (sp6Gens.getD j 1) = (unpack 36 6 (XQ.S j)).toList := by
  intro j hj
  have hj2 : j < 2 := hj
  interval_cases j
  · exact kImgA
  · exact kImgB

theorem pX : ∀ j < sp6Gens.length, permOK 36 6 (mask 6) (36 * 6) (XQ.S j) (XQ.SI j) = true :=
  fun j hj => allN_spec kPX j (by have : j < 2 := hj; omega)

theorem chainX : ChainK 36 6 sp6Gens xQWords (#v[0, 1, 2, 4, 8, 12] : Vector (Fin 36) 6)
    XQ.S XQ.SI XQ.LR XQ.TR XQ.TRI 10 XQ.BP 1 36 :=
  ⟨by norm_num, by norm_num, by norm_num, imgX, by decide, XQ.head, XQ.hl, by norm_num, XQ.hs⟩

theorem xq_eq : sp6Q = certificate (by decide) sp6Gens xQWords
    (#v[0, 1, 2, 4, 8, 12] : Vector (Fin 36) 6) (by decide) := rfl

theorem validX : sp6Q.check = true ∧ sp6Q.orderCertificate = 1451520 := by
  obtain ⟨h1, h2⟩ := chainK_check (by decide) (by decide) chainX
  rw [xq_eq]
  exact ⟨h1, h2.trans (Nat.eq_of_beq_eq_true kNX)⟩

theorem sift_of {g : Equiv.Perm (Fin 36)} {j : Nat} (hj : j < 2)
    (hg : imageList g = (unpack 36 6 (XQ.S j)).toList) :
    siftA 36 (rawLevels 36 co3Sp36Arrs co3Sp36BaseArr) co3Sp36BaseArr 0
      (Array.ofFn fun i => (g i : ℕ)) = true := by
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 (allN_spec kSift j hj)
  have harr : (Array.ofFn fun i => (g i : ℕ)) = unpack 36 6 (XQ.S j) := by
    apply Array.toList_inj.1
    rw [Array.toList_ofFn]
    exact hg
  exact siftK_soundR Co3Sp36.binds Co3Sp36.perm Co3Sp36.hl harr (Nat.eq_of_beq_eq_true h1)
    (range_of_permOK (allN_spec kPX j (by omega))) h2

theorem cntX : (cosetOrderTables sp6Q 1 2).length = RX.N := by
  have hc : rcnt (XQ.LR 0) = 36 := by decide +kernel
  have hN : RX.N = 5103 := by decide +kernel
  have h0 := Nat.eq_of_beq_eq_true kS0
  have h1 := Nat.eq_of_beq_eq_true kS1
  have hg : imageList (1 : Equiv.Perm (Fin 36)) = (unpack 36 6 One36).toList := one36
  have htr : trOrbK 36 6 XQ.LR XQ.TR
      (((#v[0, 1, 2, 4, 8, 12] : Vector (Fin 36) 6).get ⟨0, by norm_num⟩ : Fin 36) : Nat)
      (((#v[0, 1, 2, 4, 8, 12] : Vector (Fin 36) 6).get ⟨1, by norm_num⟩ : Fin 36) : Nat) =
      true := kTr
  rw [xq_eq, chainK_cosetCount_trOrb chainX (by decide) (by decide) hg (by norm_num : 0 < 2)
    (by norm_num : 2 ≤ 6) h0 h1 (by rw [hc]; norm_num) htr, hc, hN]

theorem imgRX : ∀ i < sp6InvRepWords.length, imageList (sp6InvReps.getD i 1) =
    (unpack 36 6 (RX.E (lget RX.OFF i))).toList :=
  words_img (gs := sp6Gens) rfl kSz imgX pX one36 kWX

theorem repsX : repsOK 36 (listTables sp6Gens) (listTables (sp6Gens.map (·⁻¹)))
      (cosetOrderTables sp6Q 1 2) (sp6InvReps.map toTable) 4000 = true ∧
    repSizes 36 (listTables sp6Gens) (listTables (sp6Gens.map (·⁻¹))) (sp6InvReps.map toTable)
      4000 = RX.CS :=
  repsOK_of_img (g := 2) rfl (fun j hj => imgX j hj) (fun j hj => pX j hj)
    (fun j hj => and_of_bAnd (allN_spec kCX j hj)) (by rw [kCSX]; rfl)
    (fun i hi => imgRX i (lt_of_lt_of_eq hi (by rw [kCSX]; rfl))) kOffX kPosX cntX
    (fun j hj => allN_spec kRX j hj)

theorem coverX : repsOK 36 (listTables sp6Gens) (listTables (sp6Gens.map (·⁻¹)))
      (cosetOrderTables sp6Q 1 2) (sp6InvReps.map toTable) 4000 = true ∧
    repSizes 36 (listTables sp6Gens) (listTables (sp6Gens.map (·⁻¹)))
      (sp6InvReps.map toTable) 4000 = [63, 315, 945, 3780] ∧
    (sp6InvReps.map toTable).all (ordTest 36 2) = true :=
  ⟨repsX.1, repsX.2.trans kCSX, ord_all kSz (e := 2) (List.length_map _) imgRX kOX (by norm_num)⟩

theorem centCheck_of {cw fw qw : List (List ℤ)} {gs reps : List (Equiv.Perm (Fin 36))}
    (hgs : gs = cw.map (evalCodes sp6Gens)) (hreps : reps = fw.map (evalCodes gs))
    {k kS : Nat} {bv : Vector (Fin 36) k} (hbs : bv.toList.Nodup)
    {S SI LR TR TRI : Nat → Nat} {BP : Nat}
    (hG : allN cw.length (fun j => bAnd(lettersK 2 (cw.getD j []),
      Nat.beq (wordK 36 6 (mask 6) (pidn 36 6) XQ.S XQ.SI (cw.getD j [])) (S j))) = true)
    (hP : allN cw.length (fun j => permOK 36 6 (mask 6) (36 * 6) (S j) (SI j)) = true)
    (hC : allN cw.length (fun j => bAnd(canonK 36 6 (mask 6) (36 * 6) (S j),
      canonK 36 6 (mask 6) (36 * 6) (SI j))) = true)
    (hQ : ChainK 36 6 gs qw bv S SI LR TR TRI kS BP 1 36)
    {c : Nat} (hN : Nat.beq (ordK LR k) c = true)
    {r : Equiv.Perm (Fin 36)} {R : Nat} (hr : imageList r = (unpack 36 6 R).toList)
    (hM : allN cw.length (fun j => commK 36 6 (mask 6) (36 * 6) (S j) R) = true)
    {CSN : List Nat} (hCS : CSN.length = rcnt (LR 0))
    (hc : ∀ k₀ < rcnt (LR 0), cntOrdK 36 6 (mask 6) (36 * 6) (pidn 36 6) LR TR k One36 4 k₀ =
      CSN.getD k₀ 0)
    {CS OFF : List Nat} {CI E P L K S' SI' : Nat → Nat} {N : Nat}
    (hT : Nat.beq CSN.sum N = true)
    (hW : allN fw.length (fun i => bAnd(lettersK cw.length (fw.getD i []),
      Nat.beq (wordK 36 6 (mask 6) (pidn 36 6) S SI (fw.getD i [])) (E (lget OFF i)))) = true)
    (hO : allN fw.length (fun i => bAnd(canonK 36 6 (mask 6) (36 * 6) (E (lget OFF i)),
      ordIs 36 6 (mask 6) (pidn 36 6) (E (lget OFF i)) (4 - 1))) = true)
    (hlen : fw.length = CS.length)
    (hoff : offOK CS OFF N = true) (hpos : CFSG.KC.J2Cover.allL (fun c => Nat.blt 0 c) CS = true)
    (hR : allN N (repK 36 6 S SI cw.length CS OFF CI E P L K S' SI' N 4000) = true)
    (hbig : CS.all (fun k => decide (5 ≤ k)) = true) (hk : 0 < k) :
    centCheck (certificate (by decide) gs qw bv hbs) c gs reps r = true := by
  subst hgs hreps
  have hg : ∀ j < (cw.map (evalCodes sp6Gens)).length,
      imageList ((cw.map (evalCodes sp6Gens)).getD j 1) = (unpack 36 6 (S j)).toList :=
    fun j hj => words_img (gs := sp6Gens) rfl kSz imgX pX one36 hG j (by simpa using hj)
  have hp : ∀ j < (cw.map (evalCodes sp6Gens)).length,
      permOK 36 6 (mask 6) (36 * 6) (S j) (SI j) = true :=
    fun j hj => allN_spec hP j (by simpa using hj)
  obtain ⟨hchk, hord⟩ := chainK_check (by decide) hbs hQ
  have hcnt : (cosetOrderTables (certificate (by decide) (cw.map (evalCodes sp6Gens)) qw bv hbs)
      1 4).length = N :=
    (chainK_cosetCount (by decide) hbs hQ one36 kOne (by norm_num) hk hCS hc).trans
      (Nat.eq_of_beq_eq_true hT)
  have himg : ∀ i < fw.length, imageList
      ((fw.map (evalCodes (cw.map (evalCodes sp6Gens)))).getD i 1) =
      (unpack 36 6 (E (lget OFF i))).toList :=
    words_img (gs := cw.map (evalCodes sp6Gens)) (k := cw.length) (by simp) kSz hg hp one36 hW
  obtain ⟨h1, h2⟩ := repsOK_of_img (g := cw.length) (by simp) (fun j hj => hg j (by simpa using hj))
    (fun j hj => hp j (by simpa using hj)) (fun j hj => and_of_bAnd (allN_spec hC j hj))
    (by simpa using hlen) (fun i hi => himg i (by omega)) hoff hpos hcnt
    (fun j hj => allN_spec hR j hj) (cap := 4000)
    (reps := fw.map (evalCodes (cw.map (evalCodes sp6Gens))))
  have hcomm : (cw.map (evalCodes sp6Gens)).all
      (fun g => commT 36 (toTable g) (toTable r)) = true := by
    rw [List.all_eq_true]
    intro g hg'
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg'
    have hgj := hg j hj
    rw [List.getD_eq_getElem _ _ hj] at hgj
    exact commT_of_commK hgj hr (allN_spec hM j (by simpa using hj))
  have hordT := ord_all kSz (e := 4) (List.length_map _) himg hO (by norm_num)
  have h2' : repSizes 36 (listTables (cw.map (evalCodes sp6Gens)))
      (listTables ((cw.map (evalCodes sp6Gens)).map (·⁻¹)))
      ((fw.map (evalCodes (cw.map (evalCodes sp6Gens)))).map toTable) 4000 = CS := h2
  simp only [centCheck, Bool.and_eq_true, beq_iff_eq]
  exact ⟨⟨⟨⟨⟨hchk, hord.trans (Nat.eq_of_beq_eq_true hN)⟩, hcomm⟩, h1⟩, h2' ▸ hbig⟩, hordT⟩

theorem cent_img {cw : List (List ℤ)} {S : Nat → Nat}
    (hG : allN cw.length (fun j => bAnd(lettersK 2 (cw.getD j []),
      Nat.beq (wordK 36 6 (mask 6) (pidn 36 6) XQ.S XQ.SI (cw.getD j [])) (S j))) = true) :
    ∀ j < (cw.map (evalCodes sp6Gens)).length,
      imageList ((cw.map (evalCodes sp6Gens)).getD j 1) = (unpack 36 6 (S j)).toList :=
  fun j hj => words_img (gs := sp6Gens) rfl kSz imgX pX one36 hG j (by simpa using hj)

theorem rep_img (i : Nat) (hi : i < 4) :
    imageList (sp6InvReps.getD i 1) = (unpack 36 6 (RX.E (lget RX.OFF i))).toList :=
  imgRX i hi

theorem chainC1 : ChainK 36 6 sp6CentGens1 q1Words (#v[0, 1, 4, 2, 12] : Vector (Fin 36) 5)
    C1Q.S C1Q.SI C1Q.LR C1Q.TR C1Q.TRI 10 C1Q.BP 1 36 :=
  ⟨by norm_num, by norm_num, by norm_num, cent_img kG1, by decide, C1Q.head, C1Q.hl, by norm_num,
    C1Q.hs⟩

theorem chainC2 : ChainK 36 6 sp6CentGens2 q2Words (#v[0, 1, 4, 2] : Vector (Fin 36) 4)
    C2Q.S C2Q.SI C2Q.LR C2Q.TR C2Q.TRI 9 C2Q.BP 1 36 :=
  ⟨by norm_num, by norm_num, by norm_num, cent_img kG2, by decide, C2Q.head, C2Q.hl, by norm_num,
    C2Q.hs⟩

theorem chainC3 : ChainK 36 6 sp6CentGens3 q3Words (#v[0, 1, 2, 4] : Vector (Fin 36) 4)
    C3Q.S C3Q.SI C3Q.LR C3Q.TR C3Q.TRI 11 C3Q.BP 1 36 :=
  ⟨by norm_num, by norm_num, by norm_num, cent_img kG3, by decide, C3Q.head, C3Q.hl, by norm_num,
    C3Q.hs⟩

theorem chainC4 : ChainK 36 6 sp6CentGens4 q4Words (#v[0, 1, 2, 4] : Vector (Fin 36) 4)
    C4Q.S C4Q.SI C4Q.LR C4Q.TR C4Q.TRI 10 C4Q.BP 1 36 :=
  ⟨by norm_num, by norm_num, by norm_num, cent_img kG4, by decide, C4Q.head, C4Q.hl, by norm_num,
    C4Q.hs⟩

theorem cent1 : centCheck sp6CentQ1 23040 sp6CentGens1 sp6FourReps1 sp6Rep1 = true :=
  centCheck_of (cw := c1Words) (fw := f1Words) rfl rfl (by decide) kG1 kP1 kC1 chainC1 kN1
    (rep_img 0 (by norm_num)) kM1 (by decide +kernel) N1.hc kT1 kW1 kO1 (by decide +kernel) kOff1
    kPos1 kR1 (by decide +kernel) (by norm_num)

theorem cent2 : centCheck sp6CentQ2 4608 sp6CentGens2 sp6FourReps2 sp6Rep2 = true :=
  centCheck_of (cw := c2Words) (fw := f2Words) rfl rfl (by decide) kG2 kP2 kC2 chainC2 kN2
    (rep_img 1 (by norm_num)) kM2 (by decide +kernel) N2.hc kT2 kW2 kO2 (by decide +kernel) kOff2
    kPos2 kR2 (by decide +kernel) (by norm_num)

theorem cent3 : centCheck sp6CentQ3 1536 sp6CentGens3 sp6FourReps3 sp6Rep3 = true :=
  centCheck_of (cw := c3Words) (fw := f3Words) rfl rfl (by decide) kG3 kP3 kC3 chainC3 kN3
    (rep_img 2 (by norm_num)) kM3 (by decide +kernel) N3.hc kT3 kW3 kO3 (by decide +kernel) kOff3
    kPos3 kR3 (by decide +kernel) (by norm_num)

theorem cent4 : centCheck sp6CentQ4 384 sp6CentGens4 sp6FourReps4 sp6Rep4 = true :=
  centCheck_of (cw := c4Words) (fw := f4Words) rfl rfl (by decide) kG4 kP4 kC4 chainC4 kN4
    (rep_img 3 (by norm_num)) kM4 (by decide +kernel) N4.hc kT4 kW4 kO4 (by decide +kernel) kOff4
    kPos4 kR4 (by decide +kernel) (by norm_num)

theorem facts : (sp6Q.check = true ∧ sp6Q.orderCertificate = 1451520 ∧
       siftA 36 (rawLevels 36 co3Sp36Arrs co3Sp36BaseArr) co3Sp36BaseArr 0
         (Array.ofFn fun i => (sp6A i : ℕ)) = true ∧
       siftA 36 (rawLevels 36 co3Sp36Arrs co3Sp36BaseArr) co3Sp36BaseArr 0
         (Array.ofFn fun i => (sp6B i : ℕ)) = true)
    ∧ (repsOK 36 (listTables sp6Gens) (listTables (sp6Gens.map (·⁻¹)))
         (cosetOrderTables sp6Q 1 2) (sp6InvReps.map toTable) 4000 = true ∧
       repSizes 36 (listTables sp6Gens) (listTables (sp6Gens.map (·⁻¹)))
         (sp6InvReps.map toTable) 4000 = [63, 315, 945, 3780] ∧
       (sp6InvReps.map toTable).all (ordTest 36 2) = true)
    ∧ (centCheck sp6CentQ1 23040 sp6CentGens1 sp6FourReps1 sp6Rep1 = true)
    ∧ (centCheck sp6CentQ2 4608 sp6CentGens2 sp6FourReps2 sp6Rep2 = true)
    ∧ (centCheck sp6CentQ3 1536 sp6CentGens3 sp6FourReps3 sp6Rep3 = true)
    ∧ (centCheck sp6CentQ4 384 sp6CentGens4 sp6FourReps4 sp6Rep4 = true) :=
  ⟨⟨validX.1, validX.2, sift_of (by norm_num) kImgA, sift_of (by norm_num) kImgB⟩, coverX,
    cent1, cent2, cent3, cent4⟩

end CertificateChecks.KernelLC.Sp6J

end
