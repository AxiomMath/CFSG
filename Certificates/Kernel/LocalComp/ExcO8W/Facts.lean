module

public import Certificates.Kernel.LocalComp.ExcO8W.Chains
public import CFSG.Certificates.Kernel.SporSch.ChainKConj
public import Certificates.Kernel.LocalComp.ExcO8W.Derivs
public import Certificates.Kernel.LocalComp.ExcGlue
public import Certificates.Kernel.LocalComp.E8Tables
public import CFSG.Certificates.Kernel.LocalCompExcTextSound
public import CFSG.Certificates.Kernel.BfsPinUnpack
public import CFSG.Certificates.Kernel.Spor.RawOrbHead
public import CFSG.Certificates.Kernel.Child3Reps
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.BfsPinSound
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutCheckBase

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.ExcO8W

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Certificates
open CFSG.Sporadic.Schreier.Native CFSG.Monster.B.Mathieu CFSG.ComponentClassification.M12Cover
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch.MOC CFSG.KS.M11
open CFSG.KS.SporSch.CodesImg CFSG.KC.Child3 CFSG.KC.LocalComp.ExcDeriv
open CFSG.ComponentClassification.RankTwoClassical.ExcO8W
open CFSG.ComponentClassification.RankTwoClassical.ExcO8 (fixNum derivCheck)
open CFSG.EvenSmallLie.OmegaEight.Weyl CertificateChecks.KernelLC.ExcGlue
open CertificateChecks.KernelLC (E8.RT E8.NEG)

theorem sz : szOK 240 8 = true := by quickRfl

theorem kId : idK 240 8 (mask 8) = true := by quickRfl

theorem one240 : imageList (1 : Equiv.Perm (Fin 240)) = (unpack 240 8 (pidn 240 8)).toList :=
  one_img kId

theorem cOne : canonK 240 8 (mask 8) (240 * 8) One240 = true := by quickRfl

theorem refls_len : refls.length = 240 := by rw [refls, List.length_map, List.length_range]

theorem reflArrs_get (r : Nat) (hr : r < 240) : reflArrs[r]! = unpack 240 8 (E8.RT r) := by
  rw [reflArrs, getElem!_pos _ r (by simpa using hr), List.getElem_toArray, List.getElem_map,
    List.getElem_range, CertificateChecks.KernelLC.E8.refl_eq r hr]

theorem kRI : allN 240 (fun k => invEqK 240 8 (mask 8) (240 * 8) (E8.RT k) (E8.RT k)) = true := by
  quickRfl

theorem imgR : ∀ j < refls.length, imageList (refls.getD j 1) = (unpack 240 8 (E8.RT j)).toList := by
  intro j hj
  rw [refls_len] at hj
  rw [refls, List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map, List.getElem_range]
  exact permOrId_img (arr := fun k => reflArrs[k]!) reflArrs_get kRI kRI j hj

theorem pR : ∀ j < refls.length, permOK 240 8 (mask 8) (240 * 8) (E8.RT j) (E8.RT j) = true :=
  fun j hj => allN_spec kRI j (lt_of_lt_of_eq hj refls_len)

theorem kZI : invEqK 240 8 (mask 8) (240 * 8) E8.NEG E8.NEG = true := by quickRfl

theorem imgZ : imageList zC = (unpack 240 8 E8.NEG).toList :=
  CertificateChecks.KernelLQT.He4148.imageList_of_rep
    (CertificateChecks.KernelLQT.He4148.unpack_size' _ _ _)
    (CertificateChecks.KernelLQT.He4148.unpack_facts CertificateChecks.KernelLC.E8.neg_eq kZI
      kZI).2.1

theorem corrZ : Corr 240 8 zs [E8.NEG] := List.Forall₂.cons imgZ List.Forall₂.nil

theorem tGens_eq : tGens = tWords.map (evalCodes refls) := by simp only [tGens, tab_eq]

theorem tGens_len : tGens.length = 13 := by rw [tGens_eq, List.length_map]; rfl

theorem kTW : allN tWords.length (fun j => bAnd(lettersK 240 (tWords.getD j []),
    Nat.beq (wordK 240 8 (mask 8) (pidn 240 8) E8.RT E8.RT (tWords.getD j [])) (TQ.S j))) =
    true := by quickRfl

theorem imgT : ∀ j < tGens.length, imageList (tGens.getD j 1) = (unpack 240 8 (TQ.S j)).toList := by
  rw [tGens_eq]
  intro j hj
  exact words_img refls_len sz imgR pR one240 kTW j (by simpa using hj)

theorem kPT : allN 13 (fun j => permOK 240 8 (mask 8) (240 * 8) (TQ.S j) (TQ.SI j)) = true := by
  quickRfl

theorem pT : ∀ j < tGens.length, permOK 240 8 (mask 8) (240 * 8) (TQ.S j) (TQ.SI j) = true :=
  fun j hj => allN_spec kPT j (lt_of_lt_of_eq hj tGens_len)

theorem kX24 : Nat.beq (wordK 240 8 (mask 8) (pidn 240 8) TQ.S TQ.SI [3, 2, 1]) X24 = true := by
  quickRfl
theorem kX60 : Nat.beq (wordK 240 8 (mask 8) (pidn 240 8) TQ.S TQ.SI [1]) X60 = true := by
  quickRfl
theorem kX4 : Nat.beq (wordK 240 8 (mask 8) (pidn 240 8) TQ.S TQ.SI [5, 4, 3, 2, 1]) X4 = true := by
  quickRfl
theorem kX8 : Nat.beq (wordK 240 8 (mask 8) (pidn 240 8) TQ.S TQ.SI [10, 8, 1]) X8 = true := by
  quickRfl

theorem imgX24 : imageList x24 = (unpack 240 8 X24).toList := by
  have h1 : lettersK tGens.length [3, 2, 1] = true := by rw [tGens_len]; quickRfl
  rw [x24, tab_eq, evalCodes_img sz imgT pT one240 h1, Nat.eq_of_beq_eq_true kX24]

theorem imgX60 : imageList x60 = (unpack 240 8 X60).toList := by
  have h1 : lettersK tGens.length [1] = true := by rw [tGens_len]; quickRfl
  rw [x60, tab_eq, evalCodes_img sz imgT pT one240 h1, Nat.eq_of_beq_eq_true kX60]

theorem imgX4 : imageList x4 = (unpack 240 8 X4).toList := by
  have h1 : lettersK tGens.length [5, 4, 3, 2, 1] = true := by rw [tGens_len]; quickRfl
  rw [x4, tab_eq, evalCodes_img sz imgT pT one240 h1, Nat.eq_of_beq_eq_true kX4]

theorem imgX8 : imageList x8 = (unpack 240 8 X8).toList := by
  have h1 : lettersK tGens.length [10, 8, 1] = true := by rw [tGens_len]; quickRfl
  rw [x8, tab_eq, evalCodes_img sz imgT pT one240 h1, Nat.eq_of_beq_eq_true kX8]

theorem corrXs : Corr 240 8 xs [X24, X60, X4, X8] :=
  List.Forall₂.cons imgX24 (List.Forall₂.cons imgX60 (List.Forall₂.cons imgX4
    (List.Forall₂.cons imgX8 List.Forall₂.nil)))

theorem s24Gens_eq : s24Gens = s24Words.map (evalCodes tGens) := by simp only [s24Gens, tab_eq]
theorem s60Gens_eq : s60Gens = s60Words.map (evalCodes tGens) := by simp only [s60Gens, tab_eq]
theorem s4Gens_eq : s4Gens = s4Words.map (evalCodes tGens) := by simp only [s4Gens, tab_eq]
theorem s8Gens_eq : s8Gens = s8Words.map (evalCodes tGens) := by simp only [s8Gens, tab_eq]

theorem s24Gens_len : s24Gens.length = 9 := by rw [s24Gens_eq, List.length_map]; rfl
theorem s60Gens_len : s60Gens.length = 9 := by rw [s60Gens_eq, List.length_map]; rfl
theorem s4Gens_len : s4Gens.length = 8 := by rw [s4Gens_eq, List.length_map]; rfl
theorem s8Gens_len : s8Gens.length = 5 := by rw [s8Gens_eq, List.length_map]; rfl

theorem kS24 : allN s24Words.length (fun j => bAnd(lettersK 13 (s24Words.getD j []),
    Nat.beq (wordK 240 8 (mask 8) (pidn 240 8) TQ.S TQ.SI (s24Words.getD j [])) (Q24.S j))) =
    true := by quickRfl
theorem kS60 : allN s60Words.length (fun j => bAnd(lettersK 13 (s60Words.getD j []),
    Nat.beq (wordK 240 8 (mask 8) (pidn 240 8) TQ.S TQ.SI (s60Words.getD j [])) (Q60.S j))) =
    true := by quickRfl
theorem kS4 : allN s4Words.length (fun j => bAnd(lettersK 13 (s4Words.getD j []),
    Nat.beq (wordK 240 8 (mask 8) (pidn 240 8) TQ.S TQ.SI (s4Words.getD j [])) (Q4.S j))) =
    true := by quickRfl
theorem kS8 : allN s8Words.length (fun j => bAnd(lettersK 13 (s8Words.getD j []),
    Nat.beq (wordK 240 8 (mask 8) (pidn 240 8) TQ.S TQ.SI (s8Words.getD j [])) (Q8.S j))) =
    true := by quickRfl

theorem img24 : ∀ j < s24Gens.length, imageList (s24Gens.getD j 1) =
    (unpack 240 8 (Q24.S j)).toList := by
  rw [s24Gens_eq]
  intro j hj
  exact words_img tGens_len sz imgT pT one240 kS24 j (by simpa using hj)

theorem img60 : ∀ j < s60Gens.length, imageList (s60Gens.getD j 1) =
    (unpack 240 8 (Q60.S j)).toList := by
  rw [s60Gens_eq]
  intro j hj
  exact words_img tGens_len sz imgT pT one240 kS60 j (by simpa using hj)

theorem img4 : ∀ j < s4Gens.length, imageList (s4Gens.getD j 1) =
    (unpack 240 8 (Q4.S j)).toList := by
  rw [s4Gens_eq]
  intro j hj
  exact words_img tGens_len sz imgT pT one240 kS4 j (by simpa using hj)

theorem img8 : ∀ j < s8Gens.length, imageList (s8Gens.getD j 1) =
    (unpack 240 8 (Q8.S j)).toList := by
  rw [s8Gens_eq]
  intro j hj
  exact words_img tGens_len sz imgT pT one240 kS8 j (by simpa using hj)

theorem kP24 : allN 9 (fun j => permOK 240 8 (mask 8) (240 * 8) (Q24.S j) (Q24.SI j)) = true := by
  quickRfl
theorem kP60 : allN 9 (fun j => permOK 240 8 (mask 8) (240 * 8) (Q60.S j) (Q60.SI j)) = true := by
  quickRfl
theorem kP4 : allN 8 (fun j => permOK 240 8 (mask 8) (240 * 8) (Q4.S j) (Q4.SI j)) = true := by
  quickRfl
theorem kP8 : allN 5 (fun j => permOK 240 8 (mask 8) (240 * 8) (Q8.S j) (Q8.SI j)) = true := by
  quickRfl

theorem p24 : ∀ j < s24Gens.length, permOK 240 8 (mask 8) (240 * 8) (Q24.S j) (Q24.SI j) = true :=
  fun j hj => allN_spec kP24 j (lt_of_lt_of_eq hj s24Gens_len)
theorem p60 : ∀ j < s60Gens.length, permOK 240 8 (mask 8) (240 * 8) (Q60.S j) (Q60.SI j) = true :=
  fun j hj => allN_spec kP60 j (lt_of_lt_of_eq hj s60Gens_len)
theorem p4 : ∀ j < s4Gens.length, permOK 240 8 (mask 8) (240 * 8) (Q4.S j) (Q4.SI j) = true :=
  fun j hj => allN_spec kP4 j (lt_of_lt_of_eq hj s4Gens_len)
theorem p8 : ∀ j < s8Gens.length, permOK 240 8 (mask 8) (240 * 8) (Q8.S j) (Q8.SI j) = true :=
  fun j hj => allN_spec kP8 j (lt_of_lt_of_eq hj s8Gens_len)

theorem chainT : ChainK 240 8 tGens tQWords (#v[0, 1, 4, 8, 12, 16, 20] : Vector (Fin 240) 7)
    TQ.S TQ.SI TQ.LR TQ.TR TQ.TRI 22 TQ.BP 15 16 :=
  ⟨by norm_num, by norm_num, by norm_num, imgT, by decide, TQ.head, TQ.hl, by norm_num, TQ.hs⟩

theorem chain24 : ChainK 240 8 s24Gens s24QWords (#v[0, 1, 4, 8, 12, 16, 20] : Vector (Fin 240) 7)
    Q24.S Q24.SI Q24.LR Q24.TR Q24.TRI 17 Q24.BP 15 16 :=
  ⟨by norm_num, by norm_num, by norm_num, img24, by decide, Q24.head, Q24.hl, by norm_num, Q24.hs⟩

theorem chain60 : ChainK 240 8 s60Gens s60QWords (#v[0, 1, 4, 8, 12, 16, 20] : Vector (Fin 240) 7)
    Q60.S Q60.SI Q60.LR Q60.TR Q60.TRI 15 Q60.BP 15 16 :=
  ⟨by norm_num, by norm_num, by norm_num, img60, by decide, Q60.head, Q60.hl, by norm_num, Q60.hs⟩

theorem chain4 : ChainK 240 8 s4Gens s4QWords (#v[0, 1, 4, 8, 12, 16, 20] : Vector (Fin 240) 7)
    Q4.S Q4.SI Q4.LR Q4.TR Q4.TRI 14 Q4.BP 15 16 :=
  ⟨by norm_num, by norm_num, by norm_num, img4, by decide, Q4.head, Q4.hl, by norm_num, Q4.hs⟩

theorem chain8 : ChainK 240 8 s8Gens s8QWords (#v[0, 1, 4, 12, 20] : Vector (Fin 240) 5)
    Q8.S Q8.SI Q8.LR Q8.TR Q8.TRI 10 Q8.BP 15 16 :=
  ⟨by norm_num, by norm_num, by norm_num, img8, by decide, Q8.head, Q8.hl, by norm_num, Q8.hs⟩

theorem kNT : Nat.beq (ordK TQ.LR 7) 8192 = true := by quickRfl
theorem kN24 : Nat.beq (ordK Q24.LR 7) 4096 = true := by quickRfl
theorem kN60 : Nat.beq (ordK Q60.LR 7) 2048 = true := by quickRfl
theorem kN4 : Nat.beq (ordK Q4.LR 7) 2048 = true := by quickRfl
theorem kN8 : Nat.beq (ordK Q8.LR 5) 1024 = true := by quickRfl

theorem kM24 : allN 9 (fun j => Nat.beq (pcomp 240 8 (mask 8) (Q24.S j) X24)
    (pcomp 240 8 (mask 8) X24 (Q24.S j))) = true := by quickRfl
theorem kM60 : allN 9 (fun j => Nat.beq (pcomp 240 8 (mask 8) (Q60.S j) X60)
    (pcomp 240 8 (mask 8) X60 (Q60.S j))) = true := by quickRfl
theorem kM4 : allN 8 (fun j => Nat.beq (pcomp 240 8 (mask 8) (Q4.S j) X4)
    (pcomp 240 8 (mask 8) X4 (Q4.S j))) = true := by quickRfl
theorem kM8 : allN 5 (fun j => Nat.beq (pcomp 240 8 (mask 8) (Q8.S j) X8)
    (pcomp 240 8 (mask 8) X8 (Q8.S j))) = true := by quickRfl

theorem kOkW : tWords.all okW = true := by decide +kernel

theorem chain_check : censusChainCheck = true := by
  obtain ⟨hcT, hoT⟩ : tQ.check = true ∧ tQ.orderCertificate = ordK TQ.LR 7 :=
    chainK_check (by decide) (by decide) chainT
  obtain ⟨hc24, ho24⟩ : s24Q.check = true ∧ s24Q.orderCertificate = ordK Q24.LR 7 :=
    chainK_check (by decide) (by decide) chain24
  obtain ⟨hc60, ho60⟩ : s60Q.check = true ∧ s60Q.orderCertificate = ordK Q60.LR 7 :=
    chainK_check (by decide) (by decide) chain60
  obtain ⟨hc4, ho4⟩ : s4Q.check = true ∧ s4Q.orderCertificate = ordK Q4.LR 7 :=
    chainK_check (by decide) (by decide) chain4
  obtain ⟨hc8, ho8⟩ : s8Q.check = true ∧ s8Q.orderCertificate = ordK Q8.LR 5 :=
    chainK_check (by decide) (by decide) chain8
  unfold censusChainCheck
  rw [hcT, hoT, Nat.eq_of_beq_eq_true kNT, kOkW, hc24, ho24, Nat.eq_of_beq_eq_true kN24,
    comm_all s24Gens_len sz img24 imgX24 kM24, hc60, ho60, Nat.eq_of_beq_eq_true kN60,
    comm_all s60Gens_len sz img60 imgX60 kM60, hc4, ho4, Nat.eq_of_beq_eq_true kN4,
    comm_all s4Gens_len sz img4 imgX4 kM4, hc8, ho8, Nat.eq_of_beq_eq_true kN8,
    comm_all s8Gens_len sz img8 imgX8 kM8]
  rfl

theorem kSig7 : permOK 240 8 (mask 8) (240 * 8) Sig7 Sig7I = true := by quickRfl
theorem kSig5 : permOK 240 8 (mask 8) (240 * 8) Sig5 Sig5I = true := by quickRfl

noncomputable def sg7 : Equiv.Perm (Fin 240) := CFSG.KS.PK.permOf 240 fun i => pg 8 (mask 8) Sig7 i

noncomputable def sg5 : Equiv.Perm (Fin 240) := CFSG.KS.PK.permOf 240 fun i => pg 8 (mask 8) Sig5 i

theorem kJT : allN tGens.length (fun j => Nat.beq (pcomp 240 8 (mask 8) Sig7
    (pcomp 240 8 (mask 8) (TQ.S j) Sig7I)) (CQT.S j)) = true := by
  rw [tGens_len]
  quickRfl
theorem kJ24 : allN s24Gens.length (fun j => Nat.beq (pcomp 240 8 (mask 8) Sig7
    (pcomp 240 8 (mask 8) (Q24.S j) Sig7I)) (CQ24.S j)) = true := by
  rw [s24Gens_len]
  quickRfl
theorem kJ60 : allN s60Gens.length (fun j => Nat.beq (pcomp 240 8 (mask 8) Sig7
    (pcomp 240 8 (mask 8) (Q60.S j) Sig7I)) (CQ60.S j)) = true := by
  rw [s60Gens_len]
  quickRfl
theorem kJ4 : allN s4Gens.length (fun j => Nat.beq (pcomp 240 8 (mask 8) Sig7
    (pcomp 240 8 (mask 8) (Q4.S j) Sig7I)) (CQ4.S j)) = true := by
  rw [s4Gens_len]
  quickRfl
theorem kJ8 : allN s8Gens.length (fun j => Nat.beq (pcomp 240 8 (mask 8) Sig5
    (pcomp 240 8 (mask 8) (Q8.S j) Sig5I)) (CQ8.S j)) = true := by
  rw [s8Gens_len]
  quickRfl

theorem chainCT : ChainK 240 8 (tGens.map fun g => sg7 * g * sg7⁻¹) tQWords
    (#v[0, 1, 2, 3, 4, 5, 6] : Vector (Fin 240) 7) CQT.S CQT.SI CQT.LR CQT.TR CQT.TRI 22 CQT.BP
    15 16 :=
  ⟨by norm_num, by norm_num, by norm_num,
    conj_img (by norm_num) (prep_permOf kSig7).1 (prep_permOf kSig7).2 imgT kJT, by decide,
    CQT.head, CQT.hl, by norm_num, CQT.hs⟩

theorem chainC24 : ChainK 240 8 (s24Gens.map fun g => sg7 * g * sg7⁻¹) s24QWords
    (#v[0, 1, 2, 3, 4, 5, 6] : Vector (Fin 240) 7) CQ24.S CQ24.SI CQ24.LR CQ24.TR CQ24.TRI 17
    CQ24.BP 15 16 :=
  ⟨by norm_num, by norm_num, by norm_num,
    conj_img (by norm_num) (prep_permOf kSig7).1 (prep_permOf kSig7).2 img24 kJ24, by decide,
    CQ24.head, CQ24.hl, by norm_num, CQ24.hs⟩

theorem chainC60 : ChainK 240 8 (s60Gens.map fun g => sg7 * g * sg7⁻¹) s60QWords
    (#v[0, 1, 2, 3, 4, 5, 6] : Vector (Fin 240) 7) CQ60.S CQ60.SI CQ60.LR CQ60.TR CQ60.TRI 15
    CQ60.BP 15 16 :=
  ⟨by norm_num, by norm_num, by norm_num,
    conj_img (by norm_num) (prep_permOf kSig7).1 (prep_permOf kSig7).2 img60 kJ60, by decide,
    CQ60.head, CQ60.hl, by norm_num, CQ60.hs⟩

theorem chainC4 : ChainK 240 8 (s4Gens.map fun g => sg7 * g * sg7⁻¹) s4QWords
    (#v[0, 1, 2, 3, 4, 5, 6] : Vector (Fin 240) 7) CQ4.S CQ4.SI CQ4.LR CQ4.TR CQ4.TRI 14 CQ4.BP
    15 16 :=
  ⟨by norm_num, by norm_num, by norm_num,
    conj_img (by norm_num) (prep_permOf kSig7).1 (prep_permOf kSig7).2 img4 kJ4, by decide,
    CQ4.head, CQ4.hl, by norm_num, CQ4.hs⟩

theorem chainC8 : ChainK 240 8 (s8Gens.map fun g => sg5 * g * sg5⁻¹) s8QWords
    (#v[0, 1, 2, 3, 4] : Vector (Fin 240) 5) CQ8.S CQ8.SI CQ8.LR CQ8.TR CQ8.TRI 10 CQ8.BP 15 16 :=
  ⟨by norm_num, by norm_num, by norm_num,
    conj_img (by norm_num) (prep_permOf kSig5).1 (prep_permOf kSig5).2 img8 kJ8, by decide,
    CQ8.head, CQ8.hl, by norm_num, CQ8.hs⟩

theorem cntT : (cosetOrderTables tQ 1 2).length = RT.N :=
  (chainK_count_conj (by decide) (by decide) (by decide) chainT chainCT (by norm_num)).trans
    ((chainK_cosetCount (by decide) (by decide) chainCT one240 cOne (by norm_num) (by norm_num)
      (by decide) CNT.hc).trans (by decide))
theorem cnt24 : (cosetOrderTables s24Q 1 2).length = R24.N :=
  (chainK_count_conj (by decide) (by decide) (by decide) chain24 chainC24 (by norm_num)).trans
    ((chainK_cosetCount (by decide) (by decide) chainC24 one240 cOne (by norm_num) (by norm_num)
      (by decide) CN24.hc).trans (by decide))
theorem cnt60 : (cosetOrderTables s60Q 1 2).length = R60.N :=
  (chainK_count_conj (by decide) (by decide) (by decide) chain60 chainC60 (by norm_num)).trans
    ((chainK_cosetCount (by decide) (by decide) chainC60 one240 cOne (by norm_num) (by norm_num)
      (by decide) CN60.hc).trans (by decide))
theorem cnt4 : (cosetOrderTables s4Q 1 2).length = R4.N :=
  (chainK_count_conj (by decide) (by decide) (by decide) chain4 chainC4 (by norm_num)).trans
    ((chainK_cosetCount (by decide) (by decide) chainC4 one240 cOne (by norm_num) (by norm_num)
      (by decide) CN4.hc).trans (by decide))
theorem cnt8 : (cosetOrderTables s8Q 1 2).length = R8.N :=
  (chainK_count_conj (by decide) (by decide) (by decide) chain8 chainC8 (by norm_num)).trans
    ((chainK_cosetCount (by decide) (by decide) chainC8 one240 cOne (by norm_num) (by norm_num)
      (by decide) CN8.hc).trans (by decide))

theorem kCT : allN 13 (fun j => bAnd(canonK 240 8 (mask 8) (240 * 8) (TQ.S j),
    canonK 240 8 (mask 8) (240 * 8) (TQ.SI j))) = true := by quickRfl
theorem kC24 : allN 9 (fun j => bAnd(canonK 240 8 (mask 8) (240 * 8) (Q24.S j),
    canonK 240 8 (mask 8) (240 * 8) (Q24.SI j))) = true := by quickRfl
theorem kC60 : allN 9 (fun j => bAnd(canonK 240 8 (mask 8) (240 * 8) (Q60.S j),
    canonK 240 8 (mask 8) (240 * 8) (Q60.SI j))) = true := by quickRfl
theorem kC4 : allN 8 (fun j => bAnd(canonK 240 8 (mask 8) (240 * 8) (Q4.S j),
    canonK 240 8 (mask 8) (240 * 8) (Q4.SI j))) = true := by quickRfl
theorem kC8 : allN 5 (fun j => bAnd(canonK 240 8 (mask 8) (240 * 8) (Q8.S j),
    canonK 240 8 (mask 8) (240 * 8) (Q8.SI j))) = true := by quickRfl

theorem kWT : allN tRepWords.length (fun i => bAnd(lettersK 13 (tRepWords.getD i []),
    Nat.beq (wordK 240 8 (mask 8) (pidn 240 8) TQ.S TQ.SI (tRepWords.getD i []))
      (RT.E (lget RT.OFF i)))) = true := by quickRfl
theorem kW24 : allN r24Words.length (fun i => bAnd(lettersK 9 (r24Words.getD i []),
    Nat.beq (wordK 240 8 (mask 8) (pidn 240 8) Q24.S Q24.SI (r24Words.getD i []))
      (R24.E (lget R24.OFF i)))) = true := by quickRfl
theorem kW60 : allN r60Words.length (fun i => bAnd(lettersK 9 (r60Words.getD i []),
    Nat.beq (wordK 240 8 (mask 8) (pidn 240 8) Q60.S Q60.SI (r60Words.getD i []))
      (R60.E (lget R60.OFF i)))) = true := by quickRfl
theorem kW4 : allN r4Words.length (fun i => bAnd(lettersK 8 (r4Words.getD i []),
    Nat.beq (wordK 240 8 (mask 8) (pidn 240 8) Q4.S Q4.SI (r4Words.getD i []))
      (R4.E (lget R4.OFF i)))) = true := by quickRfl
theorem kW8 : allN r8Words.length (fun i => bAnd(lettersK 5 (r8Words.getD i []),
    Nat.beq (wordK 240 8 (mask 8) (pidn 240 8) Q8.S Q8.SI (r8Words.getD i []))
      (R8.E (lget R8.OFF i)))) = true := by quickRfl

theorem kOT : allN tRepWords.length (fun i => bAnd(canonK 240 8 (mask 8) (240 * 8)
    (RT.E (lget RT.OFF i)), ordIs 240 8 (mask 8) (pidn 240 8) (RT.E (lget RT.OFF i)) (2 - 1))) =
    true := by quickRfl
theorem kO24 : allN r24Words.length (fun i => bAnd(canonK 240 8 (mask 8) (240 * 8)
    (R24.E (lget R24.OFF i)), ordIs 240 8 (mask 8) (pidn 240 8) (R24.E (lget R24.OFF i)) (2 - 1))) =
    true := by quickRfl
theorem kO60 : allN r60Words.length (fun i => bAnd(canonK 240 8 (mask 8) (240 * 8)
    (R60.E (lget R60.OFF i)), ordIs 240 8 (mask 8) (pidn 240 8) (R60.E (lget R60.OFF i)) (2 - 1))) =
    true := by quickRfl
theorem kO4 : allN r4Words.length (fun i => bAnd(canonK 240 8 (mask 8) (240 * 8)
    (R4.E (lget R4.OFF i)), ordIs 240 8 (mask 8) (pidn 240 8) (R4.E (lget R4.OFF i)) (2 - 1))) =
    true := by quickRfl
theorem kO8 : allN r8Words.length (fun i => bAnd(canonK 240 8 (mask 8) (240 * 8)
    (R8.E (lget R8.OFF i)), ordIs 240 8 (mask 8) (pidn 240 8) (R8.E (lget R8.OFF i)) (2 - 1))) =
    true := by quickRfl

theorem kOffT : offOK RT.CS RT.OFF RT.N = true := by quickRfl
theorem kOff24 : offOK R24.CS R24.OFF R24.N = true := by quickRfl
theorem kOff60 : offOK R60.CS R60.OFF R60.N = true := by quickRfl
theorem kOff4 : offOK R4.CS R4.OFF R4.N = true := by quickRfl
theorem kOff8 : offOK R8.CS R8.OFF R8.N = true := by quickRfl

theorem kPosT : CFSG.KC.J2Cover.allL (fun c => Nat.blt 0 c) RT.CS = true := by quickRfl
theorem kPos24 : CFSG.KC.J2Cover.allL (fun c => Nat.blt 0 c) R24.CS = true := by quickRfl
theorem kPos60 : CFSG.KC.J2Cover.allL (fun c => Nat.blt 0 c) R60.CS = true := by quickRfl
theorem kPos4 : CFSG.KC.J2Cover.allL (fun c => Nat.blt 0 c) R4.CS = true := by quickRfl
theorem kPos8 : CFSG.KC.J2Cover.allL (fun c => Nat.blt 0 c) R8.CS = true := by quickRfl

theorem kRT : allN RT.N (repK 240 8 TQ.S TQ.SI 13 RT.CS RT.OFF RT.CI RT.E RT.P RT.L RT.K RT.S
    RT.SI RT.N 600) = true := by quickRfl
theorem kR24 : allN R24.N (repK 240 8 Q24.S Q24.SI 9 R24.CS R24.OFF R24.CI R24.E R24.P R24.L
    R24.K R24.S R24.SI R24.N 600) = true := by quickRfl
theorem kR60 : allN R60.N (repK 240 8 Q60.S Q60.SI 9 R60.CS R60.OFF R60.CI R60.E R60.P R60.L
    R60.K R60.S R60.SI R60.N 600) = true := by quickRfl
theorem kR4 : allN R4.N (repK 240 8 Q4.S Q4.SI 8 R4.CS R4.OFF R4.CI R4.E R4.P R4.L R4.K R4.S
    R4.SI R4.N 600) = true := by quickRfl
theorem kR8 : allN R8.N (repK 240 8 Q8.S Q8.SI 5 R8.CS R8.OFF R8.CI R8.E R8.P R8.L R8.K R8.S
    R8.SI R8.N 600) = true := by quickRfl

theorem tReps_eq : tReps = tRepWords.map (evalCodes tGens) := by simp only [tReps, tab_eq]

theorem imgRT : ∀ i < tRepWords.length, imageList (tReps.getD i 1) =
    (unpack 240 8 (RT.E (lget RT.OFF i))).toList := by
  rw [tReps_eq]
  exact words_img tGens_len sz imgT pT one240 kWT

theorem imgR24 : ∀ i < r24Words.length, imageList (r24Reps.getD i 1) =
    (unpack 240 8 (R24.E (lget R24.OFF i))).toList :=
  words_img s24Gens_len sz img24 p24 one240 kW24
theorem imgR60 : ∀ i < r60Words.length, imageList (r60Reps.getD i 1) =
    (unpack 240 8 (R60.E (lget R60.OFF i))).toList :=
  words_img s60Gens_len sz img60 p60 one240 kW60
theorem imgR4 : ∀ i < r4Words.length, imageList (r4Reps.getD i 1) =
    (unpack 240 8 (R4.E (lget R4.OFF i))).toList :=
  words_img s4Gens_len sz img4 p4 one240 kW4
theorem imgR8 : ∀ i < r8Words.length, imageList (r8Reps.getD i 1) =
    (unpack 240 8 (R8.E (lget R8.OFF i))).toList :=
  words_img s8Gens_len sz img8 p8 one240 kW8

theorem tReps_len : tReps.length = tRepWords.length := by rw [tReps, List.length_map]
theorem r24Reps_len : r24Reps.length = r24Words.length := by rw [r24Reps, List.length_map]
theorem r60Reps_len : r60Reps.length = r60Words.length := by rw [r60Reps, List.length_map]
theorem r4Reps_len : r4Reps.length = r4Words.length := by rw [r4Reps, List.length_map]
theorem r8Reps_len : r8Reps.length = r8Words.length := by rw [r8Reps, List.length_map]

theorem repsT : repsOK 240 (listTables tGens) (listTables (tGens.map (·⁻¹)))
      (cosetOrderTables tQ 1 2) (tReps.map toTable) 600 = true ∧
    repSizes 240 (listTables tGens) (listTables (tGens.map (·⁻¹))) (tReps.map toTable) 600 =
      RT.CS :=
  repsOK_of_img tGens_len (fun j hj => imgT j (lt_of_lt_of_eq hj tGens_len.symm))
    (fun j hj => allN_spec kPT j hj) (fun j hj => and_of_bAnd (allN_spec kCT j hj))
    (tReps_len.trans (by decide)) (fun i hi => imgRT i (lt_of_lt_of_eq hi (by decide))) kOffT
    kPosT cntT (fun j hj => allN_spec kRT j hj)

theorem reps24 : repsOK 240 (listTables s24Gens) (listTables (s24Gens.map (·⁻¹)))
      (cosetOrderTables s24Q 1 2) (r24Reps.map toTable) 600 = true :=
  (repsOK_of_img s24Gens_len (fun j hj => img24 j (lt_of_lt_of_eq hj s24Gens_len.symm))
    (fun j hj => allN_spec kP24 j hj) (fun j hj => and_of_bAnd (allN_spec kC24 j hj))
    (r24Reps_len.trans (by decide)) (fun i hi => imgR24 i (lt_of_lt_of_eq hi (by decide))) kOff24
    kPos24 cnt24 (fun j hj => allN_spec kR24 j hj)).1

theorem reps60 : repsOK 240 (listTables s60Gens) (listTables (s60Gens.map (·⁻¹)))
      (cosetOrderTables s60Q 1 2) (r60Reps.map toTable) 600 = true :=
  (repsOK_of_img s60Gens_len (fun j hj => img60 j (lt_of_lt_of_eq hj s60Gens_len.symm))
    (fun j hj => allN_spec kP60 j hj) (fun j hj => and_of_bAnd (allN_spec kC60 j hj))
    (r60Reps_len.trans (by decide)) (fun i hi => imgR60 i (lt_of_lt_of_eq hi (by decide))) kOff60
    kPos60 cnt60 (fun j hj => allN_spec kR60 j hj)).1

theorem reps4 : repsOK 240 (listTables s4Gens) (listTables (s4Gens.map (·⁻¹)))
      (cosetOrderTables s4Q 1 2) (r4Reps.map toTable) 600 = true :=
  (repsOK_of_img s4Gens_len (fun j hj => img4 j (lt_of_lt_of_eq hj s4Gens_len.symm))
    (fun j hj => allN_spec kP4 j hj) (fun j hj => and_of_bAnd (allN_spec kC4 j hj))
    (r4Reps_len.trans (by decide)) (fun i hi => imgR4 i (lt_of_lt_of_eq hi (by decide))) kOff4
    kPos4 cnt4 (fun j hj => allN_spec kR4 j hj)).1

theorem reps8 : repsOK 240 (listTables s8Gens) (listTables (s8Gens.map (·⁻¹)))
      (cosetOrderTables s8Q 1 2) (r8Reps.map toTable) 600 = true :=
  (repsOK_of_img s8Gens_len (fun j hj => img8 j (lt_of_lt_of_eq hj s8Gens_len.symm))
    (fun j hj => allN_spec kP8 j hj) (fun j hj => and_of_bAnd (allN_spec kC8 j hj))
    (r8Reps_len.trans (by decide)) (fun i hi => imgR8 i (lt_of_lt_of_eq hi (by decide))) kOff8
    kPos8 cnt8 (fun j hj => allN_spec kR8 j hj)).1

theorem cover_check : censusCoverCheck = true := by
  unfold censusCoverCheck
  rw [repsT.1, reps24, reps60, reps4, reps8, ord_all sz (e := 2) tReps_len imgRT kOT (by norm_num),
    ord_all sz (e := 2) r24Reps_len imgR24 kO24 (by norm_num),
    ord_all sz (e := 2) r60Reps_len imgR60 kO60 (by norm_num),
    ord_all sz (e := 2) r4Reps_len imgR4 kO4 (by norm_num),
    ord_all sz (e := 2) r8Reps_len imgR8 kO8 (by norm_num)]
  rfl

theorem kAR : allN 240 (fun k => bAnd(permOK 240 8 (mask 8) (240 * 8) (E8.RT k)
    (pinvS 240 8 (mask 8) (E8.RT k)), permOK 240 8 (mask 8) (240 * 8)
    (pinvS 240 8 (mask 8) (E8.RT k)) (E8.RT k))) = true := by quickRfl

theorem z1 : permOK 240 8 (mask 8) (240 * 8) E8.NEG (pinvS 240 8 (mask 8) E8.NEG) = true := by
  quickRfl

theorem z2 : permOK 240 8 (mask 8) (240 * 8) (pinvS 240 8 (mask 8) E8.NEG) E8.NEG = true := by
  quickRfl

theorem arr_check : censusArrCheck = true := by
  unfold censusArrCheck
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range]
  refine ⟨⟨fun k hk => ?_, ?_⟩, ?_⟩
  · obtain ⟨p1, p2⟩ := and_of_bAnd (allN_spec kAR k hk)
    rw [reflArrs_get k hk, CFSG.KC.BfsPin.invCand_unpack p1]
    exact ⟨Orb.isInvA_unpack p1, Orb.isInvA_unpack p2⟩
  · rw [CertificateChecks.KernelLC.E8.neg_eq, CFSG.KC.BfsPin.invCand_unpack z1]
    exact Orb.isInvA_unpack z1
  · rw [CertificateChecks.KernelLC.E8.neg_eq, CFSG.KC.BfsPin.invCand_unpack z1]
    exact Orb.isInvA_unpack z2

@[expose] noncomputable def fusOK (R : Nat) (e : ℕ × List ℤ) : Bool :=
  Prod.rec (motive := fun _ => Bool) (fun k wd =>
    bIf(Nat.beq k 0, Nat.beq R E8.NEG,
      bAnd(okW wd, bAnd(Nat.ble k 4, bAnd(lettersK 240 wd, bAnd(permOK 240 8 (mask 8) (240 * 8)
        (wordK 240 8 (mask 8) (pidn 240 8) E8.RT E8.RT wd)
        (pinvS 240 8 (mask 8) (wordK 240 8 (mask 8) (pidn 240 8) E8.RT E8.RT wd)),
      Nat.beq (pcomp 240 8 (mask 8) (pcomp 240 8 (mask 8)
        (wordK 240 8 (mask 8) (pidn 240 8) E8.RT E8.RT wd) R)
        (pinvS 240 8 (mask 8) (wordK 240 8 (mask 8) (pidn 240 8) E8.RT E8.RT wd)))
        (lget [X24, X60, X4, X8] (Nat.sub k 1)))))))) e

theorem kFus : allN tRepWords.length (fun i => fusOK (RT.E (lget RT.OFF i))
    (fusion.getD i (0, []))) = true := by quickRfl

theorem kSize : allN tRepWords.length (fun i => minK (fixCntK 8 (mask 8) (RT.E (lget RT.OFF i)) 240)
    (lget RT.CS i) (xsFix.zip xsMin)) = true := by quickRfl

theorem kF24 : Nat.beq (fixCntK 8 (mask 8) X24 240) 24 = true := by quickRfl
theorem kF60 : Nat.beq (fixCntK 8 (mask 8) X60 240) 60 = true := by quickRfl
theorem kF4 : Nat.beq (fixCntK 8 (mask 8) X4 240) 4 = true := by quickRfl
theorem kF8 : Nat.beq (fixCntK 8 (mask 8) X8 240) 8 = true := by quickRfl

theorem kNe24 : neCK 240 8 (mask 8) (240 * 8) X24 E8.NEG = true := by quickRfl
theorem kNe60 : neCK 240 8 (mask 8) (240 * 8) X60 E8.NEG = true := by quickRfl
theorem kNe4 : neCK 240 8 (mask 8) (240 * 8) X4 E8.NEG = true := by quickRfl
theorem kNe8 : neCK 240 8 (mask 8) (240 * 8) X8 E8.NEG = true := by quickRfl

theorem c24 : canonK 240 8 (mask 8) (240 * 8) X24 = true := by quickRfl
theorem c60 : canonK 240 8 (mask 8) (240 * 8) X60 = true := by quickRfl
theorem c4 : canonK 240 8 (mask 8) (240 * 8) X4 = true := by quickRfl
theorem c8 : canonK 240 8 (mask 8) (240 * 8) X8 = true := by quickRfl
theorem o24 : ordIs 240 8 (mask 8) (pidn 240 8) X24 (2 - 1) = true := by quickRfl
theorem o60 : ordIs 240 8 (mask 8) (pidn 240 8) X60 (2 - 1) = true := by quickRfl
theorem o4 : ordIs 240 8 (mask 8) (pidn 240 8) X4 (2 - 1) = true := by quickRfl
theorem o8 : ordIs 240 8 (mask 8) (pidn 240 8) X8 (2 - 1) = true := by quickRfl

theorem fix_eq {g : Equiv.Perm (Fin 240)} {P : Nat} (hg : imageList g = (unpack 240 8 P).toList) :
    fixNum g = fixCntK 8 (mask 8) P 240 := by
  unfold fixNum
  exact countFix_eq hg

theorem fusion_check : censusFusionCheck = true := by
  unfold censusFusionCheck
  have hfix : xs.map fixNum = xsFix := by
    simp only [xs, List.map_cons, List.map_nil, fix_eq imgX24, fix_eq imgX60, fix_eq imgX4,
      fix_eq imgX8, Nat.eq_of_beq_eq_true kF24, Nat.eq_of_beq_eq_true kF60,
      Nat.eq_of_beq_eq_true kF4, Nat.eq_of_beq_eq_true kF8]
    rfl
  have hxs : xs.all (fun x => ordTest 240 2 (toTable x) && !schreierPermEq x zC) = true := by
    simp only [xs, List.all_cons, List.all_nil, ordTest_of_ordIs sz imgX24 c24 (by norm_num) o24,
      ordTest_of_ordIs sz imgX60 c60 (by norm_num) o60,
      ordTest_of_ordIs sz imgX4 c4 (by norm_num) o4, ordTest_of_ordIs sz imgX8 c8 (by norm_num) o8,
      schreierPermEq_of_neCK imgX24 imgZ kNe24, schreierPermEq_of_neCK imgX60 imgZ kNe60,
      schreierPermEq_of_neCK imgX4 imgZ kNe4, schreierPermEq_of_neCK imgX8 imgZ kNe8]
    rfl
  have hfus : (tReps.zip fusion).all (fun p =>
      if p.2.1 = 0 then schreierPermEq p.1 zC
      else
        let g := tab (evalCodes refls p.2.2)
        okW p.2.2 && decide (p.2.1 ≤ xs.length) &&
          schreierPermEq (g * p.1 * g⁻¹) (xs.getD (p.2.1 - 1) 1)) = true := by
    refine all_zip_of fun i hl hm => ?_
    have hi : i < tRepWords.length := lt_of_lt_of_eq hl tReps_len
    have hr := imgRT i hi
    rw [List.getD_eq_getElem _ _ hl] at hr
    have hf := allN_spec kFus i hi
    rw [List.getD_eq_getElem _ _ hm] at hf
    generalize fusion[i] = e at hf ⊢
    obtain ⟨k, wd⟩ := e
    change bIf(Nat.beq k 0, Nat.beq (RT.E (lget RT.OFF i)) E8.NEG, _) = true at hf
    dsimp only
    by_cases hk : k = 0
    · subst hk
      rw [ite_eq_left rfl]
      exact schreierPermEq_of_img hr (Nat.eq_of_beq_eq_true hf ▸ imgZ)
    · have hb : Nat.beq k 0 = false := by
        cases e : Nat.beq k 0
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true e) hk
      rw [hb] at hf
      obtain ⟨h0, hf⟩ := and_of_bAnd hf
      obtain ⟨hk4, hf⟩ := and_of_bAnd hf
      obtain ⟨h1, hf⟩ := and_of_bAnd hf
      obtain ⟨h2, h3⟩ := and_of_bAnd hf
      rw [ite_eq_right hk, tab_eq]
      have h1' : lettersK refls.length wd = true := by rw [refls_len]; exact h1
      have hw := evalCodes_img sz imgR pR one240 h1'
      have himg := mulK_rep sz (mulK_rep sz hw hr) (invK_rep hw h2)
      rw [Nat.eq_of_beq_eq_true h3] at himg
      have hk' : k ≤ 4 := Nat.le_of_ble_eq_true hk4
      have hxl : k - 1 < xs.length := by
        change k - 1 < 4
        omega
      have hx := corrXs.getD (k - 1) hxl
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨⟨h0, hk'⟩, schreierPermEq_of_img himg hx⟩
  have hsizes : (tReps.zip (repSizes 240 (listTables tGens) (listTables (tGens.map (·⁻¹)))
      (tReps.map toTable) 600)).all (fun p =>
      (xsFix.zip xsMin).all fun q => fixNum p.1 != q.1 || decide (q.2 ≤ p.2)) = true := by
    rw [repsT.2]
    refine all_zip_of fun i hl hm => ?_
    have hi : i < tRepWords.length := lt_of_lt_of_eq hl tReps_len
    have hr := imgRT i hi
    rw [List.getD_eq_getElem _ _ hl] at hr
    have hs := allN_spec kSize i hi
    rw [lget_eq RT.CS i, List.getD_eq_getElem _ _ hm] at hs
    dsimp only
    rw [fix_eq hr]
    exact minK_spec hs
  rw [hfix, hxs, hfus, hsizes]
  rw [tReps_len]
  rfl

theorem kT24 : CFSG.KC.G13.charsEq T24.chars (derivsC d24L) = true := by quickRfl
theorem kT60 : CFSG.KC.G13.charsEq T60.chars (derivsC d60L) = true := by quickRfl
theorem kT4 : CFSG.KC.G13.charsEq T4.chars (derivsC d4L) = true := by quickRfl
theorem kT8 : CFSG.KC.G13.charsEq T8.chars (derivsC d8L) = true := by quickRfl

theorem d24_eq : d24 = d24L := by
  rw [d24, T24.eq, CFSG.KC.G13.charsEq_sound kT24]
  exact parseDerivs_derivsC_o8 (List.cons_ne_nil _ _)

theorem d60_eq : d60 = d60L := by
  rw [d60, T60.eq, CFSG.KC.G13.charsEq_sound kT60]
  exact parseDerivs_derivsC_o8 (List.cons_ne_nil _ _)

theorem d4_eq : d4 = d4L := by
  rw [d4, T4.eq, CFSG.KC.G13.charsEq_sound kT4]
  exact parseDerivs_derivsC_o8 (List.cons_ne_nil _ _)

theorem d8_eq : d8 = d8L := by
  rw [d8, T8.eq, CFSG.KC.G13.charsEq_sound kT8]
  exact parseDerivs_derivsC_o8 (List.cons_ne_nil _ _)

theorem kD24 : allN r24Words.length (fun i => bIf(Nat.beq (R24.E (lget R24.OFF i)) X24, true,
    derivK 240 8 (mask 8) (240 * 8) (pidn 240 8) E8.RT E8.RT 240 okW [E8.NEG] []
      (d24L.getD i []) [X24, R24.E (lget R24.OFF i)])) = true := by quickRfl

theorem kD60 : allN r60Words.length (fun i => bIf(Nat.beq (R60.E (lget R60.OFF i)) X60, true,
    derivK 240 8 (mask 8) (240 * 8) (pidn 240 8) E8.RT E8.RT 240 okW [E8.NEG] [24]
      (d60L.getD i []) [X60, R60.E (lget R60.OFF i)])) = true := by quickRfl

theorem kD4 : allN r4Words.length (fun i => bIf(Nat.beq (R4.E (lget R4.OFF i)) X4, true,
    derivK 240 8 (mask 8) (240 * 8) (pidn 240 8) E8.RT E8.RT 240 okW [E8.NEG] [24, 60]
      (d4L.getD i []) [X4, R4.E (lget R4.OFF i)])) = true := by quickRfl

theorem kD8 : allN r8Words.length (fun i => bIf(Nat.beq (R8.E (lget R8.OFF i)) X8, true,
    derivK 240 8 (mask 8) (240 * 8) (pidn 240 8) E8.RT E8.RT 240 okW [E8.NEG] [24, 60, 4]
      (d8L.getD i []) [X8, R8.E (lget R8.OFF i)])) = true := by quickRfl

theorem deriv_check : censusDerivCheck = true := by
  unfold censusDerivCheck
  rw [d24_eq, d60_eq, d4_eq, d8_eq,
    derivs_all_o8 sz one240 refls_len imgR pR corrZ imgX24 r24Reps_len imgR24 kD24,
    derivs_all_o8 sz one240 refls_len imgR pR corrZ imgX60 r60Reps_len imgR60 kD60,
    derivs_all_o8 sz one240 refls_len imgR pR corrZ imgX4 r4Reps_len imgR4 kD4,
    derivs_all_o8 sz one240 refls_len imgR pR corrZ imgX8 r8Reps_len imgR8 kD8,
    r24Reps_len, r60Reps_len, r4Reps_len, r8Reps_len]
  rfl

theorem facts : censusArrCheck = true ∧ censusChainCheck = true ∧ censusCoverCheck = true ∧
    censusFusionCheck = true ∧ censusDerivCheck = true :=
  ⟨arr_check, chain_check, cover_check, fusion_check, deriv_check⟩

end CertificateChecks.KernelLC.ExcO8W

end
