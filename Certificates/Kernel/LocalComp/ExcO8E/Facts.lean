module

public import Certificates.Kernel.LocalComp.ExcO8E.Bind
public import Certificates.Kernel.LocalComp.ExcO8E.DataSE
public import Certificates.Kernel.LocalComp.ExcO8E.Data48
public import Certificates.Kernel.LocalComp.ExcO8E.Data16
public import Certificates.Kernel.LocalComp.ExcO8E.Derivs
public import CFSG.Certificates.Kernel.LocalCompExcTextSound
public import CFSG.Certificates.Kernel.BfsPinUnpack
public import CFSG.Certificates.Kernel.Spor.RawOrbHead
public import CFSG.Certificates.Kernel.Child3Reps
public import Certificates.Kernel.LocalComp.ExcO8E.REa
public import Certificates.Kernel.LocalComp.ExcO8E.REb
public import Certificates.Kernel.LocalComp.ExcO8E.R48s
public import Certificates.Kernel.LocalComp.ExcO8E.R16s
public import Certificates.Kernel.LocalComp.SliceJoin
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Spor.RawOrbGrp

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.ExcO8E

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Certificates
open CFSG.Sporadic.Schreier.Native CFSG.Monster.B.Mathieu CFSG.ComponentClassification.M12Cover
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch.MOC CFSG.KS.M11
open CFSG.KS.SporSch.CodesImg CFSG.KC.Child3 CFSG.KC.LocalComp.ExcDeriv
open CFSG.ComponentClassification.RankTwoClassical.ExcO8E
open CFSG.ComponentClassification.RankTwoClassical.ExcO8 (fixNum derivCheck)
open CFSG.EvenSmallLie.OmegaEight.Weyl CertificateChecks.KernelLC.ExcGlue
open CertificateChecks.KernelLC.Slices

@[expose] noncomputable def ELI (i : Nat) : Nat := pinvS 480 9 (mask 9) (lget EL i)

theorem sz : szOK 480 9 = true := by quickRfl

theorem kId : idK 480 9 (mask 9) = true := by quickRfl

theorem one480 : imageList (1 : Equiv.Perm (Fin 480)) = (unpack 480 9 (pidn 480 9)).toList :=
  one_img kId

theorem cOne : canonK 480 9 (mask 9) (480 * 9) One480 = true := by quickRfl

theorem eGens_len : eGens.length = 8 := by rw [eGens, List.length_map, List.length_range]

theorem kEI1 : allN 8 (fun i => invEqK 480 9 (mask 9) (480 * 9) (lget EL i) (ELI i)) = true := by
  quickRfl

theorem kEI2 : allN 8 (fun i => invEqK 480 9 (mask 9) (480 * 9) (ELI i) (lget EL i)) = true := by
  quickRfl

theorem imgE : ∀ j < eGens.length, imageList (eGens.getD j 1) = (unpack 480 9 (lget EL j)).toList := by
  intro j hj
  rw [eGens_len] at hj
  rw [eGens, List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map, List.getElem_range]
  exact permOrId_img (arr := fun k => eArrs[k]!) eArrs_eq kEI1 kEI2 j hj

theorem pE : ∀ j < eGens.length, permOK 480 9 (mask 9) (480 * 9) (lget EL j) (ELI j) = true :=
  fun j hj => allN_spec kEI1 j (lt_of_lt_of_eq hj eGens_len)

theorem kZI1 : invEqK 480 9 (mask 9) (480 * 9) Z1 Z1 = true := by quickRfl
theorem kZI2 : invEqK 480 9 (mask 9) (480 * 9) Z2 Z2 = true := by quickRfl
theorem kZI3 : invEqK 480 9 (mask 9) (480 * 9) Z3 Z3 = true := by quickRfl

theorem imgZ1 : imageList z1 = (unpack 480 9 Z1).toList :=
  CertificateChecks.KernelLQT.He4148.imageList_of_rep
    (CertificateChecks.KernelLQT.He4148.unpack_size' _ _ _)
    (CertificateChecks.KernelLQT.He4148.unpack_facts z1_eq kZI1 kZI1).2.1
theorem imgZ2 : imageList z2 = (unpack 480 9 Z2).toList :=
  CertificateChecks.KernelLQT.He4148.imageList_of_rep
    (CertificateChecks.KernelLQT.He4148.unpack_size' _ _ _)
    (CertificateChecks.KernelLQT.He4148.unpack_facts z2_eq kZI2 kZI2).2.1
theorem imgZ3 : imageList z3 = (unpack 480 9 Z3).toList :=
  CertificateChecks.KernelLQT.He4148.imageList_of_rep
    (CertificateChecks.KernelLQT.He4148.unpack_size' _ _ _)
    (CertificateChecks.KernelLQT.He4148.unpack_facts z3_eq kZI3 kZI3).2.1

theorem corrZ : Corr 480 9 zs [Z1, Z2, Z3] :=
  List.Forall₂.cons imgZ1 (List.Forall₂.cons imgZ2 (List.Forall₂.cons imgZ3 List.Forall₂.nil))

theorem seGens_eq : seGens = seWords.map (evalCodes eGens) := by
  simp only [seGens, seWords, tab_eq]

theorem seGens_len : seGens.length = 4 := by rw [seGens_eq, List.length_map]; rfl

theorem kSEW : allN seWords.length (fun j => bAnd(lettersK 8 (seWords.getD j []),
    Nat.beq (wordK 480 9 (mask 9) (pidn 480 9) (lget EL) ELI (seWords.getD j [])) (SE.S j))) =
    true := by quickRfl

theorem imgSE : ∀ j < seGens.length, imageList (seGens.getD j 1) = (unpack 480 9 (SE.S j)).toList := by
  rw [seGens_eq]
  intro j hj
  exact words_img eGens_len sz imgE pE one480 kSEW j (by simpa using hj)

theorem kPSE : allN 4 (fun j => permOK 480 9 (mask 9) (480 * 9) (SE.S j) (SE.SI j)) = true := by
  quickRfl

theorem pSE : ∀ j < seGens.length, permOK 480 9 (mask 9) (480 * 9) (SE.S j) (SE.SI j) = true :=
  fun j hj => allN_spec kPSE j (lt_of_lt_of_eq hj seGens_len)

theorem kX48 : Nat.beq (wordK 480 9 (mask 9) (pidn 480 9) SE.S SE.SI
    [4, 3, 2, 4, 3, 1, 2, 4, 3, 1, 2, 4, 3, 1, 2, 1]) X48 = true := by quickRfl
theorem kX16 : Nat.beq (wordK 480 9 (mask 9) (pidn 480 9) SE.S SE.SI
    [4, 2, 3, 1, 2, 4, 1, 2, 3, 1, 2, 1]) X16 = true := by quickRfl

theorem imgX48 : imageList x48 = (unpack 480 9 X48).toList := by
  have h1 : lettersK seGens.length [4, 3, 2, 4, 3, 1, 2, 4, 3, 1, 2, 4, 3, 1, 2, 1] = true := by
    rw [seGens_len]; quickRfl
  rw [x48, tab_eq, evalCodes_img sz imgSE pSE one480 h1, Nat.eq_of_beq_eq_true kX48]

theorem imgX16 : imageList x16 = (unpack 480 9 X16).toList := by
  have h1 : lettersK seGens.length [4, 2, 3, 1, 2, 4, 1, 2, 3, 1, 2, 1] = true := by
    rw [seGens_len]; quickRfl
  rw [x16, tab_eq, evalCodes_img sz imgSE pSE one480 h1, Nat.eq_of_beq_eq_true kX16]

theorem corrXs : Corr 480 9 xs [X48, X16] :=
  List.Forall₂.cons imgX48 (List.Forall₂.cons imgX16 List.Forall₂.nil)

theorem s48Gens_eq : s48Gens = s48Words.map (evalCodes seGens) := by simp only [s48Gens, tab_eq]
theorem s16Gens_eq : s16Gens = s16Words.map (evalCodes seGens) := by simp only [s16Gens, tab_eq]

theorem s48Gens_len : s48Gens.length = 6 := by rw [s48Gens_eq, List.length_map]; rfl
theorem s16Gens_len : s16Gens.length = 5 := by rw [s16Gens_eq, List.length_map]; rfl

theorem kS48 : allN s48Words.length (fun j => bAnd(lettersK 4 (s48Words.getD j []),
    Nat.beq (wordK 480 9 (mask 9) (pidn 480 9) SE.S SE.SI (s48Words.getD j [])) (Q48.S j))) =
    true := by quickRfl
theorem kS16 : allN s16Words.length (fun j => bAnd(lettersK 4 (s16Words.getD j []),
    Nat.beq (wordK 480 9 (mask 9) (pidn 480 9) SE.S SE.SI (s16Words.getD j [])) (Q16.S j))) =
    true := by quickRfl

theorem img48 : ∀ j < s48Gens.length, imageList (s48Gens.getD j 1) =
    (unpack 480 9 (Q48.S j)).toList := by
  rw [s48Gens_eq]
  intro j hj
  exact words_img seGens_len sz imgSE pSE one480 kS48 j (by simpa using hj)

theorem img16 : ∀ j < s16Gens.length, imageList (s16Gens.getD j 1) =
    (unpack 480 9 (Q16.S j)).toList := by
  rw [s16Gens_eq]
  intro j hj
  exact words_img seGens_len sz imgSE pSE one480 kS16 j (by simpa using hj)

theorem kP48 : allN 6 (fun j => permOK 480 9 (mask 9) (480 * 9) (Q48.S j) (Q48.SI j)) = true := by
  quickRfl
theorem kP16 : allN 5 (fun j => permOK 480 9 (mask 9) (480 * 9) (Q16.S j) (Q16.SI j)) = true := by
  quickRfl

theorem p48 : ∀ j < s48Gens.length, permOK 480 9 (mask 9) (480 * 9) (Q48.S j) (Q48.SI j) = true :=
  fun j hj => allN_spec kP48 j (lt_of_lt_of_eq hj s48Gens_len)
theorem p16 : ∀ j < s16Gens.length, permOK 480 9 (mask 9) (480 * 9) (Q16.S j) (Q16.SI j) = true :=
  fun j hj => allN_spec kP16 j (lt_of_lt_of_eq hj s16Gens_len)

theorem chainSE : ChainK 480 9 seGens seQWords (#v[0, 1, 4, 240] : Vector (Fin 480) 4)
    SE.S SE.SI SE.LR SE.TR SE.TRI 9 SE.BP 30 16 :=
  ⟨by norm_num, by norm_num, by norm_num, imgSE, by decide, SE.head, SE.hl, by norm_num, SE.hs⟩

theorem chain48 : ChainK 480 9 s48Gens s48QWords (#v[0, 1, 240] : Vector (Fin 480) 3)
    Q48.S Q48.SI Q48.LR Q48.TR Q48.TRI 11 Q48.BP 30 16 :=
  ⟨by norm_num, by norm_num, by norm_num, img48, by decide, Q48.head, Q48.hl, by norm_num, Q48.hs⟩

theorem chain16 : ChainK 480 9 s16Gens s16QWords (#v[0, 1, 4, 240] : Vector (Fin 480) 4)
    Q16.S Q16.SI Q16.LR Q16.TR Q16.TRI 7 Q16.BP 30 16 :=
  ⟨by norm_num, by norm_num, by norm_num, img16, by decide, Q16.head, Q16.hl, by norm_num, Q16.hs⟩

theorem kNE : Nat.beq (ordK SE.LR 4) 16384 = true := by quickRfl
theorem kN48 : Nat.beq (ordK Q48.LR 3) 4096 = true := by quickRfl
theorem kN16 : Nat.beq (ordK Q16.LR 4) 1024 = true := by quickRfl

theorem kM48 : allN 6 (fun j => Nat.beq (pcomp 480 9 (mask 9) (Q48.S j) X48)
    (pcomp 480 9 (mask 9) X48 (Q48.S j))) = true := by quickRfl
theorem kM16 : allN 5 (fun j => Nat.beq (pcomp 480 9 (mask 9) (Q16.S j) X16)
    (pcomp 480 9 (mask 9) X16 (Q16.S j))) = true := by quickRfl

theorem chain_check : censusChainCheck = true := by
  obtain ⟨hcE, hoE⟩ : seQ.check = true ∧ seQ.orderCertificate = ordK SE.LR 4 :=
    chainK_check (by decide) (by decide) chainSE
  obtain ⟨hc48, ho48⟩ : s48Q.check = true ∧ s48Q.orderCertificate = ordK Q48.LR 3 :=
    chainK_check (by decide) (by decide) chain48
  obtain ⟨hc16, ho16⟩ : s16Q.check = true ∧ s16Q.orderCertificate = ordK Q16.LR 4 :=
    chainK_check (by decide) (by decide) chain16
  unfold censusChainCheck
  rw [hcE, hoE, Nat.eq_of_beq_eq_true kNE, hc48, ho48, Nat.eq_of_beq_eq_true kN48,
    comm_all s48Gens_len sz img48 imgX48 kM48, hc16, ho16, Nat.eq_of_beq_eq_true kN16,
    comm_all s16Gens_len sz img16 imgX16 kM16]
  rfl

theorem cntE : (cosetOrderTables seQ 1 2).length = RE.N :=
  (chainK_cosetCount (by decide) (by decide) chainSE one480 cOne (by norm_num) (by norm_num)
    (by decide) NE.hc).trans (by decide)
theorem cnt48 : (cosetOrderTables s48Q 1 2).length = R48.N :=
  (chainK_cosetCount (by decide) (by decide) chain48 one480 cOne (by norm_num) (by norm_num)
    (by decide) N48.hc).trans (by decide)
theorem cnt16 : (cosetOrderTables s16Q 1 2).length = R16.N :=
  (chainK_cosetCount (by decide) (by decide) chain16 one480 cOne (by norm_num) (by norm_num)
    (by decide) N16.hc).trans (by decide)

theorem kCE : allN 4 (fun j => bAnd(canonK 480 9 (mask 9) (480 * 9) (SE.S j),
    canonK 480 9 (mask 9) (480 * 9) (SE.SI j))) = true := by quickRfl
theorem kC48 : allN 6 (fun j => bAnd(canonK 480 9 (mask 9) (480 * 9) (Q48.S j),
    canonK 480 9 (mask 9) (480 * 9) (Q48.SI j))) = true := by quickRfl
theorem kC16 : allN 5 (fun j => bAnd(canonK 480 9 (mask 9) (480 * 9) (Q16.S j),
    canonK 480 9 (mask 9) (480 * 9) (Q16.SI j))) = true := by quickRfl

theorem kWE : allN seRepWords.length (fun i => bAnd(lettersK 4 (seRepWords.getD i []),
    Nat.beq (wordK 480 9 (mask 9) (pidn 480 9) SE.S SE.SI (seRepWords.getD i []))
      (RE.E (lget RE.OFF i)))) = true := by quickRfl
theorem kW48 : allN r48Words.length (fun i => bAnd(lettersK 6 (r48Words.getD i []),
    Nat.beq (wordK 480 9 (mask 9) (pidn 480 9) Q48.S Q48.SI (r48Words.getD i []))
      (R48.E (lget R48.OFF i)))) = true := by quickRfl
theorem kW16 : allN r16Words.length (fun i => bAnd(lettersK 5 (r16Words.getD i []),
    Nat.beq (wordK 480 9 (mask 9) (pidn 480 9) Q16.S Q16.SI (r16Words.getD i []))
      (R16.E (lget R16.OFF i)))) = true := by quickRfl

theorem kOE : allN seRepWords.length (fun i => bAnd(canonK 480 9 (mask 9) (480 * 9)
    (RE.E (lget RE.OFF i)), ordIs 480 9 (mask 9) (pidn 480 9) (RE.E (lget RE.OFF i)) (2 - 1))) =
    true := by quickRfl
theorem kO48 : allN r48Words.length (fun i => bAnd(canonK 480 9 (mask 9) (480 * 9)
    (R48.E (lget R48.OFF i)), ordIs 480 9 (mask 9) (pidn 480 9) (R48.E (lget R48.OFF i)) (2 - 1))) =
    true := by quickRfl
theorem kO16 : allN r16Words.length (fun i => bAnd(canonK 480 9 (mask 9) (480 * 9)
    (R16.E (lget R16.OFF i)), ordIs 480 9 (mask 9) (pidn 480 9) (R16.E (lget R16.OFF i)) (2 - 1))) =
    true := by quickRfl

theorem kOffE : offOK RE.CS RE.OFF RE.N = true := by quickRfl
theorem kOff48 : offOK R48.CS R48.OFF R48.N = true := by quickRfl
theorem kOff16 : offOK R16.CS R16.OFF R16.N = true := by quickRfl

theorem kPosE : CFSG.KC.J2Cover.allL (fun c => Nat.blt 0 c) RE.CS = true := by quickRfl
theorem kPos48 : CFSG.KC.J2Cover.allL (fun c => Nat.blt 0 c) R48.CS = true := by quickRfl
theorem kPos16 : CFSG.KC.J2Cover.allL (fun c => Nat.blt 0 c) R16.CS = true := by quickRfl

theorem kRE : ∀ j < RE.N, repK 480 9 SE.S SE.SI 4 RE.CS RE.OFF RE.CI RE.E RE.P RE.L RE.K RE.S
    RE.SI RE.N 600 j = true :=
  of_slices (R := repK 480 9 SE.S SE.SI 4 RE.CS RE.OFF RE.CI RE.E RE.P RE.L RE.K RE.S RE.SI RE.N
    600) (join REa.all REb.all) (by decide)
theorem kR48 : ∀ j < R48.N, repK 480 9 Q48.S Q48.SI 6 R48.CS R48.OFF R48.CI R48.E R48.P R48.L
    R48.K R48.S R48.SI R48.N 600 j = true :=
  of_slices (R := repK 480 9 Q48.S Q48.SI 6 R48.CS R48.OFF R48.CI R48.E R48.P R48.L R48.K R48.S
    R48.SI R48.N 600) R48s.all (by decide)
theorem kR16 : ∀ j < R16.N, repK 480 9 Q16.S Q16.SI 5 R16.CS R16.OFF R16.CI R16.E R16.P R16.L
    R16.K R16.S R16.SI R16.N 600 j = true :=
  of_slices (R := repK 480 9 Q16.S Q16.SI 5 R16.CS R16.OFF R16.CI R16.E R16.P R16.L R16.K R16.S
    R16.SI R16.N 600) R16s.all (by decide)

theorem seReps_eq : seReps = seRepWords.map (evalCodes seGens) := by simp only [seReps, tab_eq]

theorem imgRE : ∀ i < seRepWords.length, imageList (seReps.getD i 1) =
    (unpack 480 9 (RE.E (lget RE.OFF i))).toList := by
  rw [seReps_eq]
  exact words_img seGens_len sz imgSE pSE one480 kWE

theorem imgR48 : ∀ i < r48Words.length, imageList (r48Reps.getD i 1) =
    (unpack 480 9 (R48.E (lget R48.OFF i))).toList :=
  words_img s48Gens_len sz img48 p48 one480 kW48
theorem imgR16 : ∀ i < r16Words.length, imageList (r16Reps.getD i 1) =
    (unpack 480 9 (R16.E (lget R16.OFF i))).toList :=
  words_img s16Gens_len sz img16 p16 one480 kW16

theorem seReps_len : seReps.length = seRepWords.length := by rw [seReps, List.length_map]
theorem r48Reps_len : r48Reps.length = r48Words.length := by rw [r48Reps, List.length_map]
theorem r16Reps_len : r16Reps.length = r16Words.length := by rw [r16Reps, List.length_map]

theorem repsE : repsOK 480 (listTables seGens) (listTables (seGens.map (·⁻¹)))
      (cosetOrderTables seQ 1 2) (seReps.map toTable) 600 = true ∧
    repSizes 480 (listTables seGens) (listTables (seGens.map (·⁻¹))) (seReps.map toTable) 600 =
      RE.CS :=
  repsOK_of_img seGens_len (fun j hj => imgSE j (lt_of_lt_of_eq hj seGens_len.symm))
    (fun j hj => allN_spec kPSE j hj) (fun j hj => and_of_bAnd (allN_spec kCE j hj))
    (seReps_len.trans (by decide)) (fun i hi => imgRE i (lt_of_lt_of_eq hi (by decide))) kOffE
    kPosE cntE kRE

theorem reps48 : repsOK 480 (listTables s48Gens) (listTables (s48Gens.map (·⁻¹)))
      (cosetOrderTables s48Q 1 2) (r48Reps.map toTable) 600 = true :=
  (repsOK_of_img s48Gens_len (fun j hj => img48 j (lt_of_lt_of_eq hj s48Gens_len.symm))
    (fun j hj => allN_spec kP48 j hj) (fun j hj => and_of_bAnd (allN_spec kC48 j hj))
    (r48Reps_len.trans (by decide)) (fun i hi => imgR48 i (lt_of_lt_of_eq hi (by decide))) kOff48
    kPos48 cnt48 kR48).1

theorem reps16 : repsOK 480 (listTables s16Gens) (listTables (s16Gens.map (·⁻¹)))
      (cosetOrderTables s16Q 1 2) (r16Reps.map toTable) 600 = true :=
  (repsOK_of_img s16Gens_len (fun j hj => img16 j (lt_of_lt_of_eq hj s16Gens_len.symm))
    (fun j hj => allN_spec kP16 j hj) (fun j hj => and_of_bAnd (allN_spec kC16 j hj))
    (r16Reps_len.trans (by decide)) (fun i hi => imgR16 i (lt_of_lt_of_eq hi (by decide))) kOff16
    kPos16 cnt16 kR16).1

theorem cover_check : censusCoverCheck = true := by
  unfold censusCoverCheck
  rw [repsE.1, reps48, reps16, ord_all sz (e := 2) seReps_len imgRE kOE (by norm_num),
    ord_all sz (e := 2) r48Reps_len imgR48 kO48 (by norm_num),
    ord_all sz (e := 2) r16Reps_len imgR16 kO16 (by norm_num)]
  rfl

theorem kAE : allN 8 (fun k => bAnd(permOK 480 9 (mask 9) (480 * 9) (lget EL k)
    (pinvS 480 9 (mask 9) (lget EL k)), permOK 480 9 (mask 9) (480 * 9)
    (pinvS 480 9 (mask 9) (lget EL k)) (lget EL k))) = true := by quickRfl

theorem a1 : permOK 480 9 (mask 9) (480 * 9) Z1 (pinvS 480 9 (mask 9) Z1) = true := by quickRfl
theorem a1' : permOK 480 9 (mask 9) (480 * 9) (pinvS 480 9 (mask 9) Z1) Z1 = true := by quickRfl
theorem a2 : permOK 480 9 (mask 9) (480 * 9) Z2 (pinvS 480 9 (mask 9) Z2) = true := by quickRfl
theorem a2' : permOK 480 9 (mask 9) (480 * 9) (pinvS 480 9 (mask 9) Z2) Z2 = true := by quickRfl
theorem a3 : permOK 480 9 (mask 9) (480 * 9) Z3 (pinvS 480 9 (mask 9) Z3) = true := by quickRfl
theorem a3' : permOK 480 9 (mask 9) (480 * 9) (pinvS 480 9 (mask 9) Z3) Z3 = true := by quickRfl

theorem kW1 : Nat.beq (wordK 480 9 (mask 9) (pidn 480 9) (lget EL) ELI [1, 5, 1, 5]) Z2 = true := by
  quickRfl
theorem kW2 : Nat.beq (wordK 480 9 (mask 9) (pidn 480 9) (lget EL) ELI [5, 7, 5, 7]) Z1 = true := by
  quickRfl

theorem inv_pair {t : Array Nat} {P : Nat} (ht : t = unpack 480 9 P)
    (h1 : permOK 480 9 (mask 9) (480 * 9) P (pinvS 480 9 (mask 9) P) = true)
    (h2 : permOK 480 9 (mask 9) (480 * 9) (pinvS 480 9 (mask 9) P) P = true) :
    (CFSG.Monster.B.Co2.Native.isInvA 480 t (CFSG.Monster.B.Co2.Native.invCand 480 t) &&
      CFSG.Monster.B.Co2.Native.isInvA 480 (CFSG.Monster.B.Co2.Native.invCand 480 t) t) = true := by
  rw [ht, CFSG.KC.BfsPin.invCand_unpack h1, Orb.isInvA_unpack h1, Orb.isInvA_unpack h2]
  rfl

theorem arr_check : censusArrCheck = true := by
  unfold censusArrCheck
  have h1 : (List.range 8).all (fun i =>
      CFSG.Monster.B.Co2.Native.isInvA 480 eArrs[i]! (CFSG.Monster.B.Co2.Native.invCand 480 eArrs[i]!) &&
        CFSG.Monster.B.Co2.Native.isInvA 480 (CFSG.Monster.B.Co2.Native.invCand 480 eArrs[i]!)
          eArrs[i]!) = true := by
    rw [List.all_eq_true]
    intro k hk
    have hk' := List.mem_range.1 hk
    obtain ⟨p1, p2⟩ := and_of_bAnd (allN_spec kAE k hk')
    exact inv_pair (eArrs_eq k hk') p1 p2
  have h3 : schreierPermEq (evalCodes eGens [1, 5, 1, 5]) z2 = true := by
    have hl : lettersK eGens.length [1, 5, 1, 5] = true := by rw [eGens_len]; quickRfl
    have hw := evalCodes_img sz imgE pE one480 hl
    rw [Nat.eq_of_beq_eq_true kW1] at hw
    exact schreierPermEq_of_img hw imgZ2
  have h4 : schreierPermEq (evalCodes eGens [5, 7, 5, 7]) z1 = true := by
    have hl : lettersK eGens.length [5, 7, 5, 7] = true := by rw [eGens_len]; quickRfl
    have hw := evalCodes_img sz imgE pE one480 hl
    rw [Nat.eq_of_beq_eq_true kW2] at hw
    exact schreierPermEq_of_img hw imgZ1
  rw [h1, h3, h4]
  simp only [List.all_cons, List.all_nil, inv_pair z1_eq a1 a1', inv_pair z2_eq a2 a2',
    inv_pair z3_eq a3 a3']
  rfl

@[expose] noncomputable def fusOK (R : Nat) (e : ℕ × List ℤ) : Bool :=
  Prod.rec (motive := fun _ => Bool) (fun k wd =>
    bIf(Nat.beq k 0, memK R [Z1, Z2, Z3],
      bAnd(Nat.ble k 2, bAnd(lettersK 8 wd, bAnd(permOK 480 9 (mask 9) (480 * 9)
        (wordK 480 9 (mask 9) (pidn 480 9) (lget EL) ELI wd)
        (pinvS 480 9 (mask 9) (wordK 480 9 (mask 9) (pidn 480 9) (lget EL) ELI wd)),
      Nat.beq (pcomp 480 9 (mask 9) (pcomp 480 9 (mask 9)
        (wordK 480 9 (mask 9) (pidn 480 9) (lget EL) ELI wd) R)
        (pinvS 480 9 (mask 9) (wordK 480 9 (mask 9) (pidn 480 9) (lget EL) ELI wd)))
        (lget [X48, X16] (Nat.sub k 1))))))) e

theorem kFus : allN seRepWords.length (fun i => fusOK (RE.E (lget RE.OFF i))
    (fusion.getD i (0, []))) = true := by quickRfl

theorem kSize : allN seRepWords.length (fun i => minK (fixCntK 9 (mask 9) (RE.E (lget RE.OFF i)) 480)
    (lget RE.CS i) (xsFix.zip xsMin)) = true := by quickRfl

theorem kF48 : Nat.beq (fixCntK 9 (mask 9) X48 480) 48 = true := by quickRfl
theorem kF16 : Nat.beq (fixCntK 9 (mask 9) X16 480) 16 = true := by quickRfl

theorem n481 : neCK 480 9 (mask 9) (480 * 9) X48 Z1 = true := by quickRfl
theorem n482 : neCK 480 9 (mask 9) (480 * 9) X48 Z2 = true := by quickRfl
theorem n483 : neCK 480 9 (mask 9) (480 * 9) X48 Z3 = true := by quickRfl
theorem n161 : neCK 480 9 (mask 9) (480 * 9) X16 Z1 = true := by quickRfl
theorem n162 : neCK 480 9 (mask 9) (480 * 9) X16 Z2 = true := by quickRfl
theorem n163 : neCK 480 9 (mask 9) (480 * 9) X16 Z3 = true := by quickRfl

theorem c48 : canonK 480 9 (mask 9) (480 * 9) X48 = true := by quickRfl
theorem c16 : canonK 480 9 (mask 9) (480 * 9) X16 = true := by quickRfl
theorem o48 : ordIs 480 9 (mask 9) (pidn 480 9) X48 (2 - 1) = true := by quickRfl
theorem o16 : ordIs 480 9 (mask 9) (pidn 480 9) X16 (2 - 1) = true := by quickRfl

theorem fix_eq {g : Equiv.Perm (Fin 480)} {P : Nat} (hg : imageList g = (unpack 480 9 P).toList) :
    fixNum g = fixCntK 9 (mask 9) P 480 := by
  unfold fixNum
  exact countFix_eq hg

theorem fusion_check : censusFusionCheck = true := by
  unfold censusFusionCheck
  have hfix : xs.map fixNum = xsFix := by
    simp only [xs, List.map_cons, List.map_nil, fix_eq imgX48, fix_eq imgX16,
      Nat.eq_of_beq_eq_true kF48, Nat.eq_of_beq_eq_true kF16]
    rfl
  have hxs : xs.all (fun x => ordTest 480 2 (toTable x) && !zs.any (schreierPermEq x)) = true := by
    simp only [xs, zs, List.all_cons, List.all_nil, List.any_cons, List.any_nil,
      ordTest_of_ordIs sz imgX48 c48 (by norm_num) o48,
      ordTest_of_ordIs sz imgX16 c16 (by norm_num) o16,
      schreierPermEq_of_neCK imgX48 imgZ1 n481, schreierPermEq_of_neCK imgX48 imgZ2 n482,
      schreierPermEq_of_neCK imgX48 imgZ3 n483, schreierPermEq_of_neCK imgX16 imgZ1 n161,
      schreierPermEq_of_neCK imgX16 imgZ2 n162, schreierPermEq_of_neCK imgX16 imgZ3 n163]
    rfl
  have hfus : (seReps.zip fusion).all (fun p =>
      if p.2.1 = 0 then zs.any (schreierPermEq p.1)
      else
        let g := tab (evalCodes eGens p.2.2)
        decide (p.2.1 ≤ xs.length) &&
          schreierPermEq (g * p.1 * g⁻¹) (xs.getD (p.2.1 - 1) 1)) = true := by
    refine all_zip_of fun i hl hm => ?_
    have hi : i < seRepWords.length := lt_of_lt_of_eq hl seReps_len
    have hr := imgRE i hi
    rw [List.getD_eq_getElem _ _ hl] at hr
    have hf := allN_spec kFus i hi
    rw [List.getD_eq_getElem _ _ hm] at hf
    generalize fusion[i] = e at hf ⊢
    obtain ⟨k, wd⟩ := e
    change bIf(Nat.beq k 0, memK (RE.E (lget RE.OFF i)) [Z1, Z2, Z3], _) = true at hf
    dsimp only
    by_cases hk : k = 0
    · subst hk
      rw [ite_eq_left rfl, List.any_eq_true]
      obtain ⟨z, hz, ez⟩ := corrZ.mem (memK_spec hf)
      exact ⟨z, hz, schreierPermEq_of_img hr ez⟩
    · have hb : Nat.beq k 0 = false := by
        cases e : Nat.beq k 0
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true e) hk
      rw [hb] at hf
      obtain ⟨hk2, hf⟩ := and_of_bAnd hf
      obtain ⟨h1, hf⟩ := and_of_bAnd hf
      obtain ⟨h2, h3⟩ := and_of_bAnd hf
      rw [ite_eq_right hk, tab_eq]
      have h1' : lettersK eGens.length wd = true := by rw [eGens_len]; exact h1
      have hw := evalCodes_img sz imgE pE one480 h1'
      have himg := mulK_rep sz (mulK_rep sz hw hr) (invK_rep hw h2)
      rw [Nat.eq_of_beq_eq_true h3] at himg
      have hk' : k ≤ 2 := Nat.le_of_ble_eq_true hk2
      have hxl : k - 1 < xs.length := by
        change k - 1 < 2
        omega
      have hx := corrXs.getD (k - 1) hxl
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨hk', schreierPermEq_of_img himg hx⟩
  have hsizes : (seReps.zip (repSizes 480 (listTables seGens) (listTables (seGens.map (·⁻¹)))
      (seReps.map toTable) 600)).all (fun p =>
      (xsFix.zip xsMin).all fun q => fixNum p.1 != q.1 || decide (q.2 ≤ p.2)) = true := by
    rw [repsE.2]
    refine all_zip_of fun i hl hm => ?_
    have hi : i < seRepWords.length := lt_of_lt_of_eq hl seReps_len
    have hr := imgRE i hi
    rw [List.getD_eq_getElem _ _ hl] at hr
    have hs := allN_spec kSize i hi
    rw [lget_eq RE.CS i, List.getD_eq_getElem _ _ hm] at hs
    dsimp only
    rw [fix_eq hr]
    exact minK_spec hs
  rw [hfix, hxs, hfus, hsizes, seReps_len]
  rfl

theorem kT48 : CFSG.KC.G13.charsEq T48.chars (derivsC d48L) = true := by quickRfl
theorem kT16 : CFSG.KC.G13.charsEq T16.chars (derivsC d16L) = true := by quickRfl

theorem d48_eq : d48 = d48L := by
  rw [d48, T48.eq, CFSG.KC.G13.charsEq_sound kT48]
  exact parseDerivs_derivsC_o8 (List.cons_ne_nil _ _)

theorem d16_eq : d16 = d16L := by
  rw [d16, T16.eq, CFSG.KC.G13.charsEq_sound kT16]
  exact parseDerivs_derivsC_o8 (List.cons_ne_nil _ _)

theorem kD48 : allN r48Words.length (fun i => bIf(Nat.beq (R48.E (lget R48.OFF i)) X48, true,
    derivK 480 9 (mask 9) (480 * 9) (pidn 480 9) (lget EL) ELI 8 okW [Z1, Z2, Z3] []
      (d48L.getD i []) [X48, R48.E (lget R48.OFF i)])) = true := by quickRfl

theorem kD16 : allN r16Words.length (fun i => bIf(Nat.beq (R16.E (lget R16.OFF i)) X16, true,
    derivK 480 9 (mask 9) (480 * 9) (pidn 480 9) (lget EL) ELI 8 okW [Z1, Z2, Z3] [48]
      (d16L.getD i []) [X16, R16.E (lget R16.OFF i)])) = true := by quickRfl

theorem deriv_check : censusDerivCheck = true := by
  unfold censusDerivCheck
  rw [d48_eq, d16_eq,
    derivs_all_o8 sz one480 eGens_len imgE pE corrZ imgX48 r48Reps_len imgR48 kD48,
    derivs_all_o8 sz one480 eGens_len imgE pE corrZ imgX16 r16Reps_len imgR16 kD16,
    r48Reps_len, r16Reps_len]
  rfl

theorem facts : censusArrCheck = true ∧ censusChainCheck = true ∧ censusCoverCheck = true ∧
    censusFusionCheck = true ∧ censusDerivCheck = true :=
  ⟨arr_check, chain_check, cover_check, fusion_check, deriv_check⟩

end CertificateChecks.KernelLC.ExcO8E

end
