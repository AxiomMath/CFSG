module

public import Certificates.Kernel.LocalComp.ExcSp6.Data
public import Certificates.Kernel.LocalComp.ExcSp6.Derivs
public import Certificates.Kernel.Sporadic.Co3.T
public import Certificates.Kernel.Sporadic.Co3.M
public import Certificates.Kernel.Sporadic.Co3.Single
public import Certificates.Kernel.LocalQT.He4148.Glue
public import CFSG.Certificates.Kernel.SporSch.CodesImg
public import CFSG.Certificates.Kernel.LocalCompExcDerivSound
public import CFSG.Certificates.Kernel.LocalCompExcTextSound
public import CFSG.Certificates.Kernel.BfsPinUnpack
public import CFSG.Certificates.Kernel.Spor.RawOrbHead
public import CFSG.Certificates.Kernel.Child3Reps
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.BfsPinSound
public import CFSG.Certificates.Kernel.Spor.RawOrbGrp
public import CFSG.Certificates.Kernel.SporSch.MathieuOCSound
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutCheckBase

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.ExcSp6

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Certificates CFSG.Sporadic.Schreier.Co3
open CFSG.Sporadic.Schreier.Native CFSG.Monster.B.Mathieu CFSG.ComponentClassification.M12Cover
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch.MOC
open CFSG.KS.SporSch.CodesImg CFSG.KC.Child3 CFSG.KC.LocalComp.ExcDeriv CFSG.KS.M11
open CFSG.ComponentClassification.RankTwoClassical.ExcSp6 CertificateChecks.KernelSpor
open CertificateChecks.KernelLQT.He4148 CFSG.Sporadic.HeldB

theorem and_of_bAnd {a b : Bool} (h : bAnd(a, b) = true) : a = true ∧ b = true := by
  cases a <;> simp_all

theorem words_img {gs : List (Equiv.Perm (Fin 276))} {k : Nat} (hl : gs.length = k)
    {S SI : Nat → Nat} (hsz : szOK 276 9 = true)
    (hg : ∀ j < gs.length, imageList (gs.getD j 1) = (unpack 276 9 (S j)).toList)
    (hp : ∀ j < gs.length, permOK 276 9 (mask 9) (276 * 9) (S j) (SI j) = true)
    (hid : imageList (1 : Equiv.Perm (Fin 276)) = (unpack 276 9 (pidn 276 9)).toList)
    {ws : List (List Int)} {Ps : Nat → Nat}
    (hk : allN ws.length (fun i => bAnd(lettersK k (ws.getD i []),
      Nat.beq (wordK 276 9 (mask 9) (pidn 276 9) S SI (ws.getD i [])) (Ps i))) = true) :
    ∀ i < ws.length, imageList ((ws.map (evalCodes gs)).getD i 1) =
      (unpack 276 9 (Ps i)).toList := by
  intro i hi
  obtain ⟨h1, h2⟩ := and_of_bAnd (allN_spec hk i hi)
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map,
    ← List.getD_eq_getElem _ [] hi, evalCodes_img hsz hg hp hid (hl ▸ h1),
    Nat.eq_of_beq_eq_true h2]

theorem ord_all {e c : Nat} (hsz : szOK 276 9 = true) {reps : List (Equiv.Perm (Fin 276))}
    {Ps : Nat → Nat} (hr : reps.length = c)
    (hi : ∀ i < c, imageList (reps.getD i 1) = (unpack 276 9 (Ps i)).toList)
    (hk : allN c (fun i => bAnd(canonK 276 9 (mask 9) (276 * 9) (Ps i),
      ordIs 276 9 (mask 9) (pidn 276 9) (Ps i) (e - 1))) = true) (he : 0 < e) :
    (reps.map toTable).all (ordTest 276 e) = true := by
  rw [List.all_eq_true]
  intro t ht
  obtain ⟨r, hr', rfl⟩ := List.mem_map.1 ht
  obtain ⟨i, hi', rfl⟩ := List.getElem_of_mem hr'
  have hic : i < c := hr ▸ hi'
  obtain ⟨h1, h2⟩ := and_of_bAnd (allN_spec hk i hic)
  have himg := hi i hic
  rw [List.getD_eq_getElem _ _ hi'] at himg
  exact ordTest_of_ordIs hsz himg h1 he h2

theorem comm_all {gs : List (Equiv.Perm (Fin 276))} {k : Nat} (hl : gs.length = k)
    {S : Nat → Nat} {h : Equiv.Perm (Fin 276)} {H : Nat} (hsz : szOK 276 9 = true)
    (hg : ∀ j < gs.length, imageList (gs.getD j 1) = (unpack 276 9 (S j)).toList)
    (hh : imageList h = (unpack 276 9 H).toList)
    (hk : allN k (fun j => Nat.beq (pcomp 276 9 (mask 9) (S j) H) (pcomp 276 9 (mask 9) H (S j))) =
      true) :
    gs.all (fun g => schreierPermEq (g * h) (h * g)) = true := by
  rw [List.all_eq_true]
  intro g hg'
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg'
  have himg := hg j hj
  rw [List.getD_eq_getElem _ _ hj] at himg
  have e2 := mulK_rep hsz hh himg
  rw [← Nat.eq_of_beq_eq_true (allN_spec hk j (hl ▸ hj))] at e2
  exact schreierPermEq_of_img (mulK_rep hsz himg hh) e2

theorem all_zip_of {α β : Type} {l : List α} {m : List β} {f : α × β → Bool}
    (h : ∀ i (hl : i < l.length) (hm : i < m.length), f (l[i], m[i]) = true) :
    (l.zip m).all f = true := by
  rw [List.all_eq_true]
  intro p hp
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
  have hi' : i < min l.length m.length := by simpa using hi
  rw [List.getElem_zip]
  exact h i (by omega) (by omega)

theorem sz : szOK 276 9 = true := by quickRfl

theorem kId : idK 276 9 (mask 9) = true := by quickRfl

theorem img_one (n : Nat) :
    imageList (1 : Equiv.Perm (Fin n)) = (CFSG.Monster.B.Co2.Native.idA n).toList := by
  apply List.ext_getElem <;> simp [imageList, CFSG.Monster.B.Co2.Native.idA]

theorem one276 : imageList (1 : Equiv.Perm (Fin 276)) = (unpack 276 9 (pidn 276 9)).toList := by
  rw [idK_sound kId]
  exact img_one 276

theorem cOne : canonK 276 9 (mask 9) (276 * 9) One276 = true := by quickRfl

theorem tGens_len : tGens.length = 8 := by rw [tGens, List.length_map, List.length_range]

theorem mGens_len : mGens.length = 7 := by rw [mGens, List.length_map, List.length_range]

theorem kTS : allN 8 (fun j => Nat.beq (TQ.S j) (Co3T.S j)) = true := by quickRfl

theorem kTI : allN 8 (fun j => invEqK 276 9 (mask 9) (276 * 9) (Co3T.SI j) (Co3T.S j)) = true := by
  quickRfl

theorem kMI : allN 7 (fun j => invEqK 276 9 (mask 9) (276 * 9) (Co3M.SI j) (Co3M.S j)) = true := by
  quickRfl

theorem kZI : invEqK 276 9 (mask 9) (276 * 9) Co3Z Co3Z = true := by quickRfl

theorem imgT : ∀ j < tGens.length, imageList (tGens.getD j 1) = (unpack 276 9 (TQ.S j)).toList := by
  intro j hj
  rw [tGens_len] at hj
  rw [tGens, List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map, List.getElem_range,
    Nat.eq_of_beq_eq_true (allN_spec kTS j hj)]
  exact imageList_of_rep (unpack_size' _ _ _)
    (unpack_facts (Co3T.arr_eq j (by omega)) (allN_spec Co3T.perm j (by omega))
      (allN_spec kTI j hj)).2.1

theorem imgM : ∀ j < mGens.length, imageList (mGens.getD j 1) = (unpack 276 9 (Co3M.S j)).toList := by
  intro j hj
  rw [mGens_len] at hj
  rw [mGens, List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map, List.getElem_range]
  exact imageList_of_rep (unpack_size' _ _ _)
    (unpack_facts (Co3M.arr_eq j (by omega)) (allN_spec Co3M.perm j (by omega))
      (allN_spec kMI j hj)).2.1

theorem pM : ∀ j < mGens.length, permOK 276 9 (mask 9) (276 * 9) (Co3M.S j) (Co3M.SI j) = true :=
  fun j hj => allN_spec Co3M.perm j (by rw [mGens_len] at hj; omega)

theorem imgZ : imageList zC = (unpack 276 9 Co3Z).toList :=
  imageList_of_rep (unpack_size' _ _ _) (unpack_facts Co3Single.z_eq kZI kZI).2.1

theorem kPT : allN 8 (fun j => permOK 276 9 (mask 9) (276 * 9) (TQ.S j) (TQ.SI j)) = true := by
  quickRfl

theorem pT : ∀ j < tGens.length, permOK 276 9 (mask 9) (276 * 9) (TQ.S j) (TQ.SI j) = true :=
  fun j hj => allN_spec kPT j (tGens_len ▸ hj)

theorem kXA : Nat.beq (wordK 276 9 (mask 9) (pidn 276 9) TQ.S TQ.SI [3, 1, 3, 2]) XA = true := by
  quickRfl

theorem kXB : Nat.beq (wordK 276 9 (mask 9) (pidn 276 9) TQ.S TQ.SI [1, 5]) XB = true := by
  quickRfl

theorem imgXA : imageList xa = (unpack 276 9 XA).toList := by
  have h1 : lettersK tGens.length [3, 1, 3, 2] = true := by rw [tGens_len]; quickRfl
  rw [xa, tab_eq, evalCodes_img sz imgT pT one276 h1, Nat.eq_of_beq_eq_true kXA]

theorem imgXB : imageList xb = (unpack 276 9 XB).toList := by
  have h1 : lettersK tGens.length [1, 5] = true := by rw [tGens_len]; quickRfl
  rw [xb, tab_eq, evalCodes_img sz imgT pT one276 h1, Nat.eq_of_beq_eq_true kXB]

theorem saGens_eq : saGens = saWords.map (evalCodes tGens) := by simp only [saGens, tab_eq]

theorem sbGens_eq : sbGens = sbWords.map (evalCodes tGens) := by simp only [sbGens, tab_eq]

theorem saGens_len : saGens.length = 7 := by rw [saGens_eq, List.length_map]; rfl

theorem sbGens_len : sbGens.length = 5 := by rw [sbGens_eq, List.length_map]; rfl

theorem kSA : allN saWords.length (fun j => bAnd(lettersK 8 (saWords.getD j []),
    Nat.beq (wordK 276 9 (mask 9) (pidn 276 9) TQ.S TQ.SI (saWords.getD j [])) (SA.S j))) = true := by
  quickRfl

theorem kSB : allN sbWords.length (fun j => bAnd(lettersK 8 (sbWords.getD j []),
    Nat.beq (wordK 276 9 (mask 9) (pidn 276 9) TQ.S TQ.SI (sbWords.getD j [])) (SB.S j))) = true := by
  quickRfl

theorem imgSA : ∀ j < saGens.length, imageList (saGens.getD j 1) = (unpack 276 9 (SA.S j)).toList := by
  rw [saGens_eq]
  intro j hj
  exact words_img tGens_len sz imgT pT one276 kSA j (by simpa using hj)

theorem imgSB : ∀ j < sbGens.length, imageList (sbGens.getD j 1) = (unpack 276 9 (SB.S j)).toList := by
  rw [sbGens_eq]
  intro j hj
  exact words_img tGens_len sz imgT pT one276 kSB j (by simpa using hj)

theorem kPA : allN 7 (fun j => permOK 276 9 (mask 9) (276 * 9) (SA.S j) (SA.SI j)) = true := by
  quickRfl

theorem kPB : allN 5 (fun j => permOK 276 9 (mask 9) (276 * 9) (SB.S j) (SB.SI j)) = true := by
  quickRfl

theorem pA : ∀ j < saGens.length, permOK 276 9 (mask 9) (276 * 9) (SA.S j) (SA.SI j) = true :=
  fun j hj => allN_spec kPA j (saGens_len ▸ hj)

theorem pB : ∀ j < sbGens.length, permOK 276 9 (mask 9) (276 * 9) (SB.S j) (SB.SI j) = true :=
  fun j hj => allN_spec kPB j (sbGens_len ▸ hj)

theorem chainT : ChainK 276 9 tGens tQWords (#v[0, 1, 2] : Vector (Fin 276) 3)
    TQ.S TQ.SI TQ.LR TQ.TR TQ.TRI 10 TQ.BP 18 16 :=
  ⟨by norm_num, by norm_num, by norm_num, imgT, by decide, TQ.head, TQ.hl, by norm_num, TQ.hs⟩

theorem chainA : ChainK 276 9 saGens saQWords (#v[0, 1] : Vector (Fin 276) 2)
    SA.S SA.SI SA.LR SA.TR SA.TRI 9 SA.BP 18 16 :=
  ⟨by norm_num, by norm_num, by norm_num, imgSA, by decide, SA.head, SA.hl, by norm_num, SA.hs⟩

theorem chainB : ChainK 276 9 sbGens sbQWords (#v[0, 2] : Vector (Fin 276) 2)
    SB.S SB.SI SB.LR SB.TR SB.TRI 6 SB.BP 18 16 :=
  ⟨by norm_num, by norm_num, by norm_num, imgSB, by decide, SB.head, SB.hl, by norm_num, SB.hs⟩

theorem kNT : Nat.beq (ordK TQ.LR 3) 1024 = true := by quickRfl
theorem kNA : Nat.beq (ordK SA.LR 2) 512 = true := by quickRfl
theorem kNB : Nat.beq (ordK SB.LR 2) 128 = true := by quickRfl

theorem kMT : allN 8 (fun j => Nat.beq (pcomp 276 9 (mask 9) (TQ.S j) Co3Z)
    (pcomp 276 9 (mask 9) Co3Z (TQ.S j))) = true := by quickRfl
theorem kMA : allN 7 (fun j => Nat.beq (pcomp 276 9 (mask 9) (SA.S j) XA)
    (pcomp 276 9 (mask 9) XA (SA.S j))) = true := by quickRfl
theorem kMB : allN 5 (fun j => Nat.beq (pcomp 276 9 (mask 9) (SB.S j) XB)
    (pcomp 276 9 (mask 9) XB (SB.S j))) = true := by quickRfl

theorem chain_check : censusChainCheck = true := by
  obtain ⟨hcT, hoT⟩ : tQ.check = true ∧ tQ.orderCertificate = ordK TQ.LR 3 :=
    chainK_check (by decide) (by decide) chainT
  obtain ⟨hcA, hoA⟩ : saQ.check = true ∧ saQ.orderCertificate = ordK SA.LR 2 :=
    chainK_check (by decide) (by decide) chainA
  obtain ⟨hcB, hoB⟩ : sbQ.check = true ∧ sbQ.orderCertificate = ordK SB.LR 2 :=
    chainK_check (by decide) (by decide) chainB
  unfold censusChainCheck
  rw [hcT, hoT, Nat.eq_of_beq_eq_true kNT, hcA, hoA, Nat.eq_of_beq_eq_true kNA, hcB, hoB,
    Nat.eq_of_beq_eq_true kNB, comm_all tGens_len sz imgT imgZ kMT,
    comm_all saGens_len sz imgSA imgXA kMA, comm_all sbGens_len sz imgSB imgXB kMB]
  rfl

theorem cntT : (cosetOrderTables tQ 1 2).length = RT.N :=
  (chainK_cosetCount (by decide) (by decide) chainT one276 cOne (by norm_num) (by norm_num)
    (by decide) NT.hc).trans (by decide)

theorem cntA : (cosetOrderTables saQ 1 2).length = RA.N :=
  (chainK_cosetCount (by decide) (by decide) chainA one276 cOne (by norm_num) (by norm_num)
    (by decide) NA.hc).trans (by decide)

theorem cntB : (cosetOrderTables sbQ 1 2).length = RB.N :=
  (chainK_cosetCount (by decide) (by decide) chainB one276 cOne (by norm_num) (by norm_num)
    (by decide) NB.hc).trans (by decide)

theorem kCT : allN 8 (fun j => bAnd(canonK 276 9 (mask 9) (276 * 9) (TQ.S j),
    canonK 276 9 (mask 9) (276 * 9) (TQ.SI j))) = true := by quickRfl
theorem kCA : allN 7 (fun j => bAnd(canonK 276 9 (mask 9) (276 * 9) (SA.S j),
    canonK 276 9 (mask 9) (276 * 9) (SA.SI j))) = true := by quickRfl
theorem kCB : allN 5 (fun j => bAnd(canonK 276 9 (mask 9) (276 * 9) (SB.S j),
    canonK 276 9 (mask 9) (276 * 9) (SB.SI j))) = true := by quickRfl

theorem kWT : allN tRepWords.length (fun i => bAnd(lettersK 8 (tRepWords.getD i []),
    Nat.beq (wordK 276 9 (mask 9) (pidn 276 9) TQ.S TQ.SI (tRepWords.getD i []))
      (RT.E (lget RT.OFF i)))) = true := by quickRfl
theorem kWA : allN raWords.length (fun i => bAnd(lettersK 7 (raWords.getD i []),
    Nat.beq (wordK 276 9 (mask 9) (pidn 276 9) SA.S SA.SI (raWords.getD i []))
      (RA.E (lget RA.OFF i)))) = true := by quickRfl
theorem kWB : allN rbWords.length (fun i => bAnd(lettersK 5 (rbWords.getD i []),
    Nat.beq (wordK 276 9 (mask 9) (pidn 276 9) SB.S SB.SI (rbWords.getD i []))
      (RB.E (lget RB.OFF i)))) = true := by quickRfl

theorem kOT : allN tRepWords.length (fun i => bAnd(canonK 276 9 (mask 9) (276 * 9)
    (RT.E (lget RT.OFF i)), ordIs 276 9 (mask 9) (pidn 276 9) (RT.E (lget RT.OFF i)) (2 - 1))) =
    true := by quickRfl
theorem kOA : allN raWords.length (fun i => bAnd(canonK 276 9 (mask 9) (276 * 9)
    (RA.E (lget RA.OFF i)), ordIs 276 9 (mask 9) (pidn 276 9) (RA.E (lget RA.OFF i)) (2 - 1))) =
    true := by quickRfl
theorem kOB : allN rbWords.length (fun i => bAnd(canonK 276 9 (mask 9) (276 * 9)
    (RB.E (lget RB.OFF i)), ordIs 276 9 (mask 9) (pidn 276 9) (RB.E (lget RB.OFF i)) (2 - 1))) =
    true := by quickRfl

theorem kOffT : offOK RT.CS RT.OFF RT.N = true := by quickRfl
theorem kOffA : offOK RA.CS RA.OFF RA.N = true := by quickRfl
theorem kOffB : offOK RB.CS RB.OFF RB.N = true := by quickRfl

theorem kPosT : CFSG.KC.J2Cover.allL (fun c => Nat.blt 0 c) RT.CS = true := by quickRfl
theorem kPosA : CFSG.KC.J2Cover.allL (fun c => Nat.blt 0 c) RA.CS = true := by quickRfl
theorem kPosB : CFSG.KC.J2Cover.allL (fun c => Nat.blt 0 c) RB.CS = true := by quickRfl

theorem kRT : allN RT.N (repK 276 9 TQ.S TQ.SI 8 RT.CS RT.OFF RT.CI RT.E RT.P RT.L RT.K RT.S
    RT.SI RT.N 600) = true := by quickRfl
theorem kRA : allN RA.N (repK 276 9 SA.S SA.SI 7 RA.CS RA.OFF RA.CI RA.E RA.P RA.L RA.K RA.S
    RA.SI RA.N 600) = true := by quickRfl
theorem kRB : allN RB.N (repK 276 9 SB.S SB.SI 5 RB.CS RB.OFF RB.CI RB.E RB.P RB.L RB.K RB.S
    RB.SI RB.N 600) = true := by quickRfl

theorem tReps_eq : tReps = tRepWords.map (evalCodes tGens) := by simp only [tReps, tab_eq]

theorem imgRT : ∀ i < tRepWords.length, imageList (tReps.getD i 1) =
    (unpack 276 9 (RT.E (lget RT.OFF i))).toList := by
  rw [tReps_eq]
  exact words_img tGens_len sz imgT pT one276 kWT

theorem imgRA : ∀ i < raWords.length, imageList (raReps.getD i 1) =
    (unpack 276 9 (RA.E (lget RA.OFF i))).toList :=
  words_img saGens_len sz imgSA pA one276 kWA

theorem imgRB : ∀ i < rbWords.length, imageList (rbReps.getD i 1) =
    (unpack 276 9 (RB.E (lget RB.OFF i))).toList :=
  words_img sbGens_len sz imgSB pB one276 kWB

theorem tReps_len : tReps.length = tRepWords.length := by rw [tReps, List.length_map]
theorem raReps_len : raReps.length = raWords.length := by rw [raReps, List.length_map]
theorem rbReps_len : rbReps.length = rbWords.length := by rw [rbReps, List.length_map]

theorem repsT : repsOK 276 (listTables tGens) (listTables (tGens.map (·⁻¹)))
      (cosetOrderTables tQ 1 2) (tReps.map toTable) 600 = true ∧
    repSizes 276 (listTables tGens) (listTables (tGens.map (·⁻¹))) (tReps.map toTable) 600 =
      RT.CS :=
  repsOK_of_img tGens_len (fun j hj => imgT j (tGens_len ▸ hj)) (fun j hj => allN_spec kPT j hj)
    (fun j hj => and_of_bAnd (allN_spec kCT j hj)) (tReps_len.trans (by decide))
    (fun i hi => imgRT i (lt_of_lt_of_eq hi (by decide))) kOffT kPosT cntT
    (fun j hj => allN_spec kRT j hj)

theorem repsA : repsOK 276 (listTables saGens) (listTables (saGens.map (·⁻¹)))
      (cosetOrderTables saQ 1 2) (raReps.map toTable) 600 = true ∧
    repSizes 276 (listTables saGens) (listTables (saGens.map (·⁻¹))) (raReps.map toTable) 600 =
      RA.CS :=
  repsOK_of_img saGens_len (fun j hj => imgSA j (saGens_len ▸ hj)) (fun j hj => allN_spec kPA j hj)
    (fun j hj => and_of_bAnd (allN_spec kCA j hj)) (raReps_len.trans (by decide))
    (fun i hi => imgRA i (lt_of_lt_of_eq hi (by decide))) kOffA kPosA cntA
    (fun j hj => allN_spec kRA j hj)

theorem repsB : repsOK 276 (listTables sbGens) (listTables (sbGens.map (·⁻¹)))
      (cosetOrderTables sbQ 1 2) (rbReps.map toTable) 600 = true ∧
    repSizes 276 (listTables sbGens) (listTables (sbGens.map (·⁻¹))) (rbReps.map toTable) 600 =
      RB.CS :=
  repsOK_of_img sbGens_len (fun j hj => imgSB j (sbGens_len ▸ hj)) (fun j hj => allN_spec kPB j hj)
    (fun j hj => and_of_bAnd (allN_spec kCB j hj)) (rbReps_len.trans (by decide))
    (fun i hi => imgRB i (lt_of_lt_of_eq hi (by decide))) kOffB kPosB cntB
    (fun j hj => allN_spec kRB j hj)

theorem cover_check : censusCoverCheck = true := by
  have h1 := ord_all sz (e := 2) tReps_len imgRT kOT (by norm_num)
  have h2 := ord_all sz (e := 2) raReps_len imgRA kOA (by norm_num)
  have h3 := ord_all sz (e := 2) rbReps_len imgRB kOB (by norm_num)
  unfold censusCoverCheck
  rw [repsT.1, repsA.1, repsB.1, h1, h2, h3]
  rfl

theorem kAT : allN 8 (fun k => bAnd(permOK 276 9 (mask 9) (276 * 9) (Co3T.S k)
    (pinvS 276 9 (mask 9) (Co3T.S k)), permOK 276 9 (mask 9) (276 * 9)
    (pinvS 276 9 (mask 9) (Co3T.S k)) (Co3T.S k))) = true := by quickRfl

theorem kAM : allN 7 (fun k => bAnd(permOK 276 9 (mask 9) (276 * 9) (Co3M.S k)
    (pinvS 276 9 (mask 9) (Co3M.S k)), permOK 276 9 (mask 9) (276 * 9)
    (pinvS 276 9 (mask 9) (Co3M.S k)) (Co3M.S k))) = true := by quickRfl

theorem z1 : permOK 276 9 (mask 9) (276 * 9) Co3Z (pinvS 276 9 (mask 9) Co3Z) = true := by
  quickRfl

theorem z2 : permOK 276 9 (mask 9) (276 * 9) (pinvS 276 9 (mask 9) Co3Z) Co3Z = true := by
  quickRfl

theorem arr_check : censusArrCheck = true := by
  unfold censusArrCheck
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range]
  refine ⟨⟨⟨fun k hk => ?_, fun k hk => ?_⟩, ?_⟩, ?_⟩
  · obtain ⟨p1, p2⟩ := and_of_bAnd (allN_spec kAM k hk)
    rw [Co3M.arr_eq k (by omega), CFSG.KC.BfsPin.invCand_unpack p1]
    exact ⟨Orb.isInvA_unpack p1, Orb.isInvA_unpack p2⟩
  · obtain ⟨p1, p2⟩ := and_of_bAnd (allN_spec kAT k hk)
    rw [Co3T.arr_eq k (by omega), CFSG.KC.BfsPin.invCand_unpack p1]
    exact ⟨Orb.isInvA_unpack p1, Orb.isInvA_unpack p2⟩
  · rw [Co3Single.z_eq, CFSG.KC.BfsPin.invCand_unpack z1]
    exact Orb.isInvA_unpack z1
  · rw [Co3Single.z_eq, CFSG.KC.BfsPin.invCand_unpack z1]
    exact Orb.isInvA_unpack z2

@[expose] noncomputable def fusOK (R : Nat) (e : ℕ × List ℤ) : Bool :=
  Prod.rec (motive := fun _ => Bool) (fun k wd =>
    bIf(Nat.beq k 0, Nat.beq R Co3Z,
      bAnd(lettersK 7 wd, bAnd(permOK 276 9 (mask 9) (276 * 9)
        (wordK 276 9 (mask 9) (pidn 276 9) Co3M.S Co3M.SI wd)
        (pinvS 276 9 (mask 9) (wordK 276 9 (mask 9) (pidn 276 9) Co3M.S Co3M.SI wd)),
      Nat.beq (pcomp 276 9 (mask 9) (pcomp 276 9 (mask 9)
        (wordK 276 9 (mask 9) (pidn 276 9) Co3M.S Co3M.SI wd) R)
        (pinvS 276 9 (mask 9) (wordK 276 9 (mask 9) (pidn 276 9) Co3M.S Co3M.SI wd)))
        (nIf(Nat.beq k 1, XA, XB)))))) e

@[expose] noncomputable def sizeOK (R c : Nat) : Bool :=
  bAnd(bIf(Nat.beq (fixCntK 9 (mask 9) R 276) 12, Nat.ble 8 c, true),
    bIf(Nat.beq (fixCntK 9 (mask 9) R 276) 36, bIf(Nat.beq R Co3Z, true, Nat.ble 2 c), true))

theorem kFus : allN tRepWords.length (fun i => fusOK (RT.E (lget RT.OFF i))
    (fusion.getD i (0, []))) = true := by quickRfl

theorem kSize : allN tRepWords.length (fun i => sizeOK (RT.E (lget RT.OFF i)) (lget RT.CS i)) =
    true := by quickRfl

theorem kFZ : Nat.beq (fixCntK 9 (mask 9) Co3Z 276) 36 = true := by quickRfl
theorem kFA : Nat.beq (fixCntK 9 (mask 9) XA 276) 36 = true := by quickRfl
theorem kFB : Nat.beq (fixCntK 9 (mask 9) XB 276) 12 = true := by quickRfl
theorem kNe : neCK 276 9 (mask 9) (276 * 9) XA Co3Z = true := by quickRfl
theorem cx : canonK 276 9 (mask 9) (276 * 9) XA = true := by quickRfl
theorem ox : ordIs 276 9 (mask 9) (pidn 276 9) XA (2 - 1) = true := by quickRfl
theorem cy : canonK 276 9 (mask 9) (276 * 9) XB = true := by quickRfl
theorem oy : ordIs 276 9 (mask 9) (pidn 276 9) XB (2 - 1) = true := by quickRfl

theorem fix_eq {g : Equiv.Perm (Fin 276)} {P : Nat} (hg : imageList g = (unpack 276 9 P).toList) :
    fixCount g = fixCntK 9 (mask 9) P 276 := by
  unfold fixCount
  exact countFix_eq hg

theorem fusion_check : censusFusionCheck = true := by
  unfold censusFusionCheck
  simp only [Bool.and_eq_true, and_assoc, beq_iff_eq, Bool.not_eq_true']
  refine ⟨by rw [tReps_len]; rfl, by rw [fix_eq imgZ, Nat.eq_of_beq_eq_true kFZ],
    by rw [fix_eq imgXA, Nat.eq_of_beq_eq_true kFA], by rw [fix_eq imgXB, Nat.eq_of_beq_eq_true kFB],
    schreierPermEq_of_neCK imgXA imgZ kNe, ordTest_of_ordIs sz imgXA cx (by norm_num) ox,
    ordTest_of_ordIs sz imgXB cy (by norm_num) oy, ?_, ?_⟩
  · refine all_zip_of fun i hl hm => ?_
    have hi : i < tRepWords.length := tReps_len ▸ hl
    have hr := imgRT i hi
    rw [List.getD_eq_getElem _ _ hl] at hr
    have hf := allN_spec kFus i hi
    rw [List.getD_eq_getElem _ _ hm] at hf
    generalize fusion[i] = e at hf ⊢
    obtain ⟨k, wd⟩ := e
    change bIf(Nat.beq k 0, Nat.beq (RT.E (lget RT.OFF i)) Co3Z, _) = true at hf
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
      obtain ⟨h1, hf⟩ := and_of_bAnd hf
      obtain ⟨h2, h3⟩ := and_of_bAnd hf
      rw [ite_eq_right hk, tab_eq]
      have h1' : lettersK mGens.length wd = true := by rw [mGens_len]; exact h1
      have hw := evalCodes_img sz imgM pM one276 h1'
      have himg := mulK_rep sz (mulK_rep sz hw hr) (invK_rep hw h2)
      rw [Nat.eq_of_beq_eq_true h3] at himg
      by_cases h1k : k = 1
      · subst h1k
        rw [ite_eq_left rfl]
        exact schreierPermEq_of_img himg imgXA
      · have hb1 : Nat.beq k 1 = false := by
          cases e : Nat.beq k 1
          · rfl
          · exact absurd (Nat.eq_of_beq_eq_true e) h1k
        rw [hb1] at himg
        rw [ite_eq_right h1k]
        exact schreierPermEq_of_img himg imgXB
  · rw [repsT.2]
    refine all_zip_of fun i hl hm => ?_
    have hi : i < tRepWords.length := tReps_len ▸ hl
    have hr := imgRT i hi
    rw [List.getD_eq_getElem _ _ hl] at hr
    have hs := allN_spec kSize i hi
    rw [lget_eq RT.CS i, List.getD_eq_getElem _ _ hm] at hs
    unfold sizeOK at hs
    obtain ⟨s1, s2⟩ := and_of_bAnd hs
    dsimp only
    rw [fix_eq hr]
    simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq]
    constructor
    · cases e : Nat.beq (fixCntK 9 (mask 9) (RT.E (lget RT.OFF i)) 276) 12
      · left
        exact fun h => by rw [h, Nat.beq_refl] at e; exact Bool.false_ne_true e.symm
      · rw [e] at s1
        right
        exact Nat.le_of_ble_eq_true s1
    · cases e : Nat.beq (fixCntK 9 (mask 9) (RT.E (lget RT.OFF i)) 276) 36
      · left
        left
        exact fun h => by rw [h, Nat.beq_refl] at e; exact Bool.false_ne_true e.symm
      · rw [e] at s2
        cases ez : Nat.beq (RT.E (lget RT.OFF i)) Co3Z
        · rw [ez] at s2
          right
          exact Nat.le_of_ble_eq_true s2
        · left
          right
          exact schreierPermEq_of_img hr (Nat.eq_of_beq_eq_true ez ▸ imgZ)

theorem kDaT : CFSG.KC.G13.charsEq DaT.chars (derivsC daL) = true := by quickRfl
theorem kDbT : CFSG.KC.G13.charsEq DbT.chars (derivsC dbL) = true := by quickRfl

theorem da_eq : da = daL := by
  rw [da, DaT.eq, CFSG.KC.G13.charsEq_sound kDaT]
  exact parseDerivs_derivsC_sp6 (List.cons_ne_nil _ _)

theorem db_eq : db = dbL := by
  rw [db, DbT.eq, CFSG.KC.G13.charsEq_sound kDbT]
  exact parseDerivs_derivsC_sp6 (List.cons_ne_nil _ _)

theorem kDA : allN raWords.length (fun i => bIf(Nat.beq (RA.E (lget RA.OFF i)) XA, true,
    derivK 276 9 (mask 9) (276 * 9) (pidn 276 9) Co3M.S Co3M.SI 7 (fun _ => true) [Co3Z] [12]
      (daL.getD i []) [XA, RA.E (lget RA.OFF i)])) = true := by quickRfl

theorem kDB : allN rbWords.length (fun i => bIf(Nat.beq (RB.E (lget RB.OFF i)) XB, true,
    derivK 276 9 (mask 9) (276 * 9) (pidn 276 9) Co3M.S Co3M.SI 7 (fun _ => true) [Co3Z] []
      (dbL.getD i []) [XB, RB.E (lget RB.OFF i)])) = true := by quickRfl

theorem derivs_all {reps : List (Equiv.Perm (Fin 276))} {ds : List (List (ℕ × List ℤ × ℕ))}
    {x : Equiv.Perm (Fin 276)} {X : Nat} {forbid : List Nat} {c : Nat} {E : Nat → Nat}
    (hx : imageList x = (unpack 276 9 X).toList) (hl : reps.length = c)
    (hi : ∀ i < c, imageList (reps.getD i 1) = (unpack 276 9 (E i)).toList)
    (hk : allN c (fun i => bIf(Nat.beq (E i) X, true,
      derivK 276 9 (mask 9) (276 * 9) (pidn 276 9) Co3M.S Co3M.SI 7 (fun _ => true) [Co3Z] forbid
        (ds.getD i []) [X, E i])) = true) :
    (reps.zip ds).all (fun p => schreierPermEq p.1 x || derivCheck forbid [x, p.1] p.2) = true := by
  refine all_zip_of fun i hr hd => ?_
  have hc : i < c := hl ▸ hr
  have himg := hi i hc
  rw [List.getD_eq_getElem _ _ hr] at himg
  have h := allN_spec hk i hc
  rw [List.getD_eq_getElem _ _ hd] at h
  rw [Bool.or_eq_true]
  cases e : Nat.beq (E i) X
  · rw [e] at h
    right
    exact derivK_sound_sp6 sz one276 mGens_len imgM pM imgZ _
      (List.Forall₂.cons hx (List.Forall₂.cons himg List.Forall₂.nil)) h
  · left
    exact schreierPermEq_of_img himg (Nat.eq_of_beq_eq_true e ▸ hx)

theorem deriv_check : censusDerivCheck = true := by
  unfold censusDerivCheck
  rw [da_eq, db_eq, derivs_all imgXA raReps_len imgRA kDA, derivs_all imgXB rbReps_len imgRB kDB,
    raReps_len, rbReps_len]
  rfl

theorem facts : censusArrCheck = true ∧ censusChainCheck = true ∧ censusCoverCheck = true ∧
    censusFusionCheck = true ∧ censusDerivCheck = true :=
  ⟨arr_check, chain_check, cover_check, fusion_check, deriv_check⟩

end CertificateChecks.KernelLC.ExcSp6

end
