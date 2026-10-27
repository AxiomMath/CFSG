module

public import Certificates.Kernel.LocalComp.ExcU6.Bind
public import Certificates.Kernel.LocalComp.ExcU6.R2a
public import Certificates.Kernel.LocalComp.ExcU6.R2b
public import Certificates.Kernel.LocalComp.ExcU6.R2c
public import Certificates.Kernel.LocalComp.ExcU6.R2d
public import Certificates.Kernel.LocalComp.ExcU6.R2e
public import Certificates.Kernel.LocalComp.ExcU6.R3a
public import Certificates.Kernel.LocalComp.ExcU6.R3b
public import Certificates.Kernel.LocalComp.ExcU6.RSa
public import Certificates.Kernel.LocalComp.ExcU6.RSb
public import Certificates.Kernel.LocalComp.ExcU6.RSc
public import Certificates.Kernel.LocalComp.ExcU6.RSd
public import Certificates.Kernel.LocalComp.SliceJoin
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option linter.unusedSectionVars false

namespace CertificateChecks.KernelLC.ExcU6

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Certificates
open CFSG.Sporadic.Schreier.Native CFSG.Monster.B.Mathieu CFSG.ComponentClassification.M12Cover
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch.MOC CFSG.KS.M11
open CFSG.KS.SporSch.CodesImg CFSG.KC.Child3 CFSG.KC.LocalComp.ExcDeriv
open CFSG.ComponentClassification.RankTwoClassical.ExcU6 CFSG.EvenSmallLie.UnitarySix
open CertificateChecks.KernelLC.ExcGlue CertificateChecks.KernelU6 CertificateChecks.KernelLC.Slices

theorem kC2 : allN 8 (fun j => bAnd(canonK 693 10 (mask 10) (693 * 10) (Q2.S j),
    canonK 693 10 (mask 10) (693 * 10) (Q2.SI j))) = true := by quickRfl
theorem kC3 : allN 11 (fun j => bAnd(canonK 693 10 (mask 10) (693 * 10) (Q3.S j),
    canonK 693 10 (mask 10) (693 * 10) (Q3.SI j))) = true := by quickRfl
theorem kCS : allN 13 (fun j => bAnd(canonK 693 10 (mask 10) (693 * 10) (SQ.S j),
    canonK 693 10 (mask 10) (693 * 10) (SQ.SI j))) = true := by quickRfl

theorem kW2 : allN r2Words.length (fun i => bAnd(lettersK 8 (r2Words.getD i []),
    Nat.beq (wordK 693 10 (mask 10) (pidn 693 10) Q2.S Q2.SI (r2Words.getD i []))
      (R2.E (lget R2.OFF i)))) = true := by quickRfl
theorem kW3 : allN r3Words.length (fun i => bAnd(lettersK 11 (r3Words.getD i []),
    Nat.beq (wordK 693 10 (mask 10) (pidn 693 10) Q3.S Q3.SI (r3Words.getD i []))
      (R3.E (lget R3.OFF i)))) = true := by quickRfl
theorem kWS : allN sRepWords.length (fun i => bAnd(lettersK 13 (sRepWords.getD i []),
    Nat.beq (wordK 693 10 (mask 10) (pidn 693 10) SQ.S SQ.SI (sRepWords.getD i []))
      (RS.E (lget RS.OFF i)))) = true := by quickRfl

theorem kO2 : allN r2Words.length (fun i => bAnd(canonK 693 10 (mask 10) (693 * 10)
    (R2.E (lget R2.OFF i)), ordIs 693 10 (mask 10) (pidn 693 10) (R2.E (lget R2.OFF i)) (2 - 1))) =
    true := by quickRfl
theorem kO3 : allN r3Words.length (fun i => bAnd(canonK 693 10 (mask 10) (693 * 10)
    (R3.E (lget R3.OFF i)), ordIs 693 10 (mask 10) (pidn 693 10) (R3.E (lget R3.OFF i)) (2 - 1))) =
    true := by quickRfl

theorem kOff2 : offOK R2.CS R2.OFF R2.N = true := by quickRfl
theorem kOff3 : offOK R3.CS R3.OFF R3.N = true := by quickRfl
theorem kOffS : offOK RS.CS RS.OFF RS.N = true := by quickRfl

theorem kPos2 : CFSG.KC.J2Cover.allL (fun c => Nat.blt 0 c) R2.CS = true := by quickRfl
theorem kPos3 : CFSG.KC.J2Cover.allL (fun c => Nat.blt 0 c) R3.CS = true := by quickRfl
theorem kPosS : CFSG.KC.J2Cover.allL (fun c => Nat.blt 0 c) RS.CS = true := by quickRfl

theorem kR2 : ∀ j < R2.N, repK 693 10 Q2.S Q2.SI 8 R2.CS R2.OFF R2.CI R2.E R2.P R2.L R2.K
    R2.S R2.SI R2.N 600 j = true :=
  of_slices (R := fun j => repK 693 10 Q2.S Q2.SI 8 R2.CS R2.OFF R2.CI R2.E R2.P R2.L R2.K
    R2.S R2.SI R2.N 600 j) (join (join (join (join R2a.all R2b.all) R2c.all) R2d.all) R2e.all)
    (by decide)

theorem kR3 : ∀ j < R3.N, repK 693 10 Q3.S Q3.SI 11 R3.CS R3.OFF R3.CI R3.E R3.P R3.L R3.K
    R3.S R3.SI R3.N 600 j = true :=
  of_slices (R := fun j => repK 693 10 Q3.S Q3.SI 11 R3.CS R3.OFF R3.CI R3.E R3.P R3.L R3.K
    R3.S R3.SI R3.N 600 j) (join R3a.all R3b.all) (by decide)

theorem kRS : ∀ j < RS.N, repK 693 10 SQ.S SQ.SI 13 RS.CS RS.OFF RS.CI RS.E RS.P RS.L RS.K
    RS.S RS.SI RS.N 100 j = true :=
  of_slices (R := fun j => repK 693 10 SQ.S SQ.SI 13 RS.CS RS.OFF RS.CI RS.E RS.P RS.L RS.K
    RS.S RS.SI RS.N 100 j) (join (join (join RSa.all RSb.all) RSc.all) RSd.all) (by decide)


theorem cnt2 : (cosetOrderTables s2Q 1 2).length = R2.N :=
  (chainK_cosetCount (by decide) (by decide) chain2 one693 cOne (by norm_num) (by norm_num)
    (by decide) N2.hc).trans (by decide)
theorem cnt3 : (cosetOrderTables s3Q 1 2).length = R3.N :=
  (chainK_cosetCount (by decide) (by decide) chain3 one693 cOne (by norm_num) (by norm_num)
    (by decide) N3.hc).trans (by decide)

theorem imgR2 : ∀ i < r2Words.length, imageList (r2Reps.getD i 1) =
    (unpack 693 10 (R2.E (lget R2.OFF i))).toList :=
  words_img s2Gens_len sz img2 p2 one693 kW2
theorem imgR3 : ∀ i < r3Words.length, imageList (r3Reps.getD i 1) =
    (unpack 693 10 (R3.E (lget R3.OFF i))).toList :=
  words_img s3Gens_len sz img3 p3 one693 kW3
theorem imgRS : ∀ i < sRepWords.length, imageList (sReps.getD i 1) =
    (unpack 693 10 (RS.E (lget RS.OFF i))).toList :=
  words_img sGens_len sz imgS pS one693 kWS

theorem r2Reps_len : r2Reps.length = r2Words.length := by rw [r2Reps, List.length_map]
theorem r3Reps_len : r3Reps.length = r3Words.length := by rw [r3Reps, List.length_map]
theorem sReps_len : sReps.length = sRepWords.length := by rw [sReps, List.length_map]

theorem reps2 : repsOK 693 (listTables s2Gens) (listTables (s2Gens.map (·⁻¹)))
      (cosetOrderTables s2Q 1 2) (r2Reps.map toTable) 600 = true :=
  (repsOK_of_img s2Gens_len (fun j hj => img2 j (lt_of_lt_of_eq hj s2Gens_len.symm))
    (fun j hj => allN_spec kP2 j hj) (fun j hj => and_of_bAnd (allN_spec kC2 j hj))
    (r2Reps_len.trans (by decide)) (fun i hi => imgR2 i (lt_of_lt_of_eq hi (by decide))) kOff2
    kPos2 cnt2 kR2).1

theorem reps3 : repsOK 693 (listTables s3Gens) (listTables (s3Gens.map (·⁻¹)))
      (cosetOrderTables s3Q 1 2) (r3Reps.map toTable) 600 = true :=
  (repsOK_of_img s3Gens_len (fun j hj => img3 j (lt_of_lt_of_eq hj s3Gens_len.symm))
    (fun j hj => allN_spec kP3 j hj) (fun j hj => and_of_bAnd (allN_spec kC3 j hj))
    (r3Reps_len.trans (by decide)) (fun i hi => imgR3 i (lt_of_lt_of_eq hi (by decide))) kOff3
    kPos3 cnt3 kR3).1

theorem sizesS : repSizes 693 (listTables sGens) (listTables (sGens.map (·⁻¹)))
    (sReps.map toTable) 100 = RS.CS :=
  (repsOK_of_img (X := List.replicate RS.N #[]) sGens_len
    (fun j hj => imgS j (lt_of_lt_of_eq hj sGens_len.symm))
    (fun j hj => allN_spec SQ.perm j (by omega)) (fun j hj => and_of_bAnd (allN_spec kCS j hj))
    (sReps_len.trans (by decide)) (fun i hi => imgRS i (lt_of_lt_of_eq hi (by decide))) kOffS
    kPosS (List.length_replicate ..) kRS).2

theorem cover_check : censusCoverCheck = true := by
  unfold censusCoverCheck
  rw [reps2, reps3, ord_all sz (e := 2) r2Reps_len imgR2 kO2 (by norm_num),
    ord_all sz (e := 2) r3Reps_len imgR3 kO3 (by norm_num)]
  rfl

theorem kSize : allN sRepWords.length (fun i =>
    minK (fixCntK 10 (mask 10) (RS.E (lget RS.OFF i)) 693) (lget RS.CS i) [(53, 2), (21, 8)]) =
    true := by quickRfl

theorem size_check : censusSizeCheck = true := by
  unfold censusSizeCheck
  rw [sizesS]
  refine all_zip_of fun i hl hm => ?_
  have hi : i < sRepWords.length := lt_of_lt_of_eq hl sReps_len
  have hr := imgRS i hi
  rw [List.getD_eq_getElem _ _ hl] at hr
  have hs := allN_spec kSize i hi
  rw [lget_eq RS.CS i, List.getD_eq_getElem _ _ hm] at hs
  have h := minK_spec hs
  simp only [List.all_cons, List.all_nil, Bool.and_true] at h
  dsimp only
  rw [fixCount_img hr]
  exact h

end CertificateChecks.KernelLC.ExcU6

end
