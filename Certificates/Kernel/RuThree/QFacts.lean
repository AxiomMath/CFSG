module

public import Certificates.Kernel.RuThree.QK
public import Certificates.Kernel.RuThree.Facts
public import CFSG.Certificates.Kernel.LinesPKSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelRuThree

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.HeLoc CFSG.KC.J2H
open CFSG.KC.B3S3K CFSG.KC.Misc.ArrEnum CFSG.KC.LinesPK
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Mathieu CFSG.Monster.B.Fischer
open CFSG.RankThree.Native CFSG.RankThree.PartOne CFSG.Sporadic.RuSchreier CFSG.Sporadic.Schreier
open CFSG.Certificates CFSG.Certificates.Native CFSG.EvenSporadicStandard.RuStd.S2

theorem getMap {l : List (List ℤ)} {j : ℕ} (hj : j < l.length) :
    (l.map ruThreeEval).toArray[j]! = ruThreeEval (l.getD j []) := by
  rw [getElem!_pos _ j (by simpa using hj), List.getD_eq_getElem _ _ hj]
  simp


theorem wordBind {wd : List ℤ} {r : ℕ}
    (h : wordEqK 4060 12 (mask 12) (pidn 4060 12) S3R.S S3R.SI 11 wd r = true) :
    ruThreeEval wd = unpack 4060 12 r :=
  (wordEqK_sound ⟨binds.2.2.2.1, binds.2.2.2.2.1⟩ kPerm h).1

theorem wordSift {wd : List ℤ} {r : ℕ}
    (h : wordEqK 4060 12 (mask 12) (pidn 4060 12) S3R.S S3R.SI 11 wd r = true) :
    siftA 4060 (rawLevels 4060 ruThreeArrs ruThreeBaseArr) ruThreeBaseArr 0 (ruThreeEval wd) =
      true := by
  rw [wordBind h]
  exact (sift_iff (word_rep binds kPerm h)).2
    (sgnProd_mem (m := 11) (fun i hi => faith.2 i (by rw [hsize]; exact hi)) _
      (wordEqK_sound ⟨binds.2.2.2.1, binds.2.2.2.2.1⟩ kPerm h).2)

theorem qg_eq {k : ℕ} (hk : k < 2) : ruThreeQGens[k]! = ruThreeEval (qWords.getD k []) := by
  interval_cases k <;> rfl

theorem bindQ : BindA 4060 12 ruThreeQGens 2 QGP :=
  ⟨rfl, fun k hk => (qg_eq hk).trans (wordBind (Orb.allN_iff.1 kQW k hk))⟩

theorem ln_eq {j : ℕ} (hj : j < 13) :
    ruThreeLines[j]! = ruThreeEval (ruThreeLineWords.getD j []) :=
  getMap (by simpa [ruThreeLineWords] using hj)

theorem tr_eq {j : ℕ} (hj : j < 13) :
    ruThreeTransporters[j]! = ruThreeEval (ruThreeTransWords.getD j []) :=
  getMap (by simpa [ruThreeTransWords] using hj)

theorem bindL : BindA 4060 12 ruThreeLines 13 LNP :=
  ⟨by simp [ruThreeLines, ruThreeLineWords], fun j hj =>
    (ln_eq hj).trans (wordBind (Orb.allN_iff.1 kLW j hj))⟩

theorem bindH : BindA 4060 12 ruThreeTransporters 13 TRP :=
  ⟨by simp [ruThreeTransporters, ruThreeTransWords], fun j hj =>
    (tr_eq hj).trans (wordBind (Orb.allN_iff.1 kTW j hj))⟩

theorem enumQ : enumOK 4060 ruThreeQGens ruThreeKeys ruThreeQCert = true ∧
    ruThreeQCert.pts.size = RQ.N ∧ ∀ i < RQ.N, ruThreeQCert.pts[i]! = unpack 4060 12 (RQ.T i) := by
  have hng := Nat.eq_of_beq_eq_true kRQ.2.1
  have hb : BindA 4060 12 ruThreeQGens RQ.ng RQ.G := by
    rw [hng]
    refine ⟨rfl, fun j hj => ?_⟩
    rw [bindQ.2 j hj, Nat.eq_of_beq_eq_true (Orb.allN_iff.1 kRQ.2.2 j hj)]
  have hp : ∀ k < RQ.ng, permB 4060 12 (RQ.G k) = true := fun k hk => by
    rw [hng] at hk
    rw [Nat.eq_of_beq_eq_true (Orb.allN_iff.1 kRQ.2.2 k hk)]
    exact Orb.allN_iff.1 kQP k hk
  exact enum_of (ps := ruThreeKeys) (fuel := 40) hb hp RQ.ok keys_lt RQ.keys
    (by rw [Nat.eq_of_beq_eq_true kRQ.1]; omega)

theorem lines_ok : linesOKG 3 27 13 4060 ruThreeQGens ruThreeKeys ruThreeQCert ruThreeLines =
    true := by
  obtain ⟨h1, h2, h3⟩ := enumQ
  have hN := Nat.eq_of_beq_eq_true kRQ.1
  rw [hN] at h2 h3
  exact linesOKG_of sz h1 h2 h3
    (fun i hi => Orb.allN_iff.1 kRQP i hi) bindL kLines

theorem siftQ_ok : allLt ruThreeQGens.size
    (fun l => siftA 4060 ruThreeLevels ruThreeBaseArr 0 ruThreeQGens[l]!) = true := by
  rw [allLt_iff]
  intro l hl
  have hl' : l < 2 := hl
  rw [qg_eq hl']
  exact wordSift (Orb.allN_iff.1 kQW l hl')

theorem trans_ok : transOKG 13 4060 ruThreeTransporters ruThreeLines ruThreeRec ruThreeLevels
    ruThreeBaseArr = true :=
  transOKG_of sz (by norm_num) bindH bindL (fun j hj => Orb.allN_iff.1 kLP j hj)
    (fun j hj => by rw [tr_eq hj]; exact wordSift (Orb.allN_iff.1 kTW j hj)) kTrans

open CFSG.EvenSporadicStandard.RuStd.S2 CFSG.RankThree.PartOne CFSG.RankThree.Native
  CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.RuSchreier in
open Certificates in
theorem ok24945 :
    linesOKG 3 27 13 4060 ruThreeQGens ruThreeKeys ruThreeQCert ruThreeLines = true ∧
      allLt ruThreeQGens.size
        (fun l => siftA 4060 ruThreeLevels ruThreeBaseArr 0 ruThreeQGens[l]!) = true ∧
      transOKG 13 4060 ruThreeTransporters ruThreeLines ruThreeRec ruThreeLevels
        ruThreeBaseArr = true ∧
      allLt 13 (fun j => (List.range 1).any fun i => ruThreeRec.getD j 0 == i) = true ∧
      ruThreeRec.getD 0 0 = 0 :=
  ⟨lines_ok, siftQ_ok, trans_ok, by
    rw [allLt_iff]
    intro j hj
    interval_cases j <;> rfl, rfl⟩

end CertificateChecks.KernelRuThree

end
