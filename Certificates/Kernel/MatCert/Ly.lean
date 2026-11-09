module

public import Certificates.Data.Kernel.OpsMcertN
public import Certificates.Data.Kernel.OpsFpK
public import Certificates.Kernel.SporSch.Ly.BSData
public import Certificates.Kernel.SporSch.Ly.SevA
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.LyThreeInputs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.LyFiveInputs
public import Certificates.Kernel.MatCert.LyNF
public import Certificates.Kernel.MatCert.LyNF5
public import Certificates.Kernel.MatCert.LySnaps
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 500

namespace CertificateChecks.KernelMC

open CFSG.KC.OpsMN CFSG.KC.OpsK CFSG.KC.Ord CFSG.KD.OrdLy CFSG.SectionRank.Native
open CFSG.RankThree.Asc83Table.Native CFSG.AGLEmbedding.R3
open CertificateChecks.KernelSporSch

noncomputable abbrev OL : Ops Nat Nat := opsFpK 5 12 1332 111 8 L H CM RM ONE

@[expose] noncomputable def notStabL (X : Nat) : Bool :=
  !Nat.beq (mulR 5 12 1332 111 8 L H CM RM X LySv.UP)
    (mulR 5 12 1332 111 8 L H CM RM LySv.UP
      (Nat.land (mulR 5 12 1332 111 8 L H CM RM X LySv.UP) (2 ^ (7 * 1332) - 1)))

theorem all_of_groups {α : Type} {p : α → Bool} {fs : List α} {k m : Nat}
    (hm : fs.length ≤ m * k) (h : ∀ i < m, ((fs.drop (i * k)).take k).all p = true) :
    fs.all p = true := by
  have key : ∀ j ≤ m, (fs.take (j * k)).all p = true := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      rw [Nat.succ_mul, List.take_add, List.all_append, ih (by omega), h j (by omega)]
      rfl
  rw [← List.take_of_length_le hm]
  exact key m le_rfl

@[expose] def ly3F : List MFact := lyTzSpec.facts ++ lyCzSpec.facts

@[expose] noncomputable def ly3G (i : Nat) : Bool :=
  ((ly3F.drop (i * 30)).take 30).all (factN OL (LySn.S3 9) lyThreeN)

theorem ly3G0 : ly3G 0 = true := by quickRfl
theorem ly3G1 : ly3G 1 = true := by quickRfl
theorem ly3G2 : ly3G 2 = true := by quickRfl
theorem ly3G3 : ly3G 3 = true := by quickRfl
theorem ly3G4 : ly3G 4 = true := by quickRfl
theorem ly3G5 : ly3G 5 = true := by quickRfl
theorem ly3G6 : ly3G 6 = true := by quickRfl
theorem ly3G7 : ly3G 7 = true := by quickRfl
theorem ly3G8 : ly3G 8 = true := by quickRfl
theorem ly3G9 : ly3G 9 = true := by quickRfl

theorem ly3_facts : ly3F.all (factN OL (LySn.S3 9) lyThreeN) = true := by
  refine all_of_groups (m := 10) (k := 30) (by decide) fun i hi => ?_
  interval_cases i
  exacts [ly3G0, ly3G1, ly3G2, ly3G3, ly3G4, ly3G5, ly3G6, ly3G7, ly3G8, ly3G9]

theorem ly3_fin : (certN OL (LySn.S3 9) ⟨lyThreeN, lyThreeProg, lyTzSpec.facts ++ lyCzSpec.facts⟩ &&
      OL.eq (getN (LySn.S3 9) 0) LyBS.A && OL.eq (getN (LySn.S3 9) 1) LyBS.B &&
      decide (lyTzSpec.gen.rc0 < lyThreeN) && decide (lyTzSpec.gen.rc1 < lyThreeN) &&
      OL.eq (getN (LySn.S3 9) lyTzSpec.gen.rc0) (LyBS.CF 0) &&
      OL.eq (getN (LySn.S3 9) lyTzSpec.gen.rc1) (LyBS.CF 1)) = true := by
  have e : certN OL (LySn.S3 9) ⟨lyThreeN, lyThreeProg, lyTzSpec.facts ++ lyCzSpec.facts⟩ =
      (decide (2 ≤ lyThreeN) && lyThreeProg.all (Op.lt lyThreeN) &&
        ly3F.all (factN OL (LySn.S3 9) lyThreeN)) := rfl
  rw [e, ly3_facts]
  quickRfl

theorem ly3_rest : runN OL LyNF.restProg LyNF.initL2 (fun R =>
    certN OL R ⟨lyThreeN, lyThreeProg, lyTzSpec.facts ++ lyCzSpec.facts⟩ &&
      OL.eq (getN R 0) LyBS.A && OL.eq (getN R 1) LyBS.B &&
      decide (lyTzSpec.gen.rc0 < lyThreeN) && decide (lyTzSpec.gen.rc1 < lyThreeN) &&
      OL.eq (getN R lyTzSpec.gen.rc0) (LyBS.CF 0) &&
      OL.eq (getN R lyTzSpec.gen.rc1) (LyBS.CF 1)) = true :=
  (LySn.run3_eq _).trans ly3_fin

theorem ly3_K : regsN OL LyBS.A LyBS.B lyThreeN lyThreeProg (fun R =>
    certN OL R ⟨lyThreeN, lyThreeProg, lyTzSpec.facts ++ lyCzSpec.facts⟩ &&
      OL.eq (getN R 0) LyBS.A && OL.eq (getN R 1) LyBS.B &&
      decide (lyTzSpec.gen.rc0 < lyThreeN) && decide (lyTzSpec.gen.rc1 < lyThreeN) &&
      OL.eq (getN R lyTzSpec.gen.rc0) (LyBS.CF 0) &&
      OL.eq (getN R lyTzSpec.gen.rc1) (LyBS.CF 1)) = true :=
  (LyNF.regsN_eq_rest _).trans ly3_rest

@[expose] def ly5F : List MFact := lyTzSpec5.facts ++ lyCzSpec5.facts

@[expose] noncomputable def ly5G (i : Nat) : Bool :=
  ((ly5F.drop (i * 50)).take 50).all (factN OL (LySn.S5 3) lyFiveN)

theorem ly5G0 : ly5G 0 = true := by quickRfl
theorem ly5G1 : ly5G 1 = true := by quickRfl
theorem ly5G2 : ly5G 2 = true := by quickRfl
theorem ly5G3 : ly5G 3 = true := by quickRfl
theorem ly5G4 : ly5G 4 = true := by quickRfl
theorem ly5G5 : ly5G 5 = true := by quickRfl
theorem ly5G6 : ly5G 6 = true := by quickRfl
theorem ly5G7 : ly5G 7 = true := by quickRfl
theorem ly5G8 : ly5G 8 = true := by quickRfl
theorem ly5G9 : ly5G 9 = true := by quickRfl
theorem ly5G10 : ly5G 10 = true := by quickRfl

theorem ly5_facts : ly5F.all (factN OL (LySn.S5 3) lyFiveN) = true := by
  refine all_of_groups (m := 11) (k := 50) (by decide) fun i hi => ?_
  interval_cases i
  exacts [ly5G0, ly5G1, ly5G2, ly5G3, ly5G4, ly5G5, ly5G6, ly5G7, ly5G8, ly5G9, ly5G10]

theorem ly5_fin : (certN OL (LySn.S5 3) ⟨lyFiveN, lyFiveProg, lyTzSpec5.facts ++ lyCzSpec5.facts⟩ &&
      OL.eq (getN (LySn.S5 3) 0) LyBS.A && OL.eq (getN (LySn.S5 3) 1) LyBS.B &&
      (List.range 5).all (fun j => decide ((lyTzSpec5.gen.els.getD j default).reg < lyFiveN) &&
        OL.eq (getN (LySn.S5 3) (lyTzSpec5.gen.els.getD j default).reg) (LySv.AF (j + 2))) &&
      decide (lyTzSpec5.gen.rs < lyFiveN) && notStabL (getN (LySn.S5 3) lyTzSpec5.gen.rs)) =
      true := by
  have e : certN OL (LySn.S5 3) ⟨lyFiveN, lyFiveProg, lyTzSpec5.facts ++ lyCzSpec5.facts⟩ =
      (decide (2 ≤ lyFiveN) && lyFiveProg.all (Op.lt lyFiveN) &&
        ly5F.all (factN OL (LySn.S5 3) lyFiveN)) := rfl
  rw [e, ly5_facts]
  quickRfl

theorem ly5_rest : runN OL LyNF5.rest5 LyNF5.init5 (fun R =>
    certN OL R ⟨lyFiveN, lyFiveProg, lyTzSpec5.facts ++ lyCzSpec5.facts⟩ &&
      OL.eq (getN R 0) LyBS.A && OL.eq (getN R 1) LyBS.B &&
      (List.range 5).all (fun j => decide ((lyTzSpec5.gen.els.getD j default).reg < lyFiveN) &&
        OL.eq (getN R (lyTzSpec5.gen.els.getD j default).reg) (LySv.AF (j + 2))) &&
      decide (lyTzSpec5.gen.rs < lyFiveN) && notStabL (getN R lyTzSpec5.gen.rs)) = true :=
  (LySn.run5_eq _).trans ly5_fin

theorem ly5_K : regsN OL LyBS.A LyBS.B lyFiveN lyFiveProg (fun R =>
    certN OL R ⟨lyFiveN, lyFiveProg, lyTzSpec5.facts ++ lyCzSpec5.facts⟩ &&
      OL.eq (getN R 0) LyBS.A && OL.eq (getN R 1) LyBS.B &&
      (List.range 5).all (fun j => decide ((lyTzSpec5.gen.els.getD j default).reg < lyFiveN) &&
        OL.eq (getN R (lyTzSpec5.gen.els.getD j default).reg) (LySv.AF (j + 2))) &&
      decide (lyTzSpec5.gen.rs < lyFiveN) && notStabL (getN R lyTzSpec5.gen.rs)) = true :=
  (LyNF5.regsN_eq_rest5 _).trans ly5_rest

theorem ly3_neg : (!regsN OL LyBS.A LyBS.B lyThreeN lyThreeProg (fun R =>
    OL.eq (getN R lyTzSpec.gen.rc0) (LyBS.CF 1))) = true := by
  have h := ly3_rest
  rw [runN_eq] at h
  simp only [Bool.and_eq_true] at h
  rw [LyNF.regsN_eq_rest, runN_eq]
  change (!Nat.beq _ (LyBS.CF 1)) = true
  rw [Nat.eq_of_beq_eq_true h.1.2]
  quickRfl

theorem ly5_neg : (!notStabL (LySv.AF 2)) = true := by
  quickRfl

end CertificateChecks.KernelMC

end
