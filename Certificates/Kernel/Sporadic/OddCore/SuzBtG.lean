module

public import Certificates.Kernel.Sporadic.OddCore.SuzBtF
public import Certificates.Kernel.Sporadic.OddCore.SuzBtSF
public import Certificates.Kernel.Sporadic.OddCore.SuzC1EG
public import CFSG.Certificates.Kernel.Spor.SuzC1Base
public import CFSG.Sporadic.SuzRecog.SuzL34.Bridge
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.HeFixKFix
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzBtG

open CFSG.KC.Enum CFSG.KS CFSG.KS.BTup CertificateChecks.KernelSpor
open CFSG.Sporadic.SuzOddCore CFSG.Sporadic.SuzRecog CFSG.Sporadic.SuzRecog.C1Model
open CFSG.Sporadic.SuzRecog.SuzL34Cert CertificateChecks.KernelSpor.SuzC1EG

theorem kBM : allN 8 (fun j => Nat.beq (SuzBtM1.G j) (decK (m1Decs.getD j ([], 0)))) = true := by
  quickRfl

theorem kBS : allN 4 (fun j => Nat.beq (SuzBtS1.G j) (decK (s1pDecs.getD j ([], 0)))) = true := by
  quickRfl

theorem genSub_dec (l : List Dec) :
    genSub 1782 l.length (fun j => decPerm (l.getD j ([], 0))) = decSubgroup l := by
  unfold genSub decSubgroup
  congr 1
  ext g
  constructor
  · rintro ⟨j, hj, rfl⟩
    refine ⟨l.getD j ([], 0), ?_, rfl⟩
    rw [List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem hj
  · rintro ⟨d, hd, rfl⟩
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hd
    exact ⟨j, hj, congrArg decPerm (List.getD_eq_getElem _ _ hj)⟩

theorem pg_decK {d : List Nat × Nat} (hw : ∀ k ∈ d.1, k < 10) (hj : d.2 < 128) (x : Fin 1782) :
    pg 11 (mask 11) (decK d) x = decPerm d x := by
  rw [← CFSG.KC.HeFixK.unpack_getElem! x.2, ← (pDec hw hj).1]
  exact (tabRep_decTab hw hj).2 x

theorem m1Decs_ok {i : Nat} (hi : i < 8) : (∀ k ∈ (m1Decs.getD i ([], 0)).1, k < 10) ∧
    (m1Decs.getD i ([], 0)).2 < 128 := by
  interval_cases i <;> decide

theorem s1pDecs_ok {i : Nat} (hi : i < 4) : (∀ k ∈ (s1pDecs.getD i ([], 0)).1, k < 10) ∧
    (s1pDecs.getD i ([], 0)).2 < 128 := by
  interval_cases i <;> decide

theorem hgM : ∀ j < 8, ∀ x : Fin 1782,
    pg 11 (mask 11) (SuzBtM1.G j) x = decPerm (m1Decs.getD j ([], 0)) x := fun j hj x => by
  rw [Nat.eq_of_beq_eq_true (allN_spec kBM j hj)]
  exact pg_decK (m1Decs_ok hj).1 (m1Decs_ok hj).2 x

theorem hgS : ∀ j < 4, ∀ x : Fin 1782,
    pg 11 (mask 11) (SuzBtS1.G j) x = decPerm (s1pDecs.getD j ([], 0)) x := fun j hj x => by
  rw [Nat.eq_of_beq_eq_true (allN_spec kBS j hj)]
  exact pg_decK (s1pDecs_ok hj).1 (s1pDecs_ok hj).2 x

theorem hbM : ∀ t : Fin 3, pg 11 (mask 11) SuzBtM1.B t = c1Base t := by
  intro t
  fin_cases t <;> rfl

theorem hbS : ∀ t : Fin 3, pg 11 (mask 11) SuzBtS1.B t = c1Base t := by
  intro t
  fin_cases t <;> rfl

theorem m1_eq : genSub 1782 8 (fun j => decPerm (m1Decs.getD j ([], 0))) = decSubgroup m1Decs :=
  genSub_dec m1Decs

theorem s1_eq : genSub 1782 4 (fun j => decPerm (s1pDecs.getD j ([], 0))) = decSubgroup s1pDecs :=
  genSub_dec s1pDecs

theorem card_M1 : Nat.card (decSubgroup m1Decs) = 1024 := by
  rw [← m1_eq, ← SuzBtF.kCnt]
  refine card_genSub_of_btK (w := 11) (kw := 33) (km := mask 33) (K := SuzBtM1.K)
    (R := SuzBtM1.R) (POS := SuzBtM1.POS) (by norm_num) ?_ hgM hbM SuzBtF.kHd fun i hi => ?_
  · rw [m1_eq]
    exact decSubgroup_le_invE (by decide)
  · exact btSl_spec SuzBtF.kSl (Nat.zero_le _) (by rw [SuzBtF.kCnt] at hi; omega) hi

theorem card_S1 : Nat.card (decSubgroup s1pDecs) = 8192 := by
  rw [← s1_eq, ← SuzBtSF.kCnt]
  refine card_genSub_of_btK (w := 11) (kw := 33) (km := mask 33) (K := SuzBtS1.K)
    (R := SuzBtS1.R) (POS := SuzBtS1.POS) (by norm_num) ?_ hgS hbS SuzBtSF.kHd fun i hi => ?_
  · rw [s1_eq]
    exact decSubgroup_le_invE (by decide)
  · rw [SuzBtSF.kCnt] at hi
    rcases Nat.lt_or_ge i 4096 with h1 | h1
    · rcases Nat.lt_or_ge i 2048 with h2 | h2
      · rcases Nat.lt_or_ge i 1024 with h3 | h3
        · exact btSl_spec SuzBtSF.kSl0 (by omega) (by omega) (by rw [SuzBtSF.kCnt]; omega)
        · exact btSl_spec SuzBtSF.kSl1 (by omega) (by omega) (by rw [SuzBtSF.kCnt]; omega)
      · rcases Nat.lt_or_ge i 3072 with h3 | h3
        · exact btSl_spec SuzBtSF.kSl2 (by omega) (by omega) (by rw [SuzBtSF.kCnt]; omega)
        · exact btSl_spec SuzBtSF.kSl3 (by omega) (by omega) (by rw [SuzBtSF.kCnt]; omega)
    · rcases Nat.lt_or_ge i 6144 with h2 | h2
      · rcases Nat.lt_or_ge i 5120 with h3 | h3
        · exact btSl_spec SuzBtSF.kSl4 (by omega) (by omega) (by rw [SuzBtSF.kCnt]; omega)
        · exact btSl_spec SuzBtSF.kSl5 (by omega) (by omega) (by rw [SuzBtSF.kCnt]; omega)
      · rcases Nat.lt_or_ge i 7168 with h3 | h3
        · exact btSl_spec SuzBtSF.kSl6 (by omega) (by omega) (by rw [SuzBtSF.kCnt]; omega)
        · exact btSl_spec SuzBtSF.kSl7 (by omega) (by omega) (by rw [SuzBtSF.kCnt]; omega)

end CertificateChecks.KernelSpor.SuzBtG

end
