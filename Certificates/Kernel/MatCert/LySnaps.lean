module

public import Certificates.Kernel.MatCert.LyNF
public import Certificates.Kernel.MatCert.LyNF5
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

set_option Elab.async false


#kc_repo #kc_decls CertificateChecks.KernelMC.LySn "Certificates/Kernel/MatCert/data/ly3snaps.txt" 2255223 17368072350998598219

#kc_repo #kc_decls CertificateChecks.KernelMC.LySn "Certificates/Kernel/MatCert/data/ly5snaps.txt" 591534 2434707764083665067


public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMC.LySn

open CFSG.KC.OpsMN CFSG.KC.OpsK CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native
open CertificateChecks.KernelMC.LyNF (OL)

@[expose] def eqLN : List Nat → List Nat → Bool
  | [], [] => true
  | x :: a, y :: b => Nat.beq x y && eqLN a b
  | _, _ => false

theorem eqLN_eq : ∀ {a b : List Nat}, eqLN a b = true → a = b
  | [], [], _ => rfl
  | x :: a, y :: b, h => by
    simp only [eqLN, Bool.and_eq_true] at h
    rw [Nat.eq_of_beq_eq_true h.1, eqLN_eq h.2]
  | [], _ :: _, h => by simp [eqLN] at h
  | _ :: _, [], h => by simp [eqLN] at h

@[expose] def chunk (P : List Op) (off : Nat → Nat) (i : Nat) : List Op :=
  (P.drop (off i)).take (off (i + 1) - off i)

theorem fold_chunks {f : List Nat → Op → List Nat} {P : List Op} {off : Nat → Nat}
    {S : Nat → List Nat} {m : Nat} (h0 : off 0 = 0) (hoff : ∀ i < m, off i ≤ off (i + 1))
    (hend : P.length ≤ off m) (hc : ∀ i < m, (chunk P off i).foldl f (S i) = S (i + 1)) :
    P.foldl f (S 0) = S m := by
  have key : ∀ j ≤ m, (P.take (off j)).foldl f (S 0) = S j := by
    intro j
    induction j with
    | zero => intro _; rw [h0]; rfl
    | succ j ih =>
      intro hj
      have e : off (j + 1) = off j + (off (j + 1) - off j) := by have := hoff j (by omega); omega
      rw [e, List.take_add, List.foldl_append, ih (by omega)]
      exact hc j (by omega)
  rw [← List.take_of_length_le hend]
  exact key m le_rfl

theorem chunk_of {P : List Op} {off : Nat → Nat} {S : Nat → List Nat} {i : Nat}
    (h : runN OL (chunk P off i) (S i) (fun R => eqLN R (S (i + 1))) = true) :
    (chunk P off i).foldl (stepL OL) (S i) = S (i + 1) := by
  rw [runN_eq] at h
  exact eqLN_eq h

@[expose] def off3 (i : Nat) : Nat := [0, 16, 155, 306, 456, 608, 762, 914, 1066, 1145].getD i 0

@[expose] noncomputable def upd3 : Nat → List Nat → List Nat
  | 0, R => ((((((((((((((((R.set 7 v3_0_7).set 8 v3_0_8).set 9 v3_0_9).set 10 v3_0_10).set 11 v3_0_11).set 12 v3_0_12).set 13 v3_0_13).set 14 v3_0_14).set 15 v3_0_15).set 16 v3_0_16).set 17 v3_0_17).set 18 v3_0_18).set 19 v3_0_19).set 20 v3_0_20).set 21 v3_0_21).set 22 v3_0_22)
  | 1, R => (((((((((((((R.set 23 v3_1_23).set 24 v3_1_24).set 25 v3_1_25).set 26 v3_1_26).set 27 v3_1_27).set 28 v3_1_28).set 29 v3_1_29).set 30 v3_1_30).set 31 v3_1_31).set 32 v3_1_32).set 33 v3_1_33).set 34 v3_1_34).set 35 v3_1_35)
  | 2, R => ((((R.set 35 v3_2_35).set 36 v3_2_36).set 37 v3_2_37).set 38 v3_2_38)
  | 3, R => (R.set 38 v3_3_38)
  | 4, R => (((((((((((R.set 38 v3_4_38).set 39 v3_4_39).set 40 v3_4_40).set 41 v3_4_41).set 42 v3_4_42).set 43 v3_4_43).set 44 v3_4_44).set 45 v3_4_45).set 46 v3_4_46).set 47 v3_4_47).set 48 v3_4_48)
  | 5, R => ((((((R.set 48 v3_5_48).set 49 v3_5_49).set 50 v3_5_50).set 51 v3_5_51).set 52 v3_5_52).set 53 v3_5_53)
  | 6, R => (((R.set 53 v3_6_53).set 54 v3_6_54).set 55 v3_6_55)
  | 7, R => ((((R.set 55 v3_7_55).set 56 v3_7_56).set 57 v3_7_57).set 58 v3_7_58)
  | 8, R => (((R.set 58 v3_8_58).set 59 v3_8_59).set 60 v3_8_60)
  | _, R => R

@[expose] noncomputable def S3 (i : Nat) : List Nat :=
  Nat.rec (motive := fun _ => List Nat) LyNF.initL2 (fun j R => upd3 j R) i

theorem ch3_0 : runN OL (chunk LyNF.restProg off3 0) (S3 0)
    (fun R => eqLN R (S3 (0 + 1))) = true := by quickRfl

theorem ch3_1 : runN OL (chunk LyNF.restProg off3 1) (S3 1)
    (fun R => eqLN R (S3 (1 + 1))) = true := by quickRfl

theorem ch3_2 : runN OL (chunk LyNF.restProg off3 2) (S3 2)
    (fun R => eqLN R (S3 (2 + 1))) = true := by quickRfl

theorem ch3_3 : runN OL (chunk LyNF.restProg off3 3) (S3 3)
    (fun R => eqLN R (S3 (3 + 1))) = true := by quickRfl

theorem ch3_4 : runN OL (chunk LyNF.restProg off3 4) (S3 4)
    (fun R => eqLN R (S3 (4 + 1))) = true := by quickRfl

theorem ch3_5 : runN OL (chunk LyNF.restProg off3 5) (S3 5)
    (fun R => eqLN R (S3 (5 + 1))) = true := by quickRfl

theorem ch3_6 : runN OL (chunk LyNF.restProg off3 6) (S3 6)
    (fun R => eqLN R (S3 (6 + 1))) = true := by quickRfl

theorem ch3_7 : runN OL (chunk LyNF.restProg off3 7) (S3 7)
    (fun R => eqLN R (S3 (7 + 1))) = true := by quickRfl

theorem ch3_8 : runN OL (chunk LyNF.restProg off3 8) (S3 8)
    (fun R => eqLN R (S3 (8 + 1))) = true := by quickRfl

theorem len3 : LyNF.restProg.length ≤ off3 9 := by decide

theorem mono3 : ∀ i < 9, off3 i ≤ off3 (i + 1) := by decide

theorem run3_eq (k : List Nat → Bool) : runN OL LyNF.restProg LyNF.initL2 k = k (S3 9) := by
  rw [runN_eq]
  congr 1
  refine fold_chunks (S := S3) rfl mono3 len3 fun i hi => ?_
  interval_cases i
  · exact chunk_of ch3_0
  · exact chunk_of ch3_1
  · exact chunk_of ch3_2
  · exact chunk_of ch3_3
  · exact chunk_of ch3_4
  · exact chunk_of ch3_5
  · exact chunk_of ch3_6
  · exact chunk_of ch3_7
  · exact chunk_of ch3_8

@[expose] def off5 (i : Nat) : Nat := [0, 151, 307, 317].getD i 0

@[expose] noncomputable def upd5 : Nat → List Nat → List Nat
  | 0, R => (((((((R.set 14 v5_0_14).set 15 v5_0_15).set 16 v5_0_16).set 17 v5_0_17).set 18 v5_0_18).set 19 v5_0_19).set 20 v5_0_20)
  | 1, R => (((((((R.set 20 v5_1_20).set 21 v5_1_21).set 22 v5_1_22).set 23 v5_1_23).set 24 v5_1_24).set 25 v5_1_25).set 26 v5_1_26)
  | 2, R => ((R.set 26 v5_2_26).set 27 v5_2_27)
  | _, R => R

@[expose] noncomputable def S5 (i : Nat) : List Nat :=
  Nat.rec (motive := fun _ => List Nat) LyNF5.init5 (fun j R => upd5 j R) i

theorem ch5_0 : runN OL (chunk LyNF5.rest5 off5 0) (S5 0)
    (fun R => eqLN R (S5 (0 + 1))) = true := by quickRfl

theorem ch5_1 : runN OL (chunk LyNF5.rest5 off5 1) (S5 1)
    (fun R => eqLN R (S5 (1 + 1))) = true := by quickRfl

theorem ch5_2 : runN OL (chunk LyNF5.rest5 off5 2) (S5 2)
    (fun R => eqLN R (S5 (2 + 1))) = true := by quickRfl

theorem len5 : LyNF5.rest5.length ≤ off5 3 := by decide

theorem mono5 : ∀ i < 3, off5 i ≤ off5 (i + 1) := by decide

theorem run5_eq (k : List Nat → Bool) : runN OL LyNF5.rest5 LyNF5.init5 k = k (S5 3) := by
  rw [runN_eq]
  congr 1
  refine fold_chunks (S := S5) rfl mono5 len5 fun i hi => ?_
  interval_cases i
  · exact chunk_of ch5_0
  · exact chunk_of ch5_1
  · exact chunk_of ch5_2

end CertificateChecks.KernelMC.LySn

end
