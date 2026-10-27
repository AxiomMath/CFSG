module

public import Certificates.Kernel.Sporadic.Fi22.Five8124G

public section

namespace CertificateChecks.KernelSpor.Fv8124

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin
open CertificateChecks.KernelSpor
open CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer
open CFSG.Sporadic.FischerOddCore CFSG.KC.Fv8124
open scoped commutatorElement

theorem rep_self {t : Array ℕ} {g : Equiv.Perm (Fin 3510)} (h : Rep 3510 t g) :
    Rep 3510 t (permOfArr 3510 t) := by
  rw [permOfArr_eq_of_rep h]
  exact h

theorem rep_lineArr (j : ℕ) :
    Rep 3510 (fi22FiveLineArr j) (permOfArr 3510 (fi22FiveLineArr j)) := by
  unfold fi22FiveLineArr
  split_ifs
  · rw [q1Arr_eq]
    exact rep_self (rep_pe pQ1)
  · rw [q2Arr_eq]
    exact rep_self (rep_pe pQ2)
  · rw [q1Arr_eq, q2Arr_eq]
    exact rep_self (rep_compA (rep_pe pQ1) (CFSG.Monster.B.Fischer.rep_powA (rep_pe pQ2) _))

theorem rep_qgens :
    ∀ k < 2, Rep 3510 fi22FiveQGenArrs[k]! (permOfArr 3510 fi22FiveQGenArrs[k]!) := by
  intro k hk
  interval_cases k
  · have e : fi22FiveQGenArrs[0]! = fi22FiveQ1Arr := by simp [fi22FiveQGenArrs]
    rw [e, q1Arr_eq]
    exact rep_self (rep_pe pQ1)
  · have e : fi22FiveQGenArrs[1]! = fi22FiveQ2Arr := by simp [fi22FiveQGenArrs]
    rw [e, q2Arr_eq]
    exact rep_self (rep_pe pQ2)

theorem cgen1_get (j : ℕ) :
    (fi22FiveCGenArrs j)[1]! = conjInvA 3510 (fi22FiveHArr j) fi22FiveAArr := by
  simp [fi22FiveCGenArrs]

theorem cgen2_get (j : ℕ) :
    (fi22FiveCGenArrs j)[2]! = conjInvA 3510 (fi22FiveHArr j) fi22FiveQ2Arr := by
  simp [fi22FiveCGenArrs]

theorem rep_cgen1 (j : Fin 6) :
    Rep 3510 (fi22FiveCGenArrs j)[1]! (φ j (pe A)) := by
  rw [cgen1_get, φ_apply, aArr_eq]
  exact rep_conjInvA (validH j.2) (rep_pe pA)

theorem rep_cgen2 (j : Fin 6) :
    Rep 3510 (fi22FiveCGenArrs j)[2]! (φ j (pe Q2)) := by
  rw [cgen2_get, φ_apply, q2Arr_eq]
  exact rep_conjInvA (validH j.2) (rep_pe pQ2)

theorem rep_cgens (j : Fin 6) :
    ∀ k < 4, Rep 3510 (fi22FiveCGenArrs j)[k]! (permOfArr 3510 (fi22FiveCGenArrs j)[k]!) := by
  intro k hk
  interval_cases k
  · have e : (fi22FiveCGenArrs j)[0]! = fi22FiveLineArr j := by simp [fi22FiveCGenArrs]
    rw [e]
    exact rep_lineArr j
  · exact rep_self (rep_cgen1 j)
  · exact rep_self (rep_cgen2 j)
  · have e : (fi22FiveCGenArrs j)[3]! = fi22FiveWArr := by simp [fi22FiveCGenArrs]
    have ew : fi22FiveWArr = unpack 3510 12 W := fiveArr_eq (by norm_num)
    rw [e, ew]
    exact rep_self (rep_pe pW)

theorem trans_conj (j : Fin 6) :
    permOfArr 3510 (fi22FiveHArr j) ∈ fi22P ∧
      permOfArr 3510 (fi22FiveHArr j) * fi22FiveLine j * (permOfArr 3510 (fi22FiveHArr j))⁻¹ =
        fi22FiveLine 0 := by
  obtain ⟨h1, h2, -⟩ := trans_facts j
  refine ⟨h1, ?_⟩
  change hT j * fi22FiveLine j * (hT j)⁻¹ = fi22FiveLine 0
  rw [h2, mul_inv_cancel_right]

theorem cgen_P
    (j : Fin 6) :
    ∀ k, 1 ≤ k → k < 3 → permOfArr 3510 (fi22FiveCGenArrs j)[k]! ∈ fi22P := by
  intro k hk1 hk3
  obtain rfl | rfl : k = 1 ∨ k = 2 := by omega
  · rw [permOfArr_eq_of_rep (rep_cgen1 j)]
    exact (recHyp j).aP
  · rw [permOfArr_eq_of_rep (rep_cgen2 j)]
    exact (recHyp j).bP

theorem d_eq
    (j : Fin 6) :
    fi22FiveD j = Subgroup.closure (permsA 3510 (fi22FiveDGenArrs j)) := by
  have hC : fi22FiveC j =
      Subgroup.closure ({fi22FiveLine j, φ j (pe A), φ j (pe Q2), pe W} : Set _) := by
    unfold fi22FiveC
    rw [cgens_eq]
  have r1 := rep_cgen1 j
  have r2 := rep_cgen2 j
  have ea : permOfArr 3510
      (commutatorA 3510 (fi22FiveCGenArrs j)[1]! (fi22FiveCGenArrs j)[2]!) =
        ⁅φ j (pe A), φ j (pe Q2)⁆ := by
    rw [permOfArr_eq_of_rep (rep_commutatorA (CFSG.RankThree.Native.F2.validA_of_rep r1)
      (CFSG.RankThree.Native.F2.validA_of_rep r2)), permOfArr_eq_of_rep r1,
      permOfArr_eq_of_rep r2]
  have hD : permsA 3510 (fi22FiveDGenArrs j) =
      ({⁅φ j (pe A), φ j (pe Q2)⁆, φ j (pe Q2)} : Set _) := by
    unfold fi22FiveDGenArrs
    rw [permsA_two, ea, permOfArr_eq_of_rep r2]
  unfold fi22FiveD
  rw [hC, hD]
  exact (recHyp j).D_eq

open CFSG CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Monster.B.Fischer in
theorem holds :

    ((fi22FiveQ ≤ fi22P ∧ IsElementaryAbelian 5 fi22FiveQ ∧ Nat.card fi22FiveQ = 25 ∧
      ∃ S : Sylow 5 fi22P, (S : Subgroup fi22P) = fi22FiveQ.subgroupOf fi22P) ∧
    ({H : Subgroup (Equiv.Perm (Fin 3510)) | H ≤ fi22FiveQ ∧ Nat.card H = 5} =
        Set.range (fun i : Fin 6 => Subgroup.zpowers (fi22FiveLine i)) ∧
      Function.Injective (fun i : Fin 6 => Subgroup.zpowers (fi22FiveLine i))) ∧
    (fi22FiveW ∈ fi22R ∧ fi22FiveW ∉ fi22P ∧ orderOf fi22FiveW = 2) ∧
    ∀ i : Fin 6,
      fi22FiveC i = Subgroup.centralizer {fi22FiveLine i} ⊓ fi22R ∧
      Nat.card (fi22FiveC i) = 1200 ∧
      fi22FiveC i ⊓ fi22P = Subgroup.centralizer {fi22FiveLine i} ⊓ fi22P ∧
      Nat.card (fi22FiveC i ⊓ fi22P : Subgroup (Equiv.Perm (Fin 3510))) = 600 ∧
      fi22FiveD i ≤ fi22P ∧ IsSimpleGroup (fi22FiveD i) ∧
      (∃ g ∈ fi22FiveD i, ∃ h ∈ fi22FiveD i, g * h ≠ h * g) ∧ Nat.card (fi22FiveD i) = 60 ∧
      fi22FiveW ∈ (Subgroup.center (fi22FiveC i)).map (fi22FiveC i).subtype ∧
      Subgroup.centralizer (fi22FiveD i : Set (Equiv.Perm (Fin 3510))) ⊓ fi22FiveC i =
        Subgroup.zpowers (fi22FiveLine i) ⊔ Subgroup.zpowers fi22FiveW ∧
      Subgroup.zpowers (fi22FiveLine i) ⊓ Subgroup.zpowers fi22FiveW = ⊥ ∧
      Commute (fi22FiveLine i) fi22FiveW ∧
      Nat.card (Subgroup.centralizer (fi22FiveD i : Set (Equiv.Perm (Fin 3510))) ⊓ fi22FiveC i :
        Subgroup (Equiv.Perm (Fin 3510))) = 10 ∧
      Subgroup.centralizer (fi22FiveD i : Set (Equiv.Perm (Fin 3510))) ⊓ (fi22FiveC i ⊓ fi22P) =
        Subgroup.zpowers (fi22FiveLine i)) ∧
    (∀ i : Fin 6, permOfArr 3510 (fi22FiveHArr i) ∈ fi22P ∧
      permOfArr 3510 (fi22FiveHArr i) * fi22FiveLine i * (permOfArr 3510 (fi22FiveHArr i))⁻¹ =
        fi22FiveLine 0) ∧
    (∀ k < 2, Rep 3510 fi22FiveQGenArrs[k]! (permOfArr 3510 fi22FiveQGenArrs[k]!)) ∧
    ∀ i : Fin 6,
      (∀ k < 4, Rep 3510 (fi22FiveCGenArrs i)[k]! (permOfArr 3510 (fi22FiveCGenArrs i)[k]!)) ∧
      (∀ k, 1 ≤ k → k < 3 → permOfArr 3510 (fi22FiveCGenArrs i)[k]! ∈ fi22P) ∧
      fi22FiveD i = Subgroup.closure (permsA 3510 (fi22FiveDGenArrs i)) :=
  ⟨facts, trans_conj, rep_qgens, fun j => ⟨rep_cgens j, cgen_P j, d_eq j⟩⟩

end CertificateChecks.KernelSpor.Fv8124
