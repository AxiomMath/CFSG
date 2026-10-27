module

public import CFSG.GH74.GLS.Stage4.Q9.ModelBase
public import CFSG.CharacterTheory.PSL2Table
public import CFSG.GH74.GLS.Stage4.Q9.TablesInputs
public import CFSG.Certificates.Kernel.Q9SLSound
public import Certificates.Kernel.Q9SL.Data
import Certificates.Kernel.Q9SL.Checks
import all CFSG.GH74.GLS.Stage4.Q9.ModelBaseInputs
import all CFSG.GH74.GLS.Stage4.Q9.ModelBase
import all CFSG.GH74.GLS.Stage4.Q9.TablesInputs

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelQ9SL

open CFSG.KC.Q9SL CFSG.GH74.GLS.Stage4.Q9 CFSG.GH74.GLS.Stage4.Q9.Tables

local notation "𝕄" => Matrix (Fin 2) (Fin 2) F9

theorem allF9_mem : ∀ x : F9, x ∈ allF9 := by decide +kernel

theorem allSL2_mem (M : SL2) : M ∈ allSL2 := by
  have h := M.det_coe
  rw [Matrix.det_fin_two] at h
  simp only [allSL2, List.mem_flatMap, List.mem_filterMap]
  refine ⟨(M : 𝕄) 0 0, allF9_mem _, (M : 𝕄) 0 1, allF9_mem _, (M : 𝕄) 1 0, allF9_mem _,
    (M : 𝕄) 1 1, allF9_mem _, ?_⟩
  split
  · exact congrArg some (Subtype.ext (Matrix.eta_fin_two _).symm)
  · rename_i hne
    exact absurd h hne

theorem L_eq : allSL2.map enc = CFSG.KD.Q9SL.L := eq_of_beq ch5102enc

theorem enc_mem (M : SL2) : enc M ∈ CFSG.KD.Q9SL.L := by
  rw [← L_eq]
  exact List.mem_map_of_mem (allSL2_mem M)

theorem allSL2_length : allSL2.length = 720 := by
  rw [← List.length_map (f := enc), L_eq]
  exact (ckSort_spec ch5102sort).1

theorem allSL2_nodup : allSL2.Nodup := by
  have h : CFSG.KD.Q9SL.L.Nodup := (ckSort_spec ch5102sort).2.imp Nat.ne_of_lt
  rw [← L_eq] at h
  exact h.of_map enc

theorem of_allL {f : Nat → Bool} (h : allL CFSG.KD.Q9SL.L f = true) (M : SL2) : f (enc M) = true :=
  (allL_spec _ _).1 h _ (enc_mem M)

theorem enc_repList : ∀ j : Fin 7, enc (repList j) = ln CFSG.KD.Q9SL.RP j.val := by decide +kernel

theorem repS_repList (j : Fin 7) : repS (enc (repList j)) = j.val := by
  rw [enc_repList]
  exact ckRep_spec ch5102rep j.val j.isLt

theorem repIdx_eq_iff {M : SL2} {j : Fin 7} : repIdx M = j ↔ repS (enc M) = j.val := by
  rw [Fin.ext_iff, repIdx_val]

theorem c5102_repList : ∀ j : Fin 7, repIdx (repList j) = j := fun j =>
  repIdx_eq_iff.2 (repS_repList j)

theorem c5102_spec : ∀ M ∈ allSL2, ∃ c ∈ allSL2, IsRepOf (repList (repIdx M)) (conjSL c M) := by
  intro M _
  obtain ⟨w, hw⟩ := all2_exists _ _ _ ch5102wit (enc M) (enc_mem M)
  simp only [brec_and, brec_or, Bool.and_eq_true, Bool.or_eq_true, Nat.blt_eq, Nat.beq_eq] at hw
  obtain ⟨hw7, hw⟩ := hw
  have hwl : w < allSL2.length := by rw [allSL2_length]; exact hw7
  have hLP : ckLP (allSL2.map enc) CFSG.KD.Q9SL.LP = true := by
    rw [L_eq]
    exact ch5102lp
  have hc : ln CFSG.KD.Q9SL.LP w = enc allSL2[w] := by
    rw [ln_of_ckLP hLP w (by rw [List.length_map]; exact hwl), List.getElem_map]
  have hr : ln CFSG.KD.Q9SL.RP (repS (enc M)) = enc (repList (repIdx M)) := by
    rw [← repIdx_val, enc_repList]
  refine ⟨allSL2[w], List.getElem_mem hwl, ?_⟩
  rw [hc, hr, ← enc_conjSL, ← enc_mul_minusOne] at hw
  rcases hw with h | h
  · exact Or.inl (enc_inj h)
  · exact Or.inr (enc_inj h)

theorem j_mem (j : Fin 7) : j.val ∈ [0, 1, 2, 3, 4, 5, 6] := by
  revert j
  decide

theorem c5102_conj : ∀ j : Fin 7, ∀ d ∈ allSL2,
    repIdx (conjSL d (repList j)) = j ∧ repIdx (conjSL d (repList j * minusOne)) = j := by
  intro j d _
  have h := (allL_spec _ _).1 (of_allL ch5102conj d) j.val (j_mem j)
  simp only [brec_and, Bool.and_eq_true, Nat.beq_eq] at h
  rw [← enc_repList, ← enc_mul_minusOne, ← enc_conjSL, ← enc_conjSL] at h
  exact ⟨repIdx_eq_iff.2 h.1, repIdx_eq_iff.2 h.2⟩

theorem c5102_neg : ∀ M ∈ allSL2, repIdx (M * minusOne) = repIdx M := by
  intro M _
  have h := of_allL ch5102neg M
  simp only [Nat.beq_eq, ← enc_mul_minusOne] at h
  exact repIdx_eq_iff.2 (h.trans (repIdx_val M).symm)

theorem c5102_sigma : ∀ M ∈ allSL2, repIdx (sigmaAut M) = classSwap (repIdx M) := by
  intro M _
  have h := of_allL ch5102sig M
  simp only [Nat.beq_eq, ← enc_sigma] at h
  rw [repIdx_eq_iff, h, classSwap_val, repIdx_val]

theorem c5102_inv : ∀ M ∈ allSL2, repIdx (invSL M) = repIdx M := by
  intro M _
  have h := of_allL ch5102inv M
  simp only [Nat.beq_eq, ← enc_invSL] at h
  exact repIdx_eq_iff.2 (h.trans (repIdx_val M).symm)

theorem card_repIdx_cntL (j : Fin 7) :
    (Finset.univ.filter fun M : SL2 => repIdx M = j).card =
      cntL CFSG.KD.Q9SL.L (fun x => Nat.beq (repS x) j.val) := by
  have hU : (Finset.univ : Finset SL2) = allSL2.toFinset := by
    ext M
    simp [allSL2_mem M]
  have hF : (allSL2.toFinset.filter fun M => repIdx M = j) =
      (allSL2.filter fun M => Nat.beq (repS (enc M)) j.val).toFinset := by
    ext M
    simp [repIdx_eq_iff]
  rw [hU, hF, List.toFinset_card_of_nodup (allSL2_nodup.filter _), cntL_eq, ← L_eq,
    List.filter_map, List.length_map]
  rfl

theorem c5102_card : ∀ j : Fin 7,
    (Finset.univ.filter fun M : SL2 => repIdx M = j).card = ![2, 80, 80, 90, 180, 144, 144] j := by
  intro j
  rw [card_repIdx_cntL]
  have h := (allI_spec _ _ 0).1 ch5102cnt j.val (lt_of_lt_of_eq j.isLt rfl)
  simp only [Nat.zero_add, Nat.beq_eq] at h
  rw [h]
  fin_cases j <;> rfl

theorem zero_key : ∀ a b c : Bool,
    Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) true false c) false b)
      (Bool.rec (motive := fun _ => Bool) c true b) a = true → (a = true ↔ b = true ∨ c = true) := by
  decide

theorem c5102_zero : ∀ M ∈ allSL2, (repIdx M = 0 ↔ M = 1 ∨ M = minusOne) := by
  intro M _
  have h := zero_key _ _ _ (of_allL ch5102zero M)
  simp only [Nat.beq_eq, enc_eq_oneS, enc_eq_moneS] at h
  rw [repIdx_eq_iff]
  exact h

theorem c5102_ord : ∀ M ∈ allSL2, ordL (innerL M) = orderFn (repIdx M) (trSL2 M) := by
  intro M _
  have h := of_allL ch5102ord M
  simp only [Nat.beq_eq] at h
  rw [ordL_innerL, h, orderFn_eq, repIdx_val, trS_enc]

end CertificateChecks.KernelQ9SL
