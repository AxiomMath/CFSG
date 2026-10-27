module

public import Certificates.Kernel.Sporadic.ONVec.Mat
public import Certificates.Kernel.Sporadic.ONVec.MatS
public import Certificates.Kernel.Sporadic.ON.Final
public import CFSG.Certificates.Kernel.Spor.ONVecSound
public import CFSG.Certificates.Kernel.Spor.ONDiscSound
public import CFSG.Certificates.Kernel.Spor.ONNegSound
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Spor.PackFld
import Mathlib.Tactic.NormNum
public import CFSG.Certificates.Kernel.Spor.ONMvSound
public import CFSG.Certificates.Kernel.Spor.ONSplitSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ONVec

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON CFSG.F3.Native CFSG.Sporadic.Fi23.Native
open CFSG.Sporadic.ON.Native CFSG.ONSchreier.Native CFSG.Sporadic.Th.Native
open CertificateChecks.KernelSpor

theorem hcA : colsA.size = 154 ∧ ONV.LA.length = 154 ∧
    ∀ j < 154, colsA[j]! = wOfK (ONV.LA.getD j 0) := by
  unfold colsA rowsA
  exact ON.cols_of ONSeedA.eq ON.colsAK (ON.list_eq ONV.LA ONV.CA (allN_spec ON.listA)) rfl

theorem hcB : colsB.size = 154 ∧ ONV.LB.length = 154 ∧
    ∀ j < 154, colsB[j]! = wOfK (ONV.LB.getD j 0) := by
  unfold colsB rowsB
  exact ON.cols_of ONSeedB.eq ON.colsBK (ON.list_eq ONV.LB ONV.CB (allN_spec ON.listB)) rfl

theorem hCA : ∀ j < 154, canon (ONV.LA.getD j 0) = true :=
  ON.canon_of ON.colsAK (ON.list_eq ONV.LA ONV.CA (allN_spec ON.listA))

theorem hCB : ∀ j < 154, canon (ONV.LB.getD j 0) = true :=
  ON.canon_of ON.colsBK (ON.list_eq ONV.LB ONV.CB (allN_spec ON.listB))

theorem hroot : digitsW CFSG.ONSchreier.Data.rootDigits = wOfK (key ONV.K 0) := by
  rw [ONRoot.eq, digitsK_sound ON.rootK]

theorem keys_eq : (vorbit (digitsW CFSG.ONSchreier.Data.rootDigits)).keys =
    Array.ofFn (n := 245520) fun i => wOfK (key ONV.K i.val) := by
  unfold vorbit
  rw [hroot]
  exact bfsK_keys (SL := 240) (NS := 1023) (SO := ONV.SO) (SOI := ONV.SOI) (NX := ONV.NX)
    (K := ONV.K) hcA hcB hCA hCB rfl (by norm_num) (ON.pt_of ON.mvAll fun _ => rfl) (by norm_num)
    (Nat.eq_of_beq_eq_true ON.nx0) (Nat.eq_of_beq_eq_true ON.nx1) ON.ordAll
    (ON.pt_of ON.sortAll fun _ => rfl)

theorem canon_key : ∀ h < 245520, canon (key ONV.K h) = true := fun h hh =>
  (mvAt_spec (ON.pt_of ON.mvAll (fun _ => rfl) h hh)).1

theorem key_get {i : Nat} (hi : i < 245520) :
    (vorbit (digitsW CFSG.ONSchreier.Data.rootDigits)).keys[i]! = wOfK (key ONV.K i) := by
  rw [keys_eq, getElem!_ofFn' hi]

theorem orbit_ok : orbitOK nPts colsA colsB (vorbit (digitsW CFSG.ONSchreier.Data.rootDigits))
    (posOf (indexOf (vorbit (digitsW CFSG.ONSchreier.Data.rootDigits)).keys) nPts) 3 = true := by
  unfold vorbit posOf
  rw [hroot]
  exact orbitOK_sound (SL := 240) (NS := 1023) (SO := ONV.SO) (SOI := ONV.SOI) (NX := ONV.NX)
    (K := ONV.K) hcA hcB hCA hCB rfl (by norm_num) (ON.pt_of ON.mvAll fun _ => rfl) (by norm_num)
    (Nat.eq_of_beq_eq_true ON.nx0) (Nat.eq_of_beq_eq_true ON.nx1) ON.ordAll
    (ON.pt_of ON.sortAll fun _ => rfl) 3

theorem root_ok : ((vorbit (digitsW CFSG.ONSchreier.Data.rootDigits)).keys[0]! ==
    digitsW CFSG.ONSchreier.Data.rootDigits) = true := by
  rw [key_get (by norm_num), hroot]
  exact beq_self_eq_true _

theorem wOfK_zero : wOfK 0 = W.zero := rfl

theorem root_ne : (!(digitsW CFSG.ONSchreier.Data.rootDigits == W.zero)) = true := by
  rw [hroot, Bool.not_eq_true', beq_eq_false_iff_ne]
  intro e
  rw [← wOfK_zero] at e
  have e' := wOfK_inj (canon_key 0 (by norm_num)) (by rfl) e
  have h := rootNZ
  rw [e'] at h
  exact absurd h (by decide)

theorem ap_tab {t : Table} {T : Nat → Nat} (e : natTab t = tabArr T 245520) :
    ∀ i < 245520, ap t i = tab T i := fun i hi => by
  have hts : t.size = 245520 := by
    have := congrArg Array.size e
    unfold natTab tabArr at this
    rwa [Array.size_map, Array.size_ofFn] at this
  have := congrArg (fun x => x[i]!) e
  unfold natTab tabArr at this
  rw [getElem!_map' (by rw [hts]; exact hi), getElem!_ofFn' hi] at this
  unfold ap
  exact this

theorem disc_ok : discOK nPts (vorbit (digitsW CFSG.ONSchreier.Data.rootDigits)).alpha
    (vorbit (digitsW CFSG.ONSchreier.Data.rootDigits)).beta
    (discPar nPts (vorbit (digitsW CFSG.ONSchreier.Data.rootDigits)).alpha
      (vorbit (digitsW CFSG.ONSchreier.Data.rootDigits)).beta) = true := by
  obtain ⟨ha, hb⟩ := ON.orb_tabs ON.mvAll ON.ordAll ON.sortAll
  refine discOK_of_hits fun k hk1 hk2 => ?_
  have hk2' : k < 245520 := hk2
  obtain ⟨q, hq, h⟩ := hits_of_ordRun (A := ONV.A) (B := ONV.B) (NX := ONV.NX) (SL := 240)
    (NS := 1023) (by norm_num) (by norm_num) (Nat.eq_of_beq_eq_true ON.nx0)
    (Nat.eq_of_beq_eq_true ON.nx1) ON.ordAll k hk1 hk2'
  refine ⟨q, hq, ?_⟩
  rw [ap_tab ha q (by omega), ap_tab hb q (by omega)]
  exact h

theorem sp_eq : CFSG.ONSchreier.Data.spanIdx = ON.SP.toArray := rfl

theorem toArray_get! {L : List Nat} {t : Nat} (ht : t < L.length) : L.toArray[t]! = L.getD t 0 := by
  rw [getElem!_pos _ t (by rw [List.size_toArray]; exact ht), List.getElem_toArray,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht]
  rfl

theorem sp_lt : ∀ t < 154, List.getD ON.SP t 0 < 245520 := by
  have h := ON.span_ok
  unfold ON.spanK at h
  simp only [bAnd_iff] at h
  exact fun t ht => Nat.blt_eq.mp (allN_spec h.2.2.1 t ht)

theorem sp_len : ON.SP.length = 154 := rfl

theorem span_get {t : Nat} (ht : t < 154) :
    CFSG.ONSchreier.Data.spanIdx[t]! = List.getD ON.SP t 0 := by
  rw [sp_eq, toArray_get! (by rw [sp_len]; exact ht)]

theorem skl_get {t : Nat} (ht : t < 154) : ON.SKL.getD t 0 = key ONV.K (List.getD ON.SP t 0) := by
  rw [ON.SKL_eq, List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by rw [sp_len]; exact ht)]
  rfl

theorem skl_len : ON.SKL.length = 154 := by rw [ON.SKL_eq, List.length_map, sp_len]

theorem skl_canon : ∀ t < 154, canon (ON.SKL.getD t 0) = true := fun t ht => by
  rw [skl_get ht]
  exact canon_key _ (sp_lt t ht)

theorem span_size : CFSG.ONSchreier.Data.spanIdx.size = 154 := rfl

theorem spanRows_get {t : Nat} (ht : t < 154) :
    (spanRows (vorbit (digitsW CFSG.ONSchreier.Data.rootDigits)) CFSG.ONSchreier.Data.spanIdx)[t]! =
      wOfK (ON.SKL.getD t 0) := by
  unfold spanRows
  rw [getElem!_map' (by rw [span_size]; exact ht), span_get ht, key_get (sp_lt t ht), skl_get ht]

theorem hSR : (spanRows (vorbit (digitsW CFSG.ONSchreier.Data.rootDigits))
      CFSG.ONSchreier.Data.spanIdx).size = 154 ∧ ON.SKL.length = 154 ∧
    ∀ t < 154, (spanRows (vorbit (digitsW CFSG.ONSchreier.Data.rootDigits))
      CFSG.ONSchreier.Data.spanIdx)[t]! = wOfK (ON.SKL.getD t 0) := by
  refine ⟨?_, skl_len, fun _ ht => spanRows_get ht⟩
  unfold spanRows
  rw [Array.size_map, span_size]

theorem rc_canon : ∀ k < 154, canon (at0 ON.RC k) = true := (colsK_transpose spanK).1

theorem rc_unit : ∀ k < 154, mv ON.SKL (at0 ON.RC k) = vmk (2 ^ k) 0 := by
  have h := ON.span_ok
  unfold ON.spanK at h
  simp only [bAnd_iff] at h
  intro k hk
  have hk' := allN_spec h.2.2.2 k hk
  rw [ON.strictB_val] at hk'
  obtain ⟨-, h2⟩ := (bAnd_iff _ _).1 hk'
  exact Nat.eq_of_beq_eq_true h2

theorem basis_ok : basisOK (vorbit (digitsW CFSG.ONSchreier.Data.rootDigits))
    CFSG.ONSchreier.Data.spanIdx (rowsOf 154 CFSG.ONSchreier.Data.spanInvPayload) = true := by
  unfold basisOK
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  refine ⟨⟨span_size, ?_⟩, ?_⟩
  · rw [Array.all_eq_true]
    intro t ht
    have ht' : t < 154 := by rw [span_size] at ht; exact ht
    have e := span_get ht'
    rw [getElem!_pos _ t ht] at e
    rw [e]
    exact decide_eq_true (sp_lt t ht')
  have hT := (colsK_transpose spanK).2
  rw [← ONSpanInv.eq] at hT
  rw [hT]
  have hI : (idM 154).size = 154 := by
    unfold idM
    exact Array.size_ofFn
  refine arr_ext' (n := 154) (by unfold mulW; rw [Array.size_map, Array.size_map, rowsV_size])
    (by unfold idW; rw [Array.size_map, hI]) fun k hk => ?_
  have hp : 2 ^ k < 2 ^ 256 := Nat.pow_lt_pow_right (by norm_num) (by omega)
  unfold mulW idW
  rw [getElem!_map' (by rw [Array.size_map, rowsV_size]; exact hk),
    getElem!_map' (by rw [rowsV_size]; exact hk), rowsV_get hk, getElem!_map' (by rw [hI]; exact hk)]
  unfold idM
  rw [getElem!_ofFn' hk]
  change mulVecT _ (wOfK (at0 ON.RC k)) = ofV ⟨1 <<< k, 0⟩
  rw [mv_sound hSR skl_canon (rc_canon k hk), rc_unit k hk, ← wOfK_vmk hp (by norm_num),
    Nat.one_shiftLeft]

end CertificateChecks.KernelSpor.ONVec

end
