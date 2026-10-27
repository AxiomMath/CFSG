module

public import CFSG.Certificates.Kernel.SporSch.PairJ3CertSound
public import CFSG.Certificates.Kernel.SporSch.PairKSound
public import CFSG.Certificates.Kernel.SporSch.J4STokSound
public import CFSG.Certificates.Kernel.Spor.PrimSound
public import Certificates.Data.CFSGNative.J1.Vec

public section

namespace CertificateChecks.KernelSporSch.PairGen

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch
open CFSG.Sporadic.Schreier CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

theorem hexVectors_get (N d : Nat) (s : String) (i : Nat) (hi : i < N) :
    (PairText.hexVectors N d s)[i]! = (hexTable 1 d (d * i) s).toList := by
  rw [getElem!_pos _ i (by simpa [PairText.hexVectors] using hi)]
  unfold PairText.hexVectors hexTable
  rw [Array.getElem_ofFn, Array.toList_ofFn]
  apply List.ext_getElem
  · simp
  · intro j h1 h2
    simp [hexAt, hexVal]

theorem vec_get {cs : List Char} {N d w : Nat} {F : Nat → Nat} {s : String}
    (hs : s = String.ofList cs) (h : hexTabK cs 1 d w N F = true) (i : Nat) (hi : i < N) :
    (PairText.hexVectors N d s)[i]! = (unpack d w (F i)).toList := by
  have e := hexTabK_sound h i hi
  rw [← hs] at e
  rw [hexVectors_get N d s i hi, e]

theorem hexVectors_size (N d : Nat) (s : String) : (PairText.hexVectors N d s).size = N := by
  unfold PairText.hexVectors
  exact Array.size_ofFn

theorem wfV_of {N d w p : Nat} {V : Array (List Nat)} {F : Nat → Nat}
    (hV : ∀ i < N, V[i]! = (unpack d w (F i)).toList)
    (h : allN N (fun i => allN d (fun j => Nat.blt (pg w (mask w) (F i) j) p)) = true) :
    allLt N (fun i => CFSG.Sporadic.J1.Native.wfV p d V[i]!) = true := by
  rw [allLt_iff]
  intro i hi
  have hr := allN_spec (allN_spec h i hi)
  rw [hV i hi]
  unfold CFSG.Sporadic.J1.Native.wfV unpack
  simp only [Array.toList_ofFn, List.length_ofFn, beq_self_eq_true, Bool.true_and,
    List.all_eq_true, List.mem_ofFn, decide_eq_true_eq]
  rintro x ⟨j, rfl⟩
  exact Nat.blt_eq.mp (hr j.val j.isLt)

theorem gens_ok {n w k : Nat} {S : Array (Array Nat)} {PS PSI : Nat → Nat} (hS : S.size = k)
    (harr : ∀ j < k, S[j]! = unpack n w (PS j))
    (hp : allN k (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true) :
    allLt k (fun j => S[j]!.size == n && isInvA n S[j]! (rawInvs n S)[j]!) = true := by
  rw [allLt_iff]
  intro j hj
  have hI := invEqK_sound (allN_spec hp j hj)
  have hm : (rawInvs n S)[j]! = invCand n S[j]! := by
    rw [rawInvs, getElem!_pos (S.map (invCand n)) j (by simp [hS]; omega),
      getElem!_pos S j (by omega), Array.getElem_map]
  rw [hm, harr j hj, hI.1, hI.2]
  simp [unpack]

theorem unpack_get {n w P i : Nat} (hi : i < n) : (unpack n w P)[i]! = pg w (mask w) P i := by
  rw [getElem!_pos _ i (by simp [unpack]; omega)]
  simp [unpack]

theorem lt_of_isInvA {n : Nat} {t r : Array Nat} (h : isInvA n t r = true) {i : Nat} (hi : i < n) :
    t[i]! < n := by
  unfold isInvA at h
  rw [allLt_iff] at h
  have := h i hi
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  exact this.1

theorem vec_ne {d w P Q : Nat} (h : neK d w (mask w) (d * w) P Q = true) :
    (unpack d w P).toList ≠ (unpack d w Q).toList := by
  intro e
  have hf := neK_sound h
  rw [Array.toList_inj.mp e] at hf
  unfold eqA at hf
  have ht : allLt d (fun i => (unpack d w Q)[i]! == (unpack d w Q)[i]!) = true := by
    rw [allLt_iff]
    intro i _
    exact beq_self_eq_true _
  rw [ht] at hf
  exact Bool.noConfusion hf

theorem stab_eq {cs : List Char} {s : String}
    {R : List (List Nat) × List (Nat × List (Nat × Nat × Nat))} (hs : s = String.ofList cs)
    (h : tokK cs (encOM R) = true) : PairText.parseOrbitsMerges (PairText.tokens s) = R := by
  rw [hs, tokK_sound h, PJ3Enc.parse_encOM]

open CFSG.Sporadic.Schreier.PairNative in
theorem stab_checks {n c : Nat} {ls rs : List Nat}
    {R : List (List Nat) × List (Nat × List (Nat × Nat × Nat))} (h : stabK n c ls rs R = true) :
    (R.1.length == ls.length) = true ∧
      R.1.all (fun o => strictInc o && o.all (· < n)) = true ∧
      (R.1.map List.length == ls) = true ∧
      (R.2.map Prod.fst == rs) = true ∧
      (R.2.map (fun m => m.2.length) == rs.map fun _ => c) = true ∧
      R.2.all (fun m => m.2.all fun t => decide (t.1 < 2) && decide (t.2.1 < n) &&
        decide (t.2.2 < n)) = true := by
  obtain ⟨⟨hl, ho⟩, hr, hm⟩ := stabK_sound h
  refine ⟨?_, ?_, by rw [hl]; exact beq_self_eq_true _, by rw [hr]; exact beq_self_eq_true _, ?_, ?_⟩
  · have := congrArg List.length hl
    rw [List.length_map] at this
    rw [this]
    exact beq_self_eq_true _
  · rw [List.all_eq_true]
    intro o h'
    obtain ⟨h1, h2⟩ := ho o h'
    simp only [h1, Bool.true_and, List.all_eq_true, decide_eq_true_eq]
    exact h2
  · have e : R.2.map (fun m => m.2.length) = R.2.map (fun _ => c) :=
      List.map_congr_left fun m h' => (hm m h').1
    rw [e, ← hr, List.map_map]
    exact beq_self_eq_true _
  · rw [List.all_eq_true]
    intro m h'
    simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    exact fun t ht => ⟨⟨(((hm m h').2 t ht).1), ((hm m h').2 t ht).2.1⟩, ((hm m h').2 t ht).2.2⟩

end CertificateChecks.KernelSporSch.PairGen

end
