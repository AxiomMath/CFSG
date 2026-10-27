module

public import Certificates.Kernel.Sporadic.ON.LvData
public import Certificates.Kernel.Sporadic.ON.Final
public import CFSG.Certificates.Kernel.Spor.CBfsKSound
public import CFSG.Certificates.Kernel.Spor.RawSlSound
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ON

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON CFSG.KS.CB CFSG.ONSchreier.Native CFSG.Sporadic.ON.Native

@[expose] noncomputable def SA : Array (Array Nat) :=
  Array.ofFn (n := 7) fun j => Array.ofFn (n := 245520) fun i => TT j.val i.val

theorem SA_get {j x : Nat} (hj : j < 7) (hx : x < 245520) : (SA[j]!)[x]! = TT j x := by
  unfold SA
  rw [getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn,
    getElem!_pos _ x (by simpa using hx), Array.getElem_ofFn]

theorem SA_size : SA.size = 7 := by simp [SA]

theorem SAi_get {j x : Nat} (hj : j < 7) (hx : x < 245520) :
    ((pinvs 245520 SA)[j]!)[x]! = UU j x := by
  unfold pinvs
  rw [getElem!_pos _ j (by simpa [SA_size] using hj), Array.getElem_map,
    ← getElem!_pos SA j (by simpa [SA_size] using hj)]
  unfold SA
  rw [getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]
  exact pinvCand_get (fun x hx => (perm_facts' x hx j hj).1)
    (fun x hx => (perm_facts' x hx j hj).2.2) hx

theorem base_get {k : Nat} (hk : k < 29) : CFSG.ONSchreier.Data.baseList.toArray[k]! = bK k := by
  interval_cases k <;> rfl

theorem bK_lt {k : Nat} (hk : k < 29) : bK k < 245520 := by
  interval_cases k <;> decide

theorem fixOK : allN 29 (fun i => allN 7 (fun j =>
    Bool.beq (allN i fun k => Nat.beq (TT j (bK k)) (bK k))
      (bAnd(Nat.ble (off i) j, Nat.blt j (Nat.add (off i) (len i)))))) = true := by
  quickRfl

theorem base_size : CFSG.ONSchreier.Data.baseList.toArray.size = 29 := rfl

theorem pfixes_eq {i j : Nat} (hi : i < 29) (hj : j < 7) :
    pfixes CFSG.ONSchreier.Data.baseList.toArray SA[j]! i =
      bAnd(Nat.ble (off i) j, Nat.blt j (Nat.add (off i) (len i))) := by
  have h := allN_spec (allN_spec fixOK i hi) j hj
  have e : (allN i fun k => Nat.beq (TT j (bK k)) (bK k)) =
      bAnd(Nat.ble (off i) j, Nat.blt j (Nat.add (off i) (len i))) := by
    revert h
    cases (allN i fun k => Nat.beq (TT j (bK k)) (bK k)) <;>
      cases bAnd(Nat.ble (off i) j, Nat.blt j (Nat.add (off i) (len i))) <;> decide
  rw [← e]
  unfold pfixes allBelowN
  rw [Bool.eq_iff_iff, Nat.all_eq_finRange_all, List.all_eq_true]
  refine Iff.trans ?_ ⟨CFSG.KS.Raw.allN_of_forall, allN_spec⟩
  constructor
  · intro hp k hk
    have := hp ⟨k, hk⟩ (List.mem_finRange _)
    simp only [beq_iff_eq] at this
    rw [base_get (by omega), SA_get hj (bK_lt (by omega))] at this
    rw [this, Nat.beq_refl]
  · intro hp ⟨k, hk⟩ _
    have := Nat.eq_of_beq_eq_true (hp k hk)
    simp only [beq_iff_eq]
    rw [base_get (by omega), SA_get hj (bK_lt (by omega))]
    exact this

theorem levIdx_eq {i : Nat} (hi : i < 29) :
    levIdx SA CFSG.ONSchreier.Data.baseList.toArray i = List.range' (off i) (len i) := by
  unfold levIdx
  rw [SA_size, List.filter_congr (q := fun j => bAnd(Nat.ble (off i) j, Nat.blt j (Nat.add (off i) (len i))))
    (fun j hj => pfixes_eq hi (List.mem_range.1 hj))]
  interval_cases i <;> rfl

theorem steps_get {i j x : Nat} (hi : i < 29) (hj : j < Nat.mul 2 (len i)) (hx : x < 245520) :
    (((allSteps SA (pinvs 245520 SA) CFSG.ONSchreier.Data.baseList.toArray)[i]!)[j]!)[x]! =
      stepF i j x := by
  have hb : i < (CFSG.ONSchreier.Data.baseList.toArray).size := by rw [base_size]; exact hi
  unfold allSteps
  rw [getElem!_pos _ i (by simpa using hb), Array.getElem_ofFn]
  unfold levSteps
  rw [levIdx_eq hi]
  have hlen : len i ≤ 7 ∧ off i + len i ≤ 7 := by interval_cases i <;> decide
  unfold stepF
  rcases Nat.lt_or_ge j (len i) with h | h
  · have hjj : j < (((List.range' (off i) (len i)).map fun j => SA[j]!).toArray ++
        ((List.range' (off i) (len i)).map fun j => (pinvs 245520 SA)[j]!).toArray).size := by
      simp
      omega
    rw [getElem!_pos _ j hjj, Array.getElem_append_left (by simpa using h)]
    simp only [List.getElem_toArray, List.getElem_map, List.getElem_range', Nat.one_mul]
    rw [SA_get (by omega) hx]
    have hb' : Nat.blt j (len i) = true := Nat.blt_eq ▸ h
    rw [hb']
    rfl
  · have hjj : j < (((List.range' (off i) (len i)).map fun j => SA[j]!).toArray ++
        ((List.range' (off i) (len i)).map fun j => (pinvs 245520 SA)[j]!).toArray).size := by
      simp
      simp only [Nat.mul_eq] at hj
      omega
    rw [getElem!_pos _ j hjj, Array.getElem_append_right (by simpa using h)]
    simp only [List.getElem_toArray, List.getElem_map, List.getElem_range', List.size_toArray,
      List.length_map, List.length_range', Nat.one_mul]
    rw [SAi_get (by simp only [Nat.mul_eq] at hj; omega) hx]
    have hb' : Nat.blt j (len i) = false := by
      rw [Bool.eq_false_iff]
      intro e
      exact absurd (Nat.blt_eq ▸ e) (by omega)
    rw [hb']
    rfl

theorem invSteps_get {i j x : Nat} (hi : i < 29) (hj : j < Nat.mul 2 (len i)) (hx : x < 245520) :
    (((allInvSteps SA (pinvs 245520 SA) CFSG.ONSchreier.Data.baseList.toArray)[i]!)[j]!)[x]! =
      invF i j x := by
  have hb : i < (CFSG.ONSchreier.Data.baseList.toArray).size := by rw [base_size]; exact hi
  unfold allInvSteps
  rw [getElem!_pos _ i (by simpa using hb), Array.getElem_ofFn]
  unfold levInvSteps
  rw [levIdx_eq hi]
  have hlen : len i ≤ 7 ∧ off i + len i ≤ 7 := by interval_cases i <;> decide
  unfold invF
  rcases Nat.lt_or_ge j (len i) with h | h
  · have hjj : j < (((List.range' (off i) (len i)).map fun j => (pinvs 245520 SA)[j]!).toArray ++
        ((List.range' (off i) (len i)).map fun j => SA[j]!).toArray).size := by
      simp
      omega
    rw [getElem!_pos _ j hjj, Array.getElem_append_left (by simpa using h)]
    simp only [List.getElem_toArray, List.getElem_map, List.getElem_range', Nat.one_mul]
    rw [SAi_get (by omega) hx]
    have hb' : Nat.blt j (len i) = true := Nat.blt_eq ▸ h
    rw [hb']
    rfl
  · have hjj : j < (((List.range' (off i) (len i)).map fun j => (pinvs 245520 SA)[j]!).toArray ++
        ((List.range' (off i) (len i)).map fun j => SA[j]!).toArray).size := by
      simp
      simp only [Nat.mul_eq] at hj
      omega
    rw [getElem!_pos _ j hjj, Array.getElem_append_right (by simpa using h)]
    simp only [List.getElem_toArray, List.getElem_map, List.getElem_range', List.size_toArray,
      List.length_map, List.length_range', Nat.one_mul]
    rw [SA_get (by simp only [Nat.mul_eq] at hj; omega) hx]
    have hb' : Nat.blt j (len i) = false := by
      rw [Bool.eq_false_iff]
      intro e
      exact absurd (Nat.blt_eq ▸ e) (by omega)
    rw [hb']
    rfl

theorem steps_size {i : Nat} (hi : i < 29) :
    ((allSteps SA (pinvs 245520 SA) CFSG.ONSchreier.Data.baseList.toArray)[i]!).size =
      Nat.mul 2 (len i) := by
  have hb : i < (CFSG.ONSchreier.Data.baseList.toArray).size := by rw [base_size]; exact hi
  unfold allSteps
  rw [getElem!_pos _ i (by simpa using hb), Array.getElem_ofFn]
  unfold levSteps
  rw [levIdx_eq hi]
  simp only [Array.size_append, List.size_toArray, List.length_map, List.length_range', Nat.mul_eq]
  omega

theorem invSteps_size {i : Nat} (hi : i < 29) :
    ((allInvSteps SA (pinvs 245520 SA) CFSG.ONSchreier.Data.baseList.toArray)[i]!).size =
      Nat.mul 2 (len i) := by
  have hb : i < (CFSG.ONSchreier.Data.baseList.toArray).size := by rw [base_size]; exact hi
  unfold allInvSteps
  rw [getElem!_pos _ i (by simpa using hb), Array.getElem_ofFn]
  unfold levInvSteps
  rw [levIdx_eq hi]
  simp only [Array.size_append, List.size_toArray, List.length_map, List.length_range', Nat.mul_eq]
  omega

theorem hd0 : cbHead 245520 (Mf 0) (bK 0) (PTSf 0) (PARf 0) (LABf 0) = true := by quickRfl
theorem hd1 : cbHead 245520 (Mf 1) (bK 1) (PTSf 1) (PARf 1) (LABf 1) = true := by quickRfl
theorem hd2 : cbHead 245520 (Mf 2) (bK 2) (PTSf 2) (PARf 2) (LABf 2) = true := by quickRfl
theorem mOK : bAnd(Nat.ble (Mf 0) (Nat.mul 1023 240), bAnd(Nat.ble (Mf 1) (Nat.mul 218 240),
    Nat.ble (Mf 2) 240)) = true := by quickRfl

variable (pt0 : ∀ s < 1023, pt0S s = true) (pt1 : ∀ s < 218, pt1S s = true)
  (pt2 : ∀ s < 1, pt2S s = true) (pos0 : ∀ s < 8, pos0S s = true) (pos1 : ∀ s < 8, pos1S s = true)
  (pos2 : ∀ s < 8, pos2S s = true) (posT' : ∀ s < 29, 3 ≤ s → posT s = true)

theorem ptL_of {i NS : Nat} (hp : ∀ s < NS, ptS i s = true) (hm : Mf i ≤ NS * 240) :
    ∀ k < Mf i, cbPt 245520 (Mf i) (Nat.mul 2 (len i)) (stepF i) (PTSf i) (POSf i) (PARf i) (LABf i) k
      = true := by
  intro k hk
  have hs := hp (k / 240) (by omega)
  unfold ptS cbPtRange at hs
  have h := allBlk_spec hs (k % 240) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.mul (k / 240) 240) (k % 240) = k := by
    simp only [Nat.add_eq, Nat.mul_eq]
    omega
  rw [e] at h
  have hk' : Nat.blt k (Mf i) = true := Nat.blt_eq ▸ hk
  simpa [hk'] using h

theorem posL_of {i : Nat} (hp : ∀ s < 8, posS i s = true) :
    ∀ z < 245520, cbPos 245520 (Mf i) (PTSf i) (POSf i) z = true := by
  intro z hz
  have h := allN_spec (hp (z / 30690) (by omega)) (z % 30690) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.mul (z / 30690) 30690) (z % 30690) = z := by
    simp only [Nat.add_eq, Nat.mul_eq]
    omega
  rwa [e] at h

include pt0 pt1 pt2 pos0 pos1 pos2 posT' in
theorem level_eq {i : Nat} (hi : i < 29) :
    cbfs 245520 (bK i) (allSteps SA (pinvs 245520 SA) CFSG.ONSchreier.Data.baseList.toArray)[i]! =
      ⟨Array.ofFn (n := Mf i) fun k => PTSf i k.val, Array.ofFn (n := 245520) fun z => POSf i z.val,
        Array.ofFn (n := Mf i) fun k => PARf i k.val, Array.ofFn (n := Mf i) fun k => LABf i k.val⟩ := by
  have hst : ((allSteps SA (pinvs 245520 SA) CFSG.ONSchreier.Data.baseList.toArray)[i]!).size =
      Nat.mul 2 (len i) ∧ ∀ j < Nat.mul 2 (len i), ∀ x < 245520,
        (((allSteps SA (pinvs 245520 SA) CFSG.ONSchreier.Data.baseList.toArray)[i]!)[j]!)[x]! =
          stepF i j x :=
    ⟨steps_size hi, fun j hj x hx => steps_get hi hj hx⟩
  obtain ⟨m0, m1, m2⟩ := (by simpa only [bAnd_iff] using mOK :
    Nat.ble (Mf 0) (Nat.mul 1023 240) = true ∧ Nat.ble (Mf 1) (Nat.mul 218 240) = true ∧
      Nat.ble (Mf 2) 240 = true)
  rcases Nat.lt_or_ge i 3 with h3 | h3
  · interval_cases i
    · exact cbfsK_sound hst hd0 (ptL_of pt0 (Nat.le_of_ble_eq_true m0)) (posL_of pos0)
    · exact cbfsK_sound hst hd1 (ptL_of pt1 (Nat.le_of_ble_eq_true m1)) (posL_of pos1)
    · exact cbfsK_sound hst hd2 (ptL_of pt2 (by simpa using Nat.le_of_ble_eq_true m2)) (posL_of pos2)
  · have h := posT' i hi h3
    unfold posT at h
    obtain ⟨ha, hb, hc⟩ := (by simpa only [bAnd_iff] using h :
      cbHead (nat_lit 245520) (Mf i) (bK i) (PTSf i) (PARf i) (LABf i) = true ∧
      cbPt (nat_lit 245520) (Mf i) (Nat.mul (nat_lit 2) (len i)) (stepF i) (PTSf i) (POSf i)
        (PARf i) (LABf i) (nat_lit 0) = true ∧
      allN (nat_lit 245520) (fun z => cbPos (nat_lit 245520) (Mf i) (PTSf i) (POSf i) z) = true)
    have hM : Mf i = 1 := by interval_cases i <;> rfl
    refine cbfsK_sound hst ha (fun k hk => ?_) (allN_spec hc)
    have hk0 : k = 0 := by omega
    rw [hk0]
    exact hb

include pt0 pt1 pt2 pos0 pos1 pos2 posT' in
theorem cLevels_eq (hq : CFSG.ONSchreier.qonStrongArrs = SA) :
    cLevels 245520 CFSG.ONSchreier.Data.baseList.toArray
        (allSteps CFSG.ONSchreier.qonStrongArrs (pinvs 245520 CFSG.ONSchreier.qonStrongArrs)
          CFSG.ONSchreier.Data.baseList.toArray) =
      Array.ofFn (n := 29) fun i => (⟨Array.ofFn (n := Mf i.val) fun k => PTSf i.val k.val,
        Array.ofFn (n := 245520) fun z => POSf i.val z.val,
        Array.ofFn (n := Mf i.val) fun k => PARf i.val k.val,
        Array.ofFn (n := Mf i.val) fun k => LABf i.val k.val⟩ : CLevel) := by
  rw [hq]
  unfold cLevels
  apply Array.ext (by simpa using base_size)
  intro i h1 h2
  have hi : i < 29 := by simpa using h2
  rw [Array.getElem_ofFn, Array.getElem_ofFn]
  rw [base_get hi]
  exact level_eq pt0 pt1 pt2 pos0 pos1 pos2 posT' hi

end CertificateChecks.KernelSpor.ON

end
