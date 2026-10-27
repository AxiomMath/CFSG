module

public import Certificates.Kernel.Sporadic.OddCore.HN2091D
import Mathlib.Tactic.IntervalCases
import CFSG.Sporadic.Schreier.ONPermArr
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Spor.RawSlSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.HN2091

open CFSG.Sporadic.HNOddCore CFSG.Sporadic.HNOddCore.Native CFSG.Sporadic.HNOddCore.InvData
open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.PEnum
open CFSG.KS.BfsL CertificateChecks.KernelSpor.HND

@[expose] noncomputable def listRK (F : Nat → Nat) (L : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun x _ ih i => bAnd(Nat.beq x (r32 F i), ih (Nat.succ i))) L

theorem listRK_spec {F : Nat → Nat} :
    ∀ (L : List Nat) (i : Nat), listRK F L i = true → ∀ j < L.length, L[j]! = r32 F (i + j)
  | [], _, _, j, hj => absurd hj (by simp)
  | x :: xs, i, h, j, hj => by
    unfold listRK at h
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
    cases j with
    | zero => simpa using Nat.eq_of_beq_eq_true h1
    | succ j =>
      have := listRK_spec xs (i + 1) h2 j (by simpa using hj)
      simpa [Nat.add_assoc, Nat.add_comm 1 j] using this

theorem toArray_r32 {F : Nat → Nat} {L : List Nat} {o cnt : Nat} (hl : L.length = cnt)
    (h : listRK F L o = true) : L.toArray = Array.ofFn (n := cnt) fun i => r32 F (o + i.val) := by
  apply Array.ext
  · simp [hl]
  · intro j h1 h2
    have hj : j < L.length := by simpa using h1
    have e := listRK_spec L o h j hj
    simp only [List.getElem_toArray, Array.getElem_ofFn]
    rw [← e]
    simp [hj]

@[expose] noncomputable def genL (m : Nat) (F : Nat → Nat) (s x : Nat) : Nat :=
  r32 F (Nat.add (Nat.mul m s) x)

theorem gens_of {m k : Nat} {F : Nat → Nat} {E : List (List Nat)} (hk : E.length = k)
    (h : (List.range k).all (fun s => Nat.beq (E.getD s []).length m &&
      listRK F (E.getD s []) (Nat.mul m s)) = true) :
    ((E.map List.toArray).toArray).size = k ∧
      ∀ s < k, ∀ x < m, (((E.map List.toArray).toArray)[s]!)[x]! = genL m F s x := by
  refine ⟨by simp [hk], fun s hs x hx => ?_⟩
  have h' := List.all_eq_true.1 h s (List.mem_range.2 hs)
  simp only [Bool.and_eq_true, Nat.beq_eq] at h'
  have hl := h'.1
  have e := listRK_spec _ _ h'.2 x (by omega)
  rw [getElem!_pos _ s (by simp [hk, hs])]
  simp only [List.getElem_toArray, List.getElem_map]
  have eg : E.getD s [] = E[s]'(by omega) := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : s < E.length),
      Option.getD_some]
  rw [← eg]
  rw [getElem!_pos _ x (by rw [List.size_toArray, hl]; exact hx)]
  simp only [List.getElem_toArray]
  rw [← getElem!_pos (E.getD s []) x (by omega), e]
  rfl

theorem base12_ok {BP : Nat} (h : allN 12 (fun t => Nat.beq (pg 4 (mask 4) BP t) t) = true) :
    (base12.map Fin.val).toArray.size = 12 ∧
      ∀ t < 12, (base12.map Fin.val).toArray[t]! = pg 4 (mask 4) BP t := by
  refine ⟨by decide, fun t ht => ?_⟩
  rw [Nat.eq_of_beq_eq_true (allN_spec h t ht)]
  interval_cases t <;> rfl

theorem bp1 : allN 12 (fun t => Nat.beq (pg 4 (mask 4) HNC1.BP t) t) = true := by quickRfl
theorem bp4 : allN 12 (fun t => Nat.beq (pg 4 (mask 4) HNC4.BP t) t) = true := by quickRfl
theorem bp6 : allN 12 (fun t => Nat.beq (pg 4 (mask 4) HNC6.BP t) t) = true := by quickRfl
theorem bp4c : allN 12 (fun t => Nat.beq (pg 4 (mask 4) HNC4C.BP t) t) = true := by quickRfl

theorem p1 : allN 37 (fun j => permOK 12 4 (mask 4) (12 * 4) (HNC1.S j) (HNC1.SI j)) = true := by
  quickRfl
theorem p4 : allN 13 (fun j => permOK 12 4 (mask 4) (12 * 4) (HNC4.S j) (HNC4.SI j)) = true := by
  quickRfl
theorem p6 : allN 14 (fun j => permOK 12 4 (mask 4) (12 * 4) (HNC6.S j) (HNC6.SI j)) = true := by
  quickRfl
theorem p4c : allN 15 (fun j => permOK 12 4 (mask 4) (12 * 4) (HNC4C.S j) (HNC4C.SI j)) = true := by
  quickRfl

theorem ch1 : chainCheck 12 (natArrs c1Nat) g1Words base12 g1Sizes = true :=
  chainCheck_of (by decide +kernel) (by decide) (by decide) (by simp only [c1D, Array.toArray_toList]) (by norm_num)
    (base12_ok bp1) HNC1.head HNC1.hl (by decide +kernel) HNC1.hs p1 (by decide +kernel)
theorem ch4 : chainCheck 12 (natArrs c4Nat) g4Words base12 g4Sizes = true :=
  chainCheck_of (by decide +kernel) (by decide) (by decide) (by simp only [c4D, Array.toArray_toList]) (by norm_num)
    (base12_ok bp4) HNC4.head HNC4.hl (by decide +kernel) HNC4.hs p4 (by decide +kernel)
theorem ch6 : chainCheck 12 (natArrs c6Nat) g6Words base12 g6Sizes = true :=
  chainCheck_of (by decide +kernel) (by decide) (by decide) (by simp only [c6D, Array.toArray_toList]) (by norm_num)
    (base12_ok bp6) HNC6.head HNC6.hl (by decide +kernel) HNC6.hs p6 (by decide +kernel)
theorem ch4c : chainCheck 12 (natArrs (c4Nat.push tauList)) g4cWords base12 g4cSizes = true :=
  chainCheck_of (by decide +kernel) (by decide) (by decide) (by simp only [c4cD, Array.toArray_toList]) (by norm_num)
    (base12_ok bp4c) HNC4C.head HNC4C.hl (by decide +kernel) HNC4C.hs p4c (by decide +kernel)

theorem natChains : natChainChecks = true := by
  unfold natChainChecks
  simp only [ch1, ch4, ch6, ch4c, Bool.and_self]

theorem g1_ok : (List.range 9).all (fun s => Nat.beq (HNT.S1.E.getD s []).length 1156 &&
    listRK HS1R (HNT.S1.E.getD s []) (Nat.mul 1156 s)) = true := by quickRfl
theorem g6_ok : (List.range 12).all (fun s => Nat.beq (HNT.S6.E.getD s []).length 8800 &&
    listRK HS6R (HNT.S6.E.getD s []) (Nat.mul 8800 s)) = true := by quickRfl
theorem g4_ok : (List.range 10).all (fun s => Nat.beq ((HNT.S4.E.take 10).getD s []).length 800 &&
    listRK HS4R ((HNT.S4.E.take 10).getD s []) (Nat.mul 800 s)) = true := by quickRfl

theorem img1 : allN 9 (fun s => allN 1156 (fun x => Nat.blt (genL 1156 HS1R s x) 1156)) = true := by
  quickRfl
theorem img4 : allN 10 (fun s => allN 800 (fun x => Nat.blt (genL 800 HS4R s x) 800)) = true := by
  quickRfl
theorem img6 : allN 12 (fun s => allN 8800 (fun x => Nat.blt (genL 8800 HS6R s x) 8800)) =
    true := by
  quickRfl

theorem imgs {k m : Nat} {F : Nat → Nat} (h : allN k (fun s => allN m (fun x =>
    Nat.blt (genL m F s x) m)) = true) : ∀ s < k, ∀ x < m, genL m F s x < m :=
  fun s hs x hx => Eq.mp Nat.blt_eq (allN_spec (allN_spec h s hs) x hx)

theorem s1G : s1Perms.size = 9 ∧
    ∀ s < 9, ∀ x < 1156, (s1Perms[s]!)[x]! = genL 1156 HS1R s x := by
  rw [s1_eq]
  exact gens_of (by decide +kernel) g1_ok

theorem s6G : s6Perms.size = 12 ∧
    ∀ s < 12, ∀ x < 8800, (s6Perms[s]!)[x]! = genL 8800 HS6R s x := by
  rw [s6_eq]
  exact gens_of (by decide +kernel) g6_ok

theorem s4J_eq : s4J = ((HNT.S4.E.take 10).map List.toArray).toArray := by
  rw [s4J, s4_eq]
  apply Array.ext
  · simp
  · intro i h1 h2
    simp

theorem s4G : s4J.size = 10 ∧ ∀ s < 10, ∀ x < 800, (s4J[s]!)[x]! = genL 800 HS4R s x := by
  rw [s4J_eq]
  exact gens_of (by decide +kernel) g4_ok

theorem hd10 : bfsLHdK 1156 (r32 HO1_0.PTS 0) HO1_0.cnt HO1_0.PTS HO1_0.POS HO1_0.PAR HO1_0.LAB =
    true := by quickRfl
theorem hd11 : bfsLHdK 1156 (r32 HO1_1.PTS 0) HO1_1.cnt HO1_1.PTS HO1_1.POS HO1_1.PAR HO1_1.LAB =
    true := by quickRfl
theorem hd12 : bfsLHdK 1156 (r32 HO1_2.PTS 0) HO1_2.cnt HO1_2.PTS HO1_2.POS HO1_2.PAR HO1_2.LAB =
    true := by quickRfl
theorem hd60 : bfsLHdK 8800 (r32 HO6_0.PTS 0) HO6_0.cnt HO6_0.PTS HO6_0.POS HO6_0.PAR HO6_0.LAB =
    true := by quickRfl
theorem hd61 : bfsLHdK 8800 (r32 HO6_1.PTS 0) HO6_1.cnt HO6_1.PTS HO6_1.POS HO6_1.PAR HO6_1.LAB =
    true := by quickRfl
theorem hdF4 : bfsLHdK 800 0 HF4.cnt HF4.PTS HF4.POS HF4.PAR HF4.LAB = true := by quickRfl

theorem sl10 : bfsLSlK 1156 HO1_0.cnt 9 (genL 1156 HS1R) HO1_0.PTS HO1_0.POS HO1_0.PAR HO1_0.LAB
    0 1 = true := by quickRfl
theorem sl11 : bfsLSlK 1156 HO1_1.cnt 9 (genL 1156 HS1R) HO1_1.PTS HO1_1.POS HO1_1.PAR HO1_1.LAB
    0 945 = true := by quickRfl
theorem sl12 : bfsLSlK 1156 HO1_2.cnt 9 (genL 1156 HS1R) HO1_2.PTS HO1_2.POS HO1_2.PAR HO1_2.LAB
    0 210 = true := by quickRfl
theorem sl61 : bfsLSlK 8800 HO6_1.cnt 12 (genL 8800 HS6R) HO6_1.PTS HO6_1.POS HO6_1.PAR HO6_1.LAB
    0 1100 = true := by quickRfl
theorem slF4 : bfsLSlK 800 HF4.cnt 10 (genL 800 HS4R) HF4.PTS HF4.POS HF4.PAR HF4.LAB 0 800 =
    true := by quickRfl

@[expose] noncomputable def sl60K (s : Nat) : Bool :=
  bfsLSlK 8800 HO6_0.cnt 12 (genL 8800 HS6R) HO6_0.PTS HO6_0.POS HO6_0.PAR HO6_0.LAB
    (Nat.mul 700 s) 700

theorem sl60_0 : sl60K 0 = true := by quickRfl
theorem sl60_1 : sl60K 1 = true := by quickRfl
theorem sl60_2 : sl60K 2 = true := by quickRfl
theorem sl60_3 : sl60K 3 = true := by quickRfl
theorem sl60_4 : sl60K 4 = true := by quickRfl
theorem sl60_5 : sl60K 5 = true := by quickRfl
theorem sl60_6 : sl60K 6 = true := by quickRfl
theorem sl60_7 : sl60K 7 = true := by quickRfl
theorem sl60_8 : sl60K 8 = true := by quickRfl
theorem sl60_9 : sl60K 9 = true := by quickRfl
theorem sl60_10 : sl60K 10 = true := by quickRfl

theorem pts_of {m cnt k : Nat} {L : Nat → Nat → Nat} {PTS POS PAR LAB : Nat → Nat} {lo len : Nat}
    (h : bfsLSlK m cnt k L PTS POS PAR LAB lo len = true) :
    ∀ i, lo ≤ i → i < lo + len → i < cnt → bfsLPtK m cnt k L PTS POS PAR LAB i = true := by
  intro i h1 h2 h3
  have h' := allN_spec h (i - lo) (by omega)
  rw [CFSG.KS.Raw.strictB_eq] at h'
  have e : Nat.add lo (i - lo) = i := by
    change lo + (i - lo) = i
    omega
  rw [e] at h'
  have hb : Nat.blt i cnt = true := Eq.mpr Nat.blt_eq h3
  rw [hb] at h'
  exact h'

theorem sl60_all : ∀ s < 11, sl60K s = true := by
  intro s hs
  interval_cases s
  exacts [sl60_0, sl60_1, sl60_2, sl60_3, sl60_4, sl60_5, sl60_6, sl60_7, sl60_8, sl60_9, sl60_10]

theorem pts60 : ∀ i < HO6_0.cnt, bfsLPtK 8800 HO6_0.cnt 12 (genL 8800 HS6R) HO6_0.PTS HO6_0.POS
    HO6_0.PAR HO6_0.LAB i = true := by
  intro i hi
  have e : HO6_0.cnt = 7700 := rfl
  have hs := sl60_all (i / 700) (by omega)
  have e2 : Nat.mul 700 (i / 700) = 700 * (i / 700) := rfl
  unfold sl60K at hs
  rw [e2] at hs
  exact pts_of hs i (Nat.mul_div_le i 700) (by omega) hi

theorem lines_get {E : List (List Nat)} (i : Nat) :
    ((E.map List.toArray).toArray)[i]! = (E.getD i []).toArray := by
  by_cases h : i < E.length
  · have e : E.getD i [] = E[i] := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]
    rw [getElem!_pos _ i (by simpa using h), e]
    simp
  · have e : E.getD i [] = [] := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : E.length ≤ i),
        Option.getD_none]
    rw [getElem!_neg _ i (by simpa using h), e]
    rfl

theorem list_r32 {F : Nat → Nat} {L : List Nat} {cnt : Nat} (hl : L.length = cnt)
    (h : listRK F L 0 = true) : L.toArray = Array.ofFn (n := cnt) fun i => r32 F i.val := by
  rw [toArray_r32 hl h]
  simp only [Nat.zero_add]

theorem l10 : listRK HO1_0.PTS (HNT.O1.E.getD 0 []) 0 = true := by quickRfl
theorem l11 : listRK HO1_1.PTS (HNT.O1.E.getD 1 []) 0 = true := by quickRfl
theorem l12 : listRK HO1_2.PTS (HNT.O1.E.getD 2 []) 0 = true := by quickRfl
theorem l60 : listRK HO6_0.PTS (HNT.O6.E.getD 0 []) 0 = true := by quickRfl
theorem l61 : listRK HO6_1.PTS (HNT.O6.E.getD 1 []) 0 = true := by quickRfl

theorem o1_0 : o1Lists[0]! = Array.ofFn (n := HO1_0.cnt) fun i => r32 HO1_0.PTS i.val := by
  rw [o1_eq, lines_get]
  exact list_r32 (by decide +kernel) l10
theorem o1_1 : o1Lists[1]! = Array.ofFn (n := HO1_1.cnt) fun i => r32 HO1_1.PTS i.val := by
  rw [o1_eq, lines_get]
  exact list_r32 (by decide +kernel) l11
theorem o1_2 : o1Lists[2]! = Array.ofFn (n := HO1_2.cnt) fun i => r32 HO1_2.PTS i.val := by
  rw [o1_eq, lines_get]
  exact list_r32 (by decide +kernel) l12
theorem o6_0 : o6Lists[0]! = Array.ofFn (n := HO6_0.cnt) fun i => r32 HO6_0.PTS i.val := by
  rw [o6_eq, lines_get]
  exact list_r32 (by decide +kernel) l60
theorem o6_1 : o6Lists[1]! = Array.ofFn (n := HO6_1.cnt) fun i => r32 HO6_1.PTS i.val := by
  rw [o6_eq, lines_get]
  exact list_r32 (by decide +kernel) l61

theorem f1_size : f1Arr.size = 1156 := by
  rw [f1Arr_eq]
  decide +kernel
theorem f4_size : f4Arr.size = 800 := by
  rw [f4Arr_eq]
  decide +kernel
theorem f6_size : f6Arr.size = 8800 := by
  rw [f6Arr_eq]
  decide +kernel

theorem orb1 : ∀ i < 3, orbitOK f1Arr.size s1Perms o1Lists[i]! = true := by
  intro i hi
  rw [f1_size]
  interval_cases i
  · rw [o1_0]
    exact orbitOK_sound s1G (imgs img1) hd10 fun j hj =>
      pts_of sl10 j (Nat.zero_le _) (by have e : HO1_0.cnt = 1 := rfl; omega) hj
  · rw [o1_1]
    exact orbitOK_sound s1G (imgs img1) hd11 fun j hj =>
      pts_of sl11 j (Nat.zero_le _) (by have e : HO1_1.cnt = 945 := rfl; omega) hj
  · rw [o1_2]
    exact orbitOK_sound s1G (imgs img1) hd12 fun j hj =>
      pts_of sl12 j (Nat.zero_le _) (by have e : HO1_2.cnt = 210 := rfl; omega) hj

theorem pts4 : ∀ j < HF4.cnt, bfsLPtK 800 HF4.cnt 10 (genL 800 HS4R) HF4.PTS HF4.POS HF4.PAR
    HF4.LAB j = true := fun j hj =>
  pts_of slF4 j (Nat.zero_le _) (by have e : HF4.cnt = 800 := rfl; omega) hj

theorem bfs4 : bfsList f4Arr.size s4J 0 = Array.ofFn (n := HF4.cnt) fun i => r32 HF4.PTS i.val := by
  rw [f4_size]
  exact bfsLK_sound s4G hdF4 pts4

theorem orbits : orbitChecks = true := by
  have h1 : orbitOK f6Arr.size s6Perms o6Lists[0]! = true := by
    rw [f6_size, o6_0]
    exact orbitOK_sound s6G (imgs img6) hd60 pts60
  have h2 : orbitOK f6Arr.size s6Perms o6Lists[1]! = true := by
    rw [f6_size, o6_1]
    exact orbitOK_sound s6G (imgs img6) hd61 fun j hj =>
      pts_of sl61 j (Nat.zero_le _) (by have e : HO6_1.cnt = 1100 := rfl; omega) hj
  have h3 : orbitOK f4Arr.size s4J (bfsList f4Arr.size s4J 0) = true := by
    rw [bfs4, f4_size]
    exact orbitOK_sound s4G (imgs img4) hdF4 pts4
  have h4 : (bfsList f4Arr.size s4J 0).size = 800 := by
    rw [bfs4, Array.size_ofFn]
    rfl
  have h5 : (o1Lists.size == 3 && o1Lists.map Array.size == #[1, 945, 210]) = true := by
    rw [o1_eq]
    decide +kernel
  have h6 : (o6Lists.size == 2 && o6Lists.map Array.size == #[7700, 1100]) = true := by
    rw [o6_eq]
    decide +kernel
  unfold orbitChecks
  simp only [Bool.and_eq_true] at h5 h6
  simp only [h5.1, h5.2, h6.1, h6.2, (allBelowN_iff).2 orb1, h1, h2, h3, h4, beq_self_eq_true,
    Bool.and_self]

theorem facts2091 : natChainChecks = true ∧ orbitChecks = true := ⟨natChains, orbits⟩

end CertificateChecks.KernelSpor.HN2091

end
