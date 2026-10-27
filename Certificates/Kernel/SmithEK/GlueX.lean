
module

public import Certificates.Kernel.SmithEK.XRowsA
public import Certificates.Kernel.SmithEK.XRowsB
public import Certificates.Kernel.SmithEK.XRowsC
public import Certificates.Kernel.SmithEK.XChk
public import Certificates.Kernel.SmithEK.GlueN
public import CFSG.Certificates.Kernel.SmithEK.XSound

public section

namespace CertificateChecks.KernelSmithEK

open CFSG.SmithE CFSG.SmithE.K CFSG.KC.Misc.O73 CFSG.LargeExtraspecial.SMod20 CFSG.Sporadic.Th
  CFSG.Fischer.Native CFSG.Sporadic.Th.Native

theorem c21264chunks : ∀ c < 42, ixChunk pn.CP ix.D (16 * c) 16 = true
  | 0, _ => c21264row_0
  | 1, _ => c21264row_1
  | 2, _ => c21264row_2
  | 3, _ => c21264row_3
  | 4, _ => c21264row_4
  | 5, _ => c21264row_5
  | 6, _ => c21264row_6
  | 7, _ => c21264row_7
  | 8, _ => c21264row_8
  | 9, _ => c21264row_9
  | 10, _ => c21264row_10
  | 11, _ => c21264row_11
  | 12, _ => c21264row_12
  | 13, _ => c21264row_13
  | 14, _ => c21264row_14
  | 15, _ => c21264row_15
  | 16, _ => c21264row_16
  | 17, _ => c21264row_17
  | 18, _ => c21264row_18
  | 19, _ => c21264row_19
  | 20, _ => c21264row_20
  | 21, _ => c21264row_21
  | 22, _ => c21264row_22
  | 23, _ => c21264row_23
  | 24, _ => c21264row_24
  | 25, _ => c21264row_25
  | 26, _ => c21264row_26
  | 27, _ => c21264row_27
  | 28, _ => c21264row_28
  | 29, _ => c21264row_29
  | 30, _ => c21264row_30
  | 31, _ => c21264row_31
  | 32, _ => c21264row_32
  | 33, _ => c21264row_33
  | 34, _ => c21264row_34
  | 35, _ => c21264row_35
  | 36, _ => c21264row_36
  | 37, _ => c21264row_37
  | 38, _ => c21264row_38
  | 39, _ => c21264row_39
  | 40, _ => c21264row_40
  | 41, _ => c21264row_41
  | _ + 42, h => absurd h (by omega)

theorem c21264rows {i : Nat} (hi : i < 675) :
    ixF (ix.D.getD i 0) = ixFix pn.CP (ixS (ix.D.getD i 0)) ∧
      Nat.ble (cntK 65 (ixF (ix.D.getD i 0))) 64 = true ∧
      ixRow i (ix.D.getD i 0) ix.D = true := by
  by_cases hl : i < 672
  · have h := ixChunk_spec (c21264chunks (i / 16) (by omega)) (k := i % 16) (Nat.mod_lt _ (by omega))
    rwa [Nat.div_add_mod] at h
  · have h := ixChunk_spec c21264rowLast (k := i - 672) (by omega)
    rwa [show 672 + (i - 672) = i by omega] at h

theorem xUnpack_get {p k : Nat} (hk : k < 21) : (ivUnpack p)[k]! = at' 5 p k := by
  unfold ivUnpack
  rw [getElem!_pos _ k (by rw [Array.size_ofFn]; exact hk), Array.getElem_ofFn]

theorem xFlat_eq : (List.range 21).flatMap (fun y0 => pn.R.getD y0 []) = ix.D.map ixS := by
  decide +kernel

theorem xCollI_eq : collI = ((ix.D.map ixS).map ivUnpack).toArray := by
  unfold collI
  rw [collInvs_eq, ← xFlat_eq, List.map_flatMap]

theorem xCollI_size : collI.size = 675 := by
  rw [xCollI_eq, List.size_toArray, List.length_map, List.length_map, c21264len]

theorem xCollI_get {i : Nat} (hi : i < 675) : collI[i]! = ivUnpack (ixS (ix.D.getD i 0)) := by
  have hl : i < ix.D.length := by rw [c21264len]; exact hi
  have hs : i < ((ix.D.map ixS).map ivUnpack).toArray.size := by
    rw [List.size_toArray, List.length_map, List.length_map]
    exact hl
  rw [xCollI_eq, getElem!_pos _ i hs, List.getElem_toArray, List.getElem_map, List.getElem_map,
    List.getD_eq_getElem _ _ hl]

theorem xMem_filt {L : List (Array Nat)} {g : Array Nat → Array Nat} {p : Array Nat → Bool}
    {s : Array Nat} (hs : s ∈ (L.filterMap fun y => if p (g y) then some (g y) else none).toArray) :
    p s = true := by
  rw [List.mem_toArray, List.mem_filterMap] at hs
  obtain ⟨y, -, hy⟩ := hs
  by_cases h : p (g y) = true
  · rw [if_pos h] at hy
    cases hy
    exact h
  · rw [if_neg h] at hy
    cases hy

theorem xAdm_of_mem {s : Array Nat} (hs : s ∈ collI) : collAdm s = true := by
  unfold collI collInvs at hs
  have h := xMem_filt (L := collDom collS2) (g := collCon (collMeet collS2))
    (p := fun s => collComp s s == collId && s != collId && collAdm s) hs
  rw [Bool.and_eq_true] at h
  exact h.2

theorem xFields {i : Nat} (hi : i < 675) : ∀ k < 21, at' 5 (ixS (ix.D.getD i 0)) k < 21 := by
  intro k hk
  have hm : collI[i]! ∈ collI := by
    rw [getElem!_pos collI i (by rw [xCollI_size]; exact hi)]
    exact Array.getElem_mem _
  have h := (collAdm_parts (xAdm_of_mem hm)).2.1 k hk
  rwa [xCollI_get hi, xUnpack_get hk] at h

theorem xCP_lt {x : Nat} (hx : x < 21) : at' 9 pn.CP x < 512 := by
  have h : ∀ x < 21, uaCo[x]! < 512 := by decide +kernel
  rw [pnCP_get]
  exact h x hx

theorem xAmatN_eq {s a : Nat} (hs : ∀ k < 21, at' 5 s k < 21) :
    ∀ n ≤ 9, ixAmatN pn.CP s a n = collAmatN (ivUnpack s) a n
  | 0, _ => rfl
  | n + 1, hn => by
    change ixAmatN pn.CP s a n ^^^ (bif a.testBit n then at' 9 pn.CP (at' 5 s n) else 0) = _
    rw [xAmatN_eq hs n (by omega), collAmatN, xUnpack_get (by omega : n < 21), pnCP_get]
    cases a.testBit n <;> rfl

theorem xFix_eq {i a : Nat} (hi : i < 675) (ha : a < 512) :
    ((collFixTab collI)[i]!)[a]! = (ixF (ix.D.getD i 0)).testBit a := by
  have hs := xFields hi
  rw [collFixTab_get (by rw [xCollI_size]; exact hi) ha, xCollI_get hi, (c21264rows hi).1,
    ixFix_testBit (fun j hj => xCP_lt (hs j (by omega))) ha, xAmatN_eq hs 9 (Nat.le_refl 9)]
  unfold collAmat
  apply Bool.eq_iff_iff.2
  rw [beq_iff_eq, decide_eq_true_iff]

theorem xComp_comm {s t : Nat} (hs : ∀ k < 21, at' 5 s k < 21) (ht : ∀ k < 21, at' 5 t k < 21) :
    (collComp (ivUnpack s) (ivUnpack t) == collComp (ivUnpack t) (ivUnpack s)) = ixComm s t := by
  apply Bool.eq_iff_iff.2
  rw [beq_iff_eq, ixComm_iff]
  constructor
  · intro h k hk
    have e := congrArg (fun A : Array Nat => A[k]!) h
    simp only [collComp_get hk, xUnpack_get hk, xUnpack_get (hs k hk), xUnpack_get (ht k hk)] at e
    exact e
  · intro h
    refine array_ext_getElem! (n := 21) (by rw [collComp_size]) (by rw [collComp_size])
      fun k hk => ?_
    rw [collComp_get hk, collComp_get hk, xUnpack_get hk, xUnpack_get hk,
      xUnpack_get (ht k hk), xUnpack_get (hs k hk)]
    exact h k hk

theorem xRow {i j : Nat} (hi : i < 675) (hj : j < 675) :
    (bif ixComm (ixS (ix.D.getD i 0)) (ixS (ix.D.getD j 0)) then
        ixBit (ixC (ix.D.getD i 0)) j && (Nat.beq i j ||
          (Nat.ble (cntK 17 (Nat.land (ixF (ix.D.getD i 0)) (ixF (ix.D.getD j 0)))) 16 &&
            Nat.ble (cntK 28 (Nat.land (ixC (ix.D.getD i 0)) (ixC (ix.D.getD j 0)))) 27))
      else !ixBit (ixC (ix.D.getD i 0)) j) = true := by
  have h := ixRow_spec ix.D 0 (c21264rows hi).2.2 j (by rw [c21264len]; exact hj)
  rwa [Nat.zero_add] at h

theorem xComm_eq {i j : Nat} (hi : i < 675) (hj : j < 675) :
    ((collCommTab collI)[i]!)[j]! = ixComm (ixS (ix.D.getD i 0)) (ixS (ix.D.getD j 0)) := by
  rw [collCommTab_get (by rw [xCollI_size]; exact hi) (by rw [xCollI_size]; exact hj),
    xCollI_get hi, xCollI_get hj, xComp_comm (xFields hi) (xFields hj)]

theorem xComm_bit {i j : Nat} (hi : i < 675) (hj : j < 675) :
    ((collCommTab collI)[i]!)[j]! = (ixC (ix.D.getD i 0)).testBit j := by
  have h := xRow hi hj
  rw [xComm_eq hi hj]
  cases hc : ixComm (ixS (ix.D.getD i 0)) (ixS (ix.D.getD j 0))
  · rw [hc, cond_false, Bool.not_eq_true', ixBit_eq] at h
    exact h.symm
  · rw [hc, cond_true, Bool.and_eq_true, ixBit_eq] at h
    exact h.1.symm

theorem xBound : collBoundOK collI (collFixTab collI) (collCommTab collI) = true := by
  unfold collBoundOK
  rw [xCollI_size, Bool.and_eq_true]
  refine ⟨allIn_eq_true.2 fun i _ hi => ?_,
    allIn_eq_true.2 fun i _ hi => allIn_eq_true.2 fun j _ hj => ?_⟩
  · rw [decide_eq_true_eq]
    have e : (List.range 512).countP (fun a => ((collFixTab collI)[i]!)[a]!) =
        cntB 512 (ixF (ix.D.getD i 0)) := by
      unfold cntB
      exact List.countP_congr fun a ha => by rw [xFix_eq hi (List.mem_range.1 ha)]
    rw [e]
    exact cntB_le_of_cntK (c21264rows hi).2.1 512
  · have h := xRow hi hj
    rw [xComm_eq hi hj]
    cases hc : ixComm (ixS (ix.D.getD i 0)) (ixS (ix.D.getD j 0))
    · simp
    · rw [hc, cond_true, Bool.and_eq_true, Bool.or_eq_true, Bool.and_eq_true] at h
      rcases h.2 with h0 | ⟨h16, h27⟩
      · rw [Nat.eq_of_beq_eq_true h0, beq_self_eq_true, Bool.true_or, Bool.true_or]
      · have e1 : (List.range 512).countP (fun a => ((collFixTab collI)[i]!)[a]! &&
            ((collFixTab collI)[j]!)[a]!) =
            cntB 512 (ixF (ix.D.getD i 0) &&& ixF (ix.D.getD j 0)) := by
          unfold cntB
          exact List.countP_congr fun a ha => by
            rw [xFix_eq hi (List.mem_range.1 ha), xFix_eq hj (List.mem_range.1 ha),
              Nat.testBit_and]
        have e2 : (List.range 675).countP (fun k => ((collCommTab collI)[i]!)[k]! &&
            ((collCommTab collI)[j]!)[k]!) =
            cntB 675 (ixC (ix.D.getD i 0) &&& ixC (ix.D.getD j 0)) := by
          unfold cntB
          exact List.countP_congr fun k hk => by
            rw [xComm_bit hi (List.mem_range.1 hk), xComm_bit hj (List.mem_range.1 hk),
              Nat.testBit_and]
        have b1 : cntB 512 (ixF (ix.D.getD i 0) &&& ixF (ix.D.getD j 0)) ≤ 16 :=
          cntB_le_of_cntK h16 512
        have b2 : cntB 675 (ixC (ix.D.getD i 0) &&& ixC (ix.D.getD j 0)) ≤ 27 :=
          cntB_le_of_cntK h27 675
        rw [e1, e2, decide_eq_true b1, decide_eq_true b2, Bool.and_true, Bool.or_true]

theorem xCo : collCoOK = true := by
  have hbq : ∀ a b : Nat, (Nat.beq a b = false) = ¬ a = b := fun a b => by
    rw [← Bool.not_eq_true, Nat.beq_eq]
  have hbl : ∀ a b : Nat, (Nat.blt a b = false) = (b ≤ a) := fun a b => by
    rw [← Bool.not_eq_true, Nat.blt_eq]
    exact propext Nat.not_lt
  have h := c21264co
  unfold ixCo at h
  simp only [Bool.and_eq_true, ixAll_iff, pnCP_get] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  unfold collCoOK
  simp only [Bool.and_eq_true, allIn_eq_true]
  refine ⟨⟨⟨rfl, fun k _ hk => ?_⟩, fun k _ hk => ?_⟩, fun k _ hk => ?_⟩
  · simpa [Nat.blt_eq] using h1 k hk
  · simpa [Nat.beq_eq, ixAll_iff, allIn_eq_true, hbq] using h2 k hk
  · simpa [Nat.blt_eq, Nat.beq_eq, ixAll_iff, allIn_eq_true, hbq, hbl] using h3 k hk

theorem xValidL : ∀ (L : List (Nat × Nat × Nat × Nat × Nat)) (K : List Nat),
    (∀ st ∈ L, st.2.1 < 21 ∧ st.2.2.1 < 21 ∧ st.2.2.2.1 < 21 ∧ st.2.2.2.2 < 21) →
    ixValid pn.CP (s2K pn.CL) K L = true → collValid collS2 K L = true
  | [], _, _, _ => by rw [collValid]
  | st :: L, K, hb, h => by
    have e : ixValid pn.CP (s2K pn.CL) K (st :: L) = (K.contains st.2.1 && K.contains st.2.2.1 &&
        K.contains st.2.2.2.1 && K.contains st.2.2.2.2 && Nat.blt st.1 21 &&
        ixAll 21 (fun z => (ivP pn.CP (s2K pn.CL) z st.2.1 st.2.2.1 &&
          ivP pn.CP (s2K pn.CL) z st.2.2.2.1 st.2.2.2.2) == Nat.beq z st.1) &&
        ixValid pn.CP (s2K pn.CL) (st.1 :: K) L) := rfl
    rw [e, Bool.and_eq_true, Bool.and_eq_true, ixAll_iff] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    obtain ⟨b1, b2, b3, b4⟩ := hb st List.mem_cons_self
    rw [collValid, Bool.and_eq_true, Bool.and_eq_true, allIn_eq_true]
    refine ⟨⟨?_, fun z _ hz => ?_⟩, xValidL L (st.1 :: K) (fun s hs => hb s
      (List.mem_cons_of_mem _ hs)) h3⟩
    · simpa only [Bool.and_eq_true, Nat.blt_eq, decide_eq_true_eq] using h1
    · have hz' := h2 z hz
      unfold collQ
      rw [← ivP_eq hz b1 b2, ← ivP_eq hz b3 b4, ← beq_eq']
      exact hz'

theorem xValid : collValid collS2 collBase.toList collSteps = true :=
  xValidL collSteps collBase.toList (by decide) c21264valid

theorem xCover : allIn 0 21 (fun k => (collBase.toList ++ collSteps.map (·.1)).contains k) = true := by
  have h : ∀ k < 21, (collBase.toList ++ collSteps.map (·.1)).contains k = true := by decide
  exact allIn_eq_true.2 fun k _ hk => h k hk

theorem xFrame : collFrame collS2 0 1 4 10 3 = true :=
  (frame_iff (by decide) (by decide) (by decide) (by decide) (by decide)).1 c21264frame

theorem chkColl_eq : chkColl () = true := by
  unfold chkColl
  have hb := xBound
  unfold collI at hb
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨⟨xCo, xValid⟩, xCover⟩, xFrame⟩, hb⟩

end CertificateChecks.KernelSmithEK
