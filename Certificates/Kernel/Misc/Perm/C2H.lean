module

public import Certificates.Kernel.Misc.Perm.C2G
public import CFSG.RankThree.Native.Co2FiveCheckInputs
public import Certificates.Kernel.Misc.Perm.C2P
public import Certificates.Kernel.Misc.Perm.C2S
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CertificateChecks.KernelMisc.Co2K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.RankThree.Native.F2
open CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.Sporadic.Co2Cert (co2StrongArrs co2BaseArr)

abbrev LL : Array Level := rawLevels 2300 co2StrongArrs co2BaseArr

theorem hd22 : 0 < 22 := by norm_num

theorem idA_eq : idA 2300 = permOfMat 22 co2FiveV I22 := by
  rw [I22_eq, permOfMat_idM hd22 sys.nodup sys.lt, V_size]

theorem arr_eq {k : ℕ} (hk : k < 38) : co2FiveArr k = permOfMat 22 co2FiveV (AM k) :=
  (amF hk).2.1

theorem maps_I22 : ∀ v ∈ co2FiveV, vmul 22 v I22 ∈ co2FiveV := by
  rw [I22_eq]
  exact (inv_idM hd22 sys.lt).1

theorem sift_parts : siftM vmK mmK I22 2300 VG BS LK mL PO TIM 6 0 I22 = true ∧
    ∀ k < 38, siftM vmK mmK I22 2300 VG BS LK mL PO TIM 6 0 (AM k) = true := by
  have h := sift_ok
  unfold siftK at h
  rw [Bool.and_eq_true] at h
  exact ⟨h.1, allN_spec h.2⟩

theorem sift_of {G : ℕ} (hG : ∀ v ∈ co2FiveV, vmul 22 v G ∈ co2FiveV)
    (h : siftM vmK mmK I22 2300 VG BS LK mL PO TIM 6 0 G = true) :
    siftA 2300 LL co2BaseArr 0 (permOfMat 22 co2FiveV G) = true := by
  have h' := siftA_of_siftM sys hvm hmm I22_eq LF hBS hb 6 0 G (by rw [base_size]) hG
    (by rwa [V_size])
  rwa [V_size] at h'

theorem sift_arr {k : ℕ} (hk : k < 38) : siftA 2300 LL co2BaseArr 0 (co2FiveArr k) = true := by
  rw [arr_eq hk]
  exact sift_of (amF hk).1.1 (sift_parts.2 k hk)

theorem sift_id : siftA 2300 LL co2BaseArr 0 (idA 2300) = true := by
  rw [idA_eq]
  exact sift_of maps_I22 sift_parts.1

theorem sifts_ok : co2FiveSiftArrs.all (siftA 2300 LL co2BaseArr 0) = true := by
  rw [List.all_eq_true]
  intro a ha
  simp only [co2FiveSiftArrs, List.mem_append, List.mem_cons, List.mem_map, List.mem_range,
    co2FiveC0GenArrs, co2FiveQGenArrs, co2FiveC1GenArrs, List.not_mem_nil, or_false,
    co2FiveX0Arr, co2FiveX1Arr, co2FiveTArr, or_assoc] at ha
  have hs : ∀ k < 38, a = co2FiveArr k → siftA 2300 LL co2BaseArr 0 a = true :=
    fun k hk e => (congrArg (siftA 2300 LL co2BaseArr 0) e).trans (sift_arr hk)
  rcases ha with h | h | h | h | h | h | h | h | h | h | ⟨j, hj, h⟩
  · exact hs 0 (by norm_num) h
  · exact hs 1 (by norm_num) h
  · exact hs 8 (by norm_num) h
  · exact hs 2 (by norm_num) h
  · exact hs 3 (by norm_num) h
  · exact hs 4 (by norm_num) h
  · exact hs 5 (by norm_num) h
  · exact hs 1 (by norm_num) h
  · exact hs 6 (by norm_num) h
  · exact hs 7 (by norm_num) h
  · rw [← h]
    unfold co2FiveHArr
    split
    · exact sift_id
    · exact sift_arr (by omega)

theorem Z_maps : ∀ v ∈ co2FiveV, vmul 22 v ZM ∈ co2FiveV := by
  rw [ZM, hmm, hmm]
  exact maps_mmul (maps_mmul (amF (k := 8) (by norm_num)).1.2.1 (amF (k := 1) (by norm_num)).1.1)
    (amF (k := 8) (by norm_num)).1.1

theorem Z_eq : co2FiveZArr = permOfMat 22 co2FiveV ZM := by
  have h := conjA_permOfMat hd22 sys.nodup sys.lt (amF (k := 8) (by norm_num)).1
    (amF (k := 1) (by norm_num)).1.1
  rw [V_size, ← arr_eq (by norm_num), ← arr_eq (by norm_num)] at h
  rw [co2FiveZArr, co2FiveTArr, co2FiveX1Arr, h, ZM, hmm, hmm]

theorem fix_parts : (fixZ.all fun q => Nat.blt q 2300 && Nat.beq (vmK (VG q) ZM) (VG q)) = true ∧
    (∀ q < 2300, (!(Nat.beq (vmK (VG q) ZM) (VG q)) || fixZ.contains q) = true) ∧
    (fixZ.filter fun q => Nat.blt (PO 0 q) (mL 0)).length = 10 ∧
    (fixZ.filter fun q => Nat.blt (PO 1 q) (mL 1)).length = 3 ∧
    (fixZ.filter fun q => Nat.blt (PO 2 q) (mL 2)).length = 2 ∧
    (fixZ.filter fun q => Nat.blt (PO 3 q) (mL 3)).length = 2 ∧
    ∀ k < 4, vmK (VG k) ZM = VG k := by
  have h := fix_ok
  unfold fixK at h
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨h1, allN_spec h2, h3, h4, h5, h6, fun k hk => Nat.eq_of_beq_eq_true (allN_spec h7 k hk)⟩

theorem fix_count {i : ℕ} (hi : i < 6) :
    fixLevCount 2300 LL co2FiveZArr i = (fixZ.filter fun q => Nat.blt (PO i q) (mL i)).length := by
  obtain ⟨h1, h2, -⟩ := fix_parts
  rw [List.all_eq_true] at h1
  have h := fixLevCount_eq sys LF Z_maps (F := fixZ) (by decide)
    (fun q hq => by
      have := h1 q hq
      rw [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, hvm] at this
      exact ⟨by rw [V_size]; exact this.1, this.2⟩)
    (fun q hq hfix => by
      rw [V_size] at hq
      have := h2 q hq
      rw [hvm, hfix, Nat.beq_refl, Bool.not_true, Bool.false_or, List.contains_iff_mem] at this
      exact this) (i := i) (by rw [base_size]; exact hi)
  rwa [V_size, ← Z_eq] at h

theorem z_ok : (co2FiveZArr[0]! == 0 && co2FiveZArr[1]! == 1 && co2FiveZArr[2]! == 2 &&
    co2FiveZArr[3]! == 3) = true := by
  have hz : ∀ k < 4, co2FiveZArr[k]! = k := by
    intro k hk
    have hk' : k < co2FiveV.size := by rw [V_size]; omega
    rw [Z_eq, sys.perm_get hk', ← hvm, fix_parts.2.2.2.2.2.2 k hk, sys.vidx_eq hk']
  rw [hz 0 (by norm_num), hz 1 (by norm_num), hz 2 (by norm_num), hz 3 (by norm_num)]
  rfl

theorem pow_eq (A : ℕ) (hA : ∀ v ∈ co2FiveV, vmul 22 v A ∈ co2FiveV) (e : ℕ) :
    CFSG.Monster.B.Mathieu.powArr 2300 (permOfMat 22 co2FiveV A) e =
      permOfMat 22 co2FiveV (pwK A e) := by
  have h := powArr_permOfMat hd22 sys.nodup sys.lt hA e
  rw [V_size] at h
  rw [h, pwK, mpowW_eq hmm I22_eq]

theorem tail_ok' : tailOK 2300 LL co2FiveZArr co2FiveZPows 2 4 (idA 2300) = true := by
  have h := tailOK_of_tailM spans hmm LF Z_maps (E := co2FiveZPows) (EM := memZ)
    (fun A _ hm => by
      rw [memZ, List.any_eq_true] at hm
      obtain ⟨e, he, hAe⟩ := hm
      rw [Nat.beq_eq] at hAe
      rw [List.any_eq_true]
      refine ⟨permOfMat 22 co2FiveV A, ?_, ?_⟩
      · rw [co2FiveZPows, List.mem_map]
        refine ⟨e, he, ?_⟩
        rw [Z_eq, pow_eq ZM Z_maps, hAe]
      · rw [eqA, allLt_iff]
        exact fun i _ => beq_self_eq_true _)
    2 4 I22 (by rw [base_size]) maps_I22 tail_ok
  rwa [V_size, ← Z_eq, ← idA_eq] at h

theorem X0_maps : ∀ v ∈ co2FiveV, vmul 22 v (AM 0) ∈ co2FiveV := (amF (k := 0) (by norm_num)).1.1

theorem XP_eq {e : ℕ} (he : e < 5) :
    co2FiveX0PowArrs[e]! = permOfMat 22 co2FiveV (pwK (AM 0) e) := by
  rw [co2FiveX0PowArrs, getElem!_pos _ e (by simpa using he), Array.getElem_ofFn, co2FiveX0Arr,
    arr_eq (by norm_num),
    pow_eq _ X0_maps]

theorem XP_size : co2FiveX0PowArrs.size = 5 := by simp [co2FiveX0PowArrs]

theorem rel_parts : ∀ r ∈ co2FiveRels, r.2.2 < 5 ∧ r.1 < 6 ∧ r.2.1 < 6 ∧
    vmK (VG (BS r.1)) (pwK (AM 0) r.2.2) = VG (BS r.2.1) := by
  intro r hr
  have h := List.all_eq_true.1 rels_ok r hr
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem rels_ok' : co2FiveRels.all (fun r => decide (r.2.2 < co2FiveX0PowArrs.size) &&
      decide (r.1 < co2BaseArr.size) && decide (r.2.1 < co2BaseArr.size) &&
      (co2FiveX0PowArrs[r.2.2]!)[co2BaseArr[r.1]!]! == co2BaseArr[r.2.1]!) = true := by
  rw [List.all_eq_true]
  intro r hr
  obtain ⟨h1, h2, h3, h4⟩ := rel_parts r hr
  have hb1 : BS r.1 < co2FiveV.size := hb _ (by rw [base_size]; exact h2)
  have hb2 : BS r.2.1 < co2FiveV.size := hb _ (by rw [base_size]; exact h3)
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, XP_size, base_size]
  refine ⟨⟨⟨h1, h2⟩, h3⟩, ?_⟩
  rw [XP_eq h1, hBS _ (by rw [base_size]; exact h2), hBS _ (by rw [base_size]; exact h3),
    sys.perm_get hb1, ← hvm, h4, sys.vidx_eq hb2]

theorem pv_mem : ∀ i < co2BaseArr.size, pvf i = true → ((fun _ => 0) i, i, pve i) ∈ co2FiveRels ∧
    (fun _ => 0) i < i := by
  intro i hi hp
  rw [base_size] at hi
  interval_cases i <;> first | exact absurd hp (by decide) | exact ⟨by decide, by decide⟩

theorem ptailM_root : ptR 6 0 I22 I22 = true := by
  have hp0 : pvf 0 = false := rfl
  unfold ptR
  rw [ptailM_succ (fuel := 5), hp0, Bool.cond_false]
  apply allN_of_forall
  exact allN_of_chunks (c := 575) (n := 4) (f := ptBody) ptail_chunks

theorem ptail_ok' {c : CFSG.Monster.B.Fischer.ArrCert} (hc : c.pts.size = 3000)
    (hp : ∀ i < 3000, c.pts[i]! = permOfMat 22 co2FiveV (PC0 i)) :
    ptailOK 2300 LL co2BaseArr co2FiveX0Arr co2FiveX0PowArrs co2FiveRels c.pts.toList 6 0
      (idA 2300) = true := by
  have hse : ∀ j < 3000, f12 (SEPt 0) j < 3000 ∧ SEt j = PC0 (f12 (SEPt 0) j) := by
    intro j hj
    have := allN_spec se_ok j hj
    rw [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at this
    exact this
  have h := ptailOK_of_ptailM sys hvm hmm spans LF hBS hb X0_maps (xs := co2FiveX0PowArrs)
    (XP := pwK (AM 0)) (fun e he => XP_eq (by rwa [XP_size] at he))
    (fun e _ => by rw [pwK, mpowW_eq hmm I22_eq]; exact maps_mpow hd22 sys.lt X0_maps e)
    (rels := co2FiveRels) (fun r hr => by
      obtain ⟨h1, h2, h3, -⟩ := rel_parts r hr
      exact ⟨by rw [XP_size]; exact h1, by rw [base_size]; exact h2, by rw [base_size]; exact h3⟩)
    (E := c.pts.toList) (EM := memC0)
    (fun A _ hm => by
      unfold memC0 at hm
      rw [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hm
      obtain ⟨hlt, heq⟩ := hm
      obtain ⟨hq, hpe⟩ := hse _ hlt
      rw [List.any_eq_true]
      refine ⟨c.pts[f12 (SEPt 0) (seRow A)]!, ?_, ?_⟩
      · rw [getElem!_pos c.pts _ (by rw [hc]; exact hq)]
        exact Array.getElem_mem_toList _
      · rw [hp _ hq, ← hpe, heq, eqA, allLt_iff]
        exact fun i _ => beq_self_eq_true _)
    pv_mem 6 0 I22 I22 (by rw [base_size]) maps_I22 (by rw [I22_eq]; exact mmul_idM_idM hd22)
    (by rw [V_size]; exact ptailM_root)
  rw [V_size, ← idA_eq, ← arr_eq (k := 0) (by norm_num)] at h
  rw [co2FiveX0Arr]
  exact h

theorem chain_ok {c : CFSG.Monster.B.Fischer.ArrCert} (hc : c.pts.size = 3000)
    (hp : ∀ i < 3000, c.pts[i]! = permOfMat 22 co2FiveV (PC0 i)) :
    co2FiveChainCheck LL c = true := by
  obtain ⟨-, -, h0, h1, h2, h3, -⟩ := fix_parts
  unfold co2FiveChainCheck
  rw [sifts_ok, z_ok, fix_count (by norm_num), fix_count (by norm_num), fix_count (by norm_num),
    fix_count (by norm_num), h0, h1, h2, h3, tail_ok', rels_ok', ptail_ok' hc hp]
  rfl

end CertificateChecks.KernelMisc.Co2K

end
