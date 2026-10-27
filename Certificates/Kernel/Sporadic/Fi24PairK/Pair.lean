module

public import Certificates.Kernel.Sporadic.Fi24PairK.Lines
public import Certificates.Kernel.Sporadic.Fi24PairK.PcBound
public import Certificates.Kernel.Sporadic.Fi24PairK.Checks.O0
public import Certificates.Kernel.Sporadic.Fi24PairK.Checks.O1
import CFSG.Certificates.Kernel.Common.ForallTree

public section

namespace CertificateChecks.KernelFi24PairK

open CFSG.KC CFSG.KC.Fi24PairK CFSG.KS.Fi24PairPc CFSG.KS.Fi24PairK CFSG.Sporadic.Th
  CFSG.Sporadic.Fi24 CFSG.Perm CFSG.Sporadic.LevelChain CFSG.LocalAnalysis.WeakClosure81.SporFi24
open CFSG.KD.Fi24PairK (NV net fl och fch lvW chOf lvOf)
open CFSG.KD.Fi24PairPc (lvT lvA lvB card_T0_le card_A0_le card_B0_le)
open CFSG.Sporadic.Fi24Pair.Native

#kc_forall_tree okAll (fun g => CFSG.KD.Fi24PairK.och g = true) 18 CFSG.KD.Fi24PairK.Ck.o
#kc_forall_tree fkAll (fun g => CFSG.KD.Fi24PairK.fch g = true) 18 CFSG.KD.Fi24PairK.Ck.f

@[expose] def NestP (D : ChainData) : Prop :=
  ∀ i < D.base.size, 1 ≤ i → ∀ j < D.starts[i + 1]!, D.starts[i]! ≤ j → ∀ z ∈ W[D.sel[j]!]!,
    3 ≤ z.natAbs ∧ ∃ k < D.starts[i]!, D.starts[i - 1]! ≤ k ∧ D.sel[k]! + 3 = z.natAbs

@[expose] noncomputable def NestB (D : ChainData) : Bool :=
  (List.range D.base.size).all fun i => decide (i = 0) ||
    (List.range' D.starts[i]! (D.starts[i + 1]! - D.starts[i]!)).all fun j =>
      W[D.sel[j]!]!.all fun z => decide (3 ≤ z.natAbs) &&
        (List.range' D.starts[i - 1]! (D.starts[i]! - D.starts[i - 1]!)).any fun k =>
          D.sel[k]! + 3 == z.natAbs

theorem nestP_of {D : ChainData} (h : NestB D = true) : NestP D := by
  intro i hi hi1 j hj2 hj1 z hz
  unfold NestB at h
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq,
    List.mem_range'_1, Bool.and_eq_true, List.any_eq_true, beq_iff_eq] at h
  rcases h i hi with h1 | h1
  · omega
  obtain ⟨h4, k, hk, hk'⟩ := h1 j ⟨hj1, by omega⟩ z hz
  exact ⟨h4, k, by omega, hk.1, hk'⟩

theorem mem_take_succ {A : Array Nat} {i : ℕ} (hi : i < A.size) : A[i]! ∈ A.toList.take (i + 1) := by
  rw [getElem!_pos A i hi]
  refine List.mem_iff_getElem.2 ⟨i, by simp; omega, ?_⟩
  simp

theorem fl_mem_lvW {D : ChainData} {i k : ℕ} (hk1 : D.starts[i]! ≤ k) (hk2 : k < D.starts[i + 1]!) :
    fl D.sel[k]! ∈ lvW D i := by
  unfold CFSG.KD.Fi24PairK.lvW
  exact List.mem_map.2 ⟨k, List.mem_range'_1.2 ⟨hk1, by omega⟩, rfl⟩

theorem mem_lvW {D : ChainData} {i : ℕ} {w : List ℤ} (hw : w ∈ lvW D i) :
    ∃ k, D.starts[i]! ≤ k ∧ k < D.starts[i + 1]! ∧ w = fl D.sel[k]! := by
  unfold CFSG.KD.Fi24PairK.lvW at hw
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hw
  rw [List.mem_range'_1] at hk
  exact ⟨k, hk.1, by omega, rfl⟩


theorem cgs_mem_prev' {D : ChainData} (hnest : NestP D) :
    ∀ i, 1 ≤ i → i < D.base.size → ∀ j, D.starts[i]! ≤ j → j < D.starts[i + 1]! →
      cgs D j ∈ clvl D (i - 1) := by
  intro i hi1 hi j hj1 hj2
  unfold cgs line
  rw [CFSG.Sporadic.Fi23.slpG_eq]
  unfold wordG
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hx
  obtain ⟨h3, k', hk2, hk1, hk'⟩ := hnest i hi hi1 j hj2 hj1 z hz
  have hm : cgs D k' ∈ clvl D (i - 1) := by
    refine gs_mem_lvlGroup (cgs D) hk1 ?_
    have e : i - 1 + 1 = i := by omega
    rw [e]
    exact hk2
  unfold cgs line at hm
  have hz2 : ¬ z.natAbs ≤ 2 := by omega
  have hz3 : z.natAbs - 3 = D.sel[k']! := by omega
  simp only [hz2, ite_false, hz3]
  split_ifs
  · exact hm
  · exact Subgroup.inv_mem _ hm
  · exact Subgroup.one_mem _

theorem wEl_fl_mem {D : ChainData} {i : ℕ} {w : List ℤ} (hw : w ∈ lvW D i) :
    wEl LL w ∈ clvl D i := by
  obtain ⟨k, hk1, hk2, rfl⟩ := mem_lvW hw
  rw [(fl_eq _).2]
  exact gs_mem_lvlGroup (cgs D) hk1 hk2

theorem chain_ge {D : ChainData} {m o : ℕ} (hm : 0 < m) (ho : o + m ≤ 18)
    (hch : ∀ i < m, chOf (o + i) = D) (hlv : ∀ i < m, lvOf (o + i) = i)
    (hsz : D.base.size = m) (hbase : ∀ i < m, D.base[i]! < 306936) (hnest : NestP D) :
    ∏ l ∈ Finset.Ico 0 m, D.sizes.getD l 0 ≤ Nat.card (clvl D 0) := by
  let b : ℕ → Fin 306936 := fun i => ⟨D.base[i]! % 306936, Nat.mod_lt _ (by norm_num)⟩
  have hb : ∀ i (hi : i < m), b i = ⟨D.base[i]!, hbase i hi⟩ := fun i hi =>
    Fin.ext (Nat.mod_eq_of_lt (hbase i hi))
  refine card_chain_ge (clvl D) b (fun l => D.sizes.getD l 0) ?_ ?_ ?_ 0 hm
  · intro i hi
    refine lvlGroup_le (cgs D) _ fun j hj1 hj2 => ?_
    have h := cgs_mem_prev' hnest (i + 1) (by omega) (by omega) j hj1 hj2
    rwa [Nat.add_sub_cancel] at h
  · intro i hi g hg
    have hf := fkAll (o + (i + 1)) (Nat.lt_of_lt_of_le (by omega : o + (i + 1) < o + m) ho)
    unfold CFSG.KD.Fi24PairK.fch at hf
    rw [hch _ (by omega), hlv _ (by omega)] at hf
    have hf' : (lvW D (i + 1)).all (fun w => andB (dirOK net w)
        (fixW NV w (D.base.toList.take (i + 1)))) = true := hf
    have hstab : clvl D (i + 1) ≤ MulAction.stabilizer J (b i) := by
      refine lvlGroup_le (cgs D) _ fun k hk1 hk2 => ?_
      have hk := List.all_eq_true.1 hf' _ (fl_mem_lvW hk1 hk2)
      rw [andB_eq, Bool.and_eq_true] at hk
      have hfix := fixW_spec hk.2 D.base[i]! (mem_take_succ (by omega))
      rw [MulAction.mem_stabilizer_iff, hb i (by omega)]
      apply Fin.ext
      rw [← idx_of_lt _ (hbase i (by omega)), cgs, ← (fl_eq _).2,
        ← apZ_eq ptHyp _ hk.1 _ (hbase i (by omega)), hfix]
    exact hstab hg
  · intro i hi
    have hc := okAll (o + i) (Nat.lt_of_lt_of_le (by omega : o + i < o + m) ho)
    unfold CFSG.KD.Fi24PairK.och at hc
    rw [hch i hi, hlv i hi] at hc
    have hc' : andB ((lvW D i).all (dirOK net))
        (orbW NV (lvW D i) (CFSG.KD.Fi24PairK.nthN CFSG.KD.Fi24PairK.rd (o + i)) D.base[i]!
          (D.sizes.getD i 0)) = true := hc
    rw [andB_eq, Bool.and_eq_true] at hc'
    rw [hb i hi]
    exact orbW_le ptHyp netOK_all net0 net1 (fun w hw => List.all_eq_true.1 hc'.1 w hw) (clvl D i)
      (fun w hw => wEl_fl_mem hw) (hbase i hi) hc'.2

theorem nestT : NestP chainT := nestP_of (by decide +kernel)

theorem nestA : NestP chainA := nestP_of (by decide +kernel)

theorem nestB : NestP chainB := nestP_of (by decide +kernel)

theorem nestH : NestP chainH := nestP_of (by decide +kernel)

theorem T_ge : 2 ^ 21 ≤ Nat.card (clvl chainT 0) := by
  have h := chain_ge (D := chainT) (m := 4) (o := 0) (by norm_num) (by norm_num)
    (fun i hi => by unfold chOf; rw [if_pos (by omega)])
    (fun i hi => by unfold lvOf; rw [if_pos (by omega)]; omega) (by decide) (by decide) nestT
  have e : ∏ l ∈ Finset.Ico 0 4, chainT.sizes.getD l 0 = 2 ^ 21 := by decide +kernel
  rwa [e] at h

theorem A_ge : 2 ^ 21 * 27 ≤ Nat.card (clvl chainA 0) := by
  have h := chain_ge (D := chainA) (m := 4) (o := 4) (by norm_num) (by norm_num)
    (fun i hi => by unfold chOf; rw [if_neg (by omega), if_pos (by omega)])
    (fun i hi => by unfold lvOf; rw [if_pos (by omega)]; omega) (by decide) (by decide) nestA
  have e : ∏ l ∈ Finset.Ico 0 4, chainA.sizes.getD l 0 = 2 ^ 21 * 27 := by decide +kernel
  rwa [e] at h

theorem B_ge : 2 ^ 21 * 9 ≤ Nat.card (clvl chainB 0) := by
  have h := chain_ge (D := chainB) (m := 4) (o := 8) (by norm_num) (by norm_num)
    (fun i hi => by unfold chOf; rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)])
    (fun i hi => by unfold lvOf; rw [if_pos (by omega)]; omega) (by decide) (by decide) nestB
  have e : ∏ l ∈ Finset.Ico 0 4, chainB.sizes.getD l 0 = 2 ^ 21 * 9 := by decide +kernel
  rwa [e] at h

theorem H_ge : Nat.card J ≤ Nat.card (clvl chainH 0) := by
  have h := chain_ge (D := chainH) (m := 6) (o := 12) (by norm_num) (by norm_num)
    (fun i hi => by unfold chOf; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)])
    (fun i hi => by unfold lvOf; rw [if_neg (by omega)]; omega) (by decide) (by decide) nestH
  have e : ∏ l ∈ Finset.Ico 0 6, chainH.sizes.getD l 0 = Nat.card J := by
    rw [card_J]
    decide +kernel
  rwa [e] at h

theorem clvl_le_closure {D : ChainData} {ls : List ℕ} (h0 : D.starts[0]! = 0)
    (hls : ∀ k < D.starts[1]!, D.sel[k]! ∈ ls) :
    clvl D 0 ≤ Subgroup.closure {g | ∃ l ∈ ls, g = LL (Int.ofNat (l + 3))} := by
  refine lvlGroup_le (cgs D) _ fun k _ hk2 => Subgroup.subset_closure ?_
  rw [zero_add] at hk2
  exact ⟨D.sel[k]!, hls k hk2, by rw [LL_ofNat]; rfl⟩

theorem clvl_zero_le_sup' {D E F : ChainData} (hE0 : E.starts[0]! = 0) (hF0 : F.starts[0]! = 0)
    (h : ∀ j < D.starts[1]!, (∃ k < E.starts[1]!, D.sel[j]! = E.sel[k]!) ∨
      ∃ k < F.starts[1]!, D.sel[j]! = F.sel[k]!) :
    clvl D 0 ≤ clvl E 0 ⊔ clvl F 0 := by
  refine lvlGroup_le (cgs D) _ fun j _ hj2 => ?_
  rw [zero_add] at hj2
  rcases h j hj2 with ⟨k, hk, he⟩ | ⟨k, hk, he⟩
  · have e : cgs D j = cgs E k := by unfold cgs; rw [he]
    rw [e]
    exact Subgroup.mem_sup_left
      (gs_mem_lvlGroup (cgs E) (by rw [hE0]; omega) (by rw [zero_add]; exact hk))
  · have e : cgs D j = cgs F k := by unfold cgs; rw [he]
    rw [e]
    exact Subgroup.mem_sup_right
      (gs_mem_lvlGroup (cgs F) (by rw [hF0]; omega) (by rw [zero_add]; exact hk))

theorem pairFacts : Fi24PairFacts where
  card_T := le_antisymm ((Subgroup.card_le_of_le (clvl_le_closure (by decide) (by decide))).trans
    (card_T0_le ptHyp LL_inv)) T_ge
  card_A := le_antisymm ((Subgroup.card_le_of_le (clvl_le_closure (by decide) (by decide))).trans
    (card_A0_le ptHyp LL_inv)) A_ge
  card_B := le_antisymm ((Subgroup.card_le_of_le (clvl_le_closure (by decide) (by decide))).trans
    (card_B0_le ptHyp LL_inv)) B_ge
  sup := by
    have hle : clvl chainH 0 ≤ clvl chainA 0 ⊔ clvl chainB 0 :=
      clvl_zero_le_sup' (by decide) (by decide) (by decide)
    have h2 := Subgroup.card_le_of_le hle
    have h4 := (clvl chainA 0 ⊔ clvl chainB 0).card_le_card_group
    exact (clvl chainA 0 ⊔ clvl chainB 0).eq_top_of_card_eq (by have := H_ge; omega)

end CertificateChecks.KernelFi24PairK

end
