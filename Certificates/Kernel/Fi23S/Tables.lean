module

public import Certificates.Kernel.Fi23S.Chain
public import Certificates.Kernel.Fi23R.Fact2075
import Certificates.Kernel.Fi23S.L13a
import Certificates.Kernel.Fi23S.L13b
import Certificates.Kernel.Sporadic.ON.Gen
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import Mathlib
public import CFSG.Sporadic.Fi23.Simple

public section

set_option maxRecDepth 400000

#kon_join CFSG.KD.Fi23S.l13All CFSG.KD.Fi23S.l13F 8

namespace CertificateChecks.KernelFi23S

open CFSG.KC.Enum CFSG.KC.Fi23K CFSG.KC.Fi23R CFSG.KC.Fi23S CFSG.KD.Fi23K CFSG.KD.Fi23S
  CFSG.KS.Raw.Orb CFSG.KS.TBfs CFSG.KS.PC CFSG.KS.PEnum CFSG.Sporadic.Fi23.Native
  CFSG.Sporadic.Th.Native CFSG.Perm.Native

theorem wF_succ (L : Nat → Nat → Nat) (PAR LAB : Nat → Nat) (f k x : Nat) :
    wF L PAR LAB (f + 1) k x = if (0 < k ∧ r32 PAR k < k) then
      L (r32 LAB k) (wF L PAR LAB f (r32 PAR k) x) else x := by
  change Bool.rec (motive := fun _ => Nat) x (L (r32 LAB k) (wF L PAR LAB f (r32 PAR k) x))
    (Bool.rec (motive := fun _ => Bool) false (Nat.blt (r32 PAR k) k) (Nat.blt 0 k)) = _
  rw [bAnd_eq]
  by_cases hc : 0 < k ∧ r32 PAR k < k
  · have e : (Nat.blt 0 k && Nat.blt (r32 PAR k) k) = true := by simp [Nat.blt_eq, hc]
    rw [if_pos hc, e]
  · have e : (Nat.blt 0 k && Nat.blt (r32 PAR k) k) = false :=
      Bool.eq_false_iff.2 fun h => hc (by simpa [Nat.blt_eq] using h)
    rw [if_neg hc, e]

theorem walkF_one (L : Nat → Nat → Nat) (PAR LAB : Nat → Nat) :
    ∀ f k x, walkF L PAR LAB f k [x] = [wF L PAR LAB f k x]
  | 0, _, _ => rfl
  | f + 1, k, x => by
    rw [walkF_succ, wF_succ]
    split_ifs
    · rw [walkF_one L PAR LAB f, mapK_eq]
      rfl
    · rfl

noncomputable abbrev tv (i k : Nat) : Equiv.Perm (Fin 31671) :=
  twL 31671 SL (fun i => TTS i 2) (fun i => TTS i 3) i k

theorem wS_eq {i k x : Nat} (hi : i < 2) (hk : k < 512) (hx : x < 31671) :
    wS i k x = actN (tv i k) x := by
  have h : walkF LS (TTS i 2) (TTS i 3) k k [x] = [x].map (actN (tv i k)) :=
    walkF_eq syl_hyp hi k k hk le_rfl [x] (by simpa using hx)
  rw [walkF_one] at h
  unfold wS
  simpa using h

theorem gK_eq {k j x : Nat} (hk : k < 512) (hj : j < 512) (hx : x < 31671) :
    gK k j x = actN (tv 0 k * tv 1 j) x := by
  unfold gK
  rw [wS_eq (by decide) hj hx, wS_eq (by decide) hk (actN_lt _ hx), actN_mul]

theorem tv_mem {i k : Nat} (hi : i < 2) (hk : k < 512) :
    tv i k ∈ Xc := by
  rw [← grp_eq]
  exact tw_T23 hi k hk

theorem tt_get {i : Nat} (hi : i < 2) : (chainTrees 31671 SL sylBase)[i]! =
    trK 31671 CNTS (fun i => TTS i 0) (fun i => TTS i 1) (fun i => TTS i 2) (fun i => TTS i 3) i := by
  rw [syl_chain.1]
  exact trees_get (n := 31671) (m := 2) (CNT := CNTS) (PTS := fun i => TTS i 0)
    (POS := fun i => TTS i 1) (PAR := fun i => TTS i 2) (LAB := fun i => TTS i 3) hi

theorem treeTabs_size {i : Nat} (hi : i < 2) :
    (treeTabs 31671 (chainTrees 31671 SL sylBase)[i]! SL).size = 512 := by
  rw [tt_get hi]
  unfold treeTabs
  rw [Array.size_ofFn, pts_size]
  rfl

theorem treeTabs_ap {i k y : Nat} (hi : i < 2) (hk : k < 512) (hy : y < 31671) :
    ap (treeTabs 31671 (chainTrees 31671 SL sylBase)[i]! SL)[k]! y = actN (tv i k) y := by
  rw [tt_get hi]
  have hs : (treeTabs 31671 (trK 31671 CNTS (fun i => TTS i 0) (fun i => TTS i 1)
      (fun i => TTS i 2) (fun i => TTS i 3) i) SL).size = 512 := by
    unfold treeTabs
    rw [Array.size_ofFn, pts_size]
    rfl
  rw [getElem!_pos _ k (by rw [hs]; exact hk)]
  unfold treeTabs
  simp only [Array.getElem_ofFn]
  have hw := walk_eq syl_hyp hi k hk (Array.range 31671) (fun x hx => by simpa using hx)
  rw [hw]
  unfold ap
  rw [getElem!_pos _ y (by simp [hy]), Array.getElem_map, Array.getElem_map, Array.getElem_range,
    UInt32.toNat_ofNat']
  exact Nat.mod_eq_of_lt (lt_trans (actN_lt _ hy) (by norm_num))

theorem ap_comp {P Q : Table} {y : Nat} (hy : y < 31671) :
    ap (compT 31671 P Q) y = ap P (ap Q y) := by
  unfold compT
  conv_lhs => unfold ap
  rw [getElem!_pos _ y (by simp [hy]), Array.getElem_ofFn]
  rfl

noncomputable abbrev t0 : Array Table := treeTabs 31671 (chainTrees 31671 SL sylBase)[0]! SL
noncomputable abbrev t1 : Array Table := treeTabs 31671 (chainTrees 31671 SL sylBase)[1]! SL

theorem leaf_ap {k j y : Nat} (hk : k < 512) (hj : j < 512) (hy : y < 31671) :
    ap (compT 31671 t0[k]! t1[j]!) y = gK k j y := by
  rw [ap_comp hy, treeTabs_ap (by decide) hj hy, treeTabs_ap (by decide) hk (actN_lt _ hy),
    gK_eq hk hj hy, actN_mul]

theorem lf13_all {k j : Nat} (hk : k < 512) (hj : j < 512) : lf13 k j = true := by
  have hs : k / 64 < 8 := by omega
  have h : l13Sl (k / 64 * 64) 64 = true := l13All (k / 64) hs
  unfold l13Sl at h
  have h' := allN_iff.1 h (k - k / 64 * 64) (by omega)
  rw [strictB_eq] at h'
  have e : Nat.add (k / 64 * 64) (k - k / 64 * 64) = k := by
    change k / 64 * 64 + (k - k / 64 * 64) = k
    omega
  rw [e] at h'
  exact allN_iff.1 h' j hj

theorem movB_spec {f : Nat → Nat} (h : movB f = true) : ∃ b < 6, f b ≠ b := by
  unfold movB at h
  rw [Bool.not_eq_true'] at h
  by_contra hc
  push_neg at hc
  have : allN 6 (fun b => Nat.beq (f b) b) = true :=
    allN_iff.2 fun b hb => by rw [Nat.beq_eq]; exact hc b hb
  rw [this] at h
  exact Bool.noConfusion h

theorem fixB_spec {f : Nat → Nat} (h : fixB f = true) : ∀ b < 6, f b = b := fun b hb =>
  Nat.eq_of_beq_eq_true (allN_iff.1 h b hb)

theorem lf13_cases {k j : Nat} (h : lf13 k j = true) :
    (code k j = 0 ∧ ∃ b < 6, gK k j (gK k j b) ≠ b) ∨
    (code k j = 1 ∧ ∀ b < 6, gK k j b = b) ∨
    (2 ≤ code k j ∧ ∃ t < 2, ∀ b < 6, gK k j (cw t (gK k j (cw t (gK k j (cw t b))))) = b) ∨
    (2 ≤ code k j ∧ ∃ u < 2, (∃ b < 6, rw13 k j u b ≠ b) ∧
      (∃ b < 6, rw13 k j u (rw13 k j u b) ≠ b) ∧
      (∃ b < 6, rw13 k j u (rw13 k j u (rw13 k j u b)) ≠ b)) := by
  unfold lf13 lf13c at h
  rw [strictB_eq, bIf_eq] at h
  split_ifs at h with h0
  · exact Or.inl ⟨Nat.eq_of_beq_eq_true h0, movB_spec h⟩
  rw [bIf_eq] at h
  split_ifs at h with h1
  · exact Or.inr (Or.inl ⟨Nat.eq_of_beq_eq_true h1, fixB_spec h⟩)
  have hc0 : code k j ≠ 0 := fun e => h0 (by rw [e]; rfl)
  have hc1 : code k j ≠ 1 := fun e => h1 (by rw [e]; rfl)
  have h2 : 2 ≤ code k j := by omega
  rw [strictB_eq, bIf_eq] at h
  split_ifs at h with h3
  · refine Or.inr (Or.inr (Or.inl ⟨h2, _, Nat.blt_eq.mp h3, fun b hb => ?_⟩))
    have := fixB_spec h b hb
    simp only [strictN_eq] at this
    exact this
  · rw [strictB_eq, bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true] at h
    have ht : Nat.land (code k j - 2) 3 < 4 := lt_of_le_of_lt Nat.and_le_right (by norm_num)
    have h3' : ¬ Nat.land (code k j - 2) 3 < 2 := fun e => h3 (Nat.blt_eq.mpr e)
    have hu : Nat.land (code k j - 2) 3 - 2 < 2 := by omega
    exact Or.inr (Or.inr (Or.inr ⟨h2, _, hu, movB_spec h.1, movB_spec h.2.1,
      movB_spec h.2.2⟩))

end CertificateChecks.KernelFi23S

end
