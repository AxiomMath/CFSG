
module

public import Certificates.Kernel.Sporadic.L2.G3

public section

namespace CertificateChecks.KernelSpor.L2G

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.FpBfs
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.SuzRecog.LevelTwo
open CFSG.Sporadic.SuzRecog.LevelTwoData CFSG.Sporadic.SuzRecog.ElimCert CFSG.Sporadic.SuzRecog
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.L2K

local notation "pgv" => pg 12 (mask 12)

attribute [local irreducible] hexTable LevelTwoPins.nbrHex LevelTwoPins.stepVHex
  LevelTwoPins.stepIHex LevelTwoPins.emapHex LevelTwoPins.spanHex

theorem bIf_or (a b : Bool) : bIf(a, true, b) = (a || b) := by cases a <;> rfl

theorem bAnd_and (a b : Bool) : bAnd(a, b) = (a && b) := by cases a <;> rfl

theorem bne_eq (a b : Nat) : (a != b) = Bool.not (Nat.beq a b) := by
  rw [bne, Q3AG.beqN]

theorem nbr_low {x : Nat} (hx : x < 2835) :
    nbr[x]! = Array.ofFn (n := 36) fun k => (hexTable 3 102060 0 LevelTwoPins.nbrHex)[36 * x + k.val]! := by
  unfold nbr nbrA
  rw [getElem!_pos _ x (by rw [Array.size_ofFn]; omega), Array.getElem_ofFn]
  simp only [hx, ↓reduceIte]
  rw [getElem!_pos _ x (by rw [Array.size_ofFn]; omega), Array.getElem_ofFn]

theorem nbr_high {x : Nat} (hx : 2835 ≤ x) : nbr[x]! = #[] := by
  unfold nbr
  by_cases h : x < 2997
  · rw [getElem!_pos _ x (by rw [Array.size_ofFn]; omega), Array.getElem_ofFn]
    simp only [show ¬ x < 2835 by omega, ↓reduceIte]
  · rw [getElem!_neg _ x (by rw [Array.size_ofFn]; omega)]
    rfl

theorem nbr_size {x : Nat} (hx : x < 2835) : (nbr[x]!).size = 36 := by
  rw [nbr_low hx, Array.size_ofFn]

theorem nbr_get {x k : Nat} (hx : x < 2835) (hk : k < 36) : (nbr[x]!)[k]! = nbK x k := by
  rw [nbr_low hx, getElem!_pos _ k (by rw [Array.size_ofFn]; omega), Array.getElem_ofFn, hexTable_at (by omega),
    Nat.zero_add]
  exact hexE L2NB.eq L2NB.all hx hk

theorem occB_eq (x y : Nat) : occB nbr[x]! y = occK x y := by
  unfold occB occK
  by_cases hx : x < 2835
  · rw [show Nat.blt x 2835 = true from nblt.2 hx, nbr_size hx]
    change _ = Bool.not (allN 36 fun k => Bool.not (Nat.beq (nbK x k) y))
    apply Bool.eq_iff_iff.2
    rw [List.any_eq_true, Bool.not_eq_true', Bool.eq_false_iff]
    constructor
    · rintro ⟨k, hk, he⟩ ha
      have hk' := List.mem_range.1 hk
      have := allN_get ha hk'
      rw [nbr_get hx hk', Q3AG.beqN] at he
      rw [he] at this
      exact Bool.false_ne_true this
    · intro hn
      by_contra hno
      apply hn
      refine CFSG.KS.Raw.allN_of_forall fun k hk => ?_
      cases hb : Nat.beq (nbK x k) y
      · rfl
      · exact absurd ⟨k, List.mem_range.2 hk, by rw [nbr_get hx hk, Q3AG.beqN, hb]⟩ hno
  · rw [nblt_f (b := 2835) hx, nbr_high (by omega)]
    rfl

theorem adjB_eq (x y : Nat) : adjB nbr x y = adjK x y := by
  unfold adjB adjK
  rw [occB_eq, occB_eq, bne_eq, bIf_or, bAnd_and]

theorem vtab_get (H : VtxOK) {s y : Nat} (hs : s < 2) (hy : y < 2997) : (vtab s)[y]! = VK s y := by
  by_cases h : y < 2835
  · exact vtab_getA (hvA H) H.sA hs h (hvtA H hs h)
  · obtain ⟨j, rfl⟩ : ∃ j, y = 2835 + j := ⟨y - 2835, by omega⟩
    exact vtab_getW (hvW H) H.sT hs (by omega) (hvtW H hs (by omega))

theorem graphOK_true (H : VtxOK) (hg : ∀ x < 2997, grChk x = true) : graphOK = true := by
  unfold graphOK
  simp only [Bool.and_eq_true, beq_iff_eq, allLt_iff]
  refine ⟨by unfold nbr; rw [Array.size_ofFn], fun s hs x hx => ?_⟩
  by_cases hxl : x < 2835
  · rw [Array.all_eq_true]
    intro k hk
    rw [nbr_size hxl] at hk
    have h := hg x hx
    unfold grChk at h
    rw [band] at h
    have h' : grK s x = true := by
      interval_cases s
      · exact h.1
      · exact h.2
    unfold grK at h'
    rw [show Nat.blt x 2835 = true from nblt.2 hxl] at h'
    have hk' := allN_get h' hk
    rw [band, nblt] at hk'
    have e : (nbr[x]!)[k]'(by rw [nbr_size hxl]; exact hk) = nbK x k := by
      rw [← getElem!_pos (nbr[x]!) k (by rw [nbr_size hxl]; exact hk)]
      exact nbr_get hxl hk
    rw [e, adjB_eq, vtab_get H hs hx, vtab_get H hs hk'.1]
    exact hk'.2
  · rw [nbr_high (by omega)]
    simp

theorem treePar_get {z : Nat} (hz : z < 2997) : treePar[z]! = tParK z := by
  unfold treePar
  rw [hexTable_at hz, show 0 + z = 2997 * 0 + z by omega]
  exact hexE L2SP.eq L2SP.all (by norm_num) hz

theorem treeDep_get {z : Nat} (hz : z < 2997) : treeDep[z]! = tDepK z := by
  unfold treeDep
  rw [hexTable_at hz, show 2997 + z = 2997 * 1 + z by omega]
  exact hexE L2SP.eq L2SP.all (by norm_num) hz

theorem sv_get {e : Nat} (he : e < 220647) :
    (hexTable 3 220647 0 LevelTwoPins.stepVHex)[e]! = sv e := by
  rw [hexTable_at he, Nat.zero_add]
  conv_lhs => rw [← Nat.div_add_mod e 147]
  exact hexE L2SV.eq L2SV.all (by have : e / 147 < 1501 := by omega
                                  exact this) (Nat.mod_lt _ (by norm_num))

theorem si_get {e : Nat} (he : e < 147098) :
    (hexTable 5 147098 0 LevelTwoPins.stepIHex)[e]! = si e := by
  rw [hexTable_at he, Nat.zero_add]
  conv_lhs => rw [← Nat.div_add_mod e 98]
  exact hexE L2SI.eq L2SI.all (by have : e / 98 < 1501 := by omega
                                  exact this) (Nat.mod_lt _ (by norm_num))

theorem steps_size : elimSteps.size = 76545 := by unfold elimSteps; rw [Array.size_ofFn]

theorem steps_tree {i : Nat} (hi : i < 2996) : elimSteps[i]! = #[S0 i, S1 i] := by
  unfold elimSteps
  rw [getElem!_pos _ i (by rw [Array.size_ofFn]; omega), Array.getElem_ofFn]
  simp only [hi, ↓reduceIte]
  rw [treePar_get (by omega)]
  unfold S0 S1
  rw [show Nat.blt i 2996 = true from nblt.2 hi]

theorem steps_tri {i : Nat} (hi : 2996 ≤ i) (hi' : i < 76545) :
    elimSteps[i]! = #[S0 i, S1 i, S2 i, S3 i, S4 i] := by
  unfold elimSteps
  rw [getElem!_pos _ i (by rw [Array.size_ofFn]; omega), Array.getElem_ofFn]
  simp only [show ¬ i < 2996 by omega, ↓reduceIte]
  unfold S0 S1 S2 S3 S4
  rw [nblt_f (b := 2996) (show ¬ i < 2996 by omega)]
  rw [sv_get (by omega), sv_get (by omega), sv_get (by omega), si_get (by omega),
    si_get (by omega)]
  rfl

theorem ends_eq {j x y : Nat} (hj : j < 76545) : endsB elimSteps[j]! x y = endsK j x y := by
  unfold endsB endsK
  by_cases h : j < 2996
  · rw [steps_tree h]
    simp only [Q3AG.beqN, bIf_or, bAnd_and, List.getElem!_toArray, List.getElem!_cons_zero,
      List.getElem!_cons_succ]
  · rw [steps_tri (by omega) hj]
    simp only [Q3AG.beqN, bIf_or, bAnd_and, List.getElem!_toArray, List.getElem!_cons_zero,
      List.getElem!_cons_succ]

theorem ty2_eq (x : Nat) : (if 2835 ≤ x then 1 else 0) = ty2 x := by
  unfold ty2
  by_cases h : 2835 ≤ x
  · rw [if_pos h, show Nat.ble 2835 x = true from nble.2 h]
  · rw [if_neg h, nble_f (a := 2835) h]

theorem triB_eq (x y z : Nat) : triB x y z = triK x y z := by
  unfold triB triK
  rw [adjB_eq, adjB_eq, adjB_eq, ty2_eq, ty2_eq, ty2_eq, Q3AG.beqN, bAnd_and, bAnd_and, bAnd_and]
  simp only [Bool.and_assoc]
  rfl

theorem stepOK_of {i : Nat} (hi : i < 76545) (h : stepK i = true) :
    stepOK 2997 nbr treePar triB elimSteps i = true := by
  unfold stepK at h
  rw [sB, sB, band, band, band, nblt, nblt] at h
  obtain ⟨ha, hb, hab, hr⟩ := h
  have A : adjB nbr (S0 i) (S1 i) = true := (adjB_eq _ _).trans hab
  rw [bif_true] at hr
  unfold stepOK
  by_cases ht : i < 2996
  · have hr := hr.1 (nblt.2 ht)
    rw [steps_tree ht]
    have T : (0 < S1 i ∧ treePar[S1 i]! = S0 i) ∨ (0 < S0 i ∧ treePar[S0 i]! = S1 i) := by
      rcases hcb : bAnd(Nat.blt 0 (S1 i), Nat.beq (tParK (S1 i)) (S0 i)) with _ | _
      · rw [hcb] at hr
        have hr' : bAnd(Nat.blt 0 (S0 i), Nat.beq (tParK (S0 i)) (S1 i)) = true := hr
        rw [band, nblt, nbeq] at hr'
        exact Or.inr ⟨hr'.1, (treePar_get ha).trans hr'.2⟩
      · rw [band, nblt, nbeq] at hcb
        exact Or.inl ⟨hcb.1, (treePar_get hb).trans hcb.2⟩
    simp only [List.getElem!_toArray, List.getElem!_cons_zero, List.getElem!_cons_succ,
      Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq, List.size_toArray,
      List.length_cons, List.length_nil, ha, hb, A, T, true_and, and_true, true_or]
  · have hr := hr.2 (nblt_f ht)
    rw [sB, sB, sB, band, band, band, band, band, nblt, nblt, nblt] at hr
    obtain ⟨hc, h1, h2, e1, e2, htri⟩ := hr
    have E1 : endsB elimSteps[S3 i]! (S0 i) (S2 i) = true := (ends_eq (by omega)).trans e1
    have E2 : endsB elimSteps[S4 i]! (S2 i) (S1 i) = true := (ends_eq (by omega)).trans e2
    have T : triB (S0 i) (S2 i) (S1 i) = true := (triB_eq _ _ _).trans htri
    rw [steps_tri (by omega) hi]
    simp only [List.getElem!_toArray, List.getElem!_cons_zero, List.getElem!_cons_succ,
      Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq, List.size_toArray,
      List.length_cons, List.length_nil, ha, hb, A, hc, h1, h2, E1, E2, T, true_and, and_true,
      or_true]

theorem emap_get {x k : Nat} (hx : x < 2835) (hk : k < 36) :
    (elimEmap[x]!)[k]! = pg 20 (mask 20) (L2EM.F x) k := by
  unfold elimEmap
  rw [getElem!_pos _ x (by rw [Array.size_ofFn]; omega), Array.getElem_ofFn]
  simp only [hx, ↓reduceIte]
  rw [getElem!_pos _ k (by rw [Array.size_ofFn]; omega), Array.getElem_ofFn, hexTable_at (by omega), Nat.zero_add]
  exact hexE L2EM.eq L2EM.all hx hk

theorem elimOK_true (hs : ∀ i < 76545, stepK i = true) (ht : ∀ x < 2997, teG x = true) :
    elimOK = true := by
  unfold elimOK ok
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq,
    decide_eq_true_eq]
  refine ⟨⟨⟨by norm_num, fun x hx => ?_⟩, fun i hi => ?_⟩, fun x hx k hk => ?_⟩
  · have h := ht x hx
    unfold teG at h
    rw [show Nat.blt x 2997 = true from nblt.2 hx, band] at h
    have h1 := h.1
    unfold treeK at h1
    by_cases h0 : x = 0
    · exact Or.inl h0
    · rw [show Nat.beq x 0 = false from Q3AG.nbeq_false h0, sB] at h1
      simp only [band, nblt] at h1
      obtain ⟨hp, hd, ha⟩ := h1
      refine Or.inr ⟨⟨by rw [treePar_get hx]; exact hp, ?_⟩, ?_⟩
      · rw [treePar_get hx, treeDep_get hp, treeDep_get hx]; exact hd
      · rw [treePar_get hx, adjB_eq]; exact ha
  · rw [steps_size] at hi
    exact stepOK_of hi (hs i hi)
  · by_cases hxl : x < 2835
    · rw [nbr_size hxl] at hk
      have h := ht x hx
      unfold teG at h
      rw [show Nat.blt x 2997 = true from nblt.2 hx, band,
        show Nat.blt x 2835 = true from nblt.2 hxl] at h
      have he2 : emK x = true := h.2
      unfold emK at he2
      have he := allN_get he2 hk
      rw [sB] at he
      rw [nbr_get hxl hk]
      by_cases hxy : x = nbK x k
      · exact Or.inl hxy
      · rw [show Nat.beq x (nbK x k) = false from Q3AG.nbeq_false hxy] at he
        by_cases hge : 2997 ≤ nbK x k
        · exact Or.inr (Or.inl hge)
        · rw [nble_f (a := 2997) hge, sB, band,
            nblt] at he
          refine Or.inr (Or.inr ⟨?_, ?_⟩)
          · rw [emap_get hxl hk, steps_size]; exact he.1
          · rw [emap_get hxl hk, ends_eq he.1]; exact he.2
    · rw [nbr_high (by omega)] at hk
      simp at hk

end CertificateChecks.KernelSpor.L2G

end
