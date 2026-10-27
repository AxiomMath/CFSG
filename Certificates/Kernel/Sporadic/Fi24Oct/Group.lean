module

public import Certificates.Kernel.Sporadic.Fi24Oct.Facts
public import Certificates.Kernel.Sporadic.Fi24ThreeO.Group
public import CFSG.Sporadic.Fi24.OctadFacts

public section

namespace CFSG.KD.Fi24Oct.Group

open CFSG.Sporadic.Fi24 (R J jR tR cls gs bbarPt permE permE_apply permF toFin24 OctadFacts)
open CFSG.Sporadic.Fi24.Native (bbarData octPerms octO0)
open CFSG.Fischer (Realizes)
open CFSG.Perm CFSG.KC CFSG.KC.Fi24ThreeO CFSG.KC.Fi24Oct CFSG.KS.Fi24ThreeO CFSG.KS.Fi24Oct
  CFSG.KD.Fi24Net CFSG.KD.Fi24Kit CFSG.KD.Fi24Oct CFSG.KD.Fi24ThreeO.Group
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three (wordElt)

attribute [local instance] CFSG.Sporadic.Fi24.rAction


theorem pts_eq : ∀ i < 24, nthO 0 pts i = bbarData[i]! := by decide +kernel

theorem perm_eq : ∀ l < 2, ∀ i < 24, nthO 0 (perm l) i = (octPerms[l]!)[i]! := by decide +kernel

theorem wc_lt : ∀ i < 24, ∀ c ∈ wc i, c < 26 := by decide +kernel

theorem nc_le : ∀ l < 2, ∀ c ∈ nc l, c ≤ 26 := by decide +kernel

theorem ow_eq : ow = octO0.map wc := by decide +kernel

theorem o0_lt : ∀ n ∈ octO0, n < 24 := by decide

@[expose] noncomputable def eltC : List ℕ → R
  | [] => 1
  | c :: cs => (if c = 26 then tR else jR (pairG gs c)) * eltC cs

theorem eltC_val (hB : Bridge) : ∀ (cs : List ℕ), (∀ c ∈ cs, c ≤ 26) → ∀ x : Fin 306936,
    (eltC cs • x).val = cP NW NT cs x.val
  | [], _, x => by
    change ((1 : R) • x).val = _
    rw [one_smul]
    rfl
  | c :: cs, hc, x => by
    change (((if c = 26 then tR else jR (pairG gs c)) * eltC cs) • x).val = _
    rw [mul_smul, cP_cons]
    have ih := eltC_val hB cs (fun d hd => hc d (List.mem_cons_of_mem c hd)) x
    have hc' := hc c List.mem_cons_self
    unfold CF
    by_cases h : c = 26
    · rw [if_pos h, if_pos h, tR_val hB, ih]
    · rw [if_neg h, if_neg h, CFSG.Sporadic.Fi24.jR_smul, hB.letter c (by omega), ih]

theorem wc_root (hB : Bridge) (i : Fin 24) :
    wordElt (wc i.val) • CFSG.Sporadic.Fi24.root = bbarPt i := by
  apply Fin.ext
  rw [root_val _ hB (wc_lt i.val i.isLt), oct_facts.1 i.val i.isLt, pts_eq i.val i.isLt]
  rfl

theorem cls_bbar_val (hB : Bridge) (i : Fin 24) (k : Fin 306936) :
    (cls (bbarPt i) • k).val = cP NW NT (dW (wc i.val)) k.val := by
  rw [← wc_root hB i]
  exact cls_word hB (wc_lt i.val i.isLt) k

theorem bbar_comm (hB : Bridge) (i j : Fin 24) :
    cls (bbarPt i) * cls (bbarPt j) = cls (bbarPt j) * cls (bbarPt i) := by
  rw [comm_iff]
  apply Fin.ext
  have hj : (bbarPt j).val = nthO 0 pts j.val := (pts_eq j.val j.isLt).symm
  rw [cls_bbar_val hB, hj, oct_facts.2.1 i.val i.isLt j.val j.isLt]

@[expose] def sepP : Fin 306936 := ⟨59207, by norm_num⟩

theorem pair_val (hB : Bridge) (a b : Fin 24) :
    ((cls (bbarPt a) * cls (bbarPt b)) • sepP).val =
      cP NW NT (dW (wc a.val)) (cP NW NT (dW (wc b.val)) sep) := by
  rw [mul_smul, cls_bbar_val hB, cls_bbar_val hB]
  rfl

theorem pair_sorted (hB : Bridge) {a b : Fin 24} (h : a ≠ b) : ∃ i j : Fin 24, i.val < j.val ∧
    ((i = a ∧ j = b) ∨ (i = b ∧ j = a)) ∧
    cls (bbarPt a) * cls (bbarPt b) = cls (bbarPt i) * cls (bbarPt j) := by
  rcases lt_or_gt_of_ne h with h | h
  · exact ⟨a, b, h, Or.inl ⟨rfl, rfl⟩, rfl⟩
  · exact ⟨b, a, h, Or.inr ⟨rfl, rfl⟩, bbar_comm hB a b⟩

theorem bbar_pair (hB : Bridge) (a b c d : Fin 24) (hab : a ≠ b) (hcd : c ≠ d) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    cls (bbarPt a) * cls (bbarPt b) ≠ cls (bbarPt c) * cls (bbarPt d) := by
  obtain ⟨i, j, hij, hs1, e1⟩ := pair_sorted hB hab
  obtain ⟨k, l, hkl, hs2, e2⟩ := pair_sorted hB hcd
  rw [e1, e2]
  intro h
  have hv := congrArg (fun g : R => (g • sepP).val) h
  simp only [pair_val hB] at hv
  have hab' := Fin.val_ne_of_ne hab
  have hac' := Fin.val_ne_of_ne hac
  have had' := Fin.val_ne_of_ne had
  have hbc' := Fin.val_ne_of_ne hbc
  have hbd' := Fin.val_ne_of_ne hbd
  refine oct_facts.2.2.1 i.val j.val k.val l.val hij hkl j.isLt l.isLt ?_ ?_ ?_ ?_ hv <;>
    rcases hs1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hs2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega

theorem prod_val (hB : Bridge) : ∀ (l : List ℕ), (∀ n ∈ l, n < 24) → ∀ p : Fin 306936,
    ((l.map fun n => cls (bbarPt (toFin24 n))).prod • p).val = cP NW NT (prodC (l.map wc)) p.val
  | [], _, p => by
    rw [List.map_nil, List.prod_nil, one_smul]
    rfl
  | n :: l, hl, p => by
    rw [List.map_cons, List.prod_cons, mul_smul, List.map_cons, cP_prodC, cls_bbar_val hB,
      prod_val hB l (fun m hm => hl m (List.mem_cons_of_mem n hm)) p]
    have hn : (toFin24 n).val = n := Nat.mod_eq_of_lt (hl n List.mem_cons_self)
    rw [hn]

theorem prod_fix (hB : Bridge) (p : Fin 306936) :
    (octO0.map fun n => cls (bbarPt (toFin24 n))).prod • p = p := by
  apply Fin.ext
  rw [prod_val hB octO0 o0_lt p, ← ow_eq]
  exact oct_facts.2.2.2.2 p.val p.isLt

theorem norm_smul (hB : Bridge) (l : Fin 2) (i : Fin 24) :
    eltC (nc l.val) • bbarPt i = bbarPt (permE l i) := by
  apply Fin.ext
  have hp := perm_eq l.val l.isLt i.val i.isLt
  have hlt := perm_lt l.val l.isLt i.val i.isLt
  rw [eltC_val hB _ (nc_le l.val l.isLt)]
  change cP NW NT (nc l.val) bbarData[i.val]! = bbarData[(octPerms[l.val]!)[i.val]! % 24]!
  rw [← pts_eq i.val i.isLt, oct_facts.2.2.2.1 l.val l.isLt i.val i.isLt, hp,
    Nat.mod_eq_of_lt (hp ▸ hlt), ← pts_eq _ (hp ▸ hlt)]

theorem realizes (hB : Bridge) (l : Fin 2) :
    Realizes (fun i => cls (bbarPt i)) (eltC (nc l.val)) (permE l) := fun i => by
  change cls (bbarPt (permE l i)) = _
  rw [← norm_smul hB l i, CFSG.Sporadic.Fi24.cls_smul_R]

theorem octadFacts_of (hB : Bridge) : OctadFacts :=
  ⟨bbar_comm hB, bbar_pair hB, prod_fix hB, fun l => ⟨_, realizes hB l⟩⟩

end CFSG.KD.Fi24Oct.Group

end
