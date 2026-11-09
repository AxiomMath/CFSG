module

public import CFSG.Certificates.Kernel.Spor.FiveKSound
public import Certificates.Kernel.Sporadic.OddCore.CentGlue
public import Certificates.Data.Kernel.Spor.FiveKE
import CFSG.Certificates.Kernel.BfsPinAlg
import CFSG.Certificates.Kernel.Spor.RawOrbHead

public section

namespace CFSG.KS.MulH

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim
open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native

theorem pcomp_assocR {n w p q r : Nat} (hp : canonK n w (mask w) (n * w) p = true)
    (hr : canonK n w (mask w) (n * w) r = true) :
    pcomp n w (mask w) (pcomp n w (mask w) p q) r =
      pcomp n w (mask w) p (pcomp n w (mask w) q r) := by
  obtain ⟨hn, hw, -, -⟩ := PF.canon_facts hp
  obtain ⟨-, -, -, hrr⟩ := PF.canon_facts hr
  have hn32 : n < 2 ^ 32 := by omega
  have hw0 := PF.w_pos hw
  refine PF.eq_of_fields hw0 (PF.pcomp_shr _ _ hn32 hw0) (PF.pcomp_shr _ _ hn32 hw0) fun i hi => ?_
  rw [PF.pg_pcomp hn32 hi, PF.pg_pcomp hn32 (hrr i hi), PF.pg_pcomp hn32 hi,
    PF.pg_pcomp hn32 hi]

theorem pcomp_idR' {n w p : Nat} (hp : canonK n w (mask w) (n * w) p = true) :
    pcomp n w (mask w) p (pidn n w) = p := by
  obtain ⟨hn, hw, hp0, -⟩ := PF.canon_facts hp
  have hn32 : n < 2 ^ 32 := by omega
  refine PF.eq_of_fields (PF.w_pos hw) (PF.pcomp_shr _ _ hn32 (PF.w_pos hw)) hp0 fun i hi => ?_
  rw [PF.pg_pcomp hn32 hi, PF.pg_pidn hn hw hi]

theorem canonK_of_invEqK {n w p q : Nat} (hs : szOK n w = true)
    (h : invEqK n w (mask w) (n * w) p q = true) :
    canonK n w (mask w) (n * w) p = true ∧ canonK n w (mask w) (n * w) q = true := by
  obtain ⟨h1, h2, h3⟩ := CFSG.KS.Raw.Orb.permOK_facts h
  have hinj : ∀ a < n, ∀ b < n, pg w (mask w) p a = pg w (mask w) p b → a = b :=
    fun a ha b hb e => by rw [← (h3 a ha).2, ← (h3 b hb).2, e]
  have himg : (Finset.range n).image (pg w (mask w) p) = Finset.range n := by
    classical
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hx
      exact Finset.mem_range.2 (h3 i (Finset.mem_range.1 hi)).1
    · rw [Finset.card_image_of_injOn fun a ha b hb e =>
        hinj a (Finset.mem_range.1 ha) b (Finset.mem_range.1 hb) e]
  refine ⟨?_, ?_⟩
  · unfold canonK
    rw [bAnd_iff, bAnd_iff, CFSG.KS.Raw.Orb.allN_iff]
    exact ⟨hs, by rw [h1]; rfl, fun i hi => Nat.blt_eq.mpr (h3 i hi).1⟩
  · have hq : ∀ v < n, pg w (mask w) q v < n := by
      intro v hv
      have hm : v ∈ (Finset.range n).image (pg w (mask w) p) := by
        rw [himg]
        exact Finset.mem_range.2 hv
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hm
      rw [(h3 i (Finset.mem_range.1 hi)).2]
      exact Finset.mem_range.1 hi
    unfold canonK
    rw [bAnd_iff, bAnd_iff, CFSG.KS.Raw.Orb.allN_iff]
    exact ⟨hs, by rw [h2]; rfl, fun v hv => Nat.blt_eq.mpr (hq v hv)⟩

theorem divParts_four : CFSG.Sporadic.Schreier.Native.divParts 4 = [2, 1] := by decide

theorem ordTest4_unpack {n w X : Nat} (hn : szOK n w = true)
    (hidc : canonK n w (mask w) (n * w) (pidn n w) = true)
    (hX : canonK n w (mask w) (n * w) X = true)
    (h : ordTest n 4 (tabT (unpack n w X)) = true) :
    (Nat.beq (pcomp n w (mask w) (pcomp n w (mask w) X X) (pcomp n w (mask w) X X)) (pidn n w) &&
      !Nat.beq (pcomp n w (mask w) X X) (pidn n w) && !Nat.beq X (pidn n w)) = true := by
  have hP : CFSG.KS.MulH.Pows n w X
      (fun e => Nat.rec (motive := fun _ => Nat) (pidn n w) (fun _ acc => pcomp n w (mask w) X acc) e) :=
    ⟨rfl, fun _ => rfl⟩
  rw [ordTest_unpack hP (CFSG.KC.BfsPin.idA_eq hn) hidc hX 4, divParts_four] at h
  simp only [List.all_cons, List.all_nil, Bool.and_true] at h
  have e1 : pcomp n w (mask w) X (pidn n w) = X := pcomp_idR' hX
  have hXX := CFSG.KC.BfsPin.canonK_pcomp hX hX
  have e4 : pcomp n w (mask w) X (pcomp n w (mask w) X (pcomp n w (mask w) X X)) =
      pcomp n w (mask w) (pcomp n w (mask w) X X) (pcomp n w (mask w) X X) :=
    (pcomp_assocR hX hXX).symm
  change (Nat.beq (pcomp n w (mask w) X (pcomp n w (mask w) X (pcomp n w (mask w) X
      (pcomp n w (mask w) X (pidn n w))))) (pidn n w) &&
    (!Nat.beq (pcomp n w (mask w) X (pcomp n w (mask w) X (pidn n w))) (pidn n w) &&
      !Nat.beq (pcomp n w (mask w) X (pidn n w)) (pidn n w))) = true at h
  rw [e1, e4] at h
  rw [Bool.and_assoc]
  exact h

theorem row_imp {a b c t : Bool}
    (h : Bool.rec (motive := fun _ => Bool) true t
      (bAnd(a, bAnd(bIf(b, false, true), bIf(c, false, true)))) = true) :
    (a && !b && !c) = true → t = true := by
  cases a <;> cases b <;> cases c <;> intro hc
  all_goals first | exact h | exact absurd hc (by decide)

theorem sylRows_all {n w k cnt cap f : Nat} {T G GI : Nat → Nat} {cg : Array Table}
    (hcap : 5 ≤ cap) (hn : szOK n w = true) (hn32 : n < 4294967296)
    (hidc : canonK n w (mask w) (n * w) (pidn n w) = true) (hg : TabsOK n w k G cg)
    (hgi : ∀ l < k, invEqK n w (mask w) (n * w) (G l) (GI l) = true)
    (hT : ∀ i < cnt, canonK n w (mask w) (n * w) (T i) = true)
    (hrow : ∀ i < cnt, (Nat.beq (pcomp n w (mask w) (pcomp n w (mask w) (T i) (T i))
        (pcomp n w (mask w) (T i) (T i))) (pidn n w) &&
      !Nat.beq (pcomp n w (mask w) (T i) (T i)) (pidn n w) && !Nat.beq (T i) (pidn n w)) = true →
        fiveTopK n w (mask w) G GI k f (T i) = true) :
    (Array.ofFn (n := cnt) fun i => tabT (unpack n w (T i.val))).all
      (fun s => !ordTest n 4 s ||
        CFSG.EvenSporadicStandard.HypOne.fiveConjOK n cap cg (cg.map (invT n)) s) = true := by
  have hgi' : TabsOK n w k GI (cg.map (invT n)) := by
    refine ⟨by rw [Array.size_map, hg.1], fun l hl => ⟨?_, (canonK_of_invEqK hn (hgi l hl)).2⟩⟩
    have hl' : l < cg.size := by rw [hg.1]; exact hl
    rw [getElem!_pos _ l (by rw [Array.size_map]; exact hl'), Array.getElem_map,
      ← getElem!_pos cg l hl', (hg.2 l hl).1, invT_unpack hn32 (hgi l hl)]
  rw [Array.all_eq_true]
  intro i hi
  rw [Array.size_ofFn] at hi
  rw [Array.getElem_ofFn]
  cases ho : ordTest n 4 (tabT (unpack n w (T i)))
  · rfl
  · rw [Bool.not_true, Bool.false_or]
    exact fiveConjOK_of_fiveTopK hcap hg hgi' (hT i hi)
      (hrow i hi (ordTest4_unpack hn hidc (hT i hi) ho))

theorem fiveTree_of_zero {α β : Type} {key : α → β} {st : Nat → α → α} {k f : Nat}
    {Kn : List α} (h : CFSG.KS.HBfs.FiveTree key st k 0 Kn) :
    CFSG.KS.HBfs.FiveTree key st k f Kn := by
  cases f with
  | zero => exact h
  | succ f =>
    rw [CFSG.KS.HBfs.FiveTree.eq_2]
    exact Or.inl h

theorem fiveE_spec (n w m : Nat) (G GI : Nat → Nat) (k S : Nat) : ∀ r L (T : List Nat),
    (∀ X ∈ T, X = S ∨ ∃ j < k, X = cjK n w m G GI j S) →
    fiveE n w m G GI k S r L (T.map (hkeyU n w m)) = true →
    ∃ T' : List Nat, (∀ X ∈ T', X = S ∨ ∃ j < k, X = cjK n w m G GI j S) ∧
      5 ≤ cntD (T'.map (hkeyU n w m)) []
  | 0, _, _, _, h => Bool.noConfusion h
  | r + 1, L, T, hT, h => by
    change strictB (Nat.land L (nat_lit 7)) (fun l =>
      bIf(Nat.blt l k, strictB (hkeyU n w m (cjK n w m G GI l S)) (fun hy =>
        bIf(Nat.ble (nat_lit 5) (cntD (List.cons hy (T.map (hkeyU n w m))) List.nil), true,
          fiveE n w m G GI k S r (Nat.shiftRight L (nat_lit 3))
            (List.cons hy (T.map (hkeyU n w m))))), false)) = true at h
    rw [CFSG.KS.PF.strictB_eqP, bIf_eqF] at h
    generalize Nat.land L 7 = l at h
    cases hl : Nat.blt l k
    · rw [hl, Bool.cond_false] at h
      exact Bool.noConfusion h
    rw [hl, Bool.cond_true, CFSG.KS.PF.strictB_eqP, bIf_eqF] at h
    have hT' : ∀ X ∈ cjK n w m G GI l S :: T, X = S ∨ ∃ j < k, X = cjK n w m G GI j S := by
      intro X hX
      rcases List.mem_cons.1 hX with rfl | hX
      · exact Or.inr ⟨l, Nat.blt_eq.mp hl, rfl⟩
      · exact hT X hX
    cases hc : Nat.ble 5 (cntD (hkeyU n w m (cjK n w m G GI l S) :: T.map (hkeyU n w m)) [])
    · rw [hc, Bool.cond_false] at h
      exact fiveE_spec n w m G GI k S r _ _ hT' h
    · exact ⟨_, hT', Nat.le_of_ble_eq_true hc⟩

theorem fiveTree_of_fiveTopE {n w : Nat} {G GI : Nat → Nat} {k f r L S : Nat}
    (h : fiveTopE n w (mask w) G GI k r L S = true) :
    CFSG.KS.HBfs.FiveTree (hkeyB n w (mask w)) (cjK n w (mask w) G GI) k f [S] := by
  change strictB (hkeyU n w (mask w) S) (fun hs => fiveE n w (mask w) G GI k S r L [hs]) = true
    at h
  rw [CFSG.KS.PF.strictB_eqP] at h
  obtain ⟨T, hT, h5⟩ := fiveE_spec n w (mask w) G GI k S r L [S]
    (fun X hX => Or.inl (List.mem_singleton.1 hX)) h
  rw [hkeyU_eq_hkeyB] at h5
  obtain ⟨Xs, h1, h2, -, h4⟩ := cnt_spec (hkeyB n w (mask w)) T []
  refine fiveTree_of_zero ?_
  rw [CFSG.KS.HBfs.FiveTree.eq_1]
  refine ⟨Xs, fun X hX => ?_, h2, by omega⟩
  rcases hT X (h1 X hX) with rfl | ⟨j, hj, rfl⟩
  · exact Or.inl List.mem_cons_self
  · exact Or.inr ⟨_, List.mem_cons_self, j, hj, rfl⟩

theorem fiveConjOK_of_treeB {n w k f cap S : Nat} {G GI : Nat → Nat} {cg cgInv : Array Table}
    (hcap : 5 ≤ cap) (hg : TabsOK n w k G cg) (hgi : TabsOK n w k GI cgInv)
    (hS : canonK n w (mask w) (n * w) S = true)
    (h : CFSG.KS.HBfs.FiveTree (hkeyB n w (mask w)) (cjK n w (mask w) G GI) k f [S]) :
    CFSG.EvenSporadicStandard.HypOne.fiveConjOK n cap cg cgInv (tabT (unpack n w S)) = true := by
  refine fiveConjOK_of_tree (f := f) hcap ?_
  rw [hg.1]
  have hst : ∀ l < k, ∀ x, canonK n w (mask w) (n * w) x = true →
      canonK n w (mask w) (n * w) (cjK n w (mask w) G GI l x) = true ∧
        tabT (unpack n w (cjK n w (mask w) G GI l x)) =
          conjT n cg[l]! cgInv[l]! (tabT (unpack n w x)) := by
    intro l hl x hx
    have h1 := CFSG.KC.BfsPin.canonK_pcomp (hg.2 l hl).2 hx
    refine ⟨CFSG.KC.BfsPin.canonK_pcomp h1 (hgi.2 l hl).2, ?_⟩
    unfold conjT
    rw [(hg.2 l hl).1, (hgi.2 l hl).1, compT_tabT _ _ fun x _ => unpack_lt hx,
      compT_tabT _ _ fun x _ => unpack_lt (hgi.2 l hl).2,
      CFSG.KC.BfsPin.compA_unpack (hg.2 l hl).2 hx, CFSG.KC.BfsPin.compA_unpack h1 (hgi.2 l hl).2]
    rfl
  have := CFSG.KS.HBfs.FiveTree.map (k := k) (st := fun l y => conjT n cg[l]! cgInv[l]! y)
    (key' := hkey n) (g := UInt64.toNat) (keyA := hkeyB n w (mask w)) (stA := cjK n w (mask w) G GI)
    (Good := fun x => canonK n w (mask w) (n * w) x = true) (fun a b e => UInt64.toNat_inj.1 e)
    (fun x => tabT (unpack n w x)) hst (fun x hx => hkeyB_tabT hx) f [S] (by simpa using hS) h
  simpa using this

theorem pow4_ne_of_pt {n w X x : Nat} (hX : canonK n w (mask w) (n * w) X = true) (hx : x < n)
    (h : Nat.beq (pg w (mask w) X (pg w (mask w) X (pg w (mask w) X (pg w (mask w) X x)))) x =
      false) :
    Nat.beq (pcomp n w (mask w) (pcomp n w (mask w) X X) (pcomp n w (mask w) X X)) (pidn n w) =
      false := by
  obtain ⟨hn, hw, -, hb⟩ := PF.canon_facts hX
  have hn32 : n < 2 ^ 32 := by omega
  cases e : Nat.beq (pcomp n w (mask w) (pcomp n w (mask w) X X) (pcomp n w (mask w) X X))
    (pidn n w)
  · rfl
  · have e' : pg w (mask w) (pcomp n w (mask w) (pcomp n w (mask w) X X)
        (pcomp n w (mask w) X X)) x = pg w (mask w) (pidn n w) x := by
      rw [Nat.eq_of_beq_eq_true e]
    have h1 : ∀ y < n, pg w (mask w) (pcomp n w (mask w) X X) y =
        pg w (mask w) X (pg w (mask w) X y) := fun y hy => PF.pg_pcomp hn32 hy
    rw [PF.pg_pcomp hn32 hx, h1 x hx, h1 _ (hb _ (hb _ hx)), PF.pg_pidn hn hw hx] at e'
    rw [e', Nat.beq_refl] at h
    exact Bool.noConfusion h

theorem sylRows_allT {n w k cnt cap f : Nat} {T G GI : Nat → Nat} {cg : Array Table}
    (hcap : 5 ≤ cap) (hn : szOK n w = true) (hn32 : n < 4294967296)
    (hidc : canonK n w (mask w) (n * w) (pidn n w) = true) (hg : TabsOK n w k G cg)
    (hgi : ∀ l < k, invEqK n w (mask w) (n * w) (G l) (GI l) = true)
    (hT : ∀ i < cnt, canonK n w (mask w) (n * w) (T i) = true)
    (hrow : ∀ i < cnt, (Nat.beq (pcomp n w (mask w) (pcomp n w (mask w) (T i) (T i))
        (pcomp n w (mask w) (T i) (T i))) (pidn n w) &&
      !Nat.beq (pcomp n w (mask w) (T i) (T i)) (pidn n w) && !Nat.beq (T i) (pidn n w)) = true →
        CFSG.KS.HBfs.FiveTree (hkeyB n w (mask w)) (cjK n w (mask w) G GI) k f [T i]) :
    (Array.ofFn (n := cnt) fun i => tabT (unpack n w (T i.val))).all
      (fun s => !ordTest n 4 s ||
        CFSG.EvenSporadicStandard.HypOne.fiveConjOK n cap cg (cg.map (invT n)) s) = true := by
  have hgi' : TabsOK n w k GI (cg.map (invT n)) := by
    refine ⟨by rw [Array.size_map, hg.1], fun l hl => ⟨?_, (canonK_of_invEqK hn (hgi l hl)).2⟩⟩
    have hl' : l < cg.size := by rw [hg.1]; exact hl
    rw [getElem!_pos _ l (by rw [Array.size_map]; exact hl'), Array.getElem_map,
      ← getElem!_pos cg l hl', (hg.2 l hl).1, invT_unpack hn32 (hgi l hl)]
  rw [Array.all_eq_true]
  intro i hi
  rw [Array.size_ofFn] at hi
  rw [Array.getElem_ofFn]
  cases ho : ordTest n 4 (tabT (unpack n w (T i)))
  · rfl
  · rw [Bool.not_true, Bool.false_or]
    exact fiveConjOK_of_treeB hcap hg hgi' (hT i hi)
      (hrow i hi (ordTest4_unpack hn hidc (hT i hi) ho))

end CFSG.KS.MulH

end
