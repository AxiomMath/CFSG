module

public import CFSG.Certificates.Kernel.Spor.FiveKSound
public import Certificates.Kernel.Sporadic.OddCore.CentGlue
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

end CFSG.KS.MulH

end
