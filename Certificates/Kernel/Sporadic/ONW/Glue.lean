module

public import Certificates.Kernel.Sporadic.ONW.Chk0
public import Certificates.Kernel.Sporadic.ONW.Chk1
public import Certificates.Kernel.Sporadic.ONW.Chk2
public import Certificates.Kernel.Sporadic.ON3.Words
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ONWitnessInputs
public import CFSG.Certificates.Kernel.BfsPinAlg
public import CFSG.Certificates.Kernel.Spor.RawOrbEval
public import CFSG.Monster.B.Co2.PermArr
public import CFSG.Sporadic.Schreier.ONPermArr
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Sporadic.Schreier.ONCheckAuxInputs
public import Certificates.Kernel.Sporadic.ON.Seven

public section

set_option maxRecDepth 400000

#kon_join CertificateChecks.KernelSpor.ONW.chkAll CertificateChecks.KernelSpor.ONW.chkS 120

namespace CertificateChecks.KernelSpor.ONW

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON CFSG.KS.TW CFSG.KS.Words
open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.RankThree.Native
open CFSG.Sporadic.ON.Native (nPts)
open CertificateChecks.KernelSpor.ON (TT UU)

theorem strictN_id (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

theorem strictB_id (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem nPts_eq : nPts = 245520 := rfl

theorem words_dec : decW (ONWW.WC 0) (ONWW.WL 0) = onThreeY[0]! ∧
    decW (ONWW.WC 1) (ONWW.WL 1) = onThreeY[1]! := by
  refine ⟨by decide +kernel, by decide +kernel⟩

theorem let7_0 : CertificateChecks.KernelSpor.ON3.Let7 onThreeY[0]! := by
  unfold CertificateChecks.KernelSpor.ON3.Let7
  decide

theorem let7_1 : CertificateChecks.KernelSpor.ON3.Let7 onThreeY[1]! := by
  unfold CertificateChecks.KernelSpor.ON3.Let7
  decide

theorem y_get {k : Nat} (hk : k < 2) {x : Nat} (hx : x < 245520) :
    (onThreeYArrs[k]!)[x]! = Y k x ∧ Y k x < 245520 := by
  have hs : onThreeY.size = 2 := rfl
  have ha : onThreeYArrs[k]! = CFSG.ONSchreier.wordArr onThreeY[k]! := by
    unfold onThreeYArrs
    rw [getElem!_pos _ k (by rw [Array.size_map, hs]; exact hk), Array.getElem_map,
      ← getElem!_pos onThreeY k (by rw [hs]; exact hk)]
    rfl
  rw [ha]
  rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
  · obtain ⟨e, hlt⟩ := CertificateChecks.KernelSpor.ON3.wordArr_get let7_0 hx
    have ey : Y 0 x = onThreeY[0]!.foldr (GZ TT UU) x :=
      (trace_eq TT UU _ _ x).trans (congrArg (fun w => w.foldr (GZ TT UU) x) words_dec.1)
    rw [ey]
    exact ⟨e, hlt⟩
  · obtain ⟨e, hlt⟩ := CertificateChecks.KernelSpor.ON3.wordArr_get let7_1 hx
    have ey : Y 1 x = onThreeY[1]!.foldr (GZ TT UU) x :=
      (trace_eq TT UU _ _ x).trans (congrArg (fun w => w.foldr (GZ TT UU) x) words_dec.2)
    rw [ey]
    exact ⟨e, hlt⟩

theorem pt_at {x : Nat} (hx : x < 245520) : ptAt x = true := by
  have hs : x / 2046 < 120 := by omega
  have h := CFSG.KS.Raw.Orb.allN_iff.1 (chkAll (x / 2046) hs) (x % 2046) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.mul (x / 2046) 2046) (x % 2046) = x := by
    simp only [Nat.add_eq, Nat.mul_eq]
    omega
  rwa [e] at h

theorem pt_facts {x : Nat} (hx : x < 245520) : PT x = Y 0 (Y 1 x) ∧
    UT x = PT (PT (PT x)) ∧ UT (UT (UT (UT (UT x)))) = x := by
  have h := pt_at hx
  unfold ptAt at h
  rw [strictB_id, strictB_id] at h
  have h' : (Nat.beq (PT x) (Y 0 (Y 1 x)) && (Nat.beq (UT x) (PT (PT (PT x))) &&
      Nat.beq (UT (UT (UT (UT (UT x))))) x)) = true := h
  simp only [Bool.and_eq_true] at h'
  obtain ⟨h1, h2, h3⟩ := h'
  have e1 := Nat.eq_of_beq_eq_true h1
  have e2 := Nat.eq_of_beq_eq_true h2
  exact ⟨e1, e2, Nat.eq_of_beq_eq_true h3⟩

theorem PT_lt {x : Nat} (hx : x < 245520) : PT x < 245520 := by
  rw [(pt_facts hx).1]
  exact (y_get (k := 0) (by norm_num) (y_get (k := 1) (by norm_num) hx).2).2

theorem UT_lt {x : Nat} (hx : x < 245520) : UT x < 245520 := by
  rw [(pt_facts hx).2.1]
  exact PT_lt (PT_lt (PT_lt hx))

theorem hN {x : Nat} (hx : x < 245520) : x < nPts := hx

theorem ofFn_get {f : Fin nPts → Nat} {x : Nat} (hx : x < 245520) :
    (Array.ofFn f)[x]! = f ⟨x, hN hx⟩ :=
  CFSG.Monster.B.Co2.getElem!_ofFn_nat f (hN hx)

@[expose] noncomputable def pA : Array Nat :=
  CFSG.ONSchreier.Native.pcomp nPts onThreeYArrs[0]! onThreeYArrs[1]!

theorem p_get {x : Nat} (hx : x < 245520) : pA[x]! = PT x := by
  unfold pA CFSG.ONSchreier.Native.pcomp
  rw [ofFn_get hx]
  dsimp only
  rw [(y_get (k := 1) (by norm_num) hx).1,
    (y_get (k := 0) (by norm_num) (y_get (k := 1) (by norm_num) hx).2).1, (pt_facts hx).1]

theorem pow_get {t : Array Nat} {f : Nat → Nat} (ht : ∀ x < 245520, t[x]! = f x ∧ f x < 245520) :
    ∀ e, ∀ x < 245520, (onSevenPow t e)[x]! = f^[e] x ∧ f^[e] x < 245520
  | 0, x, hx => by
    unfold onSevenPow CFSG.ONSchreier.Native.pid
    rw [ofFn_get hx]
    exact ⟨rfl, hx⟩
  | e + 1, x, hx => by
    obtain ⟨h1, h2⟩ := pow_get ht e x hx
    unfold onSevenPow CFSG.ONSchreier.Native.pcomp
    rw [ofFn_get hx]
    dsimp only
    rw [h1, (ht _ h2).1, Function.iterate_succ_apply']
    exact ⟨rfl, (ht _ h2).2⟩

@[expose] noncomputable def uA : Array Nat := onSevenPow pA 3

theorem u_get {x : Nat} (hx : x < 245520) : uA[x]! = UT x ∧ UT x < 245520 := by
  obtain ⟨h1, -⟩ := pow_get (fun y hy => ⟨p_get hy, PT_lt hy⟩) 3 x hx
  rw [uA, h1, (pt_facts hx).2.1]
  exact ⟨rfl, PT_lt (PT_lt (PT_lt hx))⟩

theorem uIt_eq (e x : Nat) : uIt e x = UT^[e] x := by
  induction e with
  | zero => rfl
  | succ e ih =>
    change strictN (uIt e x) UT = _
    rw [strictN_id, ih, Function.iterate_succ_apply']

theorem peq_of {t u : Array Nat} (h : ∀ i < 245520, t[i]! = u[i]!) : peq nPts t u = true := by
  unfold peq
  refine CFSG.ONSchreier.allBelowN_iff.2 fun i hi => ?_
  rw [h i hi, beq_self_eq_true]

theorem peq_false_of {i : Nat} {t u : Array Nat} (hi : i < 245520) (h : t[i]! ≠ u[i]!) :
    peq nPts t u = false := by
  rw [Bool.eq_false_iff]
  intro hp
  unfold peq at hp
  exact h (beq_iff_eq.1 (CFSG.ONSchreier.allBelowN_iff.1 hp i hi))

theorem ne_parts : (∃ x < 245520, UT x ≠ x) ∧
    ∀ k < 4, ∃ x < 245520, Y 0 (UT x) ≠ uIt (k + 1) (Y 0 x) := by
  have h := ne_ok
  unfold neOK at h
  have h' : (CFSG.KLie.CT.anyN 245520 (fun x => bIf(Nat.beq (UT x) x, false, true)) &&
      allN 4 fun k => CFSG.KLie.CT.anyN 245520 fun x =>
        bIf(Nat.beq (Y 0 (UT x)) (uIt (Nat.succ k) (Y 0 x)), false, true)) = true := h
  rw [Bool.and_eq_true] at h'
  obtain ⟨h1, h2⟩ := h'
  refine ⟨?_, fun k hk => ?_⟩
  · rw [CFSG.KC.BfsPin.anyN_eq] at h1
    obtain ⟨x, hx, e⟩ := List.any_eq_true.1 h1
    refine ⟨x, List.mem_range.1 hx, fun he => ?_⟩
    rw [he, Nat.beq_refl] at e
    exact Bool.false_ne_true e
  · have h3 := CFSG.KS.Raw.Orb.allN_iff.1 h2 k hk
    rw [CFSG.KC.BfsPin.anyN_eq] at h3
    obtain ⟨x, hx, e⟩ := List.any_eq_true.1 h3
    refine ⟨x, List.mem_range.1 hx, fun he => ?_⟩
    rw [he, Nat.beq_refl] at e
    exact Bool.false_ne_true e

theorem onWitnessChecks_true :
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Native.onWitnessChecks () = true := by
  unfold CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Native.onWitnessChecks
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Native.onWitnessCore
  have hu : onSevenPow (CFSG.ONSchreier.Native.pcomp nPts onThreeYArrs[0]! onThreeYArrs[1]!) 3 =
      uA := rfl
  rw [hu]
  have hU : ∀ y < 245520, uA[y]! = UT y ∧ UT y < 245520 := fun y hy => u_get hy
  obtain ⟨n1, n2⟩ := ne_parts
  simp only [Bool.and_eq_true, Bool.not_eq_true']
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · refine peq_of fun i hi => ?_
    rw [(pow_get hU 5 i hi).1]
    unfold CFSG.ONSchreier.Native.pid
    rw [ofFn_get hi]
    exact (pt_facts hi).2.2
  · obtain ⟨x, hx, e⟩ := n1
    refine peq_false_of hx ?_
    rw [(u_get hx).1]
    unfold CFSG.ONSchreier.Native.pid
    rw [ofFn_get hx]
    exact e
  · refine CFSG.ONSchreier.allBelowN_iff.2 fun k hk => ?_
    obtain ⟨x, hx, e⟩ := n2 k hk
    rw [Bool.not_eq_true']
    refine peq_false_of hx ?_
    have ha := y_get (k := 0) (by norm_num) hx
    have hua := y_get (k := 0) (by norm_num) (u_get hx).2
    unfold CFSG.ONSchreier.Native.pcomp
    rw [ofFn_get hx, ofFn_get hx]
    dsimp only
    rw [(u_get hx).1, hua.1, ha.1, (pow_get hU (k + 1) _ ha.2).1, ← uIt_eq]
    exact e

end CertificateChecks.KernelSpor.ONW

end
