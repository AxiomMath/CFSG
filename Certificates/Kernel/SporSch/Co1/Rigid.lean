
module

public import Certificates.Kernel.SporSch.Co1.RigidK
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.Co1Rigid

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch.M24 CFSG.KS.SporSch.Orb CFSG.KS.Mathieu
open CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.SmallF2.Native
open CertificateChecks.KernelSporSch.Co1Elem CertificateChecks.KernelSporSch.Co1Split
open CertificateChecks.KernelSporSch.Co1Gen

theorem mulU (X Y : Nat) : mul (unpack 24 24 X) (unpack 24 24 Y) = unpack 24 24 (mulK X Y) :=
  mulEqK_sound (Nat.beq_refl _)

theorem qMat_eq : qMat = unpack 24 24 (QP 0) := by
  have h : qMat = qMatP zR Data.f4vecs := by
    unfold qMat qCols qMatP qColsP qNat qNatP f4Hi f4HiP
    rfl
  rw [h, zR_eq]
  exact transOK_sound kQ

theorem qInv_eq : qInv = unpack 24 24 (QP 1) := by
  unfold qInv
  rw [qMat_eq]
  exact (invOKK_sound kQI).2

theorem ngetPL_eq : ∀ (l : List (List Nat × List Nat)) (i : Nat), ngetPL l i = l.getD i ([], [])
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: l, i + 1 => ngetPL_eq l i

theorem comp_eq : compRows = [unpack 24 24 (CC 0), unpack 24 24 (CC 1), unpack 24 24 (CC 2)] := by
  unfold compRows
  rw [c_eq 0 (by omega), c_eq 1 (by omega), gRows_eq]
  rfl

theorem eRows_eq : eRows = eRowsP fun i => unpack 24 24 (AF i) := by
  funext b
  unfold eRows eRowsP
  rw [aRows_eq]

theorem loc_eq (W : List (List Nat × List Nat)) {P : Nat → Nat} {i : Nat}
    (h : bAnd(pos3K (pr2 (ngetPL W i)), Nat.beq (locK AF CC (ngetPL W i)) (P i)) = true) :
    locRows (W.getD i ([], [])) = unpack 24 24 (P i) := by
  obtain ⟨h1, h2⟩ := (bAnd_iff (pos3K (pr2 (ngetPL W i)))
    (Nat.beq (locK AF CC (ngetPL W i)) (P i))).1 h
  rw [ngetPL_eq] at h1 h2
  unfold locRows
  rw [comp_eq, eRows_eq, ← Nat.eq_of_beq_eq_true h2]
  exact locK_sound h1 _

theorem all_range_congr {n : Nat} {p q : Nat → Bool} (h : ∀ i < n, p i = q i) :
    (List.range n).all p = (List.range n).all q := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.all_append, List.all_append, ih (fun i hi => h i (by omega)),
      List.all_cons, List.all_cons, h n (by omega), List.all_nil, List.all_nil]

theorem h_eq (i : Nat) (hi : i < 3) : hRows i = unpack 24 24 (HP i) := loc_eq _ (allN_spec kH i hi)
theorem k_eq (i : Nat) (hi : i < 3) : kRows i = unpack 24 24 (KP i) := loc_eq _ (allN_spec kK i hi)

theorem hqT_eq : hqT = Array.ofFn (n := 3) fun i => unpack 24 24 (HQ i.val) := by
  unfold hqT
  refine congrArg (Array.ofFn (n := 3)) (funext fun j => ?_)
  rw [qInv_eq, h_eq j j.2, qMat_eq, mulU, mulU, Nat.eq_of_beq_eq_true (allN_spec kHQ j j.2)]

theorem dqT_eq : dqT = Array.ofFn (n := 8) fun f => unpack 24 24 (DP f.val) := by
  unfold dqT
  refine congrArg (Array.ofFn (n := 8)) (funext fun f => ?_)
  have h := allN_spec kD f f.2
  rw [ngetL_eq] at h
  exact toArray_eq_of_bindListK h

theorem dsT_eq : dsT = Array.ofFn (n := 8) fun f => unpack 24 24 (DSP f.val) := by
  unfold dsT
  refine congrArg (Array.ofFn (n := 8)) (funext fun f => ?_)
  have hd : (Array.ofFn (n := 8) fun f => unpack 24 24 (DP f.val)).getD f.val one =
      unpack 24 24 (DP f.val) := by
    simp [Array.getD_eq_getD_getElem?, f.2]
  rw [dqT_eq, hd, qMat_eq, qInv_eq, mulU, mulU, Nat.eq_of_beq_eq_true (allN_spec kDS f f.2)]

theorem rigP_congr {Q QI g2 g2i x y a1 : Rows} {c ci c' ci' h k h' k' : Nat → Rows}
    {free : Array (Nat × Nat)} (hc : ∀ i < 2, c i = c' i ∧ ci i = ci' i)
    (hh : ∀ i < 3, h i = h' i ∧ k i = k' i) :
    rigP Q QI c ci g2 g2i x y h k a1 free = rigP Q QI c' ci' g2 g2i x y h' k' a1 free := by
  have e1 : ((List.range 2).all fun i => mul (c i) (ci i) == one) =
      (List.range 2).all fun i => mul (c' i) (ci' i) == one :=
    all_range_congr fun i hi => by rw [(hc i hi).1, (hc i hi).2]
  have e2 : ((List.range 3).all fun i => mul x (h i) == mul (k i) x) =
      (List.range 3).all fun i => mul x (h' i) == mul (k' i) x :=
    all_range_congr fun i hi => by rw [(hh i hi).1, (hh i hi).2]
  unfold rigP
  rw [e1, e2]

theorem rig : rigCheck = true := by
  have h : rigCheck = rigP qMat qInv cRows (fun i => inv (cRows i)) (gRows 2) (inv (gRows 2)) xR
      yR hRows kRows (aRows 1) freeA := by
    unfold rigCheck rigP
    rfl
  rw [h, rigP_congr (c' := fun i => unpack 24 24 (CRP i)) (ci' := fun i => unpack 24 24 (CRIP i))
    (h' := fun i => unpack 24 24 (HP i)) (k' := fun i => unpack 24 24 (KP i))
    (fun i hi => ⟨c_eq i hi, ci_eq i hi⟩) (fun i hi => ⟨h_eq i hi, k_eq i hi⟩)]
  rw [qMat_eq, qInv_eq, gRows_eq, x_eq, y_eq, aRows_eq]
  beta_reduce
  rw [(invOKK_sound (gi 2 (by omega))).2]
  exact rigK_sound kRig

theorem slicesP : ∀ s < 9, propK HQ RT Data.rigEqs (64 * s) 64 = true := by
  intro s hs
  interval_cases s
  exacts [kP0, kP1, kP2, kP3, kP4, kP5, kP6, kP7, kP8]

theorem prop : propCheck = true := by
  have h : propCheck = propCheckP hqT rankA eqsA := by
    unfold propCheck combB coefB propCheckP combBP coefBP
    rfl
  rw [h, hqT_eq]
  exact propK_sound kR slicesP

theorem free : freeCheck = true := by
  have h : freeCheck = freeCheckP rankA freeA := by
    unfold freeCheck freeCheckP
    rfl
  rw [h]
  exact freeK_sound kR kF

theorem basis : basisCheck = true := by
  have h : basisCheck = basisCheckP dqT hqT freeA := by
    unfold basisCheck basisCheckP
    rfl
  rw [h, dqT_eq, hqT_eq]
  exact basisK_sound kB

theorem cand (ε : Fin 8 → Bool) : candOK ε = true := by
  have h : candOK ε = candOKP xR yR dsT ε := by
    unfold candOK candRows candOKP candRowsP
    rfl
  rw [h, x_eq, y_eq, dsT_eq]
  refine candK_sound (X := XP) (Y := YP) (fun s hs => ?_) ε
  interval_cases s
  exacts [kC0, kC1, kC2, kC3]

end CertificateChecks.KernelSporSch.Co1Rigid

end
