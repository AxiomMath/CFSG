module

public import Certificates.Kernel.SporSch.Co3.Gen2155
public import Certificates.Kernel.SporSch.GenClosure
public import CFSG.Certificates.Kernel.SporSch.ClosureSound
public import CFSG.Sporadic.Schreier.Co3SecondImageCheckInputs
meta import CFSG.Sporadic.Schreier.Co3SecondImageCheckInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.SporSch.AnyN

public section

set_option maxRecDepth 400000

#kss_closure CertificateChecks.KernelSporSch.Co3H0 4 CFSG.Sporadic.Schreier.Co3.co3D0Kappa1 1000

namespace CertificateChecks.KernelSporSch.Co3Image

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch
open CFSG.Sporadic.Schreier.Co3 CFSG.Sporadic.Schreier.Co3.Native CFSG.Monster.B.Co2.Native
open CertificateChecks.KernelSporSch
open CertificateChecks.KernelSporSch.Co3Gen (kd_eq)

@[expose] noncomputable def PF (i : Nat) : Nat := Nat.land (Nat.shiftRight Co3H0.PP (16 * i)) 65535

@[expose] noncomputable def LF (i : Nat) : Nat := Nat.land (Nat.shiftRight Co3H0.LP (8 * i)) 255

theorem closure_ok : closureK 12 4 Co3KD 5 Co3H0.E 192 Co3H0.PP Co3H0.LP 1000 = true := by quickRfl

theorem tree_ok : allN 192 (fun i => bIf(Nat.beq i 0, true, bAnd(Nat.blt (PF i) i,
    bAnd(Nat.blt (LF i) 5, compEqK 12 4 (mask 4) (12 * 4) (Co3KD (LF i)) (Co3H0.E (PF i))
      (Co3H0.E i))))) = true := by quickRfl

theorem perm_E : allN 192 (fun i => permOK 12 4 (mask 4) (12 * 4) (Co3H0.E i)
    (pinvS 12 4 (mask 4) (Co3H0.E i))) = true := by quickRfl

theorem perm_K : allN 5 (fun k => permOK 12 4 (mask 4) (12 * 4) (Co3KD k)
    (pinvS 12 4 (mask 4) (Co3KD k))) = true := by quickRfl

theorem clos_K : allN 5 (fun k => allN 192 (fun i => anyN 192 (fun j =>
    compEqK 12 4 (mask 4) (12 * 4) (Co3KD k) (Co3H0.E i) (Co3H0.E j)))) = true := by quickRfl

theorem clos_KI : allN 5 (fun k => allN 192 (fun i => anyN 192 (fun j =>
    compEqK 12 4 (mask 4) (12 * 4) (pinvS 12 4 (mask 4) (Co3KD k)) (Co3H0.E i) (Co3H0.E j)))) =
    true := by quickRfl

theorem dist_E : allN 192 (fun i => allN i (fun j =>
    neK 12 4 (mask 4) (12 * 4) (Co3H0.E i) (Co3H0.E j))) = true := by quickRfl

theorem id_ok : idK 12 4 (mask 4) = true := by quickRfl

theorem e0 : Nat.beq (Co3H0.E 0) (pidn 12 4) = true := by quickRfl

theorem rec_eq : co3D0ImgRec = (Array.ofFn (n := 192) fun i => unpack 12 4 (Co3H0.E i.val),
    Array.ofFn (n := 192) fun i => PF i.val, Array.ofFn (n := 192) fun i => LF i.val) :=
  closureK_sound ⟨by simp [co3D0Kappa1], kd_eq⟩ closure_ok

theorem ofFn_get {α : Type} [Inhabited α] {c : Nat} {f : Fin c → α} (i : Nat) (hi : i < c) :
    (Array.ofFn f)[i]! = f ⟨i, hi⟩ := by
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

theorem isInv_of {n w P : Nat} {a : Array Nat} (ha : a = unpack n w P)
    (h : permOK n w (mask w) (n * w) P (pinvS n w (mask w) P) = true) :
    isInvA n a (invCand n a) = true := by
  obtain ⟨h1, h2⟩ := invEqK_sound (r := pinvS n w (mask w) P) h
  rw [ha, h1]
  exact h2

theorem facts : co3D0ImgRec.1.size = 192 ∧ eqA 12 co3D0ImgRec.1[0]! (idA 12) = true ∧
    (∀ i < 192, 1 ≤ i → co3D0ImgRec.2.1[i]! < i ∧ co3D0ImgRec.2.2[i]! < 5 ∧
      eqA 12 co3D0ImgRec.1[i]!
        (compA 12 co3D0Kappa1[co3D0ImgRec.2.2[i]!]! co3D0ImgRec.1[co3D0ImgRec.2.1[i]!]!) = true) ∧
    (∀ i < 192, isInvA 12 co3D0ImgRec.1[i]! (invCand 12 co3D0ImgRec.1[i]!) = true) ∧
    (∀ k < 5, isInvA 12 co3D0Kappa1[k]! (invCand 12 co3D0Kappa1[k]!) = true) ∧
    (∀ k < 5, ∀ i < 192, ∃ j < 192,
      eqA 12 (compA 12 co3D0Kappa1[k]! co3D0ImgRec.1[i]!) co3D0ImgRec.1[j]! = true) ∧
    (∀ k < 5, ∀ i < 192, ∃ j < 192,
      eqA 12 (compA 12 (invCand 12 co3D0Kappa1[k]!) co3D0ImgRec.1[i]!) co3D0ImgRec.1[j]! = true) ∧
    (∀ i < 192, ∀ j < i, eqA 12 co3D0ImgRec.1[i]! co3D0ImgRec.1[j]! = false) := by
  have hE : ∀ i < 192, (Array.ofFn (n := 192) fun i => unpack 12 4 (Co3H0.E i.val))[i]! =
      unpack 12 4 (Co3H0.E i) := fun i hi => ofFn_get i hi
  rw [rec_eq]
  refine ⟨by simp, ?_, fun i hi h1 => ?_, fun i hi => ?_, fun k hk => ?_, fun k hk i hi => ?_,
    fun k hk i hi => ?_, fun i hi j hj => ?_⟩
  · rw [hE 0 (by omega), Nat.eq_of_beq_eq_true e0, idK_sound id_ok]
    rw [← idK_sound id_ok]
    exact eqK_sound (Nat.beq_refl _)
  · have ht := allN_spec tree_ok i hi
    have hi0 : Nat.beq i 0 = false :=
      Bool.eq_false_iff.mpr fun h' => absurd (Nat.eq_of_beq_eq_true h') (by omega)
    rw [hi0] at ht
    obtain ⟨hp, ht⟩ := (bAnd_iff _ _).1 ht
    obtain ⟨hl, hc⟩ := (bAnd_iff _ _).1 ht
    have hp' := Nat.blt_eq.mp hp
    have hl' := Nat.blt_eq.mp hl
    simp only [ofFn_get i hi]
    refine ⟨by omega, by omega, ?_⟩
    rw [hE (PF i) (by omega), kd_eq (LF i) (by omega), compEqK_sound hc]
    exact eqK_sound (Nat.beq_refl _)
  · exact isInv_of (hE i hi) (allN_spec perm_E i hi)
  · exact isInv_of (kd_eq k hk) (allN_spec perm_K k hk)
  · obtain ⟨j, hj, hc⟩ := anyN_spec (allN_spec (allN_spec clos_K k hk) i hi)
    refine ⟨j, hj, ?_⟩
    rw [hE i hi, hE j hj, kd_eq k hk, compEqK_sound hc]
    exact eqK_sound (Nat.beq_refl _)
  · obtain ⟨j, hj, hc⟩ := anyN_spec (allN_spec (allN_spec clos_KI k hk) i hi)
    refine ⟨j, hj, ?_⟩
    rw [hE i hi, hE j hj, kd_eq k hk,
      (invEqK_sound (allN_spec perm_K k hk)).1, compEqK_sound hc]
    exact eqK_sound (Nat.beq_refl _)
  · rw [hE i hi, hE j (by omega)]
    exact neK_sound (allN_spec (allN_spec dist_E i hi) j hj)

end CertificateChecks.KernelSporSch.Co3Image

end
