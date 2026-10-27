module

public import Certificates.Kernel.ONSeven.Words
public import Certificates.Kernel.Sporadic.ON8.Lin

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ONS

open CFSG.KC.Enum CFSG.KS CFSG.KS.TW CFSG.KS.ONLin CFSG.ONSchreier CFSG.ONSchreier.Native
  CFSG.Sporadic.ON.Native CFSG.RankThree.Native
open CertificateChecks.KernelSpor.ON (TT UU TT_lt peq_of peq_false_of)
open CertificateChecks.KernelSpor.ON3 (LetM)
open CertificateChecks.KernelSpor.ON8 (L onP sp agree lin_TT lin_UU)

theorem lt_of_L {F : Nat → Nat} (h : L F) {x : Nat} (hx : x < 245520) : F x < 245520 := by
  obtain ⟨M, hM⟩ := h
  exact (hM x hx).1

theorem lin_WW {w : List Int} (hw : LetM 7 w) : L (WW w) :=
  lin_word (m := 7) (fun _ hh => ⟨lin_TT hh, lin_UU hh⟩) w hw

theorem lin_iter {F : Nat → Nat} (hF : L F) : ∀ e, L (iter F e)
  | 0 => Lin.id
  | e + 1 => (Lin.comp hF (lin_iter hF e)).congr fun _ _ => rfl

theorem getD_eq {α : Type} [Inhabited α] (a : Array α) {i : Nat} (d : α) (h : i < a.size) :
    a.getD i d = a[i]! := by
  simp [Array.getD, getElem!_pos a i h, h]

theorem pow_get {x : Array Nat} {F : Nat → Nat} (hF : L F) (hx : ∀ i < 245520, x[i]! = F i) :
    ∀ e, ∀ i < 245520, (onSevenPow x e)[i]! = iter F e i
  | 0, i, hi => by
    unfold onSevenPow
    exact CFSG.KS.PW.pid_get' hi
  | e + 1, i, hi => by
    unfold onSevenPow
    rw [pcomp_get hi, pow_get hF hx e i hi, hx _ (lt_of_L (lin_iter hF e) hi)]
    rfl

theorem peq_of_onP {t u : Array Nat} {F G : Nat → Nat} (hF : L F) (hG : L G)
    (ht : ∀ i < 245520, t[i]! = F i) (hu : ∀ i < 245520, u[i]! = G i) (h : onP F G = true) :
    peq nPts t u = true :=
  peq_of fun i hi => by
    have hi : i < 245520 := hi
    rw [ht i hi, hu i hi, agree hF hG h i hi]

theorem peq_false_of_ne {t u : Array Nat} {i : Nat} (hi : i < 245520) (h : t[i]! ≠ u[i]!) :
    peq nPts t u = false :=
  peq_false_of (n := nPts) hi h

end CertificateChecks.KernelSpor.ONS

end
