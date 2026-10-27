module

public import Certificates.Kernel.ONSeven.Defs
public import Certificates.Kernel.Sporadic.ON5.Final

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ONS

open CFSG.KC.Enum CFSG.KS CFSG.KS.TW CFSG.KS.PW CFSG.ONSchreier CFSG.ONSchreier.Native
  CFSG.RankThree.Native
open CertificateChecks.KernelSpor.ON (TT UU TT_lt UU_lt perm_facts' qon_SA SA_get SAi_get)
open CertificateChecks.KernelSpor.ON3 (LetM letM_invW invW)

theorem letters : LettersOK 245520 7 qonStrongArrs onSevenInvArrs TT UU := by
  intro j hj x hx
  have hi : onSevenInvArrs = pinvs 245520 CertificateChecks.KernelSpor.ON.SA := by
    unfold onSevenInvArrs
    rw [qon_SA]
  rw [qon_SA, hi, SA_get hj hx, SAi_get hj hx]
  exact ⟨rfl, rfl, TT_lt hx, UU_lt hx⟩

theorem WW_lt {w : List Int} {x : Nat} (hx : x < 245520) : WW w x < 245520 := by
  unfold WW
  induction w with
  | nil => exact hx
  | cons l w ih =>
    simp only [List.foldr_cons]
    unfold GZ
    split
    · exact TT_lt ih
    · exact UU_lt ih

theorem arr_get {w : List Int} (hw : LetM 7 w) {x : Nat} (hx : x < 245520) :
    (onSevenArr w)[x]! = WW w x :=
  (pword_get letters w hw x hx).1

theorem arr_eq {w : List Int} (hw : LetM 7 w) :
    onSevenArr w = Array.ofFn (n := 245520) fun i => WW w i.val :=
  pword_eq letters hw

theorem arr_size (w : List Int) : (onSevenArr w).size = 245520 := pword_size w

theorem GZ_inv {l : Int} (hl : l ≠ 0 ∧ l.natAbs ≤ 7) {y : Nat} (hy : y < 245520) :
    GZ TT UU l y < 245520 ∧ GZ TT UU (-l) (GZ TT UU l y) = y := by
  unfold GZ
  by_cases hp : 0 < l
  · have hn : ¬ (0 : Int) < -l := by omega
    simp only [hp, hn, ↓reduceIte, neg_neg]
    have hj : l.toNat - 1 < 7 := by omega
    exact ⟨TT_lt hy, (perm_facts' y hy _ hj).2.2⟩
  · have hn : (0 : Int) < -l := by omega
    simp only [hp, hn, ↓reduceIte]
    have hj : (-l).toNat - 1 < 7 := by omega
    have e := CertificateChecks.KernelSpor.ON.TT_UU hj hy
    exact ⟨UU_lt hy, e⟩

theorem WW_inv {w : List Int} (hw : LetM 7 w) {x : Nat} (hx : x < 245520) :
    WW (invW w) (WW w x) = x := by
  have h := (foldr_inv (G := GZ TT UU) w (fun z hz y hy => GZ_inv (hw z hz) hy) x hx).2
  unfold WW invW
  exact h

theorem GZ_inv' {l : Int} (hl : l ≠ 0 ∧ l.natAbs ≤ 7) {y : Nat} (hy : y < 245520) :
    GZ TT UU l (GZ TT UU (-l) y) = y := by
  have h := GZ_inv (l := -l) ⟨by omega, by omega⟩ hy
  rw [neg_neg] at h
  exact h.2

theorem WW_inv' {w : List Int} (hw : LetM 7 w) {x : Nat} (hx : x < 245520) :
    WW w (WW (invW w) x) = x := by
  have h := WW_inv (letM_invW hw) hx
  have e : invW (invW w) = w := by
    unfold invW
    simp [List.map_reverse, Function.comp_def]
  rwa [e] at h

theorem pcomp_get {t u : Array Nat} {i : Nat} (hi : i < 245520) :
    (pcomp 245520 t u)[i]! = t[u[i]!]! := pcomp_get' hi

theorem inv_get {w : List Int} (hw : LetM 7 w) {y : Nat} (hy : y < 245520) :
    (pinvCand 245520 (onSevenArr w))[y]! = WW (invW w) y := by
  rw [arr_eq hw]
  exact CFSG.KS.CB.pinvCand_get (fun x hx => WW_lt hx) (fun x hx => WW_inv hw hx) hy

theorem pisInv_word {w : List Int} (hw : LetM 7 w) :
    pisInv 245520 (onSevenArr w) (pinvCand 245520 (onSevenArr w)) = true :=
  CertificateChecks.KernelSpor.ON5K.pisInv_of (arr_size w) (fun x hx => arr_get hw hx)
    fun x hx => ⟨WW_lt hx, WW_inv hw hx⟩

end CertificateChecks.KernelSpor.ONS

end
