module

public import Certificates.Kernel.Sporadic.ONOrd.Arr
public import Certificates.Kernel.Sporadic.ONOrd.Defs
public import Certificates.Kernel.Sporadic.ON8.Lin
import CFSG.Certificates.Kernel.Spor.PK.Basic

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ONOrd

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON CFSG.KS.ONLin CFSG.ONSchreier.Native CFSG.Sporadic.ON.Native
open CertificateChecks.KernelSpor.ON CertificateChecks.KernelSpor.ON8

theorem strictN_v (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

theorem fA_eq (x : Nat) : fA x = TT 0 x := strictN_v x _
theorem fB_eq (x : Nat) : fB x = TT 1 x := strictN_v x _
theorem fAI_eq (x : Nat) : fAI x = UU 0 x := strictN_v x _
theorem fBI_eq (x : Nat) : fBI x = UU 1 x := strictN_v x _

theorem fAI_lt {x : Nat} (hx : x < 245520) : fAI x < 245520 := by
  rw [fAI_eq]
  exact (perm_facts' x hx 0 (by norm_num)).2.1

theorem fBI_lt {x : Nat} (hx : x < 245520) : fBI x < 245520 := by
  rw [fBI_eq]
  exact (perm_facts' x hx 1 (by norm_num)).2.1

theorem fAI_fA {x : Nat} (hx : x < 245520) : fAI (fA x) = x := by
  rw [fAI_eq, fA_eq]
  exact (perm_facts' x hx 0 (by norm_num)).2.2

theorem fBI_fB {x : Nat} (hx : x < 245520) : fBI (fB x) = x := by
  rw [fBI_eq, fB_eq]
  exact (perm_facts' x hx 1 (by norm_num)).2.2

theorem lin_fA : L fA := (lin_TT (h := 0) (by norm_num)).congr fun x _ => (fA_eq x).symm
theorem lin_fB : L fB := (lin_TT (h := 1) (by norm_num)).congr fun x _ => (fB_eq x).symm
theorem lin_fAI : L fAI := (lin_UU (h := 0) (by norm_num)).congr fun x _ => (fAI_eq x).symm
theorem lin_fBI : L fBI := (lin_UU (h := 1) (by norm_num)).congr fun x _ => (fBI_eq x).symm

theorem lin_powK {F : Nat → Nat} (hF : L F) : ∀ k, L (powK F k)
  | 0 => Lin.id
  | k + 1 => (Lin.comp hF (lin_powK hF k)).congr fun _ _ => rfl

theorem lt_of_L {F : Nat → Nat} (h : L F) {x : Nat} (hx : x < 245520) : F x < 245520 := by
  obtain ⟨M, hM⟩ := h
  exact (hM x hx).1

theorem id_of_onP {F : Nat → Nat} (hF : L F) (h : onP F (fun x => x) = true) :
    ∀ x < 245520, F x = x :=
  agree hF Lin.id h

theorem moved_of_onP {F : Nat → Nat} (h : (!onP F fun x => x) = true) : ∃ x < 245520, F x ≠ x := by
  by_contra hc
  push Not at hc
  have h1 : onP F (fun x => x) = true := by
    unfold onP
    refine PK.allN_iff.2 fun t ht => ?_
    simp only [Nat.beq_eq]
    exact hc _ (spans'.1 t ht)
  rw [h1] at h
  exact absurd h (by decide)

theorem rd_tab {T : Nat → Nat} {F : Nat → Nat} (hF : L F) (hT : ∀ x < 245520, tab T x = F x) :
    Rd (nPts ()) (tabArr T 245520) F :=
  ⟨by rw [tabArr, Array.size_ofFn], fun x hx => ⟨by rw [tabArr, CFSG.KS.PW.ofFn_get' (f := tab T) hx, hT x hx],
    lt_of_L hF hx⟩⟩

theorem rd_alpha : Rd (nPts ()) (natTab (vorbit (digitsW CFSG.ONSchreier.Data.rootDigits)).alpha) fA := by
  rw [(orb_tabs mvAll ordAll sortAll).1]
  exact rd_tab lin_fA fun x _ => (fA_eq x).symm

theorem rd_beta : Rd (nPts ()) (natTab (vorbit (digitsW CFSG.ONSchreier.Data.rootDigits)).beta) fB := by
  rw [(orb_tabs mvAll ordAll sortAll).2]
  exact rd_tab lin_fB fun x _ => (fB_eq x).symm

end CertificateChecks.KernelSpor.ONOrd

end
