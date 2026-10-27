module

public import Certificates.Kernel.EvenBN.Bind
public import Certificates.Data.TitsAschbacherE32
meta import Certificates.Data.TitsAschbacherE32
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Certificate7050Base

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelEvenBN

meta def eList : List (Array Nat) := Certificates.TitsAschbacherE32.eArrs ()
meta def fList : List (Array Nat) := Certificates.TitsAschbacherE32.fArrs ()
meta def uList : List (Array Nat) := Certificates.TitsAschbacherE32.u10Arrs ()

end CertificateChecks.KernelEvenBN

#kst_plist CertificateChecks.KernelEvenBN.ELit 11 CertificateChecks.KernelEvenBN.eList
#kst_plist CertificateChecks.KernelEvenBN.FLit 11 CertificateChecks.KernelEvenBN.fList
#kst_plist CertificateChecks.KernelEvenBN.ULit 11 CertificateChecks.KernelEvenBN.uList

namespace CertificateChecks.KernelEvenBN

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.Schreier.Tits CertificateChecks.KernelSporSch.TitsHelp
open CertificateChecks.KernelSporSch.TitsCentral CertificateChecks.KernelSpor
open CertificateChecks.KernelSpor.Tits2268 CertificateChecks.KernelSporSch
open Certificates.TitsAschbacherParrott Certificates.TitsAschbacherSecFour
open Certificates.TitsAschbacherE32

theorem strictB_app (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem all_congr_mem {α : Type} {L : List α} {f g : α → Bool} (h : ∀ x ∈ L, f x = g x) :
    L.all f = L.all g := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    simp only [List.all_cons]
    rw [h a (List.mem_cons_self ..), ih fun x hx => h x (List.mem_cons_of_mem _ hx)]

theorem any_congr_mem {α : Type} {L : List α} {f g : α → Bool} (h : ∀ x ∈ L, f x = g x) :
    L.any f = L.any g := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    simp only [List.any_cons]
    rw [h a (List.mem_cons_self ..), ih fun x hx => h x (List.mem_cons_of_mem _ hx)]

theorem all_mapU {L : List Nat} (hL : ∀ x ∈ L, C x) {f : Array Nat → Bool} {g : Nat → Bool}
    (h : ∀ x, C x → f (unpack 1755 11 x) = g x) : (L.map (unpack 1755 11)).all f = L.all g := by
  rw [List.all_map]
  exact all_congr_mem fun x hx => h x (hL x hx)

theorem any_mapU {L : List Nat} (hL : ∀ x ∈ L, C x) {f : Array Nat → Bool} {g : Nat → Bool}
    (h : ∀ x, C x → f (unpack 1755 11 x) = g x) : (L.map (unpack 1755 11)).any f = L.any g := by
  rw [List.any_map]
  exact any_congr_mem fun x hx => h x (hL x hx)

theorem getD_mapU {L : List Nat} {i : Nat} (h : i < L.length) :
    (L.map (unpack 1755 11)).getD i #[] = unpack 1755 11 (L.getD i 0) := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem getD_mem {L : List Nat} {i : Nat} (h : i < L.length) : L.getD i 0 ∈ L := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  exact List.getElem_mem h

theorem hW {w : List Nat} (hw : hLetters w = true) :
    hArr w = unpack 1755 11 (wP TitsH.S w) ∧ C (wP TitsH.S w) := by
  refine chain_gen bindsH canH fun j hj => ?_
  have := List.all_eq_true.1 hw j hj
  simp only [decide_eq_true_eq] at this
  omega

theorem nW {w : List Nat} (hw : nLetters w = true) :
    nArr w = unpack 1755 11 (wP TitsN.S w) ∧ C (wP TitsN.S w) := by
  refine chain_gen bindsN canN fun j hj => ?_
  have := List.all_eq_true.1 hw j hj
  simp only [decide_eq_true_eq] at this
  omega

@[expose] noncomputable def EL : List Nat := ELit

@[expose] noncomputable def FL : List Nat := FLit

@[expose] noncomputable def UL : List Nat := ULit

theorem elK : (((List.range 32).map fun m => wP V (u8Bits m)) == EL) = true := by quickRfl
theorem flK : (((List.range 32).map fun m => wP V (fBits m)) == FL) = true := by quickRfl
theorem ulK : (((List.range 8).map fun m => wP V (u10Bits m)) == UL) = true := by quickRfl

theorem listU_eq {n : Nat} {b : Nat → List Nat} (hb : ∀ m < n, ∀ j ∈ b m, j < 13) {L : List Nat}
    (hL : (((List.range n).map fun m => wP V (b m)) == L) = true) :
    (List.range n).map (fun m => vProd (b m)) = L.map (unpack 1755 11) ∧ ∀ x ∈ L, C x := by
  rw [← beq_iff_eq.1 hL]
  refine ⟨?_, fun x hx => ?_⟩
  · rw [List.map_map]
    exact List.map_congr_left fun m hm => (vProd_eq (hb m (List.mem_range.1 hm))).1
  · obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hx
    exact (vProd_eq (hb m (List.mem_range.1 hm))).2

theorem eArrs_eq : eArrs () = EL.map (unpack 1755 11) ∧ ∀ x ∈ EL, C x := listU_eq (by decide) elK
theorem fArrs_eq : fArrs () = FL.map (unpack 1755 11) ∧ ∀ x ∈ FL, C x := listU_eq (by decide) flK
theorem u10Arrs_eq : u10Arrs () = UL.map (unpack 1755 11) ∧ ∀ x ∈ UL, C x :=
  listU_eq (by decide) ulK

theorem EL_len : EL.length = 32 := by rw [← beq_iff_eq.1 elK]; simp
theorem FL_len : FL.length = 32 := by rw [← beq_iff_eq.1 flK]; simp
theorem UL_len : UL.length = 8 := by rw [← beq_iff_eq.1 ulK]; simp

@[expose] noncomputable def xkC (e : Bool × Bool × List Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (wP TitsH.S e.2.2) (wP TitsN.S e.2.2) e.1

@[expose] noncomputable def xkL (e : Bool × Bool × List Nat) : List Nat :=
  (Bool.rec (motive := fun _ => List Nat) EL FL e.2.1).map fun x =>
    pcomp 1755 11 (mask 11) (pcomp 1755 11 (mask 11) (xkC e) x) (pinvS 1755 11 (mask 11) (xkC e))

theorem xkK : xkData.all (fun e => permOK 1755 11 (mask 11) (1755 * 11) (xkC e)
    (pinvS 1755 11 (mask 11) (xkC e)) && canonK 1755 11 (mask 11) (1755 * 11)
      (pinvS 1755 11 (mask 11) (xkC e))) = true := by quickRfl

theorem xkC_eq {e : Bool × Bool × List Nat} (he : e ∈ xkData) :
    xkConj e = unpack 1755 11 (xkC e) ∧ C (xkC e) := by
  have hl : (if e.1 then nLetters e.2.2 else hLetters e.2.2) = true := by revert e; decide
  unfold xkConj xkC
  cases h : e.1
  · rw [h] at hl
    exact hW hl
  · rw [h] at hl
    exact nW hl

theorem xkSet_eq {e : Bool × Bool × List Nat} (he : e ∈ xkData) :
    xkSet (EL.map (unpack 1755 11)) (FL.map (unpack 1755 11)) e = (xkL e).map (unpack 1755 11) ∧
      ∀ x ∈ xkL e, C x := by
  obtain ⟨hc, cc⟩ := xkC_eq he
  have k := List.all_eq_true.1 xkK e he
  simp only [Bool.and_eq_true] at k
  obtain ⟨kp, ki⟩ := k
  have hi : invCand 1755 (unpack 1755 11 (xkC e)) = unpack 1755 11 (pinvS 1755 11 (mask 11) (xkC e)) :=
    CFSG.KC.BfsPin.invCand_unpack kp
  have hL : (if e.2.1 = true then FL.map (unpack 1755 11) else EL.map (unpack 1755 11)) =
      (Bool.rec (motive := fun _ => List Nat) EL FL e.2.1).map (unpack 1755 11) ∧
      ∀ x ∈ Bool.rec (motive := fun _ => List Nat) EL FL e.2.1, C x := by
    cases e.2.1
    · exact ⟨rfl, eArrs_eq.2⟩
    · exact ⟨rfl, fArrs_eq.2⟩
  unfold xkSet xkL
  simp only []
  rw [hc, hi, hL.1, List.map_map, List.map_map]
  refine ⟨List.map_congr_left fun x hx => ?_, fun y hy => ?_⟩
  · simp only [Function.comp]
    rw [cmpU cc (hL.2 x hx), cmpU (cmpC cc (hL.2 x hx)) ki]
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
    exact cmpC (cmpC cc (hL.2 x hx)) ki

end CertificateChecks.KernelEvenBN

end
