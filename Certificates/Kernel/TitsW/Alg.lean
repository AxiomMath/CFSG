module

public import Certificates.Kernel.TitsW.Defs
public import CFSG.Certificates.Kernel.BfsPinAlg
public import CFSG.Sporadic.Schreier.TitsBasic
import CFSG.Certificates.Kernel.Spor.PrimSound
import CFSG.Certificates.Kernel.Spor.Loops
import CFSG.Certificates.Kernel.Spor.RawOrbHead
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.Spor.PinvSSound
import CFSG.Monster.B.Co2.PermArr
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Spor.RawOrbGrp

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelTitsW

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.Schreier.Tits CertificateChecks.KernelMisc

@[expose] def Gd (p : Nat) : Prop := PP 1755 11 p

theorem szT : szOK 1755 11 = true := by quickRfl

theorem sN (y : Nat) (k : Nat → Nat) : strictN y k = k y := by cases y <;> rfl

theorem Gd.mul {p q : Nat} (hp : Gd p) (hq : Gd q) : Gd (pm p q) := PP.mul hp hq

theorem Gd.inv {p : Nat} (hp : Gd p) : Gd (pv p) := PP.inv hp

theorem Gd.one : Gd pe := PP.id szT

theorem ppw_succ (p k : Nat) : ppw p (k + 1) = pm p (ppw p k) := sN _ _

theorem ppw_zero (p : Nat) : ppw p 0 = pe := rfl

theorem Gd.pow {p : Nat} (hp : Gd p) : ∀ k, Gd (ppw p k)
  | 0 => Gd.one
  | k + 1 => by
    rw [ppw_succ]
    exact hp.mul (Gd.pow hp k)

theorem Gd_brec (b : Bool) {x y : Nat} (hx : Gd x) (hy : Gd y) :
    Gd (Bool.rec (motive := fun _ => Nat) x y b) := by
  cases b
  · exact hx
  · exact hy

theorem Gd_word {S SI : Nat → Nat} (hS : ∀ k, Gd (S k)) (hSI : ∀ k, Gd (SI k)) :
    ∀ wd, Gd (wordK 1755 11 (mask 11) (pidn 1755 11) S SI wd)
  | [] => Gd.one
  | z :: wd => by
    rw [CFSG.KS.Raw.Orb.wordK_cons]
    exact Gd.mul (Gd_brec _ (hSI _) (hS _)) (Gd_word hS hSI wd)

theorem DS_lt {k : Nat} (hk : k < 13) : DS k = TitsText.F (18 + k) := by
  unfold DS
  rw [show Nat.blt k 13 = true from Nat.blt_eq.mpr hk]

theorem GS_lt {k : Nat} (hk : k < 4) : GS k = TitsText.F k := by
  unfold GS
  rw [show Nat.blt k 4 = true from Nat.blt_eq.mpr hk]

theorem Gd_DS (k : Nat) : Gd (DS k) := by
  by_cases hk : k < 13
  · exact PP_of_permOK szT (allN_spec dPerm k hk)
  · have e : DS k = DS 0 := by
      unfold DS
      rw [show Nat.blt k 13 = false from by
        rw [Bool.eq_false_iff]
        intro h
        exact hk (Nat.blt_eq.mp h)]
      rfl
    rw [e]
    exact PP_of_permOK szT (allN_spec dPerm 0 (by norm_num))

theorem Gd_GS (k : Nat) : Gd (GS k) := by
  by_cases hk : k < 4
  · exact PP_of_permOK szT (allN_spec gPerm k hk)
  · have e : GS k = GS 0 := by
      unfold GS
      rw [show Nat.blt k 4 = false from by
        rw [Bool.eq_false_iff]
        intro h
        exact hk (Nat.blt_eq.mp h)]
      rfl
    rw [e]
    exact PP_of_permOK szT (allN_spec gPerm 0 (by norm_num))

theorem Gd_WD (wd : List Int) : Gd (WD wd) :=
  Gd_word Gd_DS (fun k => (Gd_DS k).inv) wd

theorem Gd_WG (wd : List Int) : Gd (WG wd) :=
  Gd_word Gd_GS (fun k => (Gd_GS k).inv) wd

theorem wordArr_pk {A : Array (Array Nat)} {k : Nat} {S SI : Nat → Nat}
    (hA : A.size = k ∧ ∀ j < k, A[j]! = unpack 1755 11 (S j))
    (hp : allN k (fun j => permOK 1755 11 (mask 11) (1755 * 11) (S j) (SI j)) = true)
    {wd : List Int} (hl : lettersK k wd = true) :
    wordArr 1755 A wd = unpack 1755 11 (wordK 1755 11 (mask 11) (pidn 1755 11) S SI wd) := by
  have hw : wordEqK 1755 11 (mask 11) (pidn 1755 11) S SI k wd
      (wordK 1755 11 (mask 11) (pidn 1755 11) S SI wd) = true := by
    rw [wordEqK]
    simp only [bAnd_iff, szT, hl, true_and]
    exact Nat.beq_refl _
  exact (wordEqK_sound hA hp hw).1

theorem titsD_bind : titsDerivedArrs.size = 13 ∧
    ∀ j < 13, titsDerivedArrs[j]! = unpack 1755 11 (DS j) :=
  ⟨by simp [titsDerivedArrs, titsField1755], fun j hj => by
    rw [TitsText.titsDerivedArrs_get hj, DS_lt hj]⟩

theorem titsG_bind : titsGenArrs.size = 4 ∧ ∀ j < 4, titsGenArrs[j]! = unpack 1755 11 (GS j) :=
  ⟨by simp [titsGenArrs, titsField1755], fun j hj => by
    rw [titsGenArrs, titsField1755, getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn,
      TitsText.titsArr1755_eq (by omega), GS_lt hj]
    simp⟩

theorem wordArr_D {wd : List Int} (hl : lettersK 13 wd = true) :
    wordArr 1755 titsDerivedArrs wd = unpack 1755 11 (WD wd) :=
  wordArr_pk titsD_bind dPerm hl

theorem wordArr_G {wd : List Int} (hl : lettersK 4 wd = true) :
    wordArr 1755 titsGenArrs wd = unpack 1755 11 (WG wd) :=
  wordArr_pk titsG_bind gPerm hl

theorem derived_get {j : Nat} (hj : j < 13) : titsDerivedArrs[j]! = unpack 1755 11 (DS j) :=
  titsD_bind.2 j hj

theorem gen_get {j : Nat} (hj : j < 4) : titsGenArrs[j]! = unpack 1755 11 (GS j) :=
  titsG_bind.2 j hj

theorem compA_G {p q : Nat} (hp : Gd p) (hq : Gd q) :
    compA 1755 (unpack 1755 11 p) (unpack 1755 11 q) = unpack 1755 11 (pm p q) :=
  compA_PP hp hq

theorem invCand_G {p : Nat} (hp : Gd p) :
    invCand 1755 (unpack 1755 11 p) = unpack 1755 11 (pv p) :=
  invCand_PP hp

theorem eqA_G {p q : Nat} (hp : Gd p) (hq : Gd q) :
    eqA 1755 (unpack 1755 11 p) (unpack 1755 11 q) = Nat.beq p q :=
  eqA_PP hp hq

theorem idA_G : idA 1755 = unpack 1755 11 pe := idA_eq szT

theorem isInvA_G {p : Nat} (hp : Gd p) :
    isInvA 1755 (unpack 1755 11 p) (unpack 1755 11 (pv p)) = true := by
  have h := CFSG.KS.PinvS.permOK_pinvS hp.1 hp.2
  obtain ⟨-, -, h3⟩ := CFSG.KS.Raw.Orb.permOK_facts h
  rw [isInvA, CFSG.Monster.B.Co2.allLt_iff]
  intro i hi
  rw [CFSG.KS.Raw.Orb.unpack_get hi, CFSG.KS.Raw.Orb.unpack_get (h3 i hi).1]
  simp [h3 i hi]

theorem pow_G {p : Nat} (hp : Gd p) {f : Nat → Array Nat} (h0 : f 0 = idA 1755)
    (hs : ∀ k, f (k + 1) = compA 1755 (unpack 1755 11 p) (f k)) :
    ∀ k, f k = unpack 1755 11 (ppw p k)
  | 0 => by rw [h0, idA_G, ppw_zero]
  | k + 1 => by rw [hs, pow_G hp h0 hs k, compA_G hp (hp.pow k), ppw_succ]

theorem lettersK_append (j : Nat) : ∀ a b : List Int,
    lettersK j (a ++ b) = (lettersK j a && lettersK j b)
  | [], b => by
    change lettersK j b = (true && lettersK j b)
    rw [Bool.true_and]
  | z :: a, b => by
    rw [List.cons_append, CFSG.KS.Raw.Orb.lettersK_cons, CFSG.KS.Raw.Orb.lettersK_cons,
      lettersK_append j a b]
    simp [Bool.and_assoc]

theorem lettersK_flatten_replicate {j : Nat} {w : List Int} (h : lettersK j w = true) :
    ∀ k, lettersK j (List.replicate k w).flatten = true
  | 0 => rfl
  | k + 1 => by
    rw [List.replicate_succ, List.flatten_cons, lettersK_append, h,
      lettersK_flatten_replicate h k]
    rfl

theorem allLt_allN (n : Nat) (f : Nat → Bool) : allLt n f = allN n f := by
  apply Bool.eq_iff_iff.mpr
  rw [CFSG.Monster.B.Co2.allLt_iff, CFSG.KS.Raw.Orb.allN_iff]

end CertificateChecks.KernelTitsW

end
