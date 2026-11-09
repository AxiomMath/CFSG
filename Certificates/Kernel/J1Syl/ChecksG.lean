module

public import Certificates.Kernel.J1Syl.Defs
public import Certificates.Kernel.Sporadic.ON.Gen
import CFSG.Certificates.Kernel.Spor.Loops
import CFSG.Certificates.Kernel.Spor.PackFld
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kon_slices CertificateChecks.KernelJ1Syl.fMov 5 8
#kon_slices CertificateChecks.KernelJ1Syl.fMov 9 10

namespace CertificateChecks.KernelJ1Syl

open CFSG.KC.Enum CFSG.KS.PEnum CFSG.Sporadic.J1.Sylow.Native CertificateChecks.KernelSpor.J1K

@[expose] noncomputable def movW (w : List Int) : Bool :=
  movesAll.notK (movesAll.memB (keyOf (wp fW (xp w (wp (invWord fW) (nat_lit 0))))
    (wp fW (xp w (wp (invWord fW) (nat_lit 1))))) (keys2 w))

@[expose] noncomputable def fMov8D : Bool :=
  allN (nat_lit 300) fun d => movW ((TWL.drop 2400).getD d [])

theorem fMov8D_ok : fMov8D = true := by quickRfl

private theorem strictB_eqG (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem slice_of {L N s : Nat} {p : Nat → Bool}
    (h : ∀ d < L, Nat.add (Nat.mul s L) d < N → p (Nat.add (Nat.mul s L) d) = true) :
    slice L N s p = true := by
  unfold slice
  refine CFSG.KS.PackFld.allN_of_forall fun d hd => ?_
  rw [strictB_eqG]
  show bIf(Nat.blt (Nat.add (Nat.mul s L) d) N, p (Nat.add (Nat.mul s L) d), true) = true
  cases hb : Nat.blt (Nat.add (Nat.mul s L) d) N
  · rfl
  · have hb' := hb
    rw [Nat.blt_eq] at hb'
    exact h d hd hb'

theorem getD_drop2400 (d : Nat) : (TWL.drop 2400).getD d [] = TWL.getD (2400 + d) [] := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem fMov8 : fMov (nat_lit 8) = true := by
  unfold fMov
  refine slice_of fun d hd _ => ?_
  have e : Nat.add (Nat.mul (nat_lit 8) (nat_lit 300)) d = 2400 + d := by
    show 8 * 300 + d = 2400 + d
    omega
  rw [e]
  have h : movW ((TWL.drop 2400).getD d []) = true := CFSG.KS.allN_spec fMov8D_ok d hd
  rw [getD_drop2400] at h
  cases hz : Nat.beq (2400 + d) (nat_lit 0)
  · exact h
  · have hz' : 2400 + d = 0 := Nat.eq_of_beq_eq_true hz
    omega

end CertificateChecks.KernelJ1Syl

end
