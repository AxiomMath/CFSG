
module

public import Certificates.Kernel.Sporadic.Fi22.E2067T
public import CFSG.Certificates.Kernel.Spor.TextSound
public import CFSG.Certificates.Kernel.SporSch.DerivsSound
public import CFSG.Certificates.Kernel.Spor.PrimSound
public import CFSG.Certificates.Kernel.Spor.RawSlSound
public import CFSG.Sporadic.FischerOddCore.Fi22ExtCheckInputs
public import Certificates.Kernel.Misc.Perm.HexCmd
meta import CFSG.Sporadic.FischerOddCore.Fi22ExtCheckInputs
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Fi22E2067

meta def invM : Array (Array Nat) := (Array.range 185).map fun L =>
  CFSG.Monster.B.Co2.Native.invCand 3510 (CFSG.Sporadic.FischerOddCore.fi22ExtArr L)

end CertificateChecks.KernelSpor.Fi22E2067

#kmisc_packarrs CertificateChecks.KernelSpor.Fi22E2067.EI CertificateChecks.KernelSpor.Fi22E2067.invM 12

namespace CertificateChecks.KernelSpor.Fi22E2067

open CFSG.KC.Enum CFSG.KS CFSG.KS.Text CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin
open CFSG.Sporadic.FischerOddCore CFSG.Monster.B.Fischer CFSG.Monster.B.Co2.Native

theorem isInv_of {n w P Q : Nat} {a : Array Nat} (ha : a = unpack n w P)
    (h : permOK n w (mask w) (n * w) P Q = true) :
    isInvA n a (invCand n a) = true := by
  obtain ⟨h1, h2⟩ := invEqK_sound (r := Q) h
  rw [ha, h1]
  exact h2

@[expose] noncomputable def permSl (s : Nat) : Bool :=
  allN 20 (fun j => strictB (Nat.add (Nat.mul 20 s) j) (fun L => bIf(Nat.blt L 185,
    permOK 3510 12 (mask 12) (3510 * 12) (Fi22ExtT.L L) (EI L), true)))

theorem ps0 : permSl 0 = true := by quickRfl
theorem ps1 : permSl 1 = true := by quickRfl
theorem ps2 : permSl 2 = true := by quickRfl
theorem ps3 : permSl 3 = true := by quickRfl
theorem ps4 : permSl 4 = true := by quickRfl
theorem ps5 : permSl 5 = true := by quickRfl
theorem ps6 : permSl 6 = true := by quickRfl
theorem ps7 : permSl 7 = true := by quickRfl
theorem ps8 : permSl 8 = true := by quickRfl
theorem ps9 : permSl 9 = true := by quickRfl

theorem perm3510 {L : Nat} (hL : L < 185) :
    permOK 3510 12 (mask 12) (3510 * 12) (Fi22ExtT.L L) (EI L) = true := by
  have hs : ∀ s < 10, permSl s = true := by
    intro s hs
    interval_cases s
    exacts [ps0, ps1, ps2, ps3, ps4, ps5, ps6, ps7, ps8, ps9]
  have h := allN_spec (hs (L / 20) (by omega)) (L % 20) (Nat.mod_lt _ (by norm_num))
  rw [strictB_eq] at h
  have e : Nat.add (Nat.mul 20 (L / 20)) (L % 20) = L := by
    change 20 * (L / 20) + L % 20 = L
    omega
  rw [e] at h
  have hb : Nat.blt L 185 = true := Eq.mpr Nat.blt_eq hL
  rw [hb] at h
  exact h

theorem ext_eq {L : Nat} (hL : L < 185) : fi22ExtArr L = unpack 3510 12 (Fi22ExtT.L L) := by
  have h := hexBind_sound Fi22ExtT.all L hL
  rw [Nat.zero_add, ← Fi22ExtT.eq] at h
  exact h

theorem perm256 : allN 18 (fun L => permOK 256 9 (mask 9) (256 * 9) (Fi22E256T.L L)
    (pinvS 256 9 (mask 9) (Fi22E256T.L L))) = true := by quickRfl

theorem ext256_eq {L : Nat} (hL : L < 18) : fi22ExtArr256 L = unpack 256 9 (Fi22E256T.L L) := by
  have h := hexBind_sound Fi22E256T.all L hL
  rw [Nat.zero_add, ← Fi22E256T.eq] at h
  exact h

theorem dRange : allN 256 (fun i => Nat.blt (pg 12 (mask 12) Fi22X.DP i) 3510) = true := by
  quickRfl

theorem dInj : allN 256 (fun i => allN i (fun j =>
    Bool.not (Nat.beq (pg 12 (mask 12) Fi22X.DP j) (pg 12 (mask 12) Fi22X.DP i)))) = true := by
  quickRfl

theorem pts_len : fi22ExtSmallPointsNat.length = 256 := by
  have h := Fi22X.dArr_size
  rw [fi22ExtDArr, List.size_toArray] at h
  exact h

theorem pts_get {i : Nat} (hi : i < 256) :
    fi22ExtSmallPointsNat[i]'(by rw [pts_len]; exact hi) = pg 12 (mask 12) Fi22X.DP i := by
  have h := Fi22X.dArr_get hi
  rw [fi22ExtDArr, List.getElem!_toArray, getElem!_pos _ i (by rw [pts_len]; exact hi)] at h
  exact h

theorem pts_lt : ∀ x ∈ fi22ExtSmallPointsNat, x < 3510 := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have hi' : i < 256 := by rw [pts_len] at hi; exact hi
  rw [pts_get hi']
  exact Eq.mp Nat.blt_eq (allN_spec dRange i hi')

theorem pts_nodup : fi22ExtSmallPointsNat.Nodup := by
  rw [List.nodup_iff_pairwise_ne, List.pairwise_iff_getElem]
  intro i j hi hj hij
  have hj' : j < 256 := by rw [pts_len] at hj; exact hj
  rw [pts_get (by omega), pts_get hj']
  intro he
  have h := allN_spec (allN_spec dInj j hj') i hij
  rw [he, Nat.beq_refl] at h
  exact absurd h (by decide)

theorem words_eq :
    CFSG.Monster.B.Fischer.wordsOK = CFSG.Sporadic.Schreier.Co3.Native.wordsOK := rfl

theorem dk : CFSG.KS.SporSch.derivK 10 18 fi22ExtSmallDerivations = true := by quickRfl

theorem layout_eq :
    CFSG.Monster.B.Fischer.layoutOK = CFSG.Sporadic.Schreier.Co3.Native.layoutOK := rfl

theorem facts2067 : layoutOK fi22ExtBytes3510 3 3510 185 = true ∧
    layoutOK fi22ExtBytes256 2 256 18 = true ∧
    (∀ L < 185, isInvA 3510 (fi22ExtArr L) (invCand 3510 (fi22ExtArr L)) = true) ∧
    (∀ L < 18, isInvA 256 (fi22ExtArr256 L) (invCand 256 (fi22ExtArr256 L)) = true) ∧
    (∀ x ∈ fi22ExtSmallPointsNat, x < 3510) ∧ fi22ExtSmallPointsNat.Nodup ∧
    fi22ExtSmallPointsNat.length = 256 ∧ (∀ c ∈ fi22ExtGlobalClasses, c < 6) ∧
    fi22ExtGlobalClasses.length = 79 ∧ fi22ExtClassSizes.length = 79 ∧
    wordsOK fi22ExtSmallGenCount 18 fi22ExtSmallDerivations = true := by
  refine ⟨?_, ?_, fun L hL => isInv_of (ext_eq hL) (perm3510 hL),
    fun L hL => isInv_of (ext256_eq hL) (allN_spec perm256 L hL), pts_lt, pts_nodup, pts_len,
    by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  · rw [fi22ExtBytes3510, Fi22ExtT.eq, layout_eq]
    exact CFSG.KS.SporSch.hexBind_layout Fi22ExtT.all rfl
  · rw [fi22ExtBytes256, Fi22E256T.eq, layout_eq]
    exact CFSG.KS.SporSch.hexBind_layout Fi22E256T.all rfl
  · rw [words_eq]
    exact CFSG.KS.SporSch.derivK_sound dk

end CertificateChecks.KernelSpor.Fi22E2067

end
