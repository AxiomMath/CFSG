module

public import Certificates.Kernel.Sporadic.Tits.Bind2264
public import CFSG.Certificates.Kernel.BfsPinSound
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.Kernel.BfsPinUnpack

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Tits2264

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.Sporadic.Schreier.Tits
open CFSG.Monster.B.Co2.Native CertificateChecks.KernelMisc

@[expose] noncomputable def commP (u v : Nat) : Nat :=
  pcomp 1755 11 (mask 11) (pcomp 1755 11 (mask 11) (pcomp 1755 11 (mask 11)
    (pinvS 1755 11 (mask 11) u) (pinvS 1755 11 (mask 11) v)) u) v

@[expose] noncomputable def G (k : Nat) : Nat :=
  nIf(Nat.beq k 0, TitsText.F 0, nIf(Nat.beq k 1, TitsText.F 1, nIf(Nat.beq k 2, TitsText.F 2,
    TitsText.F 3)))

@[expose] noncomputable def GI (k : Nat) : Nat := pinvS 1755 11 (mask 11) (G k)

@[expose] noncomputable def Up (j : Nat) : Nat := wordK 1755 11 (mask 11) (pidn 1755 11) G GI (titsU j)
@[expose] noncomputable def Vp (j : Nat) : Nat := wordK 1755 11 (mask 11) (pidn 1755 11) G GI (titsV j)
@[expose] noncomputable def Dp (j : Nat) : Nat := commP (Up j) (Vp j)

@[expose] noncomputable def Dk (k : Nat) : Nat := nIf(Nat.beq k 0, Dp 0, Dp 1)
@[expose] noncomputable def DIk (k : Nat) : Nat := pinvS 1755 11 (mask 11) (Dk k)

@[expose] noncomputable def Rp (j : Nat) : Nat :=
  wordK 1755 11 (mask 11) (pidn 1755 11) Dk DIk (titsPerfR j)
@[expose] noncomputable def Sp (j : Nat) : Nat :=
  wordK 1755 11 (mask 11) (pidn 1755 11) Dk DIk (titsPerfS j)
@[expose] noncomputable def Ep (j : Nat) : Nat := commP (Rp j) (Sp j)

@[expose] noncomputable def permC (u : Nat) : Bool :=
  bAnd(permOK 1755 11 (mask 11) (1755 * 11) u (pinvS 1755 11 (mask 11) u),
    bAnd(canonK 1755 11 (mask 11) (1755 * 11) u,
      canonK 1755 11 (mask 11) (1755 * 11) (pinvS 1755 11 (mask 11) u)))

theorem gOK : allN 4 (fun k => permC (G k)) = true := by quickRfl
theorem wOK : allN 2 (fun j => bAnd(permC (Up j), bAnd(permC (Vp j), bAnd(permC (Dp j),
    bAnd(permC (Rp j), bAnd(permC (Sp j), permC (Ep j))))))) = true := by quickRfl
theorem lettersOK' : allN 2 (fun j => bAnd(lettersK 4 (titsU j), bAnd(lettersK 4 (titsV j),
    bAnd(lettersK 2 (titsPerfR j), lettersK 2 (titsPerfS j))))) = true := by quickRfl
theorem dOK : allN 2 (fun j => Nat.beq (Dp j) (TitsD.S j)) = true := by quickRfl
theorem eOK : allN 2 (fun j => Nat.beq (Ep j) (TitsP.S j)) = true := by quickRfl
theorem idOK : bAnd(canonK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11), idK 1755 11 (mask 11)) =
    true := by quickRfl

theorem permC_spec {u : Nat} (h : permC u = true) :
    permOK 1755 11 (mask 11) (1755 * 11) u (pinvS 1755 11 (mask 11) u) = true ∧
    canonK 1755 11 (mask 11) (1755 * 11) u = true ∧
    canonK 1755 11 (mask 11) (1755 * 11) (pinvS 1755 11 (mask 11) u) = true := by
  unfold permC at h
  simpa only [bAnd_iff] using h

theorem w_spec {j : Nat} (hj : j < 2) : permC (Up j) = true ∧ permC (Vp j) = true ∧
    permC (Dp j) = true ∧ permC (Rp j) = true ∧ permC (Sp j) = true ∧ permC (Ep j) = true := by
  simpa only [bAnd_iff] using allN_spec wOK j hj

theorem commArr_unpack {u v : Nat} (hu : permC u = true) (hv : permC v = true) :
    commArr 1755 (unpack 1755 11 u) (unpack 1755 11 v) = unpack 1755 11 (commP u v) := by
  obtain ⟨pu, cu, ciu⟩ := permC_spec hu
  obtain ⟨pv, cv, civ⟩ := permC_spec hv
  unfold commArr commP
  rw [invCand_unpack pu, invCand_unpack pv, compA_unpack ciu civ,
    compA_unpack (canonK_pcomp ciu civ) cu, compA_unpack (canonK_pcomp (canonK_pcomp ciu civ) cu) cv]

theorem gens_bind : titsGenArrs.size = 4 ∧ ∀ k < 4, titsGenArrs[k]! = unpack 1755 11 (G k) := by
  refine ⟨by simp [titsGenArrs, titsField1755], fun k hk => ?_⟩
  rw [gen_eq hk]
  interval_cases k <;> rfl

theorem gens_perm : allN 4 (fun k => permOK 1755 11 (mask 11) (1755 * 11) (G k) (GI k)) = true := by
  quickRfl

theorem wordU {j : Nat} (hj : j < 2) : wordArr 1755 titsGenArrs (titsU j) = unpack 1755 11 (Up j) := by
  interval_cases j
  · exact (wordEqK_sound gens_bind gens_perm (by unfold wordEqK; quickRfl)).1
  · exact (wordEqK_sound gens_bind gens_perm (by unfold wordEqK; quickRfl)).1

theorem wordV {j : Nat} (hj : j < 2) : wordArr 1755 titsGenArrs (titsV j) = unpack 1755 11 (Vp j) := by
  interval_cases j
  · exact (wordEqK_sound gens_bind gens_perm (by unfold wordEqK; quickRfl)).1
  · exact (wordEqK_sound gens_bind gens_perm (by unfold wordEqK; quickRfl)).1

theorem titsDArr_eq {j : Nat} (hj : j < 2) : titsDArr j = unpack 1755 11 (Dp j) := by
  obtain ⟨hU, hV, -⟩ := w_spec hj
  unfold titsDArr Dp
  rw [wordU hj, wordV hj, commArr_unpack hU hV]

theorem dArrs_bind : titsDArrs.size = 2 ∧ ∀ k < 2, titsDArrs[k]! = unpack 1755 11 (Dk k) := by
  refine ⟨by simp [titsDArrs], fun k hk => ?_⟩
  rw [titsDArrs, getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn, titsDArr_eq hk]
  interval_cases k <;> rfl

theorem dArrs_perm : allN 2 (fun k => permOK 1755 11 (mask 11) (1755 * 11) (Dk k) (DIk k)) = true := by
  quickRfl

theorem wordR {j : Nat} (hj : j < 2) : wordArr 1755 titsDArrs (titsPerfR j) = unpack 1755 11 (Rp j) := by
  interval_cases j
  · exact (wordEqK_sound dArrs_bind dArrs_perm (by unfold wordEqK; quickRfl)).1
  · exact (wordEqK_sound dArrs_bind dArrs_perm (by unfold wordEqK; quickRfl)).1

theorem wordS {j : Nat} (hj : j < 2) : wordArr 1755 titsDArrs (titsPerfS j) = unpack 1755 11 (Sp j) := by
  interval_cases j
  · exact (wordEqK_sound dArrs_bind dArrs_perm (by unfold wordEqK; quickRfl)).1
  · exact (wordEqK_sound dArrs_bind dArrs_perm (by unfold wordEqK; quickRfl)).1

theorem titsEArr_eq {j : Nat} (hj : j < 2) : titsEArr j = unpack 1755 11 (Ep j) := by
  obtain ⟨-, -, -, hR, hS, -⟩ := w_spec hj
  unfold titsEArr Ep
  rw [wordR hj, wordS hj, commArr_unpack hR hS]

end CertificateChecks.KernelSpor.Tits2264

end
