module

public import Certificates.Kernel.LocalComp.M12End.Data
public import Certificates.Kernel.Census.M12Chain
public import CFSG.Certificates.Kernel.BfsPinSetSound
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicM12EndTests
import CFSG.Certificates.Kernel.Spor.SiftRSound
import CFSG.Certificates.Kernel.Common.Harness
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.M12End

open CFSG.KC.Enum CFSG.KC.BfsPin CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.Monster.B.Co2
open CFSG.Monster.B.Co2.Native CFSG.RankThree.Native CFSG.Monster.B.Fischer
open CFSG.ComponentClassification.RankTwoSporadic.M12 CertificateChecks.KernelCensus

theorem binds : Binds 24 5 M12C.S 12 5 M12C.BP m12S m12BaseArr := by
  have h : m12S.size = 12 ∧ (∀ j < 12, m12S[j]! = unpack 24 5 (M12C.S j)) ∧
      m12BaseArr.size = 5 ∧ ∀ t < 5, m12BaseArr[t]! = pg 5 (mask 5) M12C.BP t := by
    decide +kernel
  exact ⟨by norm_num, by norm_num, by norm_num, h.1, h.2.1, h.2.2.1, h.2.2.2⟩

theorem hperm : allN 12 (fun j => permOK 24 5 (mask 5) (24 * 5) (M12C.S j) (M12C.SI j)) = true := by
  quickRfl

@[expose] noncomputable def pk (t : Array Nat) : Nat := packA 5 t.toList

@[expose] noncomputable def inPA (t : Array Nat) : Bool :=
  bAnd(bindArrK t 24 5 (pk t), bAnd(canonK 24 5 (mask 5) (24 * 5) (pk t),
    siftK 24 5 (mask 5) (24 * 5) (pidn 24 5) M12C.LR M12C.TRI M12C.BP 5 0 (pk t)))

theorem inPA_sound {t : Array Nat} (h : inPA t = true) : m12InP m12S t = true := by
  unfold inPA at h
  obtain ⟨hb, h2⟩ := (bAnd_iff _ _).1 h
  obtain ⟨hc, hs⟩ := (bAnd_iff _ _).1 h2
  have hc' := hc
  simp only [canonK, bAnd_iff] at hc'
  exact siftK_soundR binds hperm M12C.hl (unpack_eq_of_bindArrK hb)
    (Nat.eq_of_beq_eq_true hc'.2.1) (range_of_canonK hc) hs

theorem allLt_mono {n : Nat} {p q : Nat → Bool} (h : ∀ i < n, p i = true → q i = true)
    (hp : allLt n p = true) : allLt n q = true :=
  allLt_iff.2 fun i hi => h i hi (allLt_iff.1 hp i hi)

theorem kId : idK 24 5 (mask 5) = true := by quickRfl
theorem kPid : canonK 24 5 (mask 5) (24 * 5) (pidn 24 5) = true := by quickRfl

theorem bE0 : (Nat.beq m12E0.size E0.ng && allN E0.ng fun k => bindArrK m12E0[k]! 24 5 (E0.G k)) =
    true := by quickRfl
theorem pE0 : allN E0.ng (fun k => permOK 24 5 (mask 5) (24 * 5) (E0.G k)
    (pinvS 24 5 (mask 5) (E0.G k))) = true := by quickRfl
theorem keyE0 : keysK 24 5 m12PS E0.N E0.T = true := by quickRfl

theorem bL : (Nat.beq m12EndL.size L.ng && allN L.ng fun k => bindArrK m12EndL[k]! 24 5 (L.G k)) =
    true := by quickRfl
theorem pL : allN L.ng (fun k => permOK 24 5 (mask 5) (24 * 5) (L.G k)
    (pinvS 24 5 (mask 5) (L.G k))) = true := by quickRfl
theorem keyL : keysK 24 5 m12PS L.N L.T = true := by quickRfl

theorem setE0 : enumOK 24 m12E0 m12PS (enumBfs 24 m12E0 m12PS m12Fuel) = true ∧
    (∀ x, x ∈ (enumBfs 24 m12E0 m12PS m12Fuel).pts ↔ ∃ i < E0.N, unpack 24 5 (E0.T i) = x) ∧
    (enumBfs 24 m12E0 m12PS m12Fuel).pts.size = E0.N :=
  enumBfs_of_bfsK_set (binds_of_check bE0).1 (binds_of_check bE0).2
    (fun k hk => allN_spec pE0 k hk) kId kPid E0.ok m12PS_lt keyE0 (by decide)

theorem setL : enumOK 24 m12EndL m12PS (enumBfs 24 m12EndL m12PS m12Fuel) = true ∧
    (∀ x, x ∈ (enumBfs 24 m12EndL m12PS m12Fuel).pts ↔ ∃ i < L.N, unpack 24 5 (L.T i) = x) ∧
    (enumBfs 24 m12EndL m12PS m12Fuel).pts.size = L.N :=
  enumBfs_of_bfsK_set (binds_of_check bL).1 (binds_of_check bL).2
    (fun k hk => allN_spec pL k hk) kId kPid L.ok m12PS_lt keyL (by decide)

theorem kE0fpf : allN E0.N (fun i => eqA 24 (unpack 24 5 (E0.T i)) (idA 24) ||
    m12FpfA (unpack 24 5 (E0.T i))) = true := by quickRfl

theorem kT0 : inPA (m12T0 m12E0) = true := by quickRfl

theorem e0OK : m12EndE0OK m12S m12E0 = true := by
  obtain ⟨hok, hmem, hsz⟩ := setE0
  unfold m12EndE0OK
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨⟨by decide +kernel, hok⟩, ?_⟩, by decide +kernel⟩, ?_⟩, by decide +kernel⟩,
    inPA_sound kT0⟩
  · rw [hsz]
    decide +kernel
  · exact allLt_pts (f := fun x => eqA 24 x (idA 24) || m12FpfA x) hmem
      (fun i hi => allN_spec kE0fpf i hi)

theorem kA0 : inPA m12EndA0 = true := by quickRfl

theorem kE0a : (List.range E0.N).any (fun i => eqA 24 (conjInvA 24 m12EndA0 (m12T0 m12E0))
    (unpack 24 5 (E0.T i))) = false := by decide +kernel

theorem kLeaves : allLt m12EndLeaves.size (fun i => inPA m12EndLeaves[i]! &&
    allLt m12E0.size fun j => m12CommA m12EndLeaves[i]! m12E0[j]!) = true := by quickRfl

theorem conjOK : m12EndConjOK m12S m12E0 m12EndA0 m12EndLeaves = true := by
  obtain ⟨-, hmem, -⟩ := setE0
  unfold m12EndConjOK
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨by decide +kernel, inPA_sound kA0⟩, by decide +kernel⟩, ?_⟩, ?_, by decide +kernel⟩
  · simp only [m12InEnum, any_pts hmem, kE0a, Bool.not_false]
  · refine allLt_mono (fun i _ h => ?_) kLeaves
    rw [Bool.and_eq_true] at h ⊢
    exact ⟨inPA_sound h.1, h.2⟩

theorem kGL : allLt m12EndL.size (fun i => inPA m12EndL[i]! &&
    allLt m12E0.size fun j => m12CommA m12EndL[i]! m12E0[j]!) = true := by quickRfl

theorem kLt : (List.range L.N).any (fun i => eqA 24 (m12T0 m12E0) (unpack 24 5 (L.T i))) =
    false := by decide +kernel

theorem kLinv : allN L.N (fun i =>
    !eqA 24 (compA 24 (unpack 24 5 (L.T i)) (unpack 24 5 (L.T i))) (idA 24) ||
      eqA 24 (unpack 24 5 (L.T i)) (idA 24) || !m12FpfA (unpack 24 5 (L.T i))) = true := by
  quickRfl

theorem kSig : inPA m12EndSigma = true := by quickRfl
theorem kC0 : inPA m12EndC0 = true := by quickRfl

theorem derOK : m12EndDerOK m12S m12E0 m12EndL m12EndSigma m12EndC0 m12EndZ = true := by
  obtain ⟨hok, hmem, hsz⟩ := setL
  unfold m12EndDerOK
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨hok, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ⟨⟨⟨⟨⟨⟨by decide +kernel, inPA_sound kSig⟩,
    by decide +kernel⟩, by decide +kernel⟩, by decide +kernel⟩, inPA_sound kC0⟩,
    by decide +kernel⟩⟩
  · rw [hsz]
    decide +kernel
  · refine allLt_mono (fun i _ h => ?_) kGL
    rw [Bool.and_eq_true] at h ⊢
    exact ⟨inPA_sound h.1, h.2⟩
  · simp only [m12InEnum, any_pts hmem, kLt, Bool.not_false]
  · exact allLt_pts (f := fun x => !eqA 24 (compA 24 x x) (idA 24) || eqA 24 x (idA 24) ||
      !m12FpfA x) hmem (fun i hi => allN_spec kLinv i hi)

theorem m12EndCheck_eq_true :
    m12EndCheck m12S m12E0 m12EndA0 m12EndLeaves m12EndL m12EndSigma m12EndC0 m12EndZ = true := by
  unfold m12EndCheck
  simp only [e0OK, conjOK, derOK, Bool.and_self]

end CertificateChecks.KernelLC.M12End

end
