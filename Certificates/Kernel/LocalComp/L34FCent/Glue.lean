module

public import Certificates.Kernel.LocalComp.L34FCent.Chk
public import Certificates.Kernel.LocalComp.L34Syl.Glue
public import CFSG.Certificates.Kernel.L34AutSound
public import Certificates.Data.Seitz77L34FCent
import CFSG.Certificates.Kernel.L34FieldSound
import CFSG.Certificates.Kernel.L34KeySound
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.L34FCent

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K CFSG.KC.L34KSnd
open CFSG.KC.L34W CFSG.KC.L34Aut CertificateChecks.KernelLC.L34X
open CertificateChecks.KernelLC.L34Cert CFSG.PSL3Four.Native
open CFSG.KC.L34Scan (pts_get')
open CFSG.KLie.CT (andB orB notB)

theorem fc_of {lo n : Nat} (h : fcent6126 lo n = true) {i : Nat} (h1 : 1344 * lo ≤ i)
    (h2 : i < 1344 * (lo + n)) :
    cen4Pt (L34SyF.T 1) (L34SyF.T 2) (L34SyF.T 3) (L34SyF.T 4) (L34R.T i) = true := by
  unfold fcent6126 at h
  simp only [sB] at h
  have h' := CFSG.KS.Raw.Orb.allN_iff.1 h (i / 1344 - lo) (by omega)
  have h'' := CFSG.KS.Raw.Orb.allN_iff.1 h' (i % 1344) (Nat.mod_lt _ (by decide))
  have e : Nat.add (Nat.mul 1344 (Nat.add lo (i / 1344 - lo))) (i % 1344) = i := by
    change 1344 * (lo + (i / 1344 - lo)) + i % 1344 = i
    omega
  rw [e] at h''
  exact h''

theorem fcAll : ∀ i < 241920,
    cen4Pt (L34SyF.T 1) (L34SyF.T 2) (L34SyF.T 3) (L34SyF.T 4) (L34R.T i) = true := by
  intro i hi
  rcases Nat.lt_or_ge i (1344 * 15) with h | h0
  · exact fc_of kc0 (by omega) (by omega)
  rcases Nat.lt_or_ge i (1344 * 30) with h | h1
  · exact fc_of kc1 (by omega) (by omega)
  rcases Nat.lt_or_ge i (1344 * 45) with h | h2
  · exact fc_of kc2 (by omega) (by omega)
  rcases Nat.lt_or_ge i (1344 * 60) with h | h3
  · exact fc_of kc3 (by omega) (by omega)
  rcases Nat.lt_or_ge i (1344 * 75) with h | h4
  · exact fc_of kc4 (by omega) (by omega)
  rcases Nat.lt_or_ge i (1344 * 90) with h | h5
  · exact fc_of kc5 (by omega) (by omega)
  rcases Nat.lt_or_ge i (1344 * 105) with h | h6
  · exact fc_of kc6 (by omega) (by omega)
  rcases Nat.lt_or_ge i (1344 * 120) with h | h7
  · exact fc_of kc7 (by omega) (by omega)
  rcases Nat.lt_or_ge i (1344 * 135) with h | h8
  · exact fc_of kc8 (by omega) (by omega)
  rcases Nat.lt_or_ge i (1344 * 150) with h | h9
  · exact fc_of kc9 (by omega) (by omega)
  rcases Nat.lt_or_ge i (1344 * 165) with h | h10
  · exact fc_of kc10 (by omega) (by omega)
  · exact fc_of kc11 (by omega) (by omega)

theorem memF {x : Nat} (h : notB (notInK 16 L34SyF.T x) = true) :
    memTab (pts 42 6 16 L34SyF.T) (unpack 42 6 x) = true := by
  obtain ⟨q, hq, e⟩ := (CFSG.KS.PEnum.found_indexOf_iff _ _).1 (CFSG.KC.L34Field.found_of_notIn h)
  unfold memTab
  rw [anyBelow_iff]
  exact ⟨q, hq, by rw [e]; exact beq_self_eq_true _⟩

theorem notFoundF {y : Nat} (hy : Cn y) (h : notInK 16 L34SyF.T y = true) :
    found (indexOf (pts 42 6 16 L34SyF.T)) (pts 42 6 16 L34SyF.T) (unpack 42 6 y) = false := by
  have hn := notIn_sound (x := unpack 42 6 y) rfl hy (fun i hi => L34Syl.cF hi) h
  cases hf : found (indexOf (pts 42 6 16 L34SyF.T)) (pts 42 6 16 L34SyF.T) (unpack 42 6 y)
  · rfl
  · obtain ⟨k, hk, e⟩ := (CFSG.KS.PEnum.found_indexOf_iff _ _).1 hf
    unfold notInOK at hn
    have h1 := CFSG.KS.BfsReplay.allBelow_iff.1 hn k hk
    rw [e, beq_self_eq_true] at h1
    exact absurd h1 (by decide)

theorem cen4_sound {x : Nat} (hx : Cn x)
    (h : cen4Pt (L34SyF.T 1) (L34SyF.T 2) (L34SyF.T 3) (L34SyF.T 4) x = true) :
    (!(allBelow (pts 42 6 16 L34SyF.T).size fun i =>
        comp 42 (pts 42 6 16 L34SyF.T)[i]! (unpack 42 6 x) ==
          comp 42 (unpack 42 6 x) (pts 42 6 16 L34SyF.T)[i]!) ||
      memTab (pts 42 6 16 L34SyF.T) (unpack 42 6 x)) = true := by
  unfold cen4Pt at h
  rcases orB_iff.1 h with h | h
  · have hf : ∀ j < 16, commPt 42 6 x (L34SyF.T j) = false →
        (allBelow (pts 42 6 16 L34SyF.T).size fun i =>
          comp 42 (pts 42 6 16 L34SyF.T)[i]! (unpack 42 6 x) ==
            comp 42 (unpack 42 6 x) (pts 42 6 16 L34SyF.T)[i]!) = false := by
      intro j hj hcf
      rw [← Bool.not_eq_true, CFSG.KS.BfsReplay.allBelow_iff]
      intro hall
      have h1 := hall j (by rw [size_pts]; exact hj)
      rw [pts_get' hj, beq_iff_eq] at h1
      rw [(commPt_iff hx (L34Syl.cF hj)).2 h1.symm] at hcf
      exact Bool.noConfusion hcf
    rcases andB_false (notB_iff.1 h) with h | h
    · rw [hf 1 (by decide) h]
      rfl
    rcases andB_false h with h | h
    · rw [hf 2 (by decide) h]
      rfl
    rcases andB_false h with h | h
    · rw [hf 3 (by decide) h]
      rfl
    · rw [hf 4 (by decide) h]
      rfl
  · rw [memF h, Bool.or_true]

theorem fcent_true :
    Certificates.Seitz77L34.l34FCentCheck (enumBFS 42 gTabs 241920).tabs = true := by
  have cr3 : Cn (RP 2) := cnRP (by decide)
  unfold Certificates.Seitz77L34.l34FCentCheck
  dsimp only
  rw [L34Syl.hF.2.1, hR.1, L34Syl.hF.1]
  simp only [Bool.and_eq_true, Bool.true_and]
  refine ⟨⟨by rw [size_pts]; rfl, ?_⟩, ?_⟩
  · unfold centScanOK
    rw [size_pts 42 6 241920, CFSG.KS.BfsReplay.allBelow_iff]
    intro k hk
    beta_reduce
    rw [pts_get' hk]
    exact cen4_sound (pinR.canon k hk) (fcAll k hk)
  · have h := kconj
    unfold fconj6126 at h
    rw [sB] at h
    obtain ⟨a, ha, e⟩ := CFSG.KC.L34Key.exists_of_notB_allN' h
    have hin : notInK 16 L34SyF.T (pcomp 42 6 (mask 6) (pcomp 42 6 (mask 6) (RP 2) (L34SyF.T a))
        (RP 2)) = true := by
      cases hv : notInK 16 L34SyF.T (pcomp 42 6 (mask 6) (pcomp 42 6 (mask 6) (RP 2) (L34SyF.T a))
        (RP 2))
      · rw [hv] at e
        exact absurd e (by decide)
      · rfl
    rw [size_pts, anyBelow_iff]
    refine ⟨a, ha, ?_⟩
    rw [pts_get' ha, r3_eq, conjTab, comp_unpack' cr3 (L34Syl.cF ha),
      comp_unpack' (canonK_pcomp cr3 (L34Syl.cF ha)) cr3,
      notFoundF (canonK_pcomp (canonK_pcomp cr3 (L34Syl.cF ha)) cr3) hin]
    rfl

end CertificateChecks.KernelLC.L34FCent

end
