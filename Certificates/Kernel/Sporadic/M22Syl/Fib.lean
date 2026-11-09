module

public import Certificates.Kernel.Sporadic.M22Syl.Checks
public import Certificates.Data.Kernel.Spor.PCountW
public import CFSG.Certificates.Kernel.Spor.MSylowSound
public meta import Certificates.Kernel.Sporadic.M22Syl.Checks
meta import Certificates.Kernel.SporSch.Mathieu.Gen
meta import Certificates.Kernel.Sporadic.RawGen
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelSpor.M22Syl

open CFSG.KS.SporSch.MOCG

meta def fibW (wd : List Int) : Array Nat := evalW 22 #[tAM, tBM] wd

meta def tCA1M : Array Nat := fibW [-2, 1, -2, 1, 2, 1, 2, 1, -2, 1, -2]
meta def tCA1iM : Array Nat := invA tCA1M
meta def tCA2M : Array Nat := fibW [-2, 1, 2, 2, 1, 2, 1, -2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2]
meta def tCA2iM : Array Nat := invA tCA2M
meta def tFR2M : Array Nat := fibW [-2, 1, -2, 1, -2, 1, -2, 1, 2, 2]
meta def tFR3M : Array Nat := fibW [2, 1, 2, 1, 2, 1, 2, 1, 2, 2]

meta def fibDFS (r : Array Nat) (fuel : Nat) : List Nat := Id.run do
  let mut s1 : List Nat := [CFSG.KS.RawGen.pack 5 r]
  let mut s2 : List (Array Nat) := [r]
  for _ in [0:fuel] do
    match s2 with
    | [] => pure ()
    | e :: rest =>
      s2 := rest
      for g in [tCA1M, tCA2M] do
        let z := comp g (comp e (invA g))
        let p := CFSG.KS.RawGen.pack 5 z
        if !s1.contains p then
          s1 := p :: s1
          s2 := z :: s2
  return s1

meta def YfM : Array Nat :=
  (fibDFS tBM 384 ++ fibDFS tBiM 384 ++ fibDFS tFR2M 384 ++ fibDFS tFR3M 384).toArray

end CertificateChecks.KernelSpor.M22Syl

#ks_perm CertificateChecks.KernelSpor.M22Syl.CA1 5 CertificateChecks.KernelSpor.M22Syl.tCA1M
#ks_perm CertificateChecks.KernelSpor.M22Syl.CA1i 5 CertificateChecks.KernelSpor.M22Syl.tCA1iM
#ks_perm CertificateChecks.KernelSpor.M22Syl.CA2 5 CertificateChecks.KernelSpor.M22Syl.tCA2M
#ks_perm CertificateChecks.KernelSpor.M22Syl.CA2i 5 CertificateChecks.KernelSpor.M22Syl.tCA2iM
#ks_perm CertificateChecks.KernelSpor.M22Syl.FR2 5 CertificateChecks.KernelSpor.M22Syl.tFR2M
#ks_perm CertificateChecks.KernelSpor.M22Syl.FR3 5 CertificateChecks.KernelSpor.M22Syl.tFR3M
#kss_list CertificateChecks.KernelSpor.M22Syl.Yf CertificateChecks.KernelSpor.M22Syl.YfM

namespace CertificateChecks.KernelSpor.M22Syl

open CFSG.KC.Enum CFSG.KS CFSG.KS.PCnt CFSG.KS.MSyl CFSG.Sporadic.Schreier

set_option maxRecDepth 100000

@[expose] noncomputable def fibOrb (r : Nat) : List Nat := conjDFS 22 5 (mask 5) CA1 CA1i CA2 CA2i r 384

theorem yf_eq : (fibOrb B ++ fibOrb Bi ++ fibOrb FR2 ++ fibOrb FR3 == Yf) = true := by
  quickRfl

theorem yf_dist : distB Yf = true := by
  quickRfl

@[expose] noncomputable def survL (L : List Nat) : Bool :=
  allL (fun y => Nat.beq (survF 22 5 (mask 5) I A Ai B ZB m22Derivs ES PT 11 6 4 y) 0) L

@[expose] noncomputable def yfP (k : Nat) : List Nat := (Yf.drop (192 * k)).take 192

theorem yf_s0 : survL (yfP 0) = true := by quickRfl
theorem yf_s1 : survL (yfP 1) = true := by quickRfl
theorem yf_s2 : survL (yfP 2) = true := by quickRfl
theorem yf_s3 : survL (yfP 3) = true := by quickRfl
theorem yf_s4 : survL (yfP 4) = true := by quickRfl
theorem yf_s5 : survL (yfP 5) = true := by quickRfl
theorem yf_s6 : survL (yfP 6) = true := by quickRfl
theorem yf_s7 : survL (yfP 7) = true := by quickRfl

theorem yf_len : Yf.length = 1536 := by decide +kernel

theorem yf_surv : ∀ y ∈ Yf, survF 22 5 (mask 5) I A Ai B ZB m22Derivs ES PT 11 6 4 y = 0 := by
  have hs : ∀ k < 8, survL (yfP k) = true := by
    intro k hk
    interval_cases k
    exacts [yf_s0, yf_s1, yf_s2, yf_s3, yf_s4, yf_s5, yf_s6, yf_s7]
  intro y hy
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hy
  have hi' : i < 1536 := yf_len ▸ hi
  have hm : Yf[i] ∈ yfP (i / 192) := by
    rw [yfP, List.mem_take_iff_getElem]
    refine ⟨i % 192, ?_, ?_⟩
    · simp only [List.length_drop, yf_len]
      omega
    · simp only [List.getElem_drop]
      congr 1
      omega
  exact Nat.eq_of_beq_eq_true ((allL_iff _ _).1 (hs (i / 192) (by omega)) _ hm)

end CertificateChecks.KernelSpor.M22Syl

end
