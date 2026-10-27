module

public import Certificates.Kernel.SuzFuse17320.Checks
public import Certificates.Kernel.SuzA17321.Facts
public import Certificates.Kernel.SuzThree13637.BindFacts

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSuzFuse17320

open CFSG.KS hiding levels
open CFSG.KC.Enum CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.KC.B3S3K CFSG.KC.BfsPin
open CertificateChecks.KernelSpor CertificateChecks.KernelSuzPump CertificateChecks.KernelSuzA17321
open CFSG.HardMathSupport.Dickson.I271.TabSuzFuse
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT
open CFSG.Monster.B.Co2.Native CFSG.RankThree.Native CFSG.Monster.B.Fischer CFSG.Monster.B.Mathieu
  CFSG.Certificates.Native CFSG.RankThree.PartOne CFSG.Sporadic.SuzOddCore
open CFSG.Monster.B.Co2 (allLt_iff)

theorem hXB : xBArr (levels ()) = unpack 1782 11 XB := by
  unfold xBArr
  exact rebuild_eq rbB

theorem pDK {i : Nat} (hi : i < 5) : permB 1782 11 (DK i) = true := Orb.allN_iff.1 pD i hi

theorem hDK {i : Nat} (hi : i < 5) : (dGens ())[i]! = unpack 1782 11 (DK i) :=
  (CFSG.KD.SuzThree13637.d_gen hi).1

theorem ppDK {i : Nat} (hi : i < 5) (e : Nat) : PP 1782 11 (pw3 (DK i) e) :=
  pp_ppow hw (pp_of_permB hw (pDK hi)) e

theorem powDK {i : Nat} (hi : i < 5) (e : Nat) :
    powArr 1782 (dGens ())[i]! e = unpack 1782 11 (pw3 (DK i) e) := by
  rw [hDK hi]
  exact pow_unpack hw (pDK hi) e

theorem ppEP (k : Nat) : PP 1782 11 (EP k) :=
  (ppDK (by norm_num) _).mul ((ppDK (by norm_num) _).mul ((ppDK (by norm_num) _).mul
    ((ppDK (by norm_num) _).mul (ppDK (by norm_num) _))))

theorem E_get {k : Nat} (hk : k < 243) : (dElts ())[k]! = unpack 1782 11 (EP k) := by
  rw [dElts, getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]
  unfold dProd
  rw [powDK (by norm_num : 0 < 5), powDK (by norm_num : 1 < 5), powDK (by norm_num : 2 < 5),
    powDK (by norm_num : 3 < 5), powDK (by norm_num : 4 < 5),
    compA_PP (ppDK (by norm_num) _) (ppDK (by norm_num) _),
    compA_PP (ppDK (by norm_num) _) ((ppDK (by norm_num) _).mul (ppDK (by norm_num) _)),
    compA_PP (ppDK (by norm_num) _)
      ((ppDK (by norm_num) _).mul ((ppDK (by norm_num) _).mul (ppDK (by norm_num) _))),
    compA_PP (ppDK (by norm_num) _) ((ppDK (by norm_num) _).mul
      ((ppDK (by norm_num) _).mul ((ppDK (by norm_num) _).mul (ppDK (by norm_num) _))))]
  rfl

theorem ord_of {G : Nat} (hp : permB 1782 11 G = true)
    (h3 : Nat.beq (pw3 G 3) (pidn 1782 11) = true) (h1 : Nat.beq G (pidn 1782 11) = false) :
    eqA 1782 (powArr 1782 (unpack 1782 11 G) 3) (idA 1782) = true ∧
      eqA 1782 (unpack 1782 11 G) (idA 1782) = false := by
  rw [pow_unpack hw hp, idA_eq hw, eqA_PP (pp_ppow hw (pp_of_permB hw hp) 3) (PP.id hw),
    eqA_PP (pp_of_permB hw hp) (PP.id hw)]
  exact ⟨h3, h1⟩

theorem fuseK_all {k : Nat} (hk : k < 243) (h0 : k ≠ 0) : fuseK k = true := by
  have hs : ∀ j < 11, fuseS j = true := by
    intro j hj
    interval_cases j
    exacts [s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10]
  obtain ⟨j, i, hi, rfl⟩ : ∃ j i, i < 22 ∧ k = 22 * j + i + 1 :=
    ⟨(k - 1) / 22, (k - 1) % 22, Nat.mod_lt _ (by norm_num), by omega⟩
  exact Orb.allN_iff.1 (hs j (by omega)) i hi

theorem tgt_eq (k : Nat) : (if (fuseCls[k]! == 0) = true then xAArr (levels ()) else
    xBArr (levels ())) = unpack 1782 11 (tgt k) ∧ PP 1782 11 (tgt k) := by
  unfold tgt
  cases (fuseCls[k]! == 0)
  · simp only [Bool.false_eq_true, ↓reduceIte, cond_false]
    exact ⟨hXB, pp_of_permB hw pXB⟩
  · simp only [↓reduceIte, cond_true]
    exact ⟨KernelSuzA17321.hX, pp_of_permB hw KernelSuzA17321.pX⟩

theorem fuse_k {k : Nat} (hk : k < 243) (h0 : k ≠ 0) :
    (validA 1782 (fuseArr (levels ()) k) && inP (levels ()) (fuseArr (levels ()) k) &&
      eqA 1782 (conjA 1782 (fuseArr (levels ()) k) (dElts ())[k]!)
        (if (fuseCls[k]! == 0) = true then xAArr (levels ()) else xBArr (levels ()))) = true := by
  have hf := fuseK_all hk h0
  unfold fuseK fuseKT at hf
  simp only [Bool.and_eq_true] at hf
  obtain ⟨hr, ⟨hp, hs⟩, hc⟩ := hf
  have hH : fuseArr (levels ()) k = unpack 1782 11 (HK k) := by
    unfold fuseArr
    exact rebuild_eq hr
  obtain ⟨ht, hpt⟩ := tgt_eq k
  have hpe := permB_of_pp (ppEP k)
  rw [hH, E_get hk, ht, conj_unpack hw hp hpe,
    eqA_PP (pp_of_permB hw (permB_pcomp hw hp (permB_pcomp hw hpe (permB_pinvS hw hp)))) hpt,
    validA_of hp, inP_of hs]
  simpa using hc

theorem fuse_ok : fuseCheck () = true := by
  obtain ⟨a3, a1⟩ := ord_of KernelSuzA17321.pX ordX.1 ordX.2.1
  obtain ⟨b3, b1⟩ := ord_of pXB ordX.2.2.1 ordX.2.2.2
  have vA : validA 1782 (unpack 1782 11 XP) = true := validA_of KernelSuzA17321.pX
  have vB : validA 1782 (unpack 1782 11 XB) = true := validA_of pXB
  have iA : inP (levels ()) (unpack 1782 11 XP) = true := inP_of siftX.1
  have iB : inP (levels ()) (unpack 1782 11 XB) = true := inP_of siftX.2
  have z1 : (fuseTuples.size == 243) = true := by decide +kernel
  have z2 : (fuseCls.size == 243) = true := by decide +kernel
  have hall : allLt 243 (fun k => k == 0 || (validA 1782 (fuseArr (levels ()) k) &&
      inP (levels ()) (fuseArr (levels ()) k) &&
      eqA 1782 (conjA 1782 (fuseArr (levels ()) k) (dElts ())[k]!)
        (if (fuseCls[k]! == 0) = true then xAArr (levels ()) else xBArr (levels ())))) = true := by
    rw [allLt_iff]
    intro k hk
    by_cases h0 : k = 0
    · subst h0
      rfl
    · rw [fuse_k hk h0, Bool.or_true]
  unfold fuseCheck
  simp only []
  rw [hall]
  rw [KernelSuzA17321.hX, hXB]
  simp only [vA, vB, iA, iB, a3, a1, b3, b1, z1, z2, Bool.not_false, Bool.and_self, Bool.and_true]

end CertificateChecks.KernelSuzFuse17320

end
