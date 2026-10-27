module

public import Certificates.Kernel.Fi22Rank.Q2Tree
public import Certificates.Kernel.Fi22Rank.Q2Kill
public import Certificates.Kernel.Fi22Rank.Q2Text
public import CFSG.Certificates.Kernel.Fi22Rank.Sound
public import CFSG.Certificates.Kernel.Fi22Rk.Side
public import CFSG.Certificates.Kernel.Spor.HexNumsSound
public import CFSG.Certificates.Kernel.Common.ForallTree
public import Certificates.Data.Fi22Twist
public import CFSG.Certificates.Kernel.Spor.RawOrbHead
public import CFSG.Certificates.Kernel.Spor.PinvSSound
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.Kernel.Spor.RawOrbGrp
public import CFSG.Open.Defs

public section

namespace CertificateChecks.KernelFi22Rank.Q2

open CFSG.KC.Enum CFSG.KC.E27Lie CFSG.KC.Fi22Rank CFSG.KC.Fi22Rk CFSG.KS CFSG.KS.E27Lie
open CFSG.KS.Fi22Rank CFSG.KC.BfsPin CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.KS.Raw
open CFSG.RankThree.Native CFSG.LocalAnalysis.GLTheoremA.H1017.Fi22TwistNative

#kc_forall_tree treeAll (fun q => ch431010tree q = true) 46
  CertificateChecks.KernelFi22Rank.Q2.ch431010tree

#kc_forall_tree sortAll (fun q => ch431010sort q = true) 46
  CertificateChecks.KernelFi22Rank.Q2.ch431010sort

#kc_forall_tree killAll (fun q => ch431010kill q = true) 46
  CertificateChecks.KernelFi22Rank.Q2.ch431010kill

#kc_forall_tree smallAll (fun c => ch431010small c = true) 57
  CertificateChecks.KernelFi22Rank.Q2.ch431010small

theorem szA : szOK 3510 12 = true := by decide

theorem hexNums_same (d : Nat) (s : String) :
    hexNums d s = CFSG.Sporadic.FischerOddCore.hexNums d s := rfl

theorem rowsOf_same (m : Nat) (a : Array Nat) :
    rowsOf m a = CFSG.LocalAnalysis.GLTheoremA.H1017.Fi24RankNative.rowsOf m a := rfl

theorem qGens_eq : qGens 2 = CFSG.LocalAnalysis.GLTheoremA.H1017.Fi24RankNative.rowsOf 3510
    (unpack (3510 * 5) 12 CertificateChecks.KernelFi22Rank.T.F) := by
  have e : qGens 2 = rowsOf 3510 (hexNums 3 qGensHex2) := rfl
  rw [e, rowsOf_same, hexNums_same,
    CFSG.KS.HexNums.hexNums_of CertificateChecks.KernelFi22Rank.T.eq
      CertificateChecks.KernelFi22Rank.T.ok]

theorem prep_of_PP {P : ℕ} (hP : PP 3510 12 P) :
    CFSG.KS.E27Lie.PRep 3510 12 (MonoidHom.id _) P (permOfArr 3510 (unpack 3510 12 P)) := by
  have hrep := (rep_permOfArr (CFSG.KS.Raw.Orb.isInvA_unpack
    (CFSG.KS.PinvS.permOK_pinvS hP.1 hP.2))).1
  refine ⟨(CFSG.KS.PF.canon_facts hP.1).2.2.1, fun i => ?_⟩
  rw [MonoidHom.id_apply, ← hrep i, CFSG.KS.Raw.Orb.unpack_get i.isLt]

theorem GI_vals : GI 0 = 1 ∧ GI 1 = 345 ∧ GI 2 = 2 ∧ GI 3 = 3 ∧ GI 4 = 292 := by
  decide +kernel

theorem q2_abelian (A : Subgroup (Equiv.Perm (Fin 3510)))
    (hA : A ≤ Subgroup.closure (permsA 3510 (qGens 2)))
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) : Nat.card A < 243 := by
  obtain ⟨hsz, hget⟩ := CFSG.KC.Fi22RkS.rows_of (m := 3510) (K := 5) (w := 12) (by norm_num) szA
    rowsT
  have hPP : ∀ k < 5, PP 3510 12 (key (GI k)) := fun k hk => (hget k hk).2
  obtain ⟨g0, -, g2, g3, -⟩ := GI_vals
  have hgPP : ∀ j < 3, PP 3510 12 (gk j) := by
    intro j hj
    interval_cases j
    · have h := hPP 0 (by norm_num)
      rwa [key, g0] at h
    · have h := hPP 2 (by norm_num)
      rwa [key, g2] at h
    · have h := hPP 3 (by norm_num)
      rwa [key, g3] at h
  have hR := permRep (G := Equiv.Perm (Fin 3510)) (n := 3510) (w := 12) (by norm_num) (by norm_num)
    (ψ := MonoidHom.id _) Function.injective_id
  have hGs : ∀ x ∈ permsA 3510 (qGens 2), ∃ i < 729,
      CFSG.KS.E27Lie.PRep 3510 12 (MonoidHom.id _) (key i) x := by
    rintro x ⟨k, hk, rfl⟩
    have hk' : k < (qGens 2).size := hk
    rw [qGens_eq, hsz] at hk'
    refine ⟨GI k, ?_, ?_⟩
    · obtain ⟨e0, e1, e2, e3, e4⟩ := GI_vals
      interval_cases k <;> simp only [e0, e1, e2, e3, e4] <;> norm_num
    · beta_reduce
      rw [qGens_eq, (hget k hk').1]
      exact prep_of_PP (hPP k hk')
  have hb := blk_all (b := 16) (n := 729) (m := 46) (by norm_num) (by norm_num) treeAll
  have hk := blk_all (b := 16) (n := 729) (m := 46) (by norm_num) (by norm_num) killAll
  exact card_lt_of_checks (n := 729) (m := 3) (nr := 57) (nb := 27) hR
    (g := fun j => permOfArr 3510 (unpack 3510 12 (gk j))) (fun j hj => prep_of_PP (hgPP j hj))
    (fun i hi => ((bAnd_iff _ _).1 (hb i hi)).1)
    (fun i hi j hj => allN_spec ((bAnd_iff _ _).1 (hb i hi)).2 j hj)
    (blk_all (by norm_num) (by norm_num : 729 ≤ 16 * 46) sortAll)
    (fun a ha => ((bAnd_iff _ _).1 (hk a ha)).1) smallAll
    (fun a ha => ((bAnd_iff _ _).1 (hk a ha)).2) rfl (by norm_num) hGs A hA hcomm

end CertificateChecks.KernelFi22Rank.Q2

end
