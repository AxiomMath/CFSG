module

public import Certificates.Kernel.Misc.Perm.J2Cent
public import Certificates.Kernel.Misc.Perm.J2Enum
public import Certificates.Kernel.Misc.Perm.J2Rel
public import CFSG.RankThree.PartTwo.Sec4.Sporadic.J2Gen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMisc.J2Cent

open CFSG.KS CFSG.Monster.B.Co2 CFSG.ComponentClassification.J2Cover
open CFSG.RankThree.PartTwo.Sec4.Sporadic.J2 CFSG.RankThree.Native
open CertificateChecks.KernelMisc.J2Fam CertificateChecks.KernelMisc.J2En
open CertificateChecks.KernelMisc.J2C3 (X)

theorem gen_eq_P : Raw.Orb.Gen 315 autStrong 2 = P := by
  unfold Raw.Orb.Gen P
  congr 1
  ext g
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨i, hi⟩, rfl⟩
    interval_cases i
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨⟨0, by norm_num⟩, rfl⟩
    · exact ⟨⟨1, by norm_num⟩, rfl⟩

theorem card_centralizer_eq (g : GJ) :
    Nat.card (Subgroup.centralizer ({g} : Set GJ)) =
      Nat.card {h : Equiv.Perm (Fin 315) //
        h ∈ Raw.Orb.Gen 315 autStrong 2 ∧ h * g.1 = g.1 * h} :=
  Nat.card_congr
    { toFun := fun c => ⟨c.1.1, (SetLike.ext_iff.1 gen_eq_P _).2 c.1.2,
        congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 c.2)⟩
      invFun := fun h => ⟨⟨h.1, (SetLike.ext_iff.1 gen_eq_P _).1 h.2.1⟩,
        Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext h.2.2)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem card_centralizer_x {g : GJ} (hg : Rep 315 xArr g.1) :
    Nat.card (Subgroup.centralizer ({g} : Set GJ)) = 36 := by
  rw [card_centralizer_eq]
  exact card_cent_x ((SetLike.ext_iff.1 gen_eq_P _).2 g.2)
    (Raw.Orb.prep_of_rep (by rw [← J2C3.hx]; exact hg))

theorem card_centralizer_v1 {g : GJ} (hg : Rep 315 v1Arr g.1) :
    Nat.card (Subgroup.centralizer ({g} : Set GJ)) = 240 := by
  rw [card_centralizer_eq]
  exact card_cent_v1 ((SetLike.ext_iff.1 gen_eq_P _).2 g.2)
    (Raw.Orb.prep_of_rep (by rw [← hv1]; exact hg))

theorem keyPts_lt : ∀ p ∈ keyPts, p < 315 := by decide

theorem gensCa_spec :
    ∀ k < gensCaArr.size, validA 315 gensCaArr[k]! = true ∧ inP gensCaArr[k]! = true :=
  fun k hk => okA_spec (okga k (ga_size ▸ hk))

theorem gensCv_spec :
    ∀ k < gensCvArr.size, validA 315 gensCvArr[k]! = true ∧ inP gensCvArr[k]! = true :=
  fun k hk => okA_spec (okgv k (gv_size ▸ hk))

theorem gensCa_comm (k : ℕ) (hk : k < gensCaArr.size) : commA gensCaArr[k]! xArr = true := by
  rw [ga_size] at hk
  have hr : R gensCaArr[k]! (GA k) := ⟨hga k hk, pGA k hk⟩
  rw [hr.commA rX]
  interval_cases k <;> quickRfl

theorem gensCv_comm (k : ℕ) (hk : k < gensCvArr.size) : commA gensCvArr[k]! v1Arr = true := by
  rw [gv_size] at hk
  have hr : R gensCvArr[k]! (GV k) := ⟨hgv k hk, pGV k hk⟩
  rw [hr.commA rV1]
  interval_cases k <;> quickRfl

theorem centralizer_x_eq {g : GJ} (hg : Rep 315 xArr g.1) :
    Subgroup.centralizer ({g} : Set GJ) = subOf gensCaArr := by
  refine (Subgroup.eq_of_le_of_card_ge ?_ ?_).symm
  · refine subOf_le_of gensCaArr gensCa_spec fun k hk => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (commute_of_commA (rep_gElt _ _ k hk) hg (gensCa_comm k hk)).eq
  · rw [card_centralizer_x hg, card_subOf keyPts_lt enumCa gensCa_spec, sizeCa]

theorem centralizer_v1_eq {g : GJ} (hg : Rep 315 v1Arr g.1) :
    Subgroup.centralizer ({g} : Set GJ) = subOf gensCvArr := by
  refine (Subgroup.eq_of_le_of_card_ge ?_ ?_).symm
  · refine subOf_le_of gensCvArr gensCv_spec fun k hk => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (commute_of_commA (rep_gElt _ _ k hk) hg (gensCv_comm k hk)).eq
  · rw [card_centralizer_v1 hg, card_subOf keyPts_lt enumCv gensCv_spec, sizeCv]

theorem centralizer_eltOf_x :
    Nat.card (Subgroup.centralizer ({eltOf xArr J2C3.okx} : Set GJ)) = 36 ∧
      Subgroup.centralizer ({eltOf xArr J2C3.okx} : Set GJ) = subOf gensCaArr :=
  ⟨card_centralizer_x (rep_eltOf _), centralizer_x_eq (rep_eltOf _)⟩

theorem centralizer_eltOf_v1 :
    Nat.card (Subgroup.centralizer ({eltOf v1Arr okv1} : Set GJ)) = 240 ∧
      Subgroup.centralizer ({eltOf v1Arr okv1} : Set GJ) = subOf gensCvArr :=
  ⟨card_centralizer_v1 (rep_eltOf _), centralizer_v1_eq (rep_eltOf _)⟩

end CertificateChecks.KernelMisc.J2Cent

end
