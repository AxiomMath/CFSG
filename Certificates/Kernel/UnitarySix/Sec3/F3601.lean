module

public import Certificates.Kernel.UnitarySix.Sec3.E3601
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU6.Sec3

open CFSG.KC.U6Sec3 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Enum CFSG.Monster.B.Co2.Native
open CFSG.EvenSmallLie.UnitarySix.YamadaSec3 CFSG.RankThree.Native CFSG.KC.U6
open CFSG.Monster.B.Co2 (allLt_iff)

theorem kA1G : ((List.range chA1.gens.length).all fun j =>
      sfZ (pcomp 693 10 (mask 10) (CA1.S j) (CA1.S j))) &&
    ((List.range chA1.gens.length).all fun j => (List.range chA1.gens.length).all fun i =>
      sfZ (pcomp 693 10 (mask 10) (pcomp 693 10 (mask 10) (CA1.S j) (CA1.S i))
        (pcomp 693 10 (mask 10) (CA1.SI j) (CA1.SI i)))) = true := by
  decide +kernel

theorem kLabA3 : ((List.range chA3.gens.length).all fun j => allN 693 fun p =>
    pg 10 (mask 10) sec3LabA3 (pg 10 (mask 10) (CA3.S j) p) == pg 10 (mask 10) sec3LabA3 p) =
      true := by
  decide +kernel

theorem labA3_k : labA3Check = true := by
  unfold labA3Check
  rw [Bool.and_eq_true]
  refine ⟨by decide, ?_⟩
  rw [chA3_K.O_all]
  refine List.all_eq_true.2 fun j hj => allLt_iff.2 fun p hp => ?_
  have hj' := PermK.canon (chA3_P j (List.mem_range.1 hj))
  rw [unpack_get hp, labA3_eq _ (canon_lt hj' hp), labA3_eq _ hp]
  exact allN_spec (List.all_eq_true.1 kLabA3 j hj) p hp

@[expose] noncomputable def natK (w : List ℤ) : ℕ :=
  w.foldr (fun c acc => pcomp 693 10 (mask 10) (letK U.LT (c.natAbs - 1)) acc) (pidn 693 10)

theorem kLetC : ∀ k < 46, canonK 693 10 (mask 10) (693 * 10) (letK U.LT k) = true := by
  decide +kernel

theorem natK_spec : ∀ w : List ℤ, (∀ c ∈ w, c.natAbs - 1 < 46) →
    w.foldr (fun c acc => compA 693 (CFSG.EvenSmallLie.UnitarySix.letterArrs[c.natAbs - 1]!) acc)
      (idA 693) = unpack 693 10 (natK w) ∧ canonK 693 10 (mask 10) (693 * 10) (natK w) = true
  | [], _ => ⟨hidA, hid⟩
  | c :: w, hw => by
    obtain ⟨ih, ihc⟩ := natK_spec w fun d hd => hw d (List.mem_cons_of_mem _ hd)
    have hc := hw c List.mem_cons_self
    have e : natK (c :: w) = pcomp 693 10 (mask 10) (letK U.LT (c.natAbs - 1)) (natK w) := rfl
    rw [List.foldr_cons, ih, letterArrs_eq _ hc, comp_unpack (kLetC _ hc) ihc, e]
    exact ⟨rfl, canon_comp (kLetC _ hc) ihc⟩

theorem kUA : (CFSG.EvenSmallLie.UnitarySix.aWords.all fun w => strictB (natK w) fun X =>
    PermK X (pinvS 693 10 (mask 10) X) && sfA2 X) = true := by
  decide +kernel

end CertificateChecks.KernelU6.Sec3
