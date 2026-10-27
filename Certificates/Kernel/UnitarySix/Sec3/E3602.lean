module

public import Certificates.Kernel.UnitarySix.Sec3.E3602Chk
public import Certificates.Kernel.UnitarySix.Sec3.G3602
public import Certificates.Kernel.UnitarySix.Sec3.E3601
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU6.Sec3

open CFSG.KC.U6Sec3 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Enum CFSG.Monster.B.Co2.Native
open CFSG.EvenSmallLie.UnitarySix.YamadaSec3 CFSG.RankThree.Native

theorem memL_eq (k : ℕ) : ∀ L : List ℕ, memL k L = L.contains k
  | [] => rfl
  | h :: t => by
    have e : memL k (h :: t) = (Nat.beq h k || memL k t) := rfl
    rw [e, memL_eq k t, List.contains_cons]
    apply Bool.eq_iff_iff.2
    simp only [Bool.or_eq_true, Nat.beq_eq, beq_iff_eq]
    exact ⟨fun h1 => h1.elim (fun h2 => Or.inl h2.symm) Or.inr,
      fun h1 => h1.elim (fun h2 => Or.inl h2.symm) Or.inr⟩

section

variable {L : List ℕ} (hL : ∀ t ∈ L, canonK 693 10 (mask 10) (693 * 10) t = true)
include hL

theorem id_L : eqA 693 (unpack 693 10 (prodL 693 10 (mask 10) L)) (idA 693) =
    strictB (prodL 693 10 (mask 10) L) isId := by
  rw [strictB_eq, eq_id (prodL_canon hL)]
  rfl

theorem a2Orb_L : a2OrbAt (unpack 693 10 (prodL 693 10 (mask 10) L)) = a2OrbL L := by
  unfold a2OrbAt a2OrbL key3
  rw [prodL_get hL (by norm_num), prodL_get hL (by norm_num), prodL_get hL (by norm_num),
    id_L hL, memL_eq]
  rfl

theorem a1Orb_L : a1OrbAt (unpack 693 10 (prodL 693 10 (mask 10) L)) = a1OrbL L := by
  unfold a1OrbAt a1OrbL
  rw [prodL_get hL (by norm_num), id_L hL, memL_eq, memL_eq, gA14_get]

theorem sing_L : singAt (unpack 693 10 (prodL 693 10 (mask 10) L)) = singL L := by
  unfold singAt singL
  rw [prodL_get hL (i := 1) (by norm_num), prodL_get hL (ptL_lt hL (by norm_num)), memL_eq,
    memL_eq]

end

end CertificateChecks.KernelU6.Sec3
