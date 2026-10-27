module

public import Certificates.Kernel.UnitarySix.Sec3.E3601Chk
public import Certificates.Kernel.UnitarySix.Sec3.G3601
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU6.Sec3

open CFSG.KC.U6Sec3 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Enum CFSG.Monster.B.Co2.Native
open CFSG.EvenSmallLie.UnitarySix.YamadaSec3 CFSG.RankThree.Native

theorem commA_unpack {X Y : ℕ} (hX : canonK 693 10 (mask 10) (693 * 10) X = true)
    (hY : canonK 693 10 (mask 10) (693 * 10) Y = true) :
    commA (unpack 693 10 X) (unpack 693 10 Y) = commK X Y := by
  unfold commA commK
  rw [comp_unpack hX hY, comp_unpack hY hX, eq_unpack (canon_comp hX hY) (canon_comp hY hX)]

theorem ptL_lt {L : List ℕ} (hL : ∀ t ∈ L, canonK 693 10 (mask 10) (693 * 10) t = true) {p : ℕ}
    (hp : p < 693) : ptL 10 (mask 10) L p < 693 := by
  rw [← prodL_get hL hp, unpack_get hp]
  exact canon_lt (prodL_canon hL) hp

theorem commFail_unpack {L : List ℕ} (hL : ∀ t ∈ L, canonK 693 10 (mask 10) (693 * 10) t = true)
    {Y : ℕ} (hY : canonK 693 10 (mask 10) (693 * 10) Y = true) :
    commFail (unpack 693 10 (prodL 693 10 (mask 10) L)) (unpack 693 10 Y) = commFailK L Y := by
  unfold commFail commFailK
  apply Bool.eq_iff_iff.2
  simp only [List.any_eq_true]
  refine exists_congr fun p => and_congr_right fun hp => ?_
  have hp' : p < 693 := by
    simp only [commPts, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl <;> norm_num
  rw [unpack_get hp', prodL_get hL (canon_lt hY hp'), prodL_get hL hp',
    unpack_get (ptL_lt hL hp')]

theorem range_all_congr {n : ℕ} {f g : ℕ → Bool} (h : ∀ j < n, f j = g j) :
    (List.range n).all f = (List.range n).all g :=
  Bool.eq_iff_iff.2 (by
    simp only [List.all_eq_true, List.mem_range]
    exact forall₂_congr fun j hj => by rw [h j hj])

theorem range_any_congr {n : ℕ} {f g : ℕ → Bool} (h : ∀ j < n, f j = g j) :
    (List.range n).any f = (List.range n).any g :=
  Bool.eq_iff_iff.2 (by
    simp only [List.any_eq_true, List.mem_range]
    exact exists_congr fun j => and_congr_right fun hj => by rw [h j hj])

theorem O_all_comm {c : ChainData} {kS nb BP NS : ℕ} {PS PSI LR TR TRI : ℕ → ℕ}
    (h : ChainK c kS nb BP NS PS PSI LR TR TRI)
    (hP : ∀ j < c.gens.length, PermK (PS j) (PSI j) = true) {X : ℕ}
    (hX : canonK 693 10 (mask 10) (693 * 10) X = true) :
    (c.O.all fun s => commA (unpack 693 10 X) s) =
      (List.range c.gens.length).all fun j => commK X (PS j) := by
  rw [h.O_all]
  exact range_all_congr fun j hj => commA_unpack hX (PermK.canon (hP j hj))

theorem chS_P' : ∀ j < chS.gens.length, PermK (CS.S j) (CS.SI j) = true := chS_P

end CertificateChecks.KernelU6.Sec3
