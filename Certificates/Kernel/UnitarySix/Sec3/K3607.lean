module

public import Certificates.Kernel.UnitarySix.Sec3.K3607Chk
public import Certificates.Kernel.UnitarySix.Sec3.K3606
public import Certificates.Kernel.UnitarySix.Sec3.Chains3607
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU6.Sec3

open CFSG.KC.U6Sec3 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Enum CFSG.Monster.B.Co2.Native
open CFSG.EvenSmallLie.UnitarySix.YamadaSec3 CFSG.RankThree.Native
open CFSG.EvenSmallLie.UnitarySix.YamadaHAut (dTab sTab d2Tab dsTab d2sTab)
open CFSG.Monster.B.Co2 (allLt_iff)

theorem dArr_unpack {q : ℕ} (hq : q < 6) : dArr[q]! = unpack 693 10 (dPK q) := by
  apply Array.ext (by rw [dArr_size q hq]; simp [unpack])
  intro x h1 _
  have hx : x < 693 := by rwa [dArr_size q hq] at h1
  rw [← getElem!_pos _ x h1, dK_eq hq hx, ← dPK_get q hq x hx, ← unpack_get hx,
    getElem!_pos _ x (by simp [unpack, hx])]

theorem cntK_eq (f : ℕ → Bool) : ∀ n, cntK n f = (List.range n).countP f
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.countP_append, ← cntK_eq f n]
    have e : cntK (n + 1) f = Nat.add (cntK n f) (Bool.rec 0 1 (f n)) := rfl
    rw [e]
    cases h : f n <;> simp [h]

theorem c11a_L {L : List ℕ} (hL : ∀ t ∈ L, canonK 693 10 (mask 10) (693 * 10) t = true) :
    c11aAt (unpack 693 10 (prodL 693 10 (mask 10) L)) = c11aL L := by
  have h1 : fixCnt (unpack 693 10 (prodL 693 10 (mask 10) L)) =
      cntK 693 (fun p => ptL 10 (mask 10) L p == p) := by
    rw [cntK_eq]
    exact List.countP_congr fun p hp => by rw [prodL_get hL (List.mem_range.1 hp)]
  have h2 : fixCnt gz = cntK 693 (fun p => pg 10 (mask 10) (sec3G 14) p == p) := by
    rw [cntK_eq, gz, hG 14 (by norm_num)]
    exact List.countP_congr fun p hp => by rw [unpack_get (List.mem_range.1 hp)]
  have h3 : eqA 693 (unpack 693 10 (prodL 693 10 (mask 10) L)) gz =
      Nat.beq (prodL 693 10 (mask 10) L) (sec3G 14) := by
    rw [gz, hG 14 (by norm_num), eq_unpack (prodL_canon hL) (hc 14 (by norm_num))]
  unfold c11aAt c11aL
  rw [h1, h2, h3, strictB_eq]

theorem a4Comm_eq {Y : ℕ} (hY : canonK 693 10 (mask 10) (693 * 10) Y = true) :
    (chA4.O.all fun g => eqA 693 (compA 693 (unpack 693 10 Y) g) (compA 693 g (unpack 693 10 Y)))
      = a4CommK Y := by
  rw [chA4_K.O_all]
  have hl : chA4.gens.length = 4 := rfl
  rw [hl]
  unfold a4CommK
  refine range_all_congr fun j hj => ?_
  have hj' := PermK.canon (chA4_P j (hl ▸ hj))
  rw [comp_unpack hY hj', comp_unpack hj' hY, eq_unpack (canon_comp hY hj') (canon_comp hj' hY)]

theorem c6_L {L : List ℕ} (hL : ∀ t ∈ L, canonK 693 10 (mask 10) (693 * 10) t = true) :
    c6At (unpack 693 10 (prodL 693 10 (mask 10) L)) = c6L L := by
  have hX := prodL_canon hL
  unfold c6At c6L
  rw [strictB_eq, List.all_cons, List.all_cons, List.all_nil, Bool.and_true,
    dArr_unpack (by norm_num : 0 < 6), dArr_unpack (by norm_num : 3 < 6),
    comp_unpack hX (dPK_canon 0 (by norm_num)), comp_unpack hX (dPK_canon 3 (by norm_num)),
    a4Comm_eq (canon_comp hX (dPK_canon 0 (by norm_num))),
    a4Comm_eq (canon_comp hX (dPK_canon 3 (by norm_num))), eq_id hX]
  rfl

theorem dselK_eq : ∀ q < 6, dselK q (pinvS 693 10 (mask 10) (dPK 0))
    (pinvS 693 10 (mask 10) (dPK 1)) (pinvS 693 10 (mask 10) (dPK 2))
    (pinvS 693 10 (mask 10) (dPK 3)) (pinvS 693 10 (mask 10) (dPK 4))
    (pinvS 693 10 (mask 10) (dPK 5)) = pinvS 693 10 (mask 10) (dPK q) := by
  intro q hq
  interval_cases q <;> rfl

theorem fixF_lt : ∀ p ∈ fixF, p < 693 := by decide

theorem c7Pt_eq {X XI Z ZI G GI q : ℕ} (hX : PermK X XI = true) (hZ : PermK Z ZI = true)
    (hG : PermK G GI = true) (hq : q < 6) :
    c7PtW (unpack 693 10 X) (unpack 693 10 Z) dArr[q]! (unpack 693 10 G) =
      c7PtK X XI Z ZI (pinvS 693 10 (mask 10) (dPK q)) q G GI := by
  have hd := dPK_perm q hq
  have cX := PermK.canon hX
  have cXI := PermK.canon_inv hX
  have cZ := PermK.canon hZ
  have cZI := PermK.canon_inv hZ
  have cG := PermK.canon hG
  have cGI := PermK.canon_inv hG
  have cD := PermK.canon hd
  have cDI := PermK.canon_inv hd
  unfold c7PtW c7PtK
  rw [dArr_unpack hq, PermK.inv hX, PermK.inv hZ, PermK.inv hG, PermK.inv hd,
    comp_unpack cX cZ, comp_unpack (canon_comp cX cZ) cD,
    comp_unpack (canon_comp (canon_comp cX cZ) cD) cG, comp_unpack cDI cZI,
    comp_unpack (canon_comp cDI cZI) cXI, comp_unpack (canon_comp (canon_comp cDI cZI) cXI) cGI,
    comp_unpack (canon_comp (canon_comp (canon_comp cX cZ) cD) cG)
      (canon_comp (canon_comp (canon_comp cDI cZI) cXI) cGI)]
  apply Bool.eq_iff_iff.2
  simp only [List.any_eq_true]
  refine exists_congr fun p => and_congr_right fun hp => ?_
  have hp' := fixF_lt p hp
  have b1 := canon_lt cGI hp'
  have b2 := canon_lt cXI b1
  have b3 := canon_lt cZI b2
  have b4 := canon_lt cDI b3
  have b5 := canon_lt cG b4
  have b6 := canon_lt cD b5
  have b7 := canon_lt cZ b6
  rw [unpack_get hp', comp_get (canon_comp (canon_comp (canon_comp cX cZ) cD) cG)
      (canon_comp (canon_comp (canon_comp cDI cZI) cXI) cGI) hp',
    comp_get (canon_comp (canon_comp cDI cZI) cXI) cGI hp', comp_get (canon_comp cDI cZI) cXI b1,
    comp_get cDI cZI b2, comp_get (canon_comp (canon_comp cX cZ) cD) cG b4,
    comp_get (canon_comp cX cZ) cD b5, comp_get cX cZ b6, dPK_get q hq _ b5]

theorem conjInv_w {w : List ℕ} (hw : ∀ k ∈ w, k < 18) (hp : PermK (wK w) (wKI w) = true)
    {X : ℕ} (hX : canonK 693 10 (mask 10) (693 * 10) X = true) :
    conjInvA 693 (wA w) (unpack 693 10 X) =
      unpack 693 10 (pcomp 693 10 (mask 10) (wKI w) (pcomp 693 10 (mask 10) X (wK w))) := by
  rw [(wK_spec hw).1, conjInv_unpack hp hX]

theorem conjInv_canon {g gi X : ℕ} (hp : PermK g gi = true)
    (hX : canonK 693 10 (mask 10) (693 * 10) X = true) :
    canonK 693 10 (mask 10) (693 * 10) (pcomp 693 10 (mask 10) gi (pcomp 693 10 (mask 10) X g)) =
      true :=
  canon_comp (PermK.canon_inv hp) (canon_comp hX (PermK.canon hp))

end CertificateChecks.KernelU6.Sec3
