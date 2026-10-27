
module

public import Certificates.Kernel.Misc.Perm.J2C3C
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.J2C3

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Misc.ArrEnum
open CFSG.RankThree.PartTwo.Sec4.Sporadic.J2 CFSG.ComponentClassification.J2Cover
open CFSG.Certificates.Native CFSG.Monster.B.Co2.Native CFSG.RankThree.Native
open CFSG.Monster.B.Mathieu

@[expose] noncomputable def B (j : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) X (fun i _ => Nat.rec (motive := fun _ => ℕ) Y
    (fun i' _ => Nat.rec (motive := fun _ => ℕ) (cm X Y) (fun _ _ => cm X (cm Y Y)) i') i) j

theorem hb (j : ℕ) (hj : 1 ≤ j) (hj3 : j ≤ 3) : bArr j = unpack 315 9 (B j) := by
  interval_cases j
  · have e : bArr 1 = yArr := by simp [bArr]
    rw [e]
    exact hy
  · have e : bArr 2 = compA 315 xArr yArr := by simp [bArr]
    rw [e, hx, hy, comp_unpack hw pX pY]
    rfl
  · have e : bArr 3 = compA 315 xArr (compA 315 yArr yArr) := by simp [bArr]
    rw [e, hx, hy, comp_unpack hw pY pY, comp_unpack hw pX (by quickRfl)]
    rfl

theorem inE_of (j a c t : ℕ) (hj : 1 ≤ j) (hj3 : j ≤ 3) (ha : a < 3) (hc : c < 3)
    (hpB : permB 315 9 (B j) = true) (ht : permB 315 9 t = true)
    (hq : permB 315 9 (cm (ppow 315 9 (mask 9) (pidn 315 9) Z a)
      (ppow 315 9 (mask 9) (pidn 315 9) (B j) c)) = true)
    (h : Nat.beq t (cm (ppow 315 9 (mask 9) (pidn 315 9) Z a)
      (ppow 315 9 (mask 9) (pidn 315 9) (B j) c)) = true) :
    inE j (unpack 315 9 t) = true := by
  unfold inE
  rw [List.any_eq_true]
  refine ⟨a, List.mem_range.2 ha, ?_⟩
  rw [List.any_eq_true]
  refine ⟨c, List.mem_range.2 hc, ?_⟩
  rw [hz, hb j hj hj3, pow_unpack hw pZ, pow_unpack hw hpB, comp_unpack hw (by
    interval_cases a <;> quickRfl) (by interval_cases j <;> interval_cases c <;> quickRfl)]
  exact eqT ht hq h

theorem dwit (j k a c a' c' : ℕ) (hj : 1 ≤ j) (hj3 : j ≤ 3) (hk : k < 216) (ha : a < 3)
    (hc : c < 3) (ha' : a' < 3) (hc' : c' < 3) (hpB : permB 315 9 (B j) = true)
    (h1 : permB 315 9 (cm (pinvS 315 9 (mask 9) (NPP.F k)) (cm Z (NPP.F k))) = true)
    (h2 : permB 315 9 (cm (pinvS 315 9 (mask 9) (NPP.F k)) (cm X (NPP.F k))) = true)
    (q1 : permB 315 9 (cm (ppow 315 9 (mask 9) (pidn 315 9) Z a)
      (ppow 315 9 (mask 9) (pidn 315 9) (B j) c)) = true)
    (q2 : permB 315 9 (cm (ppow 315 9 (mask 9) (pidn 315 9) Z a')
      (ppow 315 9 (mask 9) (pidn 315 9) (B j) c')) = true)
    (e1 : Nat.beq (cm (pinvS 315 9 (mask 9) (NPP.F k)) (cm Z (NPP.F k)))
      (cm (ppow 315 9 (mask 9) (pidn 315 9) Z a) (ppow 315 9 (mask 9) (pidn 315 9) (B j) c)) =
        true)
    (e2 : Nat.beq (cm (pinvS 315 9 (mask 9) (NPP.F k)) (cm X (NPP.F k)))
      (cm (ppow 315 9 (mask 9) (pidn 315 9) Z a') (ppow 315 9 (mask 9) (pidn 315 9) (B j) c')) =
        true) :
    ((List.range cNP.pts.size).any fun k =>
      inE j (conjInvA 315 cNP.pts[k]! zArr) && inE j (conjInvA 315 cNP.pts[k]! xArr)) = true := by
  rw [List.any_eq_true]
  refine ⟨k, List.mem_range.2 (by rw [np.1]; exact hk), ?_⟩
  rw [np.2.1 k hk, hz, hx, conjInv_unpack hw (npp k hk) pZ, conjInv_unpack hw (npp k hk) pX,
    Bool.and_eq_true]
  exact ⟨inE_of j a c _ hj hj3 ha hc hpB h1 q1 e1, inE_of j a' c' _ hj hj3 ha' hc' hpB h2 q2 e2⟩

theorem delta : chkDelta = true := by
  unfold chkDelta
  rw [List.all_eq_true]
  intro j hj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl
  · exact dwit 1 12 1 0 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl)
      (by quickRfl) (by quickRfl) (by quickRfl)
  · exact dwit 2 33 2 0 0 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl)
      (by quickRfl) (by quickRfl) (by quickRfl)
  · exact dwit 3 3 2 0 0 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl)
      (by quickRfl) (by quickRfl) (by quickRfl)

theorem enum : chkEnum = true := by
  unfold chkEnum
  rw [enumP3, enumCz, enumNZ, enumNP, p3.1, cz.1, nz.1, np.1]
  rfl

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
  CFSG.RankThree.PartTwo.Sec4.Sporadic CFSG.RankThree.PartTwo.Sec4.Sporadic.J2
  CFSG.ComponentClassification.J2Cover CFSG.Certificates.Native CFSG.Monster.B.Co2.Native in
open Certificates in
theorem facts : j2Check3 = true := by
  unfold j2Check3
  rw [elts, enum, cls, npAll, fix, six, tenAll, sets, delta]
  rfl

end CertificateChecks.KernelMisc.J2C3

end
