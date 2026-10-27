module

public import Certificates.Kernel.Misc.TitsJ47.Data
public import Certificates.Kernel.SporSch.Tits.Central2263
public import CFSG.Certificates.Kernel.Misc.TitsPiSound
public import CFSG.Certificates.Kernel.Spor.JoinSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMisc.TitsJ47

open CFSG.Quasithin.RuType.J47 CFSG.Quasithin.RuRank3
open CFSG.Sporadic.Schreier.Tits CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates
  CFSG.Certificates.Native CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.Join
open CertificateChecks.KernelSpor.Tits2264 CertificateChecks.KernelSporSch
open CertificateChecks.KernelSporSch.TitsAction CertificateChecks.KernelMisc

abbrev C (p : Nat) : Prop := canonK 1755 11 (mask 11) (1755 * 11) p = true

theorem cpc {p q : Nat} (hp : C p) (hq : C q) : C (pc p q) := CFSG.KC.BfsPin.canonK_pcomp hp hq

theorem mul_eq {p q : Nat} (hp : C p) (hq : C q) :
    compA 1755 (unpack 1755 11 p) (unpack 1755 11 q) = unpack 1755 11 (pc p q) :=
  CFSG.KC.BfsPin.compA_unpack hp hq

theorem eq_eq {p q : Nat} (hp : C p) (hq : C q) :
    eqA 1755 (unpack 1755 11 p) (unpack 1755 11 q) = Nat.beq p q :=
  CFSG.KC.BfsPin.eqA_unpack hp hq

theorem get_eq {p : Nat} (hp : C p) (i : Nat) : (unpack 1755 11 p)[i]! = pt p i := by
  unfold C canonK at hp
  simp only [bAnd_iff] at hp
  exact TitsCommon.unpack_get0 hp.2.1

theorem beqN (a b : Nat) : (a == b) = Nat.beq a b := by
  cases h : Nat.beq a b
  · rw [beq_eq_false_iff_ne]
    intro e
    rw [e, Nat.beq_refl] at h
    exact absurd h (by decide)
  · rw [beq_iff_eq]
    exact Nat.eq_of_beq_eq_true h

theorem all_congr {n : Nat} {f g : Nat → Bool} (h : ∀ k < n, f k = g k) :
    (List.range n).all f = (List.range n).all g := by
  rw [Bool.eq_iff_iff]
  simp only [List.all_eq_true, List.mem_range]
  exact ⟨fun H k hk => (h k hk) ▸ H k hk, fun H k hk => (h k hk).symm ▸ H k hk⟩

theorem any_congr {n : Nat} {f g : Nat → Bool} (h : ∀ k < n, f k = g k) :
    (List.range n).any f = (List.range n).any g := by
  rw [Bool.eq_iff_iff]
  simp only [List.any_eq_true, List.mem_range]
  exact ⟨fun ⟨k, hk, H⟩ => ⟨k, hk, (h k hk) ▸ H⟩, fun ⟨k, hk, H⟩ => ⟨k, hk, (h k hk).symm ▸ H⟩⟩

theorem lp {v k : Nat} (hv : v < 2925) (hk : k < 3) : titsLinePtArr[3 * v + k]! = lpK (3 * v + k) :=
  lp_get (by omega)

theorem lp_lt {v k : Nat} (hv : v < 2925) (hk : k < 3) : lpK (3 * v + k) < 1755 := by
  obtain ⟨h1, h2, h3⟩ := facts.2.2.2.1 v hv
  rw [← lp hv hk]
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl
  · rw [Nat.add_zero]
    omega
  · omega
  · omega

theorem onLine_eq (p : Nat) {v : Nat} (hv : v < 2925) : onLine p v = onLineK p v := by
  unfold onLine onLineK
  rw [lp_get (i := 3 * v) (by omega), lp_get (i := 3 * v + 1) (by omega),
    lp_get (i := 3 * v + 2) (by omega), beqN, beqN, beqN]

theorem lineFixed_eq {P v : Nat} (hP : C P) (hv : v < 2925) :
    lineFixedA (unpack 1755 11 P) v = lineFixedK P v := by
  unfold lineFixedA lineFixedK
  refine all_congr fun k hk => ?_
  simp only []
  rw [lp_get (i := 3 * v + k) (by omega), lp_get (i := 3 * v) (by omega),
    lp_get (i := 3 * v + 1) (by omega), lp_get (i := 3 * v + 2) (by omega), get_eq hP, beqN, beqN,
    beqN]

theorem lineMaps_eq {P v w : Nat} (hP : C P) (hv : v < 2925) (hw : w < 2925) :
    lineMapsA (unpack 1755 11 P) v w = lineMapsK P v w := by
  unfold lineMapsA lineMapsK
  refine all_congr fun k hk => ?_
  rw [lp hv hk, get_eq hP, onLine_eq _ hw]

theorem inS_eq {P : Nat} (hP : C P) :
    CFSG.Quasithin.RuType.J47.inS (unpack 1755 11 P) = inSK P := by
  unfold CFSG.Quasithin.RuType.J47.inS inSK
  rw [get_eq hP, beqN, lineFixed_eq hP (by norm_num)]

theorem fix_eq {P : Nat} (hP : C P) :
    ptFixCount (unpack 1755 11 P) = (List.range 1755).countP fun x => Nat.beq (pt P x) x := by
  unfold ptFixCount
  refine List.countP_congr fun x _ => ?_
  rw [get_eq hP, beqN]

theorem idA_eq : idA 1755 = unpack 1755 11 idK := TitsCentral.id_eq

theorem cid : C idK := TitsCentral.canId

theorem pow_eq {x : Nat} (hx : C x) :
    ∀ k, powArr 1755 (unpack 1755 11 x) k = unpack 1755 11 (powK x k) ∧ C (powK x k)
  | 0 => ⟨idA_eq, cid⟩
  | k + 1 => by
    obtain ⟨h1, h2⟩ := pow_eq hx k
    refine ⟨?_, cpc hx h2⟩
    change compA 1755 _ (powArr 1755 _ k) = _
    rw [h1, mul_eq hx h2]
    rfl

theorem arr_eq {k : Nat} (hk : k < 7) : j47Arr k = unpack 1755 11 (X k) := by
  have h := hexTable_join_sound (d := 3) (n₀ := 1755) (w := 11) (c := 1) (N := 7) J47T.all
    j47_join k hk
  rw [← J47T.eq] at h
  exact h

theorem permX {k : Nat} (hk : k < 7) : permC (X k) = true := allN_spec perms.1 k hk

theorem cX {k : Nat} (hk : k < 7) : C (X k) := (permC_spec (permX hk)).2.1

theorem cXi {k : Nat} (hk : k < 7) : C (pi (X k)) := (permC_spec (permX hk)).2.2

theorem inv_eq {k : Nat} (hk : k < 7) : invA (unpack 1755 11 (X k)) = unpack 1755 11 (pi (X k)) :=
  (invEqK_sound (permC_spec (permX hk)).1).1

theorem cZ : C TitsZ := TitsCommon.canonZ

theorem pi_eq : CFSG.Quasithin.titsPiArr = unpack 1755 11 TitsPi.P :=
  CFSG.KC.TitsPi.cmpL_sound TitsPi.bind

theorem cPi : C TitsPi.P := (permC_spec perms.2.2).2.1

theorem conj_eq {k : Nat} (hk : k < 7) {x : Nat} (hx : C x) :
    conjA (unpack 1755 11 (X k)) (unpack 1755 11 x) = unpack 1755 11 (cj (X k) x) := by
  unfold conjA mulA
  rw [inv_eq hk, mul_eq (cX hk) hx, mul_eq (cpc (cX hk) hx) (cXi hk)]
  rfl

theorem conjInv_eq {k : Nat} (hk : k < 7) {x : Nat} (hx : C x) :
    conjInvA (unpack 1755 11 (X k)) (unpack 1755 11 x) = unpack 1755 11 (cji (X k) x) := by
  unfold conjInvA mulA
  rw [inv_eq hk, mul_eq (cXi hk) hx, mul_eq (cpc (cXi hk) hx) (cX hk)]
  rfl

theorem cj' : C jK := allN_spec canon 0 (by norm_num)
theorem cv1 : C v1K := allN_spec canon 1 (by norm_num)
theorem cv2 : C v2K := allN_spec canon 2 (by norm_num)
theorem cu : C uK := allN_spec canon 3 (by norm_num)
theorem ct : C tK := allN_spec canon 4 (by norm_num)
theorem czp : C zpK := allN_spec canon 5 (by norm_num)
theorem cjp : C jpK := allN_spec canon 6 (by norm_num)
theorem cw1 : C w1K := allN_spec canon 7 (by norm_num)
theorem ctp : C tpK := allN_spec canon 8 (by norm_num)

theorem a1_eq : a1Arr = unpack 1755 11 (X 0) := arr_eq (by norm_num)
theorem f2_eq : f2Arr = unpack 1755 11 (X 1) := arr_eq (by norm_num)
theorem e_eq : eArr = unpack 1755 11 (X 2) := arr_eq (by norm_num)
theorem c_eq : cArr = unpack 1755 11 (X 3) := arr_eq (by norm_num)
theorem b0_eq : b0Arr = unpack 1755 11 (X 4) := arr_eq (by norm_num)
theorem aa_eq : aaArr = unpack 1755 11 (X 5) := arr_eq (by norm_num)
theorem ab_eq : abArr = unpack 1755 11 (X 6) := arr_eq (by norm_num)

theorem j_eq : jArr = unpack 1755 11 jK := by
  rw [jArr, a1_eq, e_eq, conj_eq (by norm_num) (cX (by norm_num))]
  rfl

theorem v1_eq : v1Arr = unpack 1755 11 v1K := by
  rw [v1Arr, a1_eq, TitsCommon.z_eq, conjInv_eq (by norm_num) cZ]
  rfl

theorem v2_eq : v2Arr = unpack 1755 11 v2K := by
  rw [v2Arr, e_eq, v1_eq, conj_eq (by norm_num) cv1]
  rfl

theorem u_eq : uArr = unpack 1755 11 uK := by
  rw [uArr, a1_eq, v2_eq, conj_eq (by norm_num) cv2]
  rfl

theorem t_eq : tArr = unpack 1755 11 tK := by
  rw [tArr, u_eq, TitsCommon.z_eq]
  unfold mulA
  rw [mul_eq cu cZ]
  rfl

theorem zp_eq : zpArr = unpack 1755 11 zpK := by
  rw [zpArr, f2_eq, v1_eq, conjInv_eq (by norm_num) cv1]
  rfl

theorem jp_eq : jpArr = unpack 1755 11 jpK := by
  rw [jpArr, f2_eq, e_eq, conjInv_eq (by norm_num) (cX (by norm_num))]
  rfl

theorem w1_eq : w1Arr = unpack 1755 11 w1K := by
  rw [w1Arr, a1_eq, t_eq, conjInv_eq (by norm_num) ct]
  rfl

theorem tp_eq : tpArr = unpack 1755 11 tpK := by
  rw [tpArr, f2_eq, w1_eq, conjInv_eq (by norm_num) cw1]
  rfl

theorem prodI_eq {p : Nat} : prodI p = unpack 1755 11 (prodIK p) := by
  unfold prodI mulA
  rw [aa_eq, ab_eq, (pow_eq (cX (by norm_num)) _).1, (pow_eq (cX (by norm_num)) _).1,
    mul_eq (pow_eq (cX (by norm_num)) _).2 (pow_eq (cX (by norm_num)) _).2]
  rfl

theorem cI {p : Nat} (hp : p < 16) : C (prodIK p) := allN_spec canonI.1 p hp

end CertificateChecks.KernelMisc.TitsJ47

end
