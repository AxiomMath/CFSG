module

public import Certificates.Kernel.HS100.KGData
public import Certificates.Kernel.HS100.Chain
public import CFSG.Certificates.Kernel.BfsPinAlg
public import CFSG.Certificates.Kernel.BfsPinSetSound
public import CFSG.Certificates.Kernel.Misc.ArrBind
public import CFSG.Certificates.Kernel.Spor.PcompFacts
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHS100

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin
open CFSG.KC.Misc.ArrEnum (arrBind_sound)
open CFSG.RankThree.Native CFSG.Monster.B.Co2.Native
open CFSG.ComponentClassification.CatFC.KGHS3

theorem kg_hw : szOK 100 7 = true := by quickRfl

theorem pp_kgMul {p q : ℕ} (hp : PP 100 7 p) (hq : PP 100 7 q) : PP 100 7 (kgMul p q) :=
  hp.mul hq

theorem pp_kgInv {p : ℕ} (hp : PP 100 7 p) : PP 100 7 (kgInv p) := hp.inv

theorem kgPw_succ (p k : ℕ) : kgPw p (k + 1) = kgMul p (kgPw p k) :=
  CFSG.KS.PF.strictN_eqP (kgPw p k) (fun q => pcomp 100 7 (mask 7) p q)

theorem pp_kgPw {p : ℕ} (hp : PP 100 7 p) : ∀ k, PP 100 7 (kgPw p k)
  | 0 => PP.id kg_hw
  | k + 1 => by
    rw [kgPw_succ]
    exact pp_kgMul hp (pp_kgPw hp k)

theorem mul_unpack {p q : ℕ} (hp : PP 100 7 p) (hq : PP 100 7 q) :
    compA 100 (unpack 100 7 p) (unpack 100 7 q) = unpack 100 7 (kgMul p q) := compA_PP hp hq

theorem inv_unpack {p : ℕ} (hp : PP 100 7 p) :
    invCand 100 (unpack 100 7 p) = unpack 100 7 (kgInv p) := invCand_PP hp

theorem pw_unpack {p : ℕ} (hp : PP 100 7 p) :
    ∀ k, hsPwArr (unpack 100 7 p) k = unpack 100 7 (kgPw p k)
  | 0 => by
    rw [hsPwArr.eq_1]
    exact idA_eq kg_hw
  | k + 1 => by
    rw [hsPwArr.eq_2, pw_unpack hp k, mul_unpack hp (pp_kgPw hp k), kgPw_succ]

theorem eq_unpack {p q : ℕ} (hp : PP 100 7 p) (hq : PP 100 7 q) :
    eqA 100 (unpack 100 7 p) (unpack 100 7 q) = Nat.beq p q := eqA_PP hp hq

theorem id_unpack : idA 100 = unpack 100 7 (pidn 100 7) := idA_eq kg_hw

theorem kgC3_sound {A B G : Array ℕ} {a b g : ℕ} (hA : A = unpack 100 7 a)
    (hB : B = unpack 100 7 b) (hG : G = unpack 100 7 g) (pa : PP 100 7 a) (pb : PP 100 7 b)
    (pg : PP 100 7 g) (h : kgC3 a b g = true) :
    eqA 100 (hsPwArr A 3) (idA 100) = true ∧ eqA 100 (hsPwArr B 3) (idA 100) = true ∧
      eqA 100 A (idA 100) = false ∧ eqA 100 (compA 100 A B) (compA 100 B A) = true ∧
      eqA 100 (compA 100 G A) (compA 100 B G) = true ∧
      eqA 100 (compA 100 G B) (compA 100 (compA 100 A B) G) = true := by
  subst hA hB hG
  have pi := PP.id kg_hw
  rw [kgC3.eq_1] at h
  simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  rw [pw_unpack pa, pw_unpack pb, id_unpack, eq_unpack (pp_kgPw pa 3) pi,
    eq_unpack (pp_kgPw pb 3) pi, eq_unpack pa pi, mul_unpack pa pb, mul_unpack pb pa,
    mul_unpack pg pa, mul_unpack pb pg, mul_unpack pg pb, mul_unpack (pp_kgMul pa pb) pg,
    eq_unpack (pp_kgMul pa pb) (pp_kgMul pb pa), eq_unpack (pp_kgMul pg pa) (pp_kgMul pb pg),
    eq_unpack (pp_kgMul pg pb) (pp_kgMul (pp_kgMul pa pb) pg)]
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem kgC5_sound {X Y G Z : Array ℕ} {x y g : ℕ} (hX : X = unpack 100 7 x)
    (hY : Y = unpack 100 7 y) (hG : G = unpack 100 7 g)
    (hZ : Z = compA 100 (compA 100 (compA 100 X Y) (invCand 100 X)) (invCand 100 Y))
    (px : PP 100 7 x) (py : PP 100 7 y) (pg : PP 100 7 g) (h : kgC5 x y g (kgZ x y) = true) :
    eqA 100 (hsPwArr Z 5) (idA 100) = true ∧ eqA 100 Z (idA 100) = false ∧
      eqA 100 (compA 100 X Z) (compA 100 Z X) = true ∧
      eqA 100 (compA 100 Y Z) (compA 100 Z Y) = true ∧
      eqA 100 (compA 100 G Z) (compA 100 (hsPwArr Z 2) G) = true := by
  subst hX hY hG
  have pi := PP.id kg_hw
  have pz : PP 100 7 (kgZ x y) :=
    pp_kgMul (pp_kgMul (pp_kgMul px py) (pp_kgInv px)) (pp_kgInv py)
  have hz : Z = unpack 100 7 (kgZ x y) := by
    rw [hZ, mul_unpack px py, inv_unpack px, inv_unpack py,
      mul_unpack (pp_kgMul px py) (pp_kgInv px),
      mul_unpack (pp_kgMul (pp_kgMul px py) (pp_kgInv px)) (pp_kgInv py), kgZ.eq_1]
  subst hz
  rw [kgC5.eq_1] at h
  simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  rw [pw_unpack pz, pw_unpack pz, id_unpack, eq_unpack (pp_kgPw pz 5) pi, eq_unpack pz pi,
    mul_unpack px pz, mul_unpack pz px, mul_unpack py pz, mul_unpack pz py, mul_unpack pg pz,
    mul_unpack (pp_kgPw pz 2) pg, eq_unpack (pp_kgMul px pz) (pp_kgMul pz px),
    eq_unpack (pp_kgMul py pz) (pp_kgMul pz py),
    eq_unpack (pp_kgMul pg pz) (pp_kgMul (pp_kgPw pz 2) pg)]
  exact ⟨h1, h2, h3, h4, h5⟩

theorem kgC11_sound {U H : Array ℕ} {u h : ℕ} (hU : U = unpack 100 7 u)
    (hH : H = unpack 100 7 h) (pu : PP 100 7 u) (ph : PP 100 7 h) (hc : kgC11 u h = true) :
    eqA 100 (hsPwArr U 11) (idA 100) = true ∧ eqA 100 U (idA 100) = false ∧
      eqA 100 (compA 100 H U) (compA 100 (hsPwArr U 3) H) = true := by
  subst hU hH
  have pi := PP.id kg_hw
  rw [kgC11.eq_1] at hc
  simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hc
  obtain ⟨⟨h1, h2⟩, h3⟩ := hc
  rw [pw_unpack pu, pw_unpack pu, id_unpack, eq_unpack (pp_kgPw pu 11) pi, eq_unpack pu pi,
    mul_unpack ph pu, mul_unpack (pp_kgPw pu 3) ph,
    eq_unpack (pp_kgMul ph pu) (pp_kgMul (pp_kgPw pu 3) ph)]
  exact ⟨h1, h2, h3⟩

theorem kg_binds : hsA3Arr = unpack 100 7 (KG 0) ∧ hsB3Arr = unpack 100 7 (KG 1) ∧
    hsG3Arr = unpack 100 7 (KG 2) ∧ hsX5Arr = unpack 100 7 (KG 3) ∧
    hsY5Arr = unpack 100 7 (KG 4) ∧ hsG5Arr = unpack 100 7 (KG 5) ∧
    hsU11Arr = unpack 100 7 (KG 6) ∧ hsH11Arr = unpack 100 7 (KG 7) := by
  have h := KG.bind
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨arrBind_sound h0, arrBind_sound h1, arrBind_sound h2, arrBind_sound h3,
    arrBind_sound h4, arrBind_sound h5, arrBind_sound h6, arrBind_sound h7⟩

theorem kg_pp {j : ℕ} (hj : j < 8) : PP 100 7 (KG j) :=
  PP_of_permOK kg_hw (allN_spec KG.perm j hj)

theorem kg_valid {t : Array ℕ} {j : ℕ} (hj : j < 8) (ht : t = unpack 100 7 (KG j)) :
    validA 100 t = true := by
  rw [ht]
  exact validA_unpack (allN_spec KG.perm j hj)

theorem kg_sift {t : Array ℕ} {j : ℕ} (hj : j < 8) (ht : t = unpack 100 7 (KG j)) :
    siftA 100 hs100PLevels hs100BaseArr 0 t = true :=
  siftP ht (allN_spec KG.sift j hj)

theorem kg_checks : KGHS3HSChecks := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := kg_binds
  have c3 := kgC3_sound b0 b1 b2 (kg_pp (by norm_num)) (kg_pp (by norm_num))
    (kg_pp (by norm_num)) KG.c3
  have c5 := kgC5_sound (Z := hsZArr) b3 b4 b5 rfl (kg_pp (by norm_num)) (kg_pp (by norm_num))
    (kg_pp (by norm_num)) KG.c5
  have c11 := kgC11_sound b6 b7 (kg_pp (by norm_num)) (kg_pp (by norm_num)) KG.c11
  exact ⟨kg_valid (by norm_num) b0, kg_valid (by norm_num) b1, kg_valid (by norm_num) b2,
    kg_valid (by norm_num) b3, kg_valid (by norm_num) b4, kg_valid (by norm_num) b5,
    kg_valid (by norm_num) b6, kg_valid (by norm_num) b7,
    kg_sift (by norm_num) b0, kg_sift (by norm_num) b1, kg_sift (by norm_num) b2,
    kg_sift (by norm_num) b3, kg_sift (by norm_num) b4, kg_sift (by norm_num) b5,
    kg_sift (by norm_num) b6, kg_sift (by norm_num) b7,
    c3.1, c3.2.1, c3.2.2.1, c3.2.2.2.1, c3.2.2.2.2.1, c3.2.2.2.2.2,
    c5.1, c5.2.1, c5.2.2.1, c5.2.2.2.1, c5.2.2.2.2,
    c11.1, c11.2.1, c11.2.2⟩

end CertificateChecks.KernelHS100

end
