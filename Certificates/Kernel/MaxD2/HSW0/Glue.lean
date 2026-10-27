module

public import Certificates.Kernel.MaxD2.HSW0.Checks
public import Certificates.Kernel.MaxD2.HSP.Glue
public import Certificates.Kernel.MaxD2.HSU.Checks
public import Certificates.Kernel.MaxD2.HSOver.Glue
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMaxD2.HSW0

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MaxD2 CFSG.KS.PEnum CFSG.KS.Row
open CFSG.PSL3Four.Native Certificates.MaxD2Perm Certificates.MaxD2Heis Certificates.HSOver

section

variable {D D' : Data}

theorem wT_congr (h1 : D.n = D'.n) (h2 : D.gT = D'.gT) : wT D = wT D' := by
  unfold wT giT
  rw [h1, h2]

theorem checkInv_congr (h1 : D.n = D'.n) (h2 : D.gT = D'.gT) : checkInv D = checkInv D' := by
  unfold checkInv giT
  rw [h1, h2]

theorem nGens_congr (h1 : D.n = D'.n) (h2 : D.gT = D'.gT) (h3 : D.nW = D'.nW) :
    nGens D = nGens D' := by
  unfold nGens
  rw [wT_congr h1 h2, h3]

theorem nEnum_congr (h1 : D.n = D'.n) (h2 : D.gT = D'.gT) (h3 : D.nW = D'.nW)
    (h4 : D.nOrder = D'.nOrder) : nEnum D = nEnum D' := by
  unfold nEnum
  rw [nGens_congr h1 h2 h3, h1, h4]

theorem checkN_congr (h1 : D.n = D'.n) (h2 : D.gT = D'.gT) (h3 : D.nW = D'.nW)
    (h4 : D.nOrder = D'.nOrder) : checkN D = checkN D' := by
  unfold checkN
  rw [nEnum_congr h1 h2 h3 h4, nGens_congr h1 h2 h3, h1, h4]

end

theorem pn : hsFiveDataP.n = hsOverDataP.n := rfl
theorem pg : hsFiveDataP.gT = hsOverDataP.gT := rfl
theorem pnw : hsFiveDataP.nW = hsOverDataP.nW := rfl
theorem pno : hsFiveDataP.nOrder = hsOverDataP.nOrder := rfl
theorem rn : hsFiveDataR.n = hsOverDataR.n := rfl
theorem rg : hsFiveDataR.gT = hsOverDataR.gT := rfl

theorem hD : hsFiveDataP.n = 100 := rfl

theorem wP_u {wd : List Int} {r : Nat}
    (h : wordEqK 100 7 (mask 7) (pidn 100 7) HSP.GP HSP.GPI 2 wd r = true) :
    wT hsFiveDataP wd = unpack 100 7 r := by
  rw [wT_congr pn pg]
  exact c_wT_u HSP.hypsC h

theorem wR_u {wd : List Int} {r : Nat}
    (h : wordEqK 100 7 (mask 7) (pidn 100 7) HSOver.GP HSOver.GPI 3 wd r = true) :
    wT hsFiveDataR wd = unpack 100 7 r := by
  rw [wT_congr rn rg]
  have H := HSOver.hypsM
  unfold wT giT
  rw [H.hDn]
  exact wordT_u ⟨H.hGs, H.hGb⟩ H.hGp h

theorem k_all : wordEqK 100 7 (mask 7) (pidn 100 7) HSOver.GP HSOver.GPI 3 hsOverW0W (PW 0) = true ∧
    permOK 100 7 (mask 7) (100 * 7) (PW 0) (PW 1) = true ∧
    wordEqK 100 7 (mask 7) (pidn 100 7) HSP.GP HSP.GPI 2 hsOverGAW (PW 2) = true ∧
    canonK 100 7 (mask 7) (100 * 7) (PW 2) = true ∧
    wordEqK 100 7 (mask 7) (pidn 100 7) HSP.GP HSP.GPI 2 hsOverGBW (PW 3) = true ∧
    permOK 100 7 (mask 7) (100 * 7) (PW 3) (PW 4) = true ∧
    wordEqK 100 7 (mask 7) (pidn 100 7) HSP.GP HSP.GPI 2 hsFiveDataP.uW (HSU.RE.G 0) = true ∧
    wordEqK 100 7 (mask 7) (pidn 100 7) HSP.GP HSP.GPI 2 hsFiveDataP.vW (HSU.RE.G 1) = true ∧
    allN 2 (fun i => conjInK 100 7 HSU.RE.cnt HSU.RE.T (PW 0) (PW 1) (HSU.RE.G i) (r32 HW i)) =
      true ∧
    notInK HSP.NE.cnt HSP.NE.T (PW 0) = true ∧
    allN 4 (fun j => conjInK 100 7 HSP.NE.cnt HSP.NE.T (PW 0) (PW 1) (HSP.NE.G j)
      (r32 HW (Nat.add 2 j))) = true ∧
    Nat.blt (r32 HW 6) HSP.NE.cnt = true ∧
    conjInK 100 7 HSP.NE.cnt HSP.NE.T (PW 4) xK (HSP.NE.T (r32 HW 6)) (r32 HW 7) = true := by
  have h := k_w0
  unfold w0K at h
  simp only [Bool.and_eq_true] at h
  exact h

theorem hn : szOK 100 7 = true := HSP.k_sz

theorem cw : Cn 100 7 (PW 0) ∧ Cn 100 7 (PW 1) := perm_canon k_all.2.1 hn

theorem cgb : Cn 100 7 (PW 3) ∧ Cn 100 7 (PW 4) := perm_canon k_all.2.2.2.2.2.1 hn

theorem cga : Cn 100 7 (PW 2) := k_all.2.2.2.1

theorem w_eq : wT hsFiveDataR hsOverW0W = unpack 100 7 (PW 0) := wR_u k_all.1

theorem wi_eq : invTab 100 (unpack 100 7 (PW 0)) = unpack 100 7 (PW 1) := inv_u k_all.2.1

theorem ga_eq : wT hsFiveDataP hsOverGAW = unpack 100 7 (PW 2) := wP_u k_all.2.2.1

theorem gb_eq : wT hsFiveDataP hsOverGBW = unpack 100 7 (PW 3) := wP_u k_all.2.2.2.2.1

theorem gbi_eq : invTab 100 (unpack 100 7 (PW 3)) = unpack 100 7 (PW 4) :=
  inv_u k_all.2.2.2.2.2.1

theorem rk : HSU.RE.k = 2 := rfl

theorem r_gens : GensOK 100 7 HSU.RE.k HSU.RE.G (rGens hsFiveDataP) := by
  refine ⟨by simp [rGens, rWs, rk], fun j hj => ⟨?_, (PK.allN_iff.1 HSU.k_rgc) j hj⟩⟩
  rw [rk] at hj
  unfold rGens
  rw [map_get _ (by simpa [rWs] using hj)]
  interval_cases j
  · exact wP_u k_all.2.2.2.2.2.2.1
  · exact wP_u k_all.2.2.2.2.2.2.2.1

theorem hrE : hrEnum hsFiveDataP = penumRec 100 7 HSU.RE.cnt HSU.RE.T HSU.RE.PL ∧
    enumOK 100 (rGens hsFiveDataP) (penumRec 100 7 HSU.RE.cnt HSU.RE.T HSU.RE.PL) = true := by
  unfold hrEnum
  rw [hD]
  exact penumK_left_sound hn r_gens HSU.k_rh
    (fun i hi => penumSl_spec HSU.k_rsl i (Nat.zero_le _) (by exact hi) hi)

theorem checkHR_P : checkHR hsFiveDataP = true := by
  obtain ⟨e, hok⟩ := hrE
  unfold checkHR
  rw [e, hD, hok, rec_size]
  rfl

theorem nE : nEnum hsFiveDataP = penumRec 100 7 HSP.NE.cnt HSP.NE.T HSP.NE.PL := by
  rw [nEnum_congr pn pg pnw pno]
  exact (c_nEnum_eq HSP.hypsC).1

theorem ng_get {j : Nat} (hj : j < 4) : (nGens hsFiveDataP)[j]! = unpack 100 7 (HSP.NE.G j) := by
  rw [nGens_congr pn pg pnw]
  exact c_ng_get HSP.hypsC hj

theorem ng_size : (nGens hsFiveDataP).size = 4 := by
  rw [nGens_congr pn pg pnw]
  exact (c_ngens HSP.hypsC).1

theorem ng_canon {j : Nat} (hj : j < 4) : Cn 100 7 (HSP.NE.G j) := (HSP.hypsC.hNG j hj).2

theorem nt_canon {i : Nat} (hi : i < HSP.NE.cnt) : Cn 100 7 (HSP.NE.T i) :=
  c_nt_canon HSP.hypsC hi

theorem found_rec {cnt : Nat} {T PL : Nat → Nat} {X h : Nat} (hh : h < cnt) (e : T h = X) :
    found (indexOf (penumRec 100 7 cnt T PL).tabs) (penumRec 100 7 cnt T PL).tabs
      (unpack 100 7 X) = true := by
  rw [found_iff]
  exact ⟨h, by rw [rec_size]; exact hh, by rw [rec_get hh, e]⟩

theorem conjIn_spec {cnt : Nat} {T : Nat → Nat} {g gi x h : Nat}
    (hk : conjInK 100 7 cnt T g gi x h = true) :
    h < cnt ∧ T h = pcomp 100 7 (mask 7) (pcomp 100 7 (mask 7) g x) gi := by
  unfold conjInK at hk
  obtain ⟨h1, h2⟩ := band_e hk
  exact ⟨Nat.blt_eq.mp h1, Nat.eq_of_beq_eq_true h2⟩

theorem conj_found {cnt : Nat} {T PL : Nat → Nat} {g gi x h : Nat} (hg : Cn 100 7 g)
    (hgi : Cn 100 7 gi) (hx : Cn 100 7 x) (hk : conjInK 100 7 cnt T g gi x h = true) :
    found (indexOf (penumRec 100 7 cnt T PL).tabs) (penumRec 100 7 cnt T PL).tabs
      (conjTab 100 (unpack 100 7 g) (unpack 100 7 gi) (unpack 100 7 x)) = true := by
  unfold conjTab
  rw [comp_u hg hx, comp_u (cc hg hx) hgi]
  exact found_rec (conjIn_spec hk).1 (conjIn_spec hk).2

theorem hs_w0 : Certificates.OverD2Perm.checkW0 hsFiveDataP hsFiveDataR hsOverW0W hsOverGAW
    hsOverGBW = true := by
  obtain ⟨-, -, -, -, -, -, -, -, hR, hW, hN, hl, hm⟩ := k_all
  obtain ⟨c0, c1⟩ := cw
  obtain ⟨c3, c4⟩ := cgb
  unfold Certificates.OverD2Perm.checkW0
  simp only [Bool.and_eq_true, and_assoc]
  rw [nE, hrE.1, w_eq, ga_eq, gb_eq, hD, wi_eq, gbi_eq]
  refine ⟨?_, ?_, ?_, checkHR_P, rfl, by simp [size_u], ?_, by simp [size_u], ?_, ?_, ?_, ?_, ?_⟩
  · rw [checkInv_congr pn pg]
    exact c_checkInv_of HSP.hypsC
  · rw [checkInv_congr rn rg]
    exact checkInv_of HSOver.hypsM
  · rw [checkN_congr pn pg pnw pno]
    exact c_checkN_of HSP.hypsC
  · rw [inv_comp k_all.2.1, id_u hn]
    exact beq_self_eq_true _
  · rw [inv_comp k_all.2.2.2.2.2.1, id_u hn]
    exact beq_self_eq_true _
  · have hr : (rGens hsFiveDataP).size = 2 := r_gens.1
    rw [hr, allBelow_iff']
    intro j hj
    rw [(r_gens.2 j hj).1]
    exact conj_found c0 c1 (r_gens.2 j hj).2 ((PK.allN_iff.1 hR) j hj)
  · rw [Bool.not_eq_true', Bool.eq_false_iff, ne_eq, found_iff]
    rintro ⟨i, hi, e⟩
    rw [rec_size] at hi
    rw [rec_get hi] at e
    have h := (PK.allN_iff.1 hW) i hi
    beta_reduce at h
    rw [u_inj (nt_canon hi) c0 e, Nat.beq_refl] at h
    exact absurd h (by decide)
  · rw [ng_size, allBelow_iff']
    intro j hj
    rw [ng_get hj]
    exact conj_found c0 c1 (ng_canon hj) ((PK.allN_iff.1 hN) j hj)
  · rw [anyBelow_iff]
    have hl' : r32 HW 6 < HSP.NE.cnt := Nat.blt_eq.mp hl
    refine ⟨r32 HW 6, by rw [rec_size]; exact hl', ?_⟩
    rw [rec_get hl']
    have e : conjTab 100 (unpack 100 7 (PW 0)) (unpack 100 7 (PW 1)) (unpack 100 7 (PW 2)) =
        unpack 100 7 xK := by
      unfold conjTab xK
      rw [comp_u c0 cga, comp_u (cc c0 cga) c1]
    rw [e, comp_u c4 (nt_canon hl')]
    have cx : Cn 100 7 xK := by
      unfold xK
      exact cc (cc c0 cga) c1
    rw [comp_u (cc c4 (nt_canon hl')) cx]
    exact found_rec (conjIn_spec hm).1 (conjIn_spec hm).2

end CertificateChecks.KernelMaxD2.HSW0

end
