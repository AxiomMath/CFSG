module

public import CFSG.Quasithin.Vol2.KGFactG2RuInputs
public meta import CFSG.Quasithin.Vol2.KGFactG2RuInputs
public import Certificates.Certificate2247
public import Certificates.Certificate2250
import Certificates.Kernel.SporSch.Ru.G2Ru7163K
import Certificates.Kernel.SporSch.Ru.G2Ru7164
import Certificates.Kernel.SporSch.Ru.E64
import CFSG.Quasithin.Vol2.KGFactG2RuBasic
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.Spor.RawOrbHead
import Mathlib.Tactic.IntervalCases
import CFSG.Certificates.Kernel.Spor.RawOrbGrp

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.G2Ru7163

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.RuE64 CertificateChecks.KernelSporSch.RuE64
  CertificateChecks.KernelSporSch.G2Ru7164 CFSG.Quasithin.H13.Ch4.G2Ru CFSG.Sporadic.RuSchreier
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native


theorem all_range {n : Nat} {f : Nat → Bool} (h : (List.range n).all f = true) {i : Nat}
    (hi : i < n) : f i = true :=
  List.all_eq_true.1 h i (List.mem_range.2 hi)

theorem ap_of {t : Array ℕ} {p : ℕ} {g : Equiv.Perm (Fin 4060)} (ht : Rep 4060 t g)
    (hp : t = unpack 4060 12 p) (x : Fin 4060) : ap p x = (g x : ℕ) := by
  have h := ht x
  rw [hp, CFSG.KS.Raw.Orb.unpack_get x.2] at h
  exact h

theorem apW {k : Nat} (hk : k < 6) (x : Fin 4060) : ap (WG k) x = (g2WGen k x : ℕ) :=
  ap_of (rep_g2WGenA hk) (wg_eq hk).1 x

theorem apWP {e : Nat} (_ : e < 64) (x : Fin 4060) : ap (WPk e) x = (g2WElt e x : ℕ) :=
  ap_of (rep_g2WProd e) (wprod_eq e).1 x

theorem apV {k : Nat} (hk : k < 3) (x : Fin 4060) : ap (VG k) x = (g2VGen k x : ℕ) :=
  ap_of (rep_g2VGenA hk) (vg_eq hk).1 x

theorem apVP {e : Nat} (_ : e < 8) (x : Fin 4060) : ap (VPk e) x = (g2VElt e x : ℕ) :=
  ap_of (rep_g2VProd e) (vprod_eq e).1 x

theorem vGen_memS (k : ℕ) : g2VGen k ∈ ruS := by
  unfold g2VGen
  split_ifs
  · exact g2WGen_memS 0
  · exact g2SElt_mem _

theorem g2V_leS : g2V ≤ ruS := by
  rw [g2V, Subgroup.closure_le]
  rintro _ ⟨k, -, rfl⟩
  exact vGen_memS k

theorem normB_iff {G E : ℕ → ℕ} {r m c : ℕ} (hc : c < 16384) {gG gE : ℕ → Equiv.Perm (Fin 4060)}
    (hG : ∀ k < r, ∀ x : Fin 4060, ap (G k) x = (gG k x : ℕ))
    (hE : ∀ e < m, ∀ x : Fin 4060, ap (E e) x = (gE e x : ℕ))
    (hGS : ∀ k < r, gG k ∈ ruS) (hES : ∀ e < m, gE e ∈ ruS) :
    normB G E r m c = true ↔ ∀ k < r, ∃ e < m, gC c * gG k * (gC c)⁻¹ = gE e := by
  have hm := gC_mem hc
  unfold normB
  rw [CFSG.KS.Raw.Orb.allN_iff]
  refine forall_congr' fun k => imp_congr_right fun hk => ?_
  rw [anyN_eq, List.any_eq_true]
  have key : ∀ e < m, bAnd(Nat.beq (evK LR TR c (ap (G k) 1)) (ap (E e) (evK LR TR c 1)),
      Nat.beq (evK LR TR c (ap (G k) 0)) (ap (E e) (evK LR TR c 0))) = true ↔
      gC c * gG k * (gC c)⁻¹ = gE e := by
    intro e he
    have a1 : ap (G k) 1 = ((gG k 1 : Fin 4060) : ℕ) := hG k hk 1
    have a0 : ap (G k) 0 = ((gG k 0 : Fin 4060) : ℕ) := hG k hk 0
    rw [a1, a0, ev_eq hc (gG k 1), ev_eq hc (gG k 0), ev1 hc, ev0 hc, hE e he (gC c 1),
      hE e he (gC c 0), bAnd_iff, Nat.beq_eq, Nat.beq_eq, ← Fin.ext_iff, ← Fin.ext_iff,
      mul_inv_eq_iff_eq_mul]
    constructor
    · rintro ⟨h1, h0⟩
      exact eq_of_base (ruS.mul_mem hm (hGS k hk)) (ruS.mul_mem (hES e he) hm) h1 h0
    · intro h
      exact ⟨congrArg (fun g : Equiv.Perm (Fin 4060) => g 1) h,
        congrArg (fun g : Equiv.Perm (Fin 4060) => g 0) h⟩
  constructor
  · rintro ⟨e, he, h⟩
    have he' := List.mem_range.1 he
    exact ⟨e, he', (key e he').1 h⟩
  · rintro ⟨e, he, h⟩
    exact ⟨e, List.mem_range.2 he, (key e he).2 h⟩

theorem inW_iff {t : Array ℕ} {g : Equiv.Perm (Fin 4060)} (ht : Rep 4060 t g) :
    g2InW t = true ↔ ∃ e < 64, g = g2WElt e := by
  refine ⟨eq_g2WElt_of_g2InW ht, ?_⟩
  rintro ⟨e, he, rfl⟩
  have hs : g2WArr.size = 64 := by simp [g2WArr]
  unfold g2InW
  rw [Array.any_eq_true]
  refine ⟨e, by rw [hs]; exact he, ?_⟩
  rw [← getElem!_pos g2WArr e (by rw [hs]; exact he)]
  exact (eqA_iff ht (rep_g2WArr he)).2 rfl

theorem inV_iff {t : Array ℕ} {g : Equiv.Perm (Fin 4060)} (ht : Rep 4060 t g) :
    g2InV t = true ↔ ∃ e < 8, g = g2VElt e := by
  refine ⟨eq_g2VElt_of_g2InV ht, ?_⟩
  rintro ⟨e, he, rfl⟩
  have hs : g2VArr.size = 8 := by simp [g2VArr]
  unfold g2InV
  rw [Array.any_eq_true]
  refine ⟨e, by rw [hs]; exact he, ?_⟩
  rw [← getElem!_pos g2VArr e (by rw [hs]; exact he)]
  exact (eqA_iff ht (rep_g2VArr he)).2 rfl

theorem normW_iff {t : Array ℕ} {g : Equiv.Perm (Fin 4060)} (ht : Rep 4060 t g) :
    g2NormW t = true ↔ ∀ k < 6, ∃ e < 64, g * g2WGen k * g⁻¹ = g2WElt e := by
  change allLt 6 (fun k => g2InW (compA 4060 (compA 4060 t g2WGenA[k]!) (invCand 4060 t))) = true
    ↔ _
  rw [allLt_iff]
  exact forall_congr' fun k => imp_congr_right fun hk =>
    inW_iff (rep_compA (rep_compA ht (rep_g2WGenA hk)) (rep_invCand' ht))

theorem normV_iff {t : Array ℕ} {g : Equiv.Perm (Fin 4060)} (ht : Rep 4060 t g) :
    g2NormV t = true ↔ ∀ k < 3, ∃ e < 8, g * g2VGen k * g⁻¹ = g2VElt e := by
  change allLt 3 (fun k => g2InV (compA 4060 (compA 4060 t g2VGenA[k]!) (invCand 4060 t))) = true
    ↔ _
  rw [allLt_iff]
  exact forall_congr' fun k => imp_congr_right fun hk =>
    inV_iff (rep_compA (rep_compA ht (rep_g2VGenA hk)) (rep_invCand' ht))

theorem s_part (hS : sCheck = true) :
    all2 4060 ruLevS (fun s => !g2NormW s || g2NormV s) = true := by
  have hs0 : ruLevS[0]!.pts.size = 2048 := lev_size.1
  have hs1 : ruLevS[1]!.pts.size = 8 := lev_size.2
  unfold all2
  rw [hs0, hs1, allLt_iff]
  intro a ha
  rw [allLt_iff]
  intro b hb
  have hc : 8 * a + b < 16384 := by omega
  have e1 : (8 * a + b) / 8 = a := by omega
  have e2 : (8 * a + b) % 8 = b := by omega
  have hr := rep_gC hc
  rw [e1, e2] at hr
  have h := CFSG.KS.Raw.Orb.allN_iff.1 hS (8 * a + b) hc
  have hWS : ∀ k < 6, g2WGen k ∈ ruS := fun k _ => g2WGen_memS k
  have hWE : ∀ e < 64, g2WElt e ∈ ruS := fun e _ => g2W_le (g2WElt_mem e)
  have hVS : ∀ k < 3, g2VGen k ∈ ruS := fun k _ => vGen_memS k
  have hVE : ∀ e < 8, g2VElt e ∈ ruS := fun e _ => g2V_leS (g2VElt_mem e)
  beta_reduce
  cases hw : g2NormW (prod2A 4060 ruLevS a b)
  · rfl
  · have hW := (normB_iff hc (fun k hk => apW hk) (fun e he => apWP he) hWS hWE).2
      ((normW_iff hr).1 hw)
    rw [hW] at h
    have hV : normB VG VPk 3 8 (8 * a + b) = true := h
    rw [(normV_iff hr).2 ((normB_iff hc (fun k hk => apV hk) (fun e he => apVP he) hVS hVE).1 hV)]
    rfl

theorem ra_eq {i : Nat} (hi : i < 20) :
    g2RhoA i = unpack 4060 12 (RAk i) ∧ G2Ru7164.P (RAk i) := by
  have e : g2RhoA i = CFSG.Quasithin.H13.KGRu.ruCW (g2RhoWords.getD i []) := rfl
  rw [e]
  exact cw_eq (by interval_cases i <;> decide)

theorem rhoPt_eq {i j : Nat} (hi : i < 20) (hj : j < 20) (x : Fin 4060) :
    rhoPt i j x = (((g2Rho i)⁻¹ * g2Rho j) x : ℕ) := by
  have a := ap_of (rep_g2RhoA hj) (ra_eq hj).1 x
  have b := ap_of (rep_invCand' (rep_g2RhoA hi))
    (by rw [(ra_eq hi).1, inv_eq (ra_eq hi).2]) (g2Rho j x)
  unfold rhoPt
  rw [a, b]
  rfl

theorem rho_part (hr : rhoCheck = true) : g2RhoCheck = true := by
  unfold g2RhoCheck
  rw [allLt_iff]
  intro i hi
  rw [allLt_iff]
  intro j hj
  have hc := all_range (all_range hr hi) hj
  by_cases hij : i < j
  · rw [decide_eq_true hij] at hc ⊢
    simp only [Bool.not_true, Bool.false_or] at hc ⊢
    have ht := rep_compA (rep_invCand' (rep_g2RhoA hi)) (rep_g2RhoA hj)
    cases hn : g2NormW (compA 4060 (invCand 4060 (g2RhoA i)) (g2RhoA j))
    · rfl
    · exfalso
      obtain ⟨k, hk, hall⟩ := List.any_eq_true.1 hc
      have hk' := List.mem_range.1 hk
      obtain ⟨e, he, heq⟩ := (normW_iff ht).1 hn k hk'
      have h := List.all_eq_true.1 hall e (List.mem_range.2 he)
      rw [mul_inv_eq_iff_eq_mul] at heq
      have p1 := congrArg (fun g : Equiv.Perm (Fin 4060) => ((g 1 : Fin 4060) : ℕ)) heq
      have p0 := congrArg (fun g : Equiv.Perm (Fin 4060) => ((g 0 : Fin 4060) : ℕ)) heq
      simp only [Equiv.Perm.mul_apply] at p1 p0
      have a1 : ap (WG k) 1 = ((g2WGen k 1 : Fin 4060) : ℕ) := apW hk' 1
      have a0 : ap (WG k) 0 = ((g2WGen k 0 : Fin 4060) : ℕ) := apW hk' 0
      have r1 : rhoPt i j 1 = ((((g2Rho i)⁻¹ * g2Rho j) 1 : Fin 4060) : ℕ) := rhoPt_eq hi hj 1
      have r0 : rhoPt i j 0 = ((((g2Rho i)⁻¹ * g2Rho j) 0 : Fin 4060) : ℕ) := rhoPt_eq hi hj 0
      rw [a1, a0, r1, r0, rhoPt_eq hi hj, rhoPt_eq hi hj, apWP he, apWP he] at h
      simp only [Equiv.Perm.mul_apply] at h
      rw [p1, p0] at h
      simp at h
  · rw [decide_eq_false hij]
    rfl

theorem varr_get {e : Nat} (he : e < 8) : g2VArr[e]! = g2VProd e := by
  rw [g2VArr, getElem!_pos _ e (by simpa using he), Array.getElem_ofFn]

open CFSG.Sporadic.RuSchreier CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CFSG.Quasithin.H13.Ch4.G2Ru in
open Certificates in
public theorem c7163 :
    (∀ i < 6, ∀ j < 6, eqA 4060 (compA 4060 g2WGenA[i]! g2WGenA[j]!)
      (compA 4060 g2WGenA[j]! g2WGenA[i]!) = true) ∧
      (∀ i < 6, eqA 4060 (compA 4060 g2WGenA[i]! g2WGenA[i]!) (idA 4060) = true) ∧
      eqA 4060 g2WGenA[0]! ruZA = true ∧
      (∀ e < 64, ∀ k < 6, g2InW (compA 4060 g2WGenA[k]! (g2WProd e)) = true) ∧
      g2InW g2VGenA[1]! = true ∧ g2InW g2VGenA[2]! = true ∧
      (∀ i < 8, ∀ j < 8, i < j → eqA 4060 g2VArr[i]! g2VArr[j]! = false) ∧
      (∀ e < 8, ∀ k < 3, g2InV (compA 4060 g2VGenA[k]! (g2VProd e)) = true) ∧
      g2RhoCheck = true ∧
      all2 4060 ruLevS (fun s => !g2NormW s || g2NormV s) = true := by
  have h := k7163
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨hw, hv⟩, hr⟩, hs⟩ := h
  unfold wCheck at hw
  unfold vCheck at hv
  simp only [Bool.and_eq_true] at hw hv
  obtain ⟨⟨⟨hw0, hw1⟩, hw2⟩, hw3⟩ := hw
  obtain ⟨⟨⟨hv0, hv1⟩, hv2⟩, hv3⟩ := hv
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, s_part hs⟩
  · intro i hi j hj
    obtain ⟨a1, a2⟩ := wg_eq hi
    obtain ⟨b1, b2⟩ := wg_eq hj
    rw [a1, b1, comp_eq a2 b2, comp_eq b2 a2, eq_eq (P_pc a2 b2) (P_pc b2 a2)]
    exact all_range (all_range hw0 hi) hj
  · intro i hi
    obtain ⟨a1, a2⟩ := wg_eq hi
    rw [a1, comp_eq a2 a2, G2Ru7164.id_eq, eq_eq (P_pc a2 a2) P_pid]
    exact all_range hw1 hi
  · obtain ⟨a1, a2⟩ := wg_eq (k := 0) (by norm_num)
    obtain ⟨z1, z2⟩ := powA_eq perms.1 10
    rw [a1, ruZA, CertificateChecks.KernelSporSch.RuG.c0_eq, z1, eq_eq a2 z2]
    exact hw2
  · intro e he k hk
    obtain ⟨a1, a2⟩ := wg_eq hk
    obtain ⟨p1, p2⟩ := wprod_eq e
    rw [a1, p1, comp_eq a2 p2, G2Ru7164.inW_eq (P_pc a2 p2)]
    exact all_range (all_range hw3 he) hk
  · obtain ⟨a1, a2⟩ := vg_eq (k := 1) (by norm_num)
    rw [a1, G2Ru7164.inW_eq a2]
    exact hv0
  · obtain ⟨a1, a2⟩ := vg_eq (k := 2) (by norm_num)
    rw [a1, G2Ru7164.inW_eq a2]
    exact hv1
  · intro i hi j hj hij
    have h := all_range (all_range hv2 hi) hj
    rw [varr_get hi, varr_get hj, (vprod_eq i).1, (vprod_eq j).1,
      eq_eq (vprod_eq i).2 (vprod_eq j).2]
    rw [decide_eq_true hij] at h
    revert h
    cases Nat.beq (VPk i) (VPk j) <;> simp
  · intro e he k hk
    obtain ⟨a1, a2⟩ := vg_eq hk
    obtain ⟨p1, p2⟩ := vprod_eq e
    rw [a1, p1, comp_eq a2 p2, G2Ru7164.inV_eq (P_pc a2 p2)]
    exact all_range (all_range hv3 he) hk
  · exact rho_part hr

end CertificateChecks.KernelSporSch.G2Ru7163
