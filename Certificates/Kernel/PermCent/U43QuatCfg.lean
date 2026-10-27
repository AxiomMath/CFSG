module

public import Certificates.Kernel.PermCent.U43QuatGlue
public import Certificates.Kernel.PermCent.U43QuatDF
public import Certificates.Kernel.PermCent.U43QuatC0
public import Certificates.Kernel.PermCent.U43QuatC1
public import Certificates.Kernel.PermCent.U43QuatC2
public import Certificates.Kernel.PermCent.U43QuatC3
public import Certificates.Kernel.PermCent.U43QuatC4
public import Certificates.Kernel.PermCent.U43QuatC5
public import Certificates.Kernel.PermCent.U43QuatC6
public import Certificates.Kernel.PermCent.U43QuatC7
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CU43ModelBase

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelPermCent.U43Quat

open CFSG.ComponentClassification.HarrisLit.P1.U43.Cover CFSG.ComponentClassification.HarrisLit.P1.U43
  CFSG.ComponentClassification.HarrisLit.P1.U43.Quat CFSG.LieType.Multipliers.U43 CFSG.KC.Enum CFSG.KS
  CFSG.KS.Prim CFSG.KS.Raw.Orb CFSG.KC.OrbGroup CFSG.KC.QuatK CFSG.ClassicalInvolution.Q3.TL4.E4C
  CertificateChecks.KernelPermCent.U43P1 Subgroup CFSG.Monster.B.Co2
open CFSG.EvenSporadicStandard.M24Std.CU43 (P P_eq_range tP dP fP deltaArr phiArr)

theorem permOfArr_eq_of_rep' {t : Array ℕ} {g : Equiv.Perm (Fin 820)} (h : Rep 820 t g) :
    permOfArr 820 t = g := by
  have hc : (∀ i < 820, t[i]! < 820) ∧ ∀ i < 820, ∀ j < 820, t[i]! = t[j]! → i = j :=
    ⟨fun i hi => h.lt hi, fun i hi j hj hij => by
      rw [h.apply hi, h.apply hj] at hij
      have := g.injective (Fin.ext hij)
      simpa using this⟩
  ext x
  rw [permOfArr, dite_eq_left hc]
  change t[(x : ℕ)]! = _
  exact h x

theorem rep_of_listOKK {a : Array ℕ} {p : ℕ} {g : Equiv.Perm (Fin 820)}
    (h : listOKK 820 10 a.toList p = true) (hp : PRep 820 10 p g) : Rep 820 a g := by
  obtain ⟨hl, hf⟩ := listOKK_spec h
  intro x
  have hx : (x : ℕ) < a.toList.length := by
    rw [hl]
    exact x.2
  have hs : (x : ℕ) < a.size := by simpa using hx
  rw [getElem!_pos a (x : ℕ) hs, ← hp x, hf x hx]
  exact (Array.getElem_toList hx).symm

theorem binds_df :
    listOKK 820 10 deltaArr.toList (QP 15) = true ∧ listOKK 820 10 phiArr.toList (QP 16) = true ∧
      (matK cDi).det ≠ 0 ∧ (matK cI).det ≠ 0 ∧ matOK cDi false (QP 15) = true ∧
      matOK cI true (QP 16) = true ∧
      Nat.beq (mulK 820 10 (QP 15) (QP 0)) (mulK 820 10 (QP 0) (QP 15)) = true ∧
      Nat.beq (mulK 820 10 (QP 16) (QP 0)) (mulK 820 10 (QP 0) (QP 16)) = true := by
  obtain ⟨h, -, -⟩ := bindsQ
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨-, hδ⟩, hφ⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := h
  obtain ⟨d1, d2, h2⟩ := bindsDF
  simp only [Bool.and_eq_true] at h2
  obtain ⟨⟨⟨m1, m2⟩, c1⟩, c2⟩ := h2
  exact ⟨hδ, hφ, d1, d2, m1, m2, c1, c2⟩

theorem prep_dP : PRep 820 10 (QP 15) dP := by
  obtain ⟨hδ, -, d1, -, m1, -⟩ := binds_df
  have hp := prep_matOK d1 m1
  have e : dP = eK cDi false := permOfArr_eq_of_rep' (rep_of_listOKK hδ hp)
  rw [e]
  exact hp

theorem prep_fP : PRep 820 10 (QP 16) fP := by
  obtain ⟨-, hφ, -, d2, -, m2, -⟩ := binds_df
  have hp := prep_matOK d2 m2
  have e : fP = eK cI true := permOfArr_eq_of_rep' (rep_of_listOKK hφ hp)
  rw [e]
  exact hp

theorem prep_powK {p : ℕ} {g : Equiv.Perm (Fin 820)} (hp : PRep 820 10 p g) :
    ∀ e, PRep 820 10 (powK p e) (g ^ e)
  | 0 => crep_eP.1
  | e + 1 => by
    rw [pow_succ']
    exact prep_pc hp (prep_powK hp e)

theorem prep_tPK (k : ℕ) : PRep 820 10 (tPK k) (tP k) :=
  prep_pc (prep_powK prep_fP _) (prep_powK prep_dP _)

theorem commute_tP_r0 (k : ℕ) : Commute (tP k) (qE 0) := by
  obtain ⟨-, -, -, -, -, -, c1, c2⟩ := binds_df
  have h0 := prep_qE (j := 0) (by norm_num)
  have cd : Commute dP (qE 0) := by
    have h := c1
    rw [beq_eq (by norm_num) (crep_mulK (by norm_num) (by norm_num) prep_dP h0)
      (crep_mulK (by norm_num) (by norm_num) h0 prep_dP), decide_eq_true_iff] at h
    exact h
  have cf : Commute fP (qE 0) := by
    have h := c2
    rw [beq_eq (by norm_num) (crep_mulK (by norm_num) (by norm_num) prep_fP h0)
      (crep_mulK (by norm_num) (by norm_num) h0 prep_fP), decide_eq_true_iff] at h
    exact h
  exact (cf.pow_left _).mul_left (cd.pow_left _)

theorem frame_facts :
    Nat.beq (mulK 820 10 rF rF) eP = true ∧
      (l1F.drop 2).all (fun x => Nat.beq (mulK 820 10 x x) rF) = true ∧
      (List.range 6).all (fun j => Nat.beq (mulK 820 10 (mulK 820 10 (CgIn.T (cfgIdx.getD j 0))
        (sF 2)) (gamF j)) (mulK 820 10 (gamF j) (QP 5))) = true ∧ cfgIdx.length = 6 := by
  obtain ⟨h, -, hl⟩ := bindsQ
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, hrr⟩, -⟩, -⟩, hl1⟩, hcfg⟩ := h
  exact ⟨hrr, hl1, hcfg, hl⟩

theorem sq_L1F {X : Equiv.Perm (Fin 820)}
    (hX : X ∈ (q8Elems (tRep 0) (phi (qE 3)) (phi (qE 4))).drop 2) :
    X * X = tRep 0 ∧ tRep 0 * tRep 0 = 1 := by
  obtain ⟨hrr, hl1, -⟩ := frame_facts
  have m := @crep_mulK 820 10 (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · have hF := List.forall₂_drop 2 (forall₂_q8F (a := 3) (b := 4) (by norm_num) (by norm_num))
    have h2 : ((q8Elems (tRep 0) (phi (qE 3)) (phi (qE 4))).drop 2).all
        (fun X => decide (X * X = tRep 0)) = true :=
      (all_f2 (fun a b h => beq_eq (by norm_num) (m h.1 h.1) crep_rF) hF).symm.trans hl1
    rw [List.all_eq_true] at h2
    exact decide_eq_true_iff.1 (h2 X hX)
  · rw [beq_eq (by norm_num) (m crep_rF.1 crep_rF.1) crep_eP, decide_eq_true_iff] at hrr
    exact hrr

theorem cfg_coset_all : ∀ k < 8, cfgCoset k = true := by
  intro k hk
  interval_cases k
  · exact cfg_coset0
  · exact cfg_coset1
  · exact cfg_coset2
  · exact cfg_coset3
  · exact cfg_coset4
  · exact cfg_coset5
  · exact cfg_coset6
  · exact cfg_coset7

@[expose] def CfgE (y : Equiv.Perm (Fin 820)) : Prop :=
  y * qE 1 = qE 1 * y ∧ y * qE 2 = qE 2 * y ∧ y * y = 1 ∧
    ∃ x ∈ L1E.drop 2, y * qE 3 = x * qE 3 * x⁻¹ * y ∧ y * qE 4 = x * qE 4 * x⁻¹ * y

theorem cfg_classify {g : Equiv.Perm (Fin 820)} (hg : g ∈ P)
    {k : ℕ} (hk : k < 8) (hcfg : CfgE (g * tP k)) :
    ∃ j < 6, g * tP k = qE (8 + j) * qE 5 * (qE (8 + j))⁻¹ := by
  obtain ⟨h1, h2, h3, x, hx, h4, h5⟩ := hcfg
  have m := @crep_mulK 820 10 (by norm_num) (by norm_num)
  have c1 : Commute (g * tP k) (qE 1) := h1
  have cy : Commute (g * tP k) (qE 0) := by
    have h := c1.mul_right c1
    rwa [u0_sq] at h
  have cg : Commute g (qE 0) := by
    have e : g = g * tP k * (tP k)⁻¹ := by group
    rw [e]
    exact cy.mul_left (commute_tP_r0 k).inv_left
  have hgP : phi g ∈ psi.range ⊓ centralizer ({tRep 0} : Set (Equiv.Perm (Fin 820))) := by
    refine mem_inf.2 ⟨P_eq_range ▸ phi_mem hg, mem_centralizer_singleton_iff.2 ?_⟩
    rw [← conj_r0, ← map_mul, ← map_mul, cg.eq]
  obtain ⟨i, hi, hpi⟩ := cen0_facts.1 _ hgP
  have hY : PRep 820 10 (mulK 820 10 (CgIn.T i) (sF k)) (phi (g * tP k)) := by
    rw [map_mul]
    exact prep_pcomp (by norm_num) hpi (crep_fr (prep_tPK k)).1
  have hL1 : q8Elems (tRep 0) (phi (qE 3)) (phi (qE 4)) = L1E.map phi := by
    rw [← conj_r0, q8Elems_map, L1E]
  have htw : List.Forall₂ (fun p P => PRep 820 10 p.1 P.1 ∧ PRep 820 10 p.2 P.2) twF
      (((q8Elems (tRep 0) (phi (qE 3)) (phi (qE 4))).drop 2).map fun X =>
        (X * phi (qE 3) * (X * tRep 0), X * phi (qE 4) * (X * tRep 0))) := by
    have hF := List.forall₂_drop 2 (forall₂_q8F (a := 3) (b := 4) (by norm_num) (by norm_num))
    rw [twF, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    exact hF.imp fun a b h =>
      ⟨prep_pc (prep_pc h.1 (crep_fr (prep_qE (by norm_num))).1) (prep_pc h.1 crep_rF.1),
        prep_pc (prep_pc h.1 (crep_fr (prep_qE (by norm_num))).1) (prep_pc h.1 crep_rF.1)⟩
  have hc : cfgK 820 10 eP u0F v0F u1F v1F twF (mulK 820 10 (CgIn.T i) (sF k)) = true := by
    refine (cfgK_eq (by norm_num) (by norm_num) crep_eP
      (crep_fr (prep_qE (j := 1) (by norm_num))).1 (crep_fr (prep_qE (j := 2) (by norm_num))).1
      (crep_fr (prep_qE (j := 3) (by norm_num))).1 (crep_fr (prep_qE (j := 4) (by norm_num))).1
      hY htw).2 ⟨?_, ?_, ?_, ?_⟩
    · rw [← map_mul, ← map_mul, h1]
    · rw [← map_mul, ← map_mul, h2]
    · rw [← map_mul, h3, map_one]
    · have hxF : phi x ∈ (q8Elems (tRep 0) (phi (qE 3)) (phi (qE 4))).drop 2 := by
        rw [hL1, ← List.map_drop]
        exact List.mem_map_of_mem hx
      obtain ⟨hxx, hrr⟩ := sq_L1F hxF
      have hinv : (phi x)⁻¹ = phi x * tRep 0 :=
        inv_eq_of_mul_eq_one_right (by rw [← mul_assoc, hxx, hrr])
      refine ⟨_, List.mem_map_of_mem hxF, ?_, ?_⟩
      · have e := congrArg phi h4
        rw [map_mul phi (g * tP k) (qE 3), map_mul phi (x * qE 3 * x⁻¹) (g * tP k),
          map_mul phi (x * qE 3) x⁻¹, map_mul phi x (qE 3), map_inv, hinv] at e
        exact e
      · have e := congrArg phi h5
        rw [map_mul phi (g * tP k) (qE 4), map_mul phi (x * qE 4 * x⁻¹) (g * tP k),
          map_mul phi (x * qE 4) x⁻¹, map_mul phi x (qE 4), map_inv, hinv] at e
        exact e
  have hm := cfgScanK_spec (cfg_coset_all k hk) hi hc
  cases e : Nat.beq k 2 with
  | false =>
    rw [e] at hm
    exact absurd hm List.not_mem_nil
  | true =>
    have hk2 := Nat.eq_of_beq_eq_true e
    rw [e, cond_true] at hm
    subst hk2
    obtain ⟨j, hj, hji⟩ := List.getElem_of_mem hm
    obtain ⟨-, -, hcf, hlen⟩ := frame_facts
    rw [List.all_eq_true] at hcf
    have hj6 : j < 6 := hlen ▸ hj
    have hb := hcf j (List.mem_range.2 hj6)
    rw [List.getD_eq_getElem _ _ hj, hji] at hb
    have hG : PRep 820 10 (gamF j) ((qE 6)⁻¹ * qE (8 + j)) :=
      prep_pc prep_c0inv (prep_qE (by omega))
    have h6 := of_decide_eq_true ((beq_eq (by norm_num) (m (m hpi (crep_fr (prep_tPK 2)).1).1 hG)
      (m hG (prep_qE (by norm_num)))).symm.trans hb)
    rw [← map_mul, phi_apply] at h6
    refine ⟨j, hj6, ?_⟩
    calc g * tP 2 = qE 6 * ((qE 6)⁻¹ * (g * tP 2 * qE 6) * ((qE 6)⁻¹ * qE (8 + j))) *
          (qE (8 + j))⁻¹ := by group
      _ = qE 6 * ((qE 6)⁻¹ * qE (8 + j) * qE 5) * (qE (8 + j))⁻¹ := by rw [h6]
      _ = qE (8 + j) * qE 5 * (qE (8 + j))⁻¹ := by group

end CertificateChecks.KernelPermCent.U43Quat

end
