module

public import Certificates.Kernel.Sp6Insp443.SixGlue
public import Certificates.Kernel.Sp6Insp443.Fano
public import CFSG.Certificates.Kernel.Sp6Insp443.FanoSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelS6I

open CFSG.KC CFSG.KC.Enum CFSG.KC.A45Cls CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.Prim
  CFSG.KS.Sp6I CFSG.KS.SporSch.MOC CFSG.Certificates CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Co3 CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.EvenSmallLie.Sp6
  CFSG.SectionRank.QTK.Insp443.Sp6 CFSG.SectionRank.QTK.Insp443.PermKit
  CFSG.SectionRank.QTK.Insp443.PermKit.Native CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.Native
  CertificateChecks.KernelLC.Sp6J

theorem memIs_iff {S c g : Nat} {b : Bool} (h : memIs S c g b = true) :
    memPK (36 * 6) S c g = true ↔ b = true := by
  unfold memIs at h
  rw [Orb.bIf_eq] at h
  by_cases hm : memPK (36 * 6) S c g = true
  · rw [if_pos hm] at h
    exact ⟨fun _ => h, fun _ => hm⟩
  · rw [if_neg hm, Orb.bIf_eq] at h
    by_cases hb : b = true
    · rw [if_pos hb] at h
      exact absurd h Bool.false_ne_true
    · exact ⟨fun h' => absurd h' hm, fun h' => absurd h' hb⟩

theorem bIf_not_iff {b : Bool} : bIf(b, false, true) = true ↔ b = false := by
  cases b <;> decide

theorem fanoB_facts {P S c : Nat} (h : fanoB P S c = true) :
    ∃ y : Nat → Equiv.Perm (Fin 36), (∀ j < c, PRep 36 6 (laneK (36 * 6) P j) (y j)) ∧
      (∀ j < c, y j * y j = 1) ∧ (∀ i < c, ∀ j < c, Commute (y i) (y j)) ∧
      ∀ s < 2 ^ c, PRep 36 6 (laneK (36 * 6) S s) (mprod y s c) := by
  unfold fanoB at h
  simp only [Orb.bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨y, hy⟩ := exists_lanes_inv h1
  have hyp : ∀ j < c, PRep 36 6 (laneK (36 * 6) P j) (y j) := fun j hj => (hy j hj).1
  exact ⟨y, hyp, fun j hj => (hy j hj).2, commute_of_commPK (by norm_num) (by norm_num) hyp h2,
    spanPK_prep (by norm_num) prepOne h3 hyp⟩

theorem fanoB_mem {P S c : Nat} {y : Nat → Equiv.Perm (Fin 36)}
    (hyp : ∀ j < c, PRep 36 6 (laneK (36 * 6) P j) (y j)) (hsq : ∀ j < c, y j * y j = 1)
    (hc : ∀ i < c, ∀ j < c, Commute (y i) (y j)) (h : fanoB P S c = true) {G : Nat}
    {g : Equiv.Perm (Fin 36)} (hG : PRep 36 6 G g) (sG : G >>> (36 * 6) = 0) :
    memPK (36 * 6) S (2 ^ c) G = true ↔ g ∈ Subgroup.closure (Set.range fun i : Fin c => y i) := by
  unfold fanoB at h
  simp only [Orb.bAnd_eq, Bool.and_eq_true] at h
  exact memPK_span_iff (by norm_num) (by norm_num) prepOne hyp hsq hc h.2.2 hG sG

theorem map_conj_eq_of_bases {k l : Nat} {d : Fin k → Equiv.Perm (Fin 36)}
    {e : Fin l → Equiv.Perm (Fin 36)} {y : Equiv.Perm (Fin 36)}
    (h1 : ∀ i, y * d i * y⁻¹ ∈ Subgroup.closure (Set.range e))
    (h2 : ∀ i, y⁻¹ * e i * y ∈ Subgroup.closure (Set.range d)) :
    (Subgroup.closure (Set.range d)).map (MulAut.conj y).toMonoidHom =
      Subgroup.closure (Set.range e) := by
  refine le_antisymm ?_ ?_
  · rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact h1 i
  · rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    refine ⟨_, h2 i, ?_⟩
    change MulAut.conj y _ = _
    rw [MulAut.conj_apply]
    group

theorem fanoTest_of
    {t : Nat} (ht : t < 2) (hs : ch725107f t = true)
    {g : Equiv.Perm (Fin 36)} (hg : g ∈ co3X36) {T : Table} (hT : Rep 36 T g) :
    fanoTestS 36 (cands7.getD (fanoW t) []) (spanTabs 36 (cands7.getD (fanoW t) []))
      (cands7.getD (fanoA t) []) (spanTabs 36 (cands7.getD (fanoA t) [])) (fanoRows t) T =
        false := by
  unfold ch725107f at hs
  simp only [Orb.strictB_eq, Orb.bAnd_eq, Bool.and_eq_true] at hs
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, hfu, h13, h14, h15⟩ := hs
  rw [← sp6Q_originalSubgroup] at hg
  obtain ⟨c, hcH, hc⟩ := wordNK_prep (by norm_num) prepOne prepGen prepGenInv genMem _ h1
  rw [Nat.eq_of_beq_eq_true h2] at hc
  have hci := prep_inv_of_permOK h3 hc
  obtain ⟨x, hxp, hxsq, hxc, hspW⟩ := fanoB_facts h6
  obtain ⟨a, hap, hasq, hac, hspA⟩ := fanoB_facts h9
  have hws := forall₂_of_tabsPK h4 (by rw [← lenT_eq]; exact Nat.eq_of_beq_eq_true h5) hxp
  have has := forall₂_of_tabsPK h7 (by rw [← lenT_eq]; exact Nat.eq_of_beq_eq_true h8) hap
  have hmemA : ∀ {G : Nat} {y : Equiv.Perm (Fin 36)}, PRep 36 6 G y → G >>> (36 * 6) = 0 →
      (memPK (36 * 6) (F.sA.getD t 0) 8 G = true ↔
        y ∈ Subgroup.closure (Set.range fun i : Fin 3 => a i)) :=
    fun hG sG => fanoB_mem (c := 3) hap hasq hac h9 hG sG
  have hKH0 : ∀ p, ∃ kh : (Nat → Equiv.Perm (Fin 36)) × (Nat → Equiv.Perm (Fin 36)),
      0 < p → p < 8 →
        (∀ j < 2, PRep 36 6 (laneK (36 * 6) (F.kT.getD (7 * t + p - 1) 0) j) (kh.1 j)) ∧
        (∀ j < 2, kh.1 j * kh.1 j = 1) ∧ (∀ i < 2, ∀ j < 2, Commute (kh.1 i) (kh.1 j)) ∧
        (∀ j < 5, PRep 36 6 (laneK (36 * 6) (F.hT.getD (7 * t + p - 1) 0) j) (kh.2 j)) ∧
        (∀ j < 5, kh.2 j * kh.2 j = 1) ∧ (∀ i < 5, ∀ j < 5, Commute (kh.2 i) (kh.2 j)) := by
    intro p
    by_cases hp : 0 < p ∧ p < 8
    · have hk := Orb.allN_iff.1 h10 (p - 1) (by omega)
      rw [Nat.sub_add_cancel hp.1] at hk
      unfold fanoKH at hk
      simp only [Orb.strictB_eq, Orb.bAnd_eq, Bool.and_eq_true] at hk
      obtain ⟨k, hkp, hksq, hkc, -⟩ := fanoB_facts hk.1
      obtain ⟨hh, hhp, hhsq, hhc, -⟩ := fanoB_facts hk.2.1
      exact ⟨(k, hh), fun _ _ => ⟨hkp, hksq, hkc, hhp, hhsq, hhc⟩⟩
    · exact ⟨(fun _ => 1, fun _ => 1), fun h h' => absurd ⟨h, h'⟩ hp⟩
  choose kh hkh using hKH0
  set K : Nat → Subgroup (Equiv.Perm (Fin 36)) := fun p =>
    Subgroup.closure (Set.range fun i : Fin 2 => (kh p).1 i) with hK_def
  set H : Nat → Subgroup (Equiv.Perm (Fin 36)) := fun p =>
    Subgroup.closure (Set.range fun i : Fin 5 => (kh p).2 i) with hH_def
  have hk : ∀ p, 0 < p → p < 8 → fanoKH t p = true := fun p hp hp8 => by
    have := Orb.allN_iff.1 h10 (p - 1) (by omega)
    rwa [Nat.sub_add_cancel hp] at this
  have hmemK : ∀ p, 0 < p → p < 8 → ∀ {G : Nat} {y : Equiv.Perm (Fin 36)}, PRep 36 6 G y →
      G >>> (36 * 6) = 0 → (memPK (36 * 6) (F.kS.getD (7 * t + p - 1) 0) 4 G = true ↔ y ∈ K p) := by
    intro p hp hp8 G y hG sG
    have h := hk p hp hp8
    unfold fanoKH at h
    simp only [Orb.strictB_eq, Orb.bAnd_eq, Bool.and_eq_true] at h
    obtain ⟨hkp, hksq, hkc, -⟩ := hkh p hp hp8
    exact fanoB_mem (c := 2) hkp hksq hkc h.1 hG sG
  have hmemH : ∀ p, 0 < p → p < 8 → ∀ {G : Nat} {y : Equiv.Perm (Fin 36)}, PRep 36 6 G y →
      G >>> (36 * 6) = 0 → (memPK (36 * 6) (F.hS.getD (7 * t + p - 1) 0) 32 G = true ↔
        y ∈ H p) := by
    intro p hp hp8 G y hG sG
    have h := hk p hp hp8
    unfold fanoKH at h
    simp only [Orb.strictB_eq, Orb.bAnd_eq, Bool.and_eq_true] at h
    obtain ⟨-, -, -, hhp, hhsq, hhc⟩ := hkh p hp hp8
    exact fanoB_mem (c := 5) hhp hhsq hhc h.2.1 hG sG
  have hKd : ∀ d < 8, ∀ p, 0 < p → p < 8 → (mprod a d 3 ∈ K p ↔ dot3 d p = false) := by
    intro d hd p hp hp8
    have h := hk p hp hp8
    unfold fanoKH at h
    simp only [Orb.strictB_eq, Orb.bAnd_eq, Bool.and_eq_true] at h
    rw [← hmemK p hp hp8 (hspA d hd) (laneK_shr _ _ _), memIs_iff (Orb.allN_iff.1 h.2.2.1 d hd),
      bIf_not_iff]
  have hHm : ∀ m < 64, ∀ p, 0 < p → p < 8 → (mprod x m 6 ∈ H p ↔
      bsum (fanoRows t) m p = false) := by
    intro m hm p hp hp8
    have h := hk p hp hp8
    unfold fanoKH at h
    simp only [Orb.strictB_eq, Orb.bAnd_eq, Bool.and_eq_true] at h
    rw [← hmemH p hp hp8 (hspW m hm) (laneK_shr _ _ _),
      memIs_iff (Orb.allN_iff.1 h.2.2.2.1 m hm), bIf_not_iff]
  have hKa : ∀ i < 3, ∀ p, 0 < p → p < 8 → (a i ∈ K p ↔ dot3 (Nat.shiftLeft 1 i) p = false) := by
    intro i hi p hp hp8
    have h := hk p hp hp8
    unfold fanoKH at h
    simp only [Orb.strictB_eq, Orb.bAnd_eq, Bool.and_eq_true] at h
    rw [← hmemK p hp hp8 (hap i hi) (laneK_shr _ _ _),
      memIs_iff (Orb.allN_iff.1 h.2.2.2.2.1 i hi), bIf_not_iff]
  have hHw : ∀ j < 6, ∀ p, 0 < p → p < 8 → (x j ∈ H p ↔
      ((fanoRows t).getD j 0).testBit p = false) := by
    intro j hj p hp hp8
    have h := hk p hp hp8
    unfold fanoKH at h
    simp only [Orb.strictB_eq, Orb.bAnd_eq, Bool.and_eq_true] at h
    rw [← hmemH p hp hp8 (hxp j hj) (laneK_shr _ _ _),
      memIs_iff (Orb.allN_iff.1 h.2.2.2.2.2 j hj), bIf_not_iff]
  have hfanoP : ∀ {Y YI j : Nat} {y : Equiv.Perm (Fin 36)}, PRep 36 6 Y y → PRep 36 6 YI y⁻¹ →
      fanoG t Y YI j = true →
        FanoP (Subgroup.closure (Set.range fun i : Fin 3 => a i)) K H y := by
    intro Y YI j y hY hYI hG
    unfold fanoG at hG
    simp only [Orb.bAnd_eq, Bool.and_eq_true] at hG
    obtain ⟨hA1, hA2, hP⟩ := hG
    unfold FanoP
    refine ⟨map_conj_eq_of_bases (fun i => ?_) (fun i => ?_), fun p hp hp8 => ?_⟩
    · have := (hmemA (prep_pcomp (by norm_num) hY (prep_pcomp (by norm_num) (hap i i.2) hYI))
        (shr36 _ _)).1 (Orb.allN_iff.1 hA1 i i.2)
      rwa [← mul_assoc] at this
    · have := (hmemA (prep_pcomp (by norm_num) hYI (prep_pcomp (by norm_num) (hap i i.2) hY))
        (shr36 _ _)).1 (Orb.allN_iff.1 hA2 i i.2)
      rwa [← mul_assoc] at this
    · have hq := Orb.allN_iff.1 hP (p - 1) (by omega)
      rw [Nat.sub_add_cancel hp] at hq
      simp only [Orb.strictB_eq, Orb.bAnd_eq, Bool.and_eq_true] at hq
      obtain ⟨hq0, hq8, hpq⟩ := hq
      have hq0' := Nat.blt_eq.mp hq0
      have hq8' := Nat.blt_eq.mp hq8
      refine ⟨_, hq0', hq8', ?_, ?_⟩
      · unfold fanoPQ at hpq
        simp only [Orb.strictB_eq, Orb.bAnd_eq, Bool.and_eq_true] at hpq
        refine map_conj_eq_of_bases (fun i => ?_) (fun i => ?_)
        · have := (hmemK _ hq0' hq8' (prep_pcomp (by norm_num) hY (prep_pcomp (by norm_num)
            ((hkh p hp hp8).1 i i.2) hYI)) (shr36 _ _)).1 (Orb.allN_iff.1 hpq.1 i i.2)
          rwa [← mul_assoc] at this
        · have := (hmemK p hp hp8 (prep_pcomp (by norm_num) hYI (prep_pcomp (by norm_num)
            ((hkh _ hq0' hq8').1 i i.2) hY)) (shr36 _ _)).1 (Orb.allN_iff.1 hpq.2.1 i i.2)
          rwa [← mul_assoc] at this
      · unfold fanoPQ at hpq
        simp only [Orb.strictB_eq, Orb.bAnd_eq, Bool.and_eq_true] at hpq
        refine map_conj_eq_of_bases (fun i => ?_) (fun i => ?_)
        · have := (hmemH _ hq0' hq8' (prep_pcomp (by norm_num) hY (prep_pcomp (by norm_num)
            ((hkh p hp hp8).2.2.2.1 i i.2) hYI)) (shr36 _ _)).1 (Orb.allN_iff.1 hpq.2.2.1 i i.2)
          rwa [← mul_assoc] at this
        · have := (hmemH p hp hp8 (prep_pcomp (by norm_num) hYI (prep_pcomp (by norm_num)
            ((hkh _ hq0' hq8').2.2.2.1 i i.2) hY)) (shr36 _ _)).1 (Orb.allN_iff.1 hpq.2.2.2 i i.2)
          rwa [← mul_assoc] at this
  set S₀ : Set (Equiv.Perm (Fin 36)) := {y | (∃ j < 6, y = c * sp6CentGens4.getD j 1 * c⁻¹) ∨
    ∃ q < 28, PRep 36 6 ((F.nP.getD t []).getD q 0) y} with hS₀
  have hlen4 : sp6CentGens4.length = 6 := rfl
  have hS : ∀ y ∈ S₀, FanoP (Subgroup.closure (Set.range fun i : Fin 3 => a i)) K H y := by
    rintro y (⟨j, hj, rfl⟩ | ⟨q, hq, hy⟩)
    · have hgj := Orb.allN_iff.1 h15 j hj
      simp only [Orb.strictB_eq, Orb.bAnd_eq, Bool.and_eq_true] at hgj
      obtain ⟨hpj, hfg⟩ := hgj
      have hxj := prep_of_imageList (chainC4.2.2.2.1 j (by rw [hlen4]; exact hj))
      have hxji := prep_inv_of_permOK hpj hxj
      have hY := prep_pcomp (by norm_num) hc (prep_pcomp (by norm_num) hxj hci)
      have hYI := prep_pcomp (by norm_num) hc (prep_pcomp (by norm_num) hxji hci)
      have e1 : c * (sp6CentGens4.getD j 1 * c⁻¹) = c * sp6CentGens4.getD j 1 * c⁻¹ := by group
      have e2 : c * ((sp6CentGens4.getD j 1)⁻¹ * c⁻¹) = (c * sp6CentGens4.getD j 1 * c⁻¹)⁻¹ := by
        group
      rw [e1] at hY
      rw [e2] at hYI
      exact hfanoP hY hYI hfg
    · have hq' := Orb.allN_iff.1 h14 q hq
      simp only [Orb.strictB_eq, Orb.bAnd_eq, Bool.and_eq_true] at hq'
      obtain ⟨-, -, -, hperm, -, hfg⟩ := hq'
      exact hfanoP hy (prep_inv_of_permOK hperm hy) hfg
  have hum : F.uM.getD t 0 < 2 ^ 6 := Nat.blt_eq.mp h11
  have hr4 := prepRep (i := 3) (by norm_num)
  have hux : mprod x (F.uM.getD t 0) 6 = c * (sp6InvReps.getD 3 1 * c⁻¹) := by
    refine SporSch.MOC.prep_unique (hspW _ hum) ?_
    rw [Nat.eq_of_beq_eq_true h12]
    exact prep_pcomp (by norm_num) hc (prep_pcomp (by norm_num) hr4 hci)
  have hK : ∀ g ∈ sp6Q.originalSubgroup,
      (∀ i, ∃ e, g * (fun i : Fin 6 => x i) i * g⁻¹ = eElt (fun i : Fin 6 => x i) e) →
        g ∈ Subgroup.closure S₀ := by
    intro g hg hN
    have hgz : g * mprod x (F.uM.getD t 0) 6 * g⁻¹ ∈
        Subgroup.closure (Set.range fun i : Fin 6 => x i) :=
      map_conj_closure_le hN ⟨_, mprod_mem_closure x _ 6, rfl⟩
    obtain ⟨s, hs, hsz⟩ := exists_mprod_of_mem_closure hxsq hxc hgz
    have hfs : fixK 36 6 (laneK (36 * 6) (F.sW.getD t 0) s) = 4 := by
      rw [fixK_eq (hspW s hs), hsz, fixC_conj, ← fixK_eq (hspW _ hum)]
      exact Nat.eq_of_beq_eq_true hfu
    have h13s := Orb.allN_iff.1 h13 s hs
    rw [Orb.bIf_eq, if_pos (by rw [Nat.beq_eq]; exact hfs), bIf_not_iff] at h13s
    obtain ⟨q, hq, hqs⟩ : ∃ q < 28, (F.nM.getD t []).getD q 0 = s := by
      by_contra hne
      push Not at hne
      have : allN 28 (fun q => bIf(Nat.beq ((F.nM.getD t []).getD q 0) s, false, true)) = true :=
        Orb.allN_iff.2 fun q hq => bIf_not_iff.2 (Bool.eq_false_iff.2 fun h =>
          hne q hq (Nat.eq_of_beq_eq_true h))
      rw [this] at h13s
      exact Bool.noConfusion h13s
    have hq' := Orb.allN_iff.1 h14 q hq
    simp only [Orb.strictB_eq, Orb.bAnd_eq, Bool.and_eq_true] at hq'
    obtain ⟨-, hlet, hword, hperm, hlane, -⟩ := hq'
    obtain ⟨nq, hnqH, hnq⟩ := wordNK_prep (by norm_num) prepOne prepGen prepGenInv genMem _ hlet
    rw [Nat.eq_of_beq_eq_true hword] at hnq
    have hnqi := prep_inv_of_permOK hperm hnq
    have hlq : PRep 36 6 (laneK (36 * 6) (F.sW.getD t 0) s)
        (nq * (mprod x (F.uM.getD t 0) 6 * nq⁻¹)) := by
      rw [← hqs, Nat.eq_of_beq_eq_true hlane]
      exact prep_pcomp (by norm_num) hnq (prep_pcomp (by norm_num) (hspW _ hum) hnqi)
    have hgu := (SporSch.MOC.prep_unique (hspW s hs) hlq).symm.trans hsz
    rw [hux] at hgu
    set r := sp6InvReps.getD 3 1
    have hcomm : c⁻¹ * (nq⁻¹ * g) * c * r = r * (c⁻¹ * (nq⁻¹ * g) * c) := by
      have h1 : nq * (c * (r * c⁻¹)) * nq⁻¹ * g = g * (c * (r * c⁻¹)) :=
        calc nq * (c * (r * c⁻¹)) * nq⁻¹ * g = nq * (c * (r * c⁻¹) * nq⁻¹) * g := by group
          _ = g * (c * (r * c⁻¹)) * g⁻¹ * g := by rw [hgu]
          _ = g * (c * (r * c⁻¹)) := by group
      calc c⁻¹ * (nq⁻¹ * g) * c * r
          = c⁻¹ * nq⁻¹ * (g * (c * (r * c⁻¹))) * c := by group
        _ = c⁻¹ * nq⁻¹ * (nq * (c * (r * c⁻¹)) * nq⁻¹ * g) * c := by rw [h1]
        _ = r * (c⁻¹ * (nq⁻¹ * g) * c) := by group
    have hyC : c⁻¹ * (nq⁻¹ * g) * c ∈ centralizerIn sp6Q.originalSubgroup r := by
      refine mem_centralizerIn.2 ⟨sp6Q.originalSubgroup.mul_mem
        (sp6Q.originalSubgroup.mul_mem (sp6Q.originalSubgroup.inv_mem hcH)
          (sp6Q.originalSubgroup.mul_mem (sp6Q.originalSubgroup.inv_mem hnqH) hg)) hcH, hcomm⟩
    rw [sp6_cent_spec₄.1, sp6CentQ4, certificate_originalSubgroup] at hyC
    have hmap := Subgroup.mem_map_of_mem (MulAut.conj c).toMonoidHom hyC
    rw [MonoidHom.map_closure] at hmap
    have e : (MulAut.conj c).toMonoidHom (c⁻¹ * (nq⁻¹ * g) * c) = nq⁻¹ * g := by
      change MulAut.conj c (c⁻¹ * (nq⁻¹ * g) * c) = nq⁻¹ * g
      rw [MulAut.conj_apply]
      group
    rw [e] at hmap
    have hmem : nq⁻¹ * g ∈ Subgroup.closure S₀ := by
      refine Subgroup.closure_mono ?_ hmap
      rintro _ ⟨u, hu, rfl⟩
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 (Set.mem_setOf_eq ▸ hu)
      refine Or.inl ⟨j, hlen4 ▸ hj, ?_⟩
      change MulAut.conj c _ = _
      rw [MulAut.conj_apply, List.getD_eq_getElem _ _ hj]
    have hnS : nq ∈ Subgroup.closure S₀ := Subgroup.subset_closure (Or.inr ⟨q, hq, hnq⟩)
    have e' : g = nq * (nq⁻¹ * g) := by group
    rw [e']
    exact Subgroup.mul_mem _ hnS hmem
  exact fanoTestS_false_of_gens (by norm_num) hws has hasq hac hS hK hKa hKd hHw hHm hg hT

theorem cands7_fanoTest
    {g : Equiv.Perm (Fin 36)} (hg : g ∈ co3X36) {T : Table}
    (hT : Rep 36 T g) :
    fanoTestS 36 (cands7.getD 2 []) (spanTabs 36 (cands7.getD 2 [])) (cands7.getD 0 [])
        (spanTabs 36 (cands7.getD 0 [])) rows2 T = false ∧
      fanoTestS 36 (cands7.getD 4 []) (spanTabs 36 (cands7.getD 4 [])) (cands7.getD 1 [])
        (spanTabs 36 (cands7.getD 1 [])) rows4 T = false :=
  ⟨fanoTest_of (t := 0) (by norm_num) ch725107f0 hg hT,
    fanoTest_of (t := 1) (by norm_num) ch725107f1 hg hT⟩

end CertificateChecks.KernelS6I

end
