module

import Mathlib.Tactic.IntervalCases
public import Certificates.Kernel.McL.Relators

public section

namespace CertificateChecks.KernelMcL

open CFSG.KC CFSG.KC.LceS CFSG.KC.Loop CFSG.Certificates CFSG.Certificates.LCE
  CFSG.Certificates.McLD
open CertificateChecks.KernelHe CertificateChecks.KernelRu

@[expose] noncomputable def fgx (l : ℕ) : FreeGroup (Fin 4) :=
  if l % 2 = 0 then FreeGroup.of ⟨l / 2 % 4, Nat.mod_lt _ (by norm_num)⟩
  else (FreeGroup.of ⟨l / 2 % 4, Nat.mod_lt _ (by norm_num)⟩)⁻¹

@[expose] noncomputable def fgc (c : ℕ) : FreeGroup (Fin 4) :=
  FreeGroup.of ⟨c % 4, Nat.mod_lt _ (by norm_num)⟩

@[expose] noncomputable def fword (F : ℕ → FreeGroup (Fin 4)) (W n : ℕ) : FreeGroup (Fin 4) :=
  ((List.range n).map fun i => F (wLet W i)).prod

@[expose] def rels1 : Set (FreeGroup (Fin 4)) :=
  {w | (∃ r < 79, w = fword fgx (LceS.wWord (McL.Rels.NR1 r)) (LceS.wLen (McL.Rels.NR1 r))) ∨
    (∃ r < 34, w = fword fgc (LceS.wWord (McL.Rels.GR r)) (LceS.wLen (McL.Rels.GR r)))}

abbrev G1 : Type := PresentedGroup rels1

@[expose] noncomputable def gen1 (c : ℕ) : G1 := PresentedGroup.of ⟨c % 4, Nat.mod_lt _ (by norm_num)⟩

theorem hom_fword {H : Type*} [Group H] (φ : FreeGroup (Fin 4) →* H) (F : ℕ → FreeGroup (Fin 4))
    (W n : ℕ) : φ (fword F W n) = ((List.range n).map fun i => φ (F (wLet W i))).prod := by
  rw [fword, map_list_prod, List.map_map]
  rfl

theorem bval_gen1 {W n : ℕ} (h : ∀ i < n, wLet W i < 6) :
    bval gen1 W n = PresentedGroup.mk rels1 (fword fgx W n) := by
  rw [hom_fword]
  unfold bval
  congr 1
  apply List.map_congr_left
  intro i hi
  have hl := h i (List.mem_range.mp hi)
  unfold letV fgx gen1
  split_ifs with h1 h2 <;> first | omega | simp [PresentedGroup.of]

theorem ival_gen1 {W n : ℕ} (h : ∀ i < n, wLet W i < 4) :
    ival gen1 W n = PresentedGroup.mk rels1 (fword fgc W n) := by
  rw [hom_fword]
  unfold ival
  congr 1
  apply List.map_congr_left
  intro i hi
  have hl := h i (List.mem_range.mp hi)
  split_ifs with h1
  · omega
  · rfl

theorem gr_letters : ∀ r < 34, ∀ i < LceS.wLen (McL.Rels.GR r),
    wLet (LceS.wWord (McL.Rels.GR r)) i < 4 := by
  have hNR : CFSG.KD.McL.D.NR = 34 := Nat.eq_of_beq_eq_true CFSG.KD.McL.D.xNR
  intro r hr
  exact relsOK_sound CFSG.KD.McL.D.xRel r (by rw [hNR]; exact hr)

theorem g1_nr1 : ∀ r < 79, bval gen1 (LceS.wWord (McL.Rels.NR1 r)) (LceS.wLen (McL.Rels.NR1 r)) = 1 := by
  intro r hr
  rw [bval_gen1 (nr1_letters r hr)]
  exact PresentedGroup.one_of_mem (Or.inl ⟨r, hr, rfl⟩)

theorem g1_gr : ∀ r < 34, ival gen1 (LceS.wWord (McL.Rels.GR r)) (LceS.wLen (McL.Rels.GR r)) = 1 := by
  intro r hr
  rw [ival_gen1 (gr_letters r hr)]
  exact PresentedGroup.one_of_mem (Or.inr ⟨r, hr, rfl⟩)

theorem cn_bound : ∀ (H : Type) [Group H] (z : ℕ → H),
    (∀ r < 79, bval z (LceS.wWord (McL.Rels.NR1 r)) (LceS.wLen (McL.Rels.NR1 r)) = 1) →
      Nat.card (Subgroup.closure (z '' {i | i < 3})) ≠ 0 ∧
        Nat.card (Subgroup.closure (z '' {i | i < 3})) ≤ CFSG.KD.McL.D.NORD := by
  intro H _ z hz
  have hQ := lceOk_sound CN.ok z (fun r hr => hz r hr)
  have hsub : (fun j => bval z (LceS.wWord (McL.Rels.STQ j)) (LceS.wLen (McL.Rels.STQ j))) ''
      {j | j < 65536} = {z 0 * z 1} := by
    have e : (fun j => bval z (LceS.wWord (McL.Rels.STQ j)) (LceS.wLen (McL.Rels.STQ j))) =
        fun _ => z 0 * z 1 := by
      funext j
      have hs : McL.Rels.STQ j = McL.Rels.SQ := rfl
      rw [hs, bval_eq_list z _ _ [0, 2] (by decide)]
      simp [letV]
    rw [e]
    exact Set.Nonempty.image_const ⟨0, by norm_num⟩ _
  have h6 : {g : ℕ | 2 * g < 6} = {i | i < 3} := by
    ext g
    simp only [Set.mem_ofPred_eq]
    omega
  have hQ' : (Subgroup.closure ({z 0 * z 1} : Set H)).relIndex
      (Subgroup.closure (z '' {i | i < 3})) ≠ 0 ∧
      (Subgroup.closure ({z 0 * z 1} : Set H)).relIndex
      (Subgroup.closure (z '' {i | i < 3})) ≤ CFSG.KD.McL.CN.nAlive := by
    rw [← hsub, ← h6]
    exact hQ
  have h5 : (z 0 * z 1) ^ 5 = 1 := by
    have h := hz 3 (by norm_num)
    rw [Nat.eq_of_beq_eq_true CFSG.KD.McL.Bind.p5n,
      bval_eq_list z _ _ [0, 2, 0, 2, 0, 2, 0, 2, 0, 2] (by decide)] at h
    simpa [letV, pow_succ, mul_assoc] using h
  have hc : Nat.card (Subgroup.closure ({z 0 * z 1} : Set H)) ≠ 0 ∧
      Nat.card (Subgroup.closure ({z 0 * z 1} : Set H)) ≤ 5 := by
    rw [← Subgroup.zpowers_eq_closure, Nat.card_zpowers]
    have hd : orderOf (z 0 * z 1) ∣ 5 := orderOf_dvd_of_pow_eq_one h5
    exact ⟨(Nat.pos_of_dvd_of_pos hd (by norm_num)).ne', Nat.le_of_dvd (by norm_num) hd⟩
  have c := card_le_step' hQ' hc
  have e5 : CFSG.KD.McL.CN.nAlive * 5 = CFSG.KD.McL.D.NORD := by
    rw [Nat.mul_comm]
    exact Nat.eq_of_beq_eq_true CFSG.KD.McL.Bind.cN
  rw [e5] at c
  exact c

theorem dce_append (FB HB GB TB WD : Nat → Nat) (LT TL NL ND NO nH nT nW : Nat) :
    ∀ (l1 l2 : List Nat) (x : Nat),
    McL.Dce.runFacts FB HB GB TB WD LT TL NL ND NO nH nT nW (List.append l1 l2) x =
      McL.Dce.runFacts FB HB GB TB WD LT TL NL ND NO nH nT nW l2
        (McL.Dce.runFacts FB HB GB TB WD LT TL NL ND NO nH nT nW l1 x)
  | [], _, _ => rfl
  | C :: l1, l2, x => by
    change strictN (McL.Dce.runChunk FB HB GB TB WD LT TL NL ND NO nH nT nW C x)
        (McL.Dce.runFacts FB HB GB TB WD LT TL NL ND NO nH nT nW (List.append l1 l2)) =
      McL.Dce.runFacts FB HB GB TB WD LT TL NL ND NO nH nT nW l2
        (strictN (McL.Dce.runChunk FB HB GB TB WD LT TL NL ND NO nH nT nW C x)
          (McL.Dce.runFacts FB HB GB TB WD LT TL NL ND NO nH nT nW l1))
    rw [strictN_eq', strictN_eq']
    exact dce_append FB HB GB TB WD LT TL NL ND NO nH nT nW l1 l2 _

theorem dce_join {FB HB GB TB WD : Nat → Nat} {LT TL NL ND NO nH nT nW : Nat} {l1 l2 : List Nat}
    {x y z : Nat}
    (h1 : Nat.beq (McL.Dce.runFacts FB HB GB TB WD LT TL NL ND NO nH nT nW l1 x) y = true)
    (h2 : Nat.beq (McL.Dce.runFacts FB HB GB TB WD LT TL NL ND NO nH nT nW l2 y) z = true) :
    Nat.beq (McL.Dce.runFacts FB HB GB TB WD LT TL NL ND NO nH nT nW (List.append l1 l2) x) z =
      true := by
  rw [Nat.beq_eq] at h1 h2 ⊢
  rw [dce_append, h1, h2]

theorem dce_stab : ∀ D < CFSG.KD.McL.D.ND, McL.Dce.aliveD CFSG.KD.McL.D.AL D = true → D ≠ 0 →
    ∃ (EB : ℕ → ℕ) (D' SG qb m X0 X1 Y0 Y1 : ℕ) (Cs Ce : List ℕ),
      McL.Dce.stabStart EB = true ∧
      Nat.beq (McL.Dce.runStab CFSG.KD.McL.D.FB EB CFSG.KD.McL.D.NF D' SG Cs X0) X1 = true ∧
      Nat.beq (McL.Dce.runSorted (McL.Dce.mat EB) qb m Ce Y0) Y1 = true ∧
      Nat.beq (McL.Dce.sortedCount Y1) m = true ∧ D' = D ∧ X0 = 2 ∧ X1 = m + 1 ∧ Y0 = 1 ∧
      McL.Dce.bits CFSG.KD.McL.D.MD (20 * D) 20 = m := by
  have hND : CFSG.KD.McL.D.ND = 14 := rfl
  intro D hD hal h0
  rw [hND] at hD
  interval_cases D
  · exact absurd rfl h0
  · exact ⟨_, _, _, _, _, _, _, _, _, _, _, CFSG.KD.McL.D.stab1a, CFSG.KD.McL.D.stab1b,
      CFSG.KD.McL.D.E1s, CFSG.KD.McL.D.E1n, rfl, rfl, rfl, rfl,
      Nat.eq_of_beq_eq_true CFSG.KD.McL.D.stab1m⟩
  · exact ⟨_, _, _, _, _, _, _, _, _, _, _, CFSG.KD.McL.D.stab2a, CFSG.KD.McL.D.stab2b,
      CFSG.KD.McL.D.E2s, CFSG.KD.McL.D.E2n, rfl, rfl, rfl, rfl,
      Nat.eq_of_beq_eq_true CFSG.KD.McL.D.stab2m⟩
  · exact absurd hal (by decide)
  · exact ⟨_, _, _, _, _, _, _, _, _, _, _, CFSG.KD.McL.D.stab4a, CFSG.KD.McL.D.stab4b,
      CFSG.KD.McL.D.E4s, CFSG.KD.McL.D.E4n, rfl, rfl, rfl, rfl,
      Nat.eq_of_beq_eq_true CFSG.KD.McL.D.stab4m⟩
  · exact ⟨_, _, _, _, _, _, _, _, _, _, _, CFSG.KD.McL.D.stab5a, CFSG.KD.McL.D.stab5b,
      CFSG.KD.McL.D.E5s, CFSG.KD.McL.D.E5n, rfl, rfl, rfl, rfl,
      Nat.eq_of_beq_eq_true CFSG.KD.McL.D.stab5m⟩
  · exact ⟨_, _, _, _, _, _, _, _, _, _, _, CFSG.KD.McL.D.stab6a, CFSG.KD.McL.D.stab6b,
      CFSG.KD.McL.D.E6s, CFSG.KD.McL.D.E6n, rfl, rfl, rfl, rfl,
      Nat.eq_of_beq_eq_true CFSG.KD.McL.D.stab6m⟩
  · exact ⟨_, _, _, _, _, _, _, _, _, _, _, CFSG.KD.McL.D.stab7a, CFSG.KD.McL.D.stab7b,
      CFSG.KD.McL.D.E7s, CFSG.KD.McL.D.E7n, rfl, rfl, rfl, rfl,
      Nat.eq_of_beq_eq_true CFSG.KD.McL.D.stab7m⟩
  · exact ⟨_, _, _, _, _, _, _, _, _, _, _, CFSG.KD.McL.D.stab8a, CFSG.KD.McL.D.stab8b,
      CFSG.KD.McL.D.E8s, CFSG.KD.McL.D.E8n, rfl, rfl, rfl, rfl,
      Nat.eq_of_beq_eq_true CFSG.KD.McL.D.stab8m⟩
  · exact ⟨_, _, _, _, _, _, _, _, _, _, _, CFSG.KD.McL.D.stab9a, CFSG.KD.McL.D.stab9b,
      CFSG.KD.McL.D.E9s, CFSG.KD.McL.D.E9n, rfl, rfl, rfl, rfl,
      Nat.eq_of_beq_eq_true CFSG.KD.McL.D.stab9m⟩
  · exact ⟨_, _, _, _, _, _, _, _, _, _, _, CFSG.KD.McL.D.stab10a, CFSG.KD.McL.D.stab10b,
      CFSG.KD.McL.D.E10s, CFSG.KD.McL.D.E10n, rfl, rfl, rfl, rfl,
      Nat.eq_of_beq_eq_true CFSG.KD.McL.D.stab10m⟩
  · exact ⟨_, _, _, _, _, _, _, _, _, _, _, CFSG.KD.McL.D.stab11a, CFSG.KD.McL.D.stab11b,
      CFSG.KD.McL.D.E11s, CFSG.KD.McL.D.E11n, rfl, rfl, rfl, rfl,
      Nat.eq_of_beq_eq_true CFSG.KD.McL.D.stab11m⟩
  · exact ⟨_, _, _, _, _, _, _, _, _, _, _, CFSG.KD.McL.D.stab12a, CFSG.KD.McL.D.stab12b,
      CFSG.KD.McL.D.E12s, CFSG.KD.McL.D.E12n, rfl, rfl, rfl, rfl,
      Nat.eq_of_beq_eq_true CFSG.KD.McL.D.stab12m⟩
  · exact ⟨_, _, _, _, _, _, _, _, _, _, _, CFSG.KD.McL.D.stab13a, CFSG.KD.McL.D.stab13b,
      CFSG.KD.McL.D.E13s, CFSG.KD.McL.D.E13n, rfl, rfl, rfl, rfl,
      Nat.eq_of_beq_eq_true CFSG.KD.McL.D.stab13m⟩

theorem g1_dce : Nat.card (Subgroup.closure (gen1 '' {c | c < CFSG.KD.McL.D.NL})) ≠ 0 ∧
    Nat.card (Subgroup.closure (gen1 '' {c | c < CFSG.KD.McL.D.NL})) ≤
      CFSG.KD.McL.D.NORD * CFSG.KD.McL.D.SUM ∧
    ∀ Wd n J, McL.Dce.traceOK CFSG.KD.McL.D.FB CFSG.KD.McL.D.HB CFSG.KD.McL.D.GB
      CFSG.KD.McL.D.TB CFSG.KD.McL.D.LT CFSG.KD.McL.D.TL CFSG.KD.McL.D.NL CFSG.KD.McL.D.nT
      CFSG.KD.McL.D.NF Wd n J = true → ival gen1 Wd n = 1 := by
  have hNR : CFSG.KD.McL.D.NR = 34 := Nat.eq_of_beq_eq_true CFSG.KD.McL.D.xNR
  have hI0 : CFSG.KD.McL.D.I0 < CFSG.KD.McL.D.NO := by
    have h := CFSG.KD.McL.D.xI0
    rwa [Nat.blt_eq] at h
  have hc1 : Nat.add 1 (Nat.shiftLeft CFSG.KD.McL.D.ND 20) = 1 + CFSG.KD.McL.D.ND * 2 ^ 20 := by
    decide
  have hF := dce_join (dce_join (dce_join (dce_join (dce_join (dce_join (dce_join
    (dce_join (dce_join (dce_join (dce_join (dce_join (dce_join (dce_join (dce_join (dce_join
    (dce_join (dce_join (dce_join (dce_join CFSG.KD.McL.D.f0 CFSG.KD.McL.D.f1) CFSG.KD.McL.D.f2)
    CFSG.KD.McL.D.f3) CFSG.KD.McL.D.f4) CFSG.KD.McL.D.f5) CFSG.KD.McL.D.f6) CFSG.KD.McL.D.f7)
    CFSG.KD.McL.D.f8) CFSG.KD.McL.D.f9) CFSG.KD.McL.D.f10) CFSG.KD.McL.D.f11)
    CFSG.KD.McL.D.f12) CFSG.KD.McL.D.f13) CFSG.KD.McL.D.f14) CFSG.KD.McL.D.f15)
    CFSG.KD.McL.D.f16) CFSG.KD.McL.D.f17) CFSG.KD.McL.D.f18) CFSG.KD.McL.D.f19)
    CFSG.KD.McL.D.f20
  exact dce_sound gen1 (FB := CFSG.KD.McL.D.FB) (HB := CFSG.KD.McL.D.HB)
    (GB := CFSG.KD.McL.D.GB) (TB := CFSG.KD.McL.D.TB) (OB := CFSG.KD.McL.D.OB)
    (WD := CFSG.KD.McL.D.WD) (RR := McL.Rels.GR) (NRN := McL.Rels.NR1)
    (LT := CFSG.KD.McL.D.LT) (LI := CFSG.KD.McL.D.LI) (TL := CFSG.KD.McL.D.TL)
    (NL := CFSG.KD.McL.D.NL) (ND := CFSG.KD.McL.D.ND) (NO := CFSG.KD.McL.D.NO)
    (NF := CFSG.KD.McL.D.NF) (nH := CFSG.KD.McL.D.nH) (nT := CFSG.KD.McL.D.nT)
    (nW := CFSG.KD.McL.D.nW) (NR := CFSG.KD.McL.D.NR) (I0 := CFSG.KD.McL.D.I0)
    (AL := CFSG.KD.McL.D.AL) (MD := CFSG.KD.McL.D.MD) (NORD := CFSG.KD.McL.D.NORD)
    (SUM := CFSG.KD.McL.D.SUM) (WH := CFSG.KD.McL.D.WH)
    rfl rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    CFSG.KD.McL.D.hdr rfl rfl CFSG.KD.McL.D.gom rfl rfl CFSG.KD.McL.D.psi rfl rfl
    CFSG.KD.McL.D.TSs rfl CFSG.KD.McL.D.TSn CFSG.KD.McL.D.OSs rfl CFSG.KD.McL.D.OSn
    hF rfl rfl CFSG.KD.McL.D.cov rfl hc1 dce_stab CFSG.KD.McL.D.xLet CFSG.KD.McL.D.xRel
    (by rw [hNR]; exact norm_GR) CFSG.KD.McL.D.xWords CFSG.KD.McL.D.xTsq CFSG.KD.McL.D.xNrels
    hI0 (Nat.eq_of_beq_eq_true CFSG.KD.McL.D.xT5) CFSG.KD.McL.D.xSum
    (by rw [hNR]; exact g1_gr) g1_nr1 cn_bound

theorem g1_top : Subgroup.closure (gen1 '' {c | c < CFSG.KD.McL.D.NL}) = ⊤ := by
  rw [eq_top_iff, ← PresentedGroup.closure_range_of, Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  apply Subgroup.subset_closure
  refine ⟨i.val, i.isLt, ?_⟩
  unfold gen1
  congr 1
  exact Fin.ext (Nat.mod_eq_of_lt i.isLt)

theorem g1_card : Finite G1 ∧ Nat.card G1 ≤ CFSG.KD.McL.D.NORD * CFSG.KD.McL.D.SUM :=
  KB.finite_card_le_of_top g1_top ⟨g1_dce.1, g1_dce.2.1⟩

theorem g1_traces : ∀ k < 2, ival gen1 (LceS.wWord (trw k)) (LceS.wLen (trw k)) = 1 := by
  intro k hk
  interval_cases k
  · exact g1_dce.2.2 _ _ _ CFSG.KD.McL.D.tr0
  · exact g1_dce.2.2 _ _ _ CFSG.KD.McL.D.tr1

end CertificateChecks.KernelMcL

end
