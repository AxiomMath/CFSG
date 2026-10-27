module

public import Certificates.Kernel.HSStd.PumpH39Checks
public import Certificates.Kernel.HSStd.PumpU3Glue
public import Certificates.Kernel.LocalComp.L39K
public import CFSG.Certificates.Kernel.ConjOrbSound

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelHSStd.PumpH39

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CertificateChecks.KernelLC.L39
open CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer
open CFSG.EvenSporadicStandard.HSStd.FiveY CFSG.EvenSporadicStandard.HSStd.PumpTC7
open CFSG.EvenSmallLie.Child3.SelL39
open CFSG.KC.LocalComp.ExcDeriv (fixCntK)
open CertificateChecks.KernelHSStd.PumpU3 (and_of enumOKL_of_enumOK fixCount_unpack tS_binds sz
  uPts hps)

theorem arrCertOKL_of_arrCertOK {act : ℕ → Array ℕ → Array ℕ} {ngen : ℕ}
    {valid : Array ℕ → Bool} {key : Array ℕ → ℕ} {root : Array ℕ} {c : ArrCert}
    (h : arrCertOK act ngen valid key root c = true) :
    arrCertOKL act ngen valid key root c = true := by
  simp only [arrCertOK, arrCertOKL, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
  exact ⟨h.1, List.isChain_iff_pairwise.2 h.2⟩

theorem gensK_facts {ws : List (List Int)} {ng : ℕ} {G : ℕ → ℕ} (h : gensK ws ng G = true) :
    ws.length = ng ∧ (∀ j < ng, tW (ws.getD j []) = unpack 182 8 (G j) ∧
      lettersOK 7 (ws.getD j []) = true) ∧
    ∀ k < ng, permOK 182 8 (mask 8) (182 * 8) (G k) (pinvS 182 8 (mask 8) (G k)) = true := by
  unfold gensK at h
  obtain ⟨h12, h3⟩ := and_of h
  obtain ⟨h1, h2⟩ := and_of h12
  refine ⟨Nat.eq_of_beq_eq_true h1, fun j hj => ?_, fun k hk => allN_spec h3 k hk⟩
  exact wordEqK_sound tS_binds PumpU3.permLT (allN_spec h2 j hj)

theorem map_get {ws : List (List Int)} {j : ℕ} (hj : j < ws.length) :
    (ws.map tW).toArray[j]! = tW (ws.getD j []) := by
  simp [getElem!_def, hj, List.getD_eq_getElem?_getD]

theorem groupOK_of {ws : List (List Int)} {ng N : ℕ} {G T E S : ℕ → ℕ} {SK : List ℕ}
    (hg : gensK ws ng G = true) (hk : bfsK 182 8 ng G N T E S = true)
    (hK : keysSK 182 8 tKeys N T SK = true) : groupOK ws N = true := by
  obtain ⟨hl, hw, hp⟩ := gensK_facts hg
  have hs : (ws.map tW).toArray.size = ng := by simp [hl]
  have hget : ∀ k < ng, (ws.map tW).toArray[k]! = unpack 182 8 (G k) := fun k hk => by
    rw [map_get (hl ▸ hk)]
    exact (hw k hk).1
  have h1 : ws.all (lettersOK tS.size) = true := by
    rw [List.all_eq_true]
    intro x hx
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
    rw [tS_binds.1, ← List.getD_eq_getElem _ [] hj]
    exact (hw j (hl ▸ hj)).2
  have h2 := enumOKL_of_enumOK (enumOK_of_bfsK_base (fuel := N + 1) hs hget hp hk hps hK
    (Nat.le_succ N))
  have h3 := enumBfs_pts_base (fuel := N + 1) hs hget hk hps hK (Nat.le_succ N)
  unfold groupOK
  rw [h1, h2, h3]
  simp

theorem commOK_of {ws : List (List Int)} {ng : ℕ} {G : ℕ → ℕ} {rp : ℕ}
    (hg : gensK ws ng G = true) (hc : commK ng G rp = true) (hrp : PP 182 8 rp) :
    (ws.map tW).all (fun g => eqA 182 (compA 182 g (unpack 182 8 rp))
      (compA 182 (unpack 182 8 rp) g)) = true := by
  obtain ⟨hl, hw, hp⟩ := gensK_facts hg
  rw [List.all_eq_true]
  intro x hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hy
  have hj' : j < ng := hl ▸ hj
  have e := (hw j hj').1
  rw [List.getD_eq_getElem _ [] hj] at e
  rw [e]
  have hG : PP 182 8 (G j) := PP_of_permOK sz (hp j hj')
  rw [compA_PP hG hrp, compA_PP hrp hG, eqA_PP (hG.mul hrp) (hrp.mul hG)]
  exact allN_spec hc j hj'

theorem nums' : S2.N = 128 ∧ E0.N = 128 ∧ E1.N = 128 ∧ E3.N = 13 ∧ E5.N = 13 ∧ E7.N = 128 ∧
    E9.N = 7 ∧ E10.N = 7 ∧ X.ng = 2 ∧ X.N = 7280 ∧ PumpU3.U.N = 729 := by
  have h := nums
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  tauto

theorem s2OK_true : s2OK s2Cert = true := by
  have hg := gS2
  obtain ⟨hl, hw, hp⟩ := gensK_facts hg
  have h0 : groupOK s2Words 128 = true := by
    have := groupOK_of hg S2.ok kS2
    rwa [nums'.1] at this
  unfold groupOK at h0
  obtain ⟨h12, h3⟩ := and_of h0
  obtain ⟨h1, -⟩ := and_of h12
  have hs : s2Gens.size = S2.ng := by simp [s2Gens, hl]
  have hget : ∀ k < S2.ng, s2Gens[k]! = unpack 182 8 (S2.G k) := fun k hk => by
    rw [s2Gens, map_get (hl ▸ hk)]
    exact (hw k hk).1
  have hpts := enumBfs_pts_base (fuel := 200) hs hget S2.ok hps kS2 (by rw [nums'.1]; omega)
  have hok : enumOKL 182 s2Gens tKeys s2Cert = true := enumOKL_of_enumOK (enumOK_of_bfsK_base (fuel := 200) hs hget hp S2.ok hps kS2
    (by rw [nums'.1]; omega))
  have hsz : (s2Cert.pts.size == 128) = true := by
    rw [s2Cert, hpts, Array.size_ofFn, nums'.1]
    rfl
  have hall : s2Cert.pts.toList.all (fun a => !eqA 182 (compA 182 a a) (idA 182) ||
      eqA 182 a (idA 182) || fixCount a == 22) = true := by
    rw [s2Cert, hpts, Array.toList_ofFn, List.all_eq_true]
    intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 ha
    have hpi : PP 182 8 (S2.T i) := PP_pts S2.ok hp i i.2
    rw [idA_eq sz, compA_PP hpi hpi, eqA_PP (hpi.mul hpi) (PP.id sz), eqA_PP hpi (PP.id sz),
      fixCount_unpack]
    have := allN_spec fixS2 i i.2
    simp only [Bool.or_eq_true, beq_iff_eq, Nat.beq_eq] at this ⊢
    exact this
  unfold s2OK
  rw [h1, hok, hsz, hall]
  rfl

theorem gX' : X.G 0 = LT.S 0 ∧ X.G 1 = LT.S 1 ∧ X.r0 < X.N ∧
    tW x1Word = unpack 182 8 (X.T X.r0) ∧ lettersOK 7 x1Word = true ∧
    permOK 182 8 (mask 8) (182 * 8) (X.T X.r0) (pinvS 182 8 (mask 8) (X.T X.r0)) = true := by
  have h := gX
  simp only [Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  have hw := wordEqK_sound tS_binds PumpU3.permLT h4
  exact ⟨h1, h2, h3, hw.1, hw.2, h5⟩

theorem x1_eq : x1 = unpack 182 8 (X.T X.r0) := gX'.2.2.2.1

theorem gsT_get : ∀ k < 2, gsT[k]! = unpack 182 8 (X.G k) := by
  intro k hk
  interval_cases k
  · rw [gX'.1]
    exact t_0
  · rw [gX'.2.1]
    exact t_1

theorem xOrb : arrCertOK (fun k a => conjA 182 gsT[k]! a) 2 (validA 182) (keyA 182 tKeys) x1
      xCert = true ∧ (∀ x, x ∈ xCert.pts ↔ ∃ i < X.N, unpack 182 8 (X.T i) = x) ∧
      xCert.pts.size = X.N :=
  CFSG.KC.ConjOrb.arrBfs_of_orb (ng := 2) (ngc := X.ng) (fuel := 8000)
    (act := fun k a => conjA 182 gsT[k]! a) (root := x1) (gs := gsT) (ps := tKeys)
    (nums'.2.2.2.2.2.2.2.2.1 ▸ le_refl _) gsT_get (fun _ _ _ => rfl) X.h X.cl X.tr0 gX'.2.2.1
    x1_eq (by rw [x1_eq]; exact validA_unpack gX'.2.2.2.2.2) hps X.k
    (by rw [nums'.2.2.2.2.2.2.2.2.2.1]; omega)

theorem mem_xCert {x : Array ℕ} (hx : x ∈ xCert.pts) :
    ∃ i < X.N, unpack 182 8 (X.T i) = x ∧ canonK 182 8 (mask 8) (182 * 8) (X.T i) = true := by
  obtain ⟨i, hi, rfl⟩ := (xOrb.2.1 x).1 hx
  exact ⟨i, hi, rfl, (CFSG.KC.ConjOrb.closPt_spec (X.cl i hi)).1⟩

theorem xOK_true : xOK xCert = true := by
  have h1 : lettersOK tS.size x1Word = true := by
    rw [tS_binds.1]
    exact gX'.2.2.2.2.1
  have h2 : allLt 2 (fun k => validA 182 gsT[k]!) = true := by
    rw [CFSG.Monster.B.Co2.allLt_iff]
    intro k hk
    rw [gsT_get k hk]
    have hcl := (CFSG.KC.ConjOrb.headK_spec X.h).2 k (by rw [nums'.2.2.2.2.2.2.2.2.1]; exact hk)
    unfold validA
    rw [(invEqK_sound hcl.2.2).1]
    exact (invEqK_sound hcl.2.2).2
  have h3 := arrCertOKL_of_arrCertOK xOrb.1
  have h4 : uCert.pts.toList.all (fun a => fixCount a != 20 ||
      xCert.pts.toList.any (eqA 182 a)) = true := by
    rw [uPts, Array.toList_ofFn, List.all_eq_true]
    intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 ha
    have hw := allN_spec wU i i.2
    rw [fixCount_unpack]
    cases e : Nat.beq (fixCntK 8 (mask 8) (PumpU3.U.T i) 182) 20
    · have hne : fixCntK 8 (mask 8) (PumpU3.U.T i) 182 ≠ 20 := Nat.ne_of_beq_eq_false e
      simp [hne]
    · rw [e] at hw
      simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hw
      obtain ⟨hlt, heq⟩ := hw
      have hmem : unpack 182 8 (X.T (XW i)) ∈ xCert.pts := (xOrb.2.1 _).2 ⟨_, hlt, rfl⟩
      have hc := (CFSG.KC.ConjOrb.closPt_spec (X.cl _ hlt)).1
      simp only [Bool.or_eq_true, List.any_eq_true, Array.mem_toList_iff]
      right
      refine ⟨_, hmem, ?_⟩
      rw [heq, eqA_unpack (heq ▸ hc) (heq ▸ hc), Nat.beq_refl]
  unfold xOK
  rw [h1, h2, h3, h4]
  rfl

theorem repPP (j : ℕ) (hj : j < 11) : PP 182 8 (repP j) := by
  have h := cE
  simp only [Bool.and_eq_true] at h
  exact PP_of_permOK sz (allN_spec h.1.1.1.1.1.1.1 j hj)

theorem rep_getD (j : ℕ) (hj : j < 11) : repArrs.getD j #[] = unpack 182 8 (repP j) := by
  rw [List.getD_eq_getElem _ _ (by simp [repArrs, repWords_length, hj])]
  exact rep_get j hj

theorem excl {ws : List (List Int)} {ng N k : ℕ} {G T E S : ℕ → ℕ} {SK : List ℕ} {j : ℕ}
    (hj : j < 11) (hg : gensK ws ng G = true) (hk : bfsK 182 8 ng G N T E S = true)
    (hK : keysSK 182 8 tKeys N T SK = true) (hc : commK ng G (repP j) = true) (hN : N = k)
    (hd : decide (k ∣ 2880) = false) : exclOK (repArrs.getD j #[]) ws k = true := by
  unfold exclOK
  rw [← hN, groupOK_of hg hk hK, rep_getD j hj, commOK_of hg hc (repPP j hj), hN, hd]
  rfl

theorem surv {j : ℕ} (hj : j < 11)
    (h : ∀ i < X.N, Nat.beq (pcomp 182 8 (mask 8) (X.T i) (repP j))
      (pcomp 182 8 (mask 8) (repP j) (X.T i)) = false) :
    survOK xCert (repArrs.getD j #[]) = true := by
  unfold survOK
  rw [rep_getD j hj, List.all_eq_true]
  intro x hx
  obtain ⟨i, hi, rfl, hc⟩ := mem_xCert (Array.mem_toList_iff.1 hx)
  have hr := repPP j hj
  rw [compA_unpack hc hr.1, compA_unpack hr.1 hc,
    eqA_unpack (CFSG.KC.BfsPin.canonK_pcomp hc hr.1) (CFSG.KC.BfsPin.canonK_pcomp hr.1 hc), h i hi]
  rfl

theorem repOK_all : (List.range 11).all (repOK xCert) = true := by
  have hc := cE
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨-, c0⟩, c1⟩, c3⟩, c5⟩, c7⟩, c9⟩, c10⟩ := hc
  have hs : ∀ i < X.N,
      Nat.beq (pcomp 182 8 (mask 8) (X.T i) (repP 2)) (pcomp 182 8 (mask 8) (repP 2) (X.T i)) =
        false ∧
      Nat.beq (pcomp 182 8 (mask 8) (X.T i) (repP 4)) (pcomp 182 8 (mask 8) (repP 4) (X.T i)) =
        false ∧
      Nat.beq (pcomp 182 8 (mask 8) (X.T i) (repP 6)) (pcomp 182 8 (mask 8) (repP 6) (X.T i)) =
        false ∧
      Nat.beq (pcomp 182 8 (mask 8) (X.T i) (repP 8)) (pcomp 182 8 (mask 8) (repP 8) (X.T i)) =
        false := by
    intro i hi
    have h := allN_spec sX i hi
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩
  have n := nums'
  rw [List.all_eq_true]
  intro j hj
  have hj := List.mem_range.1 hj
  interval_cases j
  · change exclOK (repArrs.getD 0 #[]) (wsOf 0) 128 = true
    exact excl (by norm_num) gE0 E0.ok kE0 c0 n.2.1 (by decide)
  · change exclOK (repArrs.getD 1 #[]) (wsOf 1) 128 = true
    exact excl (by norm_num) gE1 E1.ok kE1 c1 n.2.2.1 (by decide)
  · change survOK xCert (repArrs.getD 2 #[]) = true
    exact surv (by norm_num) fun i hi => (hs i hi).1
  · change exclOK (repArrs.getD 3 #[]) (wsOf 3) 13 = true
    exact excl (by norm_num) gE3 E3.ok kE3 c3 n.2.2.2.1 (by decide)
  · change survOK xCert (repArrs.getD 4 #[]) = true
    exact surv (by norm_num) fun i hi => (hs i hi).2.1
  · change exclOK (repArrs.getD 5 #[]) (wsOf 5) 13 = true
    exact excl (by norm_num) gE5 E5.ok kE5 c5 n.2.2.2.2.1 (by decide)
  · change survOK xCert (repArrs.getD 6 #[]) = true
    exact surv (by norm_num) fun i hi => (hs i hi).2.2.1
  · change exclOK (repArrs.getD 7 #[]) (wsOf 7) 128 = true
    exact excl (by norm_num) gE7 E7.ok kE7 c7 n.2.2.2.2.2.1 (by decide)
  · change survOK xCert (repArrs.getD 8 #[]) = true
    exact surv (by norm_num) fun i hi => (hs i hi).2.2.2
  · change exclOK (repArrs.getD 9 #[]) (wsOf 9) 7 = true
    exact excl (by norm_num) gE9 E9.ok kE9 c9 n.2.2.2.2.2.2.1 (by decide)
  · change exclOK (repArrs.getD 10 #[]) (wsOf 10) 7 = true
    exact excl (by norm_num) gE10 E10.ok kE10 c10 n.2.2.2.2.2.2.2.1 (by decide)

theorem h39OK_true : h39OK = true := by
  change (s2OK s2Cert && xOK xCert && (List.range 11).all (repOK xCert)) = true
  rw [s2OK_true, xOK_true, repOK_all]
  rfl

end CertificateChecks.KernelHSStd.PumpH39

end
