module

public import Certificates.Kernel.S63K.IChecksZ
public import Certificates.Kernel.S63K.IChecksT0
public import Certificates.Kernel.S63K.IChecksT1
public import Certificates.Kernel.S63K.IChecksS
public import Certificates.Kernel.S63K.IBind
public import Certificates.Kernel.S63K.HChecks
public import CFSG.Certificates.Kernel.S63K.ConjTreeSound
public import CFSG.LargeExtraspecial.S63CD4Model
import CFSG.Certificates.Kernel.Common.ForallTree
public import CFSG.Quasithin.Recognition.CertPermAction
public import CFSG.Quasithin.Recognition.CertTrialityCheckInputs

public section

set_option maxRecDepth 400000
set_option exponentiation.threshold 600

namespace CertificateChecks.KernelS63.I21111

open CFSG.LargeExtraspecial.S63 CFSG.KC.S63K CFSG.KC.Co1F2 CFSG.KS.SporSch.M24 CFSG.KC.Enum
  CFSG.KS CFSG.Quasithin Subgroup

#kc_forall_tree tAll (fun b => CertificateChecks.KernelS63.ID.ch21111T b = true) 54
  CertificateChecks.KernelS63.ID.ch21111T
#kc_forall_tree sAll (fun b => CertificateChecks.KernelS63.ID.ch21111S b = true) 54
  CertificateChecks.KernelS63.ID.ch21111S
#kc_forall_tree uAll (fun b => CertificateChecks.KernelS63.ID.ch21111U b = true) 4
  CertificateChecks.KernelS63.ID.ch21111U

theorem blocks {f : ℕ → Bool} {n m : ℕ}
    (hb : ∀ b < m, allN n (fun r => f (Nat.add (Nat.mul n b) r)) = true) (hn : 0 < n) :
    ∀ i < n * m, f i = true := by
  intro i hi
  have h : f (Nat.add (Nat.mul n (i / n)) (i % n)) = true :=
    MatL.allN_iff.1 (hb (i / n) (Nat.div_lt_of_lt_mul hi)) (i % n) (Nat.mod_lt _ hn)
  have e : Nat.add (Nat.mul n (i / n)) (i % n) = i := Nat.div_add_mod i n
  rwa [e] at h

theorem gens_rep {k : ℕ} (hk : k < 8) : RepE d4E (unpackR 24 (ID.G k)) (d4GenG k) := by
  rw [← ID.gens_eq k hk]
  exact repE_d4Gens hk

theorem gens_inv {k : ℕ} (hk : k < 8) : d4GenG k * d4GenG k = 1 := by
  have h := MatL.allN_iff.1 ID.invG k hk
  have e : CFSG.KC.F2W.mulW 24 (ID.G k) (ID.G k) % 2 ^ 576 = idP := by
    rw [← idM_eq, ← shiftLeft_576]
    exact Nat.eq_of_beq_eq_true h
  have h2 := repE_mul (gens_rep hk) (gens_rep hk)
  rw [mulR_unpackR, unpackR_mod, e, ← oneR_eq] at h2
  exact eq_of_repE d4E_injective h2 repE_one

theorem gens_hyp : ∀ l < 8, RepE d4E (unpackR 24 (ID.G l)) (d4GenG l) ∧ d4GenG l * d4GenG l = 1 :=
  fun _ hl => ⟨gens_rep hl, gens_inv hl⟩

theorem word_eq {w : List ℕ} (hw : ∀ k ∈ w, k < 8) :
    wordR d4Gens w = unpackR 24 (wordK ID.G idM w) :=
  wordR_eq fun k hk => ID.gens_eq k (hw k hk)

theorem roots :
    ID.ZP 0 = wordK ID.G idM wordZ % 2 ^ 576 ∧ ID.TP 0 = wordK ID.G idM wordT % 2 ^ 576 := by
  have h := ID.roots
  rw [MatL.bAnd_eq, Bool.and_eq_true, shiftLeft_576] at h
  exact ⟨Nat.eq_of_beq_eq_true h.1, Nat.eq_of_beq_eq_true h.2⟩

theorem z_rep : RepE d4E (unpackR 24 (ID.ZP 0)) d4z := by
  have e : z0R = unpackR 24 (ID.ZP 0) := by
    rw [z0R, word_eq (by decide), unpackR_mod, roots.1]
  rw [← e]
  exact repE_z0R

theorem t_rep : RepE d4E (unpackR 24 (ID.TP 0)) d4t := by
  have e : t0R = unpackR 24 (ID.TP 0) := by
    rw [t0R, word_eq (by decide), unpackR_mod, roots.2]
  rw [← e]
  exact repE_t0R

theorem ztree : ∀ i < 819, treeAtK (cjStepK ID.G) ID.ZP ID.ZQ 8 i = true :=
  MatL.allN_iff.1 ID.ztree

theorem ttree : ∀ i < 68796, treeAtK (cjStepK ID.G) ID.TP ID.TQ 8 i = true := fun i hi =>
  blocks (f := fun i => treeAtK (cjStepK ID.G) ID.TP ID.TQ 8 i) (n := 1274) (m := 54) tAll
    (by norm_num) i (by omega)

theorem zdist : bfsDistK ID.ZP ID.ZS 819 = true := ID.zdist

theorem tdist : bfsDistK ID.TP ID.TS 68796 = true :=
  MatL.allN_iff.2 fun k hk =>
    blocks (f := fun k => distAtK ID.TP ID.TS 68796 k) (n := 1274) (m := 54) sAll (by norm_num) k
      (by omega)

theorem finite_d4 : Finite trialityGroup8 := Finite.of_injective _ d4E_injective

theorem card_z : Nat.card (centralizer ({d4z} : Set trialityGroup8)) * 819 ≤
    Nat.card trialityGroup8 := by
  have := finite_d4
  exact card_centralizer_mul_le_of_treeAtK (by norm_num) gens_hyp ztree zdist z_rep

theorem card_t : Nat.card (centralizer ({d4t} : Set trialityGroup8)) * 68796 ≤
    Nat.card trialityGroup8 := by
  have := finite_d4
  exact card_centralizer_mul_le_of_treeAtK (by norm_num) gens_hyp ttree tdist t_rep

theorem u_eq : ∀ l < 4, uGens[l]! = unpackR 24 (HD.UG l) := fun l hl => by
  rw [uGens_getElem hl, ID.gens_eq _ (uIdx_lt hl), ← ID.ug_eq l hl]

noncomputable abbrev DT : EnumData := DkG HD.TP HD.TPar HD.TLab 4096

theorem ok_dt : enumOK uGens DT.El DT.P DT.K DT.idx = true ∧ DT.El.size = 4096 := by
  have h := ok_of_K uGens_size u_eq HD.repT (closOK_of_bfsK HD.repT)
  simp only [EnumData.ok, Bool.and_eq_true, beq_iff_eq] at h
  exact h

theorem uGens_hyp' : ∀ k < uGens.size, RepE d4E uGens[k]! (uGH k) ∧ uGH k * uGH k = 1 :=
  fun k hk => ⟨repE_uGens hk, gens_inv (uIdx_lt (uGens_size ▸ hk))⟩

theorem card_U : Nat.card (closure (genSet uGH uGens.size)) = 4096 := by
  rw [card_of_enumOK d4E_injective uGens_hyp' ok_dt.1, ok_dt.2]

theorem tags : ∀ i < 4096, ID.tagK i = true := fun i hi =>
  blocks (f := ID.tagK) (n := 1024) (m := 4) uAll (by norm_num) i (by omega)

theorem conj_of_mem {u : trialityGroup8} (hu : u ∈ closure (genSet uGH uGens.size))
    (huu : u * u = 1) (hu1 : u ≠ 1) : ∃ c, u = c * d4z * c⁻¹ ∨ u = c * d4t * c⁻¹ := by
  obtain ⟨i, hi, hrep⟩ := exists_mem_of_enumOK uGens_hyp' ok_dt.1 hu
  rw [ok_dt.2] at hi
  change RepE d4E (ElG HD.TP 4096)[i]! u at hrep
  rw [elG_get hi] at hrep
  have hsq : CFSG.KC.F2W.mulW 24 (HD.TP i) (HD.TP i) % 2 ^ 576 = idM := by
    have h2 := repE_mul hrep hrep
    rw [mulR_unpackR, huu] at h2
    have h1 : RepE d4E (unpackR 24 idP) (1 : trialityGroup8) := by
      rw [← oneR_eq]
      exact repE_one
    rw [mod_eq_of_repE h2 h1, Nat.mod_eq_of_lt idP_lt, idM_eq]
  have hne : HD.TP i ≠ idM := by
    intro e
    rw [e, idM_eq, ← oneR_eq] at hrep
    exact hu1 (eq_of_repE d4E_injective hrep repE_one)
  rcases tagAtK_spec (tags i hi) hsq hne with ⟨j, hj, he⟩ | ⟨j, hj, he⟩
  · obtain ⟨c, hc⟩ := exists_conj_of_treeAtK (by norm_num) gens_hyp ztree z_rep j hj
    rw [he] at hc
    exact ⟨c, Or.inl (eq_of_repE d4E_injective hrep hc)⟩
  · obtain ⟨c, hc⟩ := exists_conj_of_treeAtK (by norm_num) gens_hyp ttree t_rep j hj
    rw [he] at hc
    exact ⟨c, Or.inr (eq_of_repE d4E_injective hrep hc)⟩

theorem facts :
    (∀ k < 8, d4GenG k * d4GenG k = 1) ∧ Nat.card (closure (genSet uGH uGens.size)) = 4096 ∧
      Nat.card (centralizer ({d4z} : Set trialityGroup8)) * 819 ≤ Nat.card trialityGroup8 ∧
      Nat.card (centralizer ({d4t} : Set trialityGroup8)) * 68796 ≤ Nat.card trialityGroup8 ∧
      ∀ u ∈ closure (genSet uGH uGens.size), u * u = 1 → u ≠ 1 →
        ∃ c, u = c * d4z * c⁻¹ ∨ u = c * d4t * c⁻¹ :=
  ⟨fun _ hk => gens_inv hk, card_U, card_z, card_t, fun _ hu huu hu1 => conj_of_mem hu huu hu1⟩

end CertificateChecks.KernelS63.I21111

end
