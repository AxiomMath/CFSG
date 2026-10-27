module

public import CFSG.Sporadic.FischerOddCore.Fi22CTICheckInputs
public meta import CFSG.Sporadic.FischerOddCore.Fi22SylowCheck
public import Certificates.Kernel.Sporadic.Fi22.C2064
public import Certificates.Kernel.Sporadic.Fi22.K2064
public import CFSG.Sporadic.FischerOddCore.ClosureSearchEq
public import CFSG.Sporadic.FischerOddCore.CtiSearchSpec
public import CFSG.Certificates.NativeSchreierCard
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Fi22CtiG

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Certificates CFSG.Certificates.Native
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer
open CFSG.Sporadic.FischerOddCore CFSG.Sporadic.FischerOddCore.Native
open CFSG.Sporadic.FischerOddCore.SearchSpec
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.Fi22CtiX
open CertificateChecks.KernelSpor.Fi22CtiA

theorem inj_of_keysOK {n : ℕ} {b : List ℕ} {E : Array (Array ℕ)} (h : keysOK n b E = true) :
    ∀ i < E.size, ∀ j < E.size, E[i]! = E[j]! → i = j := by
  have hnd : (E.toList.map (keyAt n b)).Nodup := by
    have hs := CFSG.Certificates.strictIncr_pairwise h
    exact ((List.mergeSort_perm _ _).nodup_iff).1 (hs.imp ne_of_lt)
  intro i hi j hj e
  have hlen : (E.toList.map (keyAt n b)).length = E.size := by simp
  have hk : keyAt n b E[i]! = keyAt n b E[j]! := by rw [e]
  rw [getElem!_pos E i hi, getElem!_pos E j hj] at hk
  exact (hnd.getElem_inj_iff (i := i) (j := j) (hi := by rw [hlen]; exact hi)
    (hj := by rw [hlen]; exact hj)).1 (by
      simp only [List.getElem_map, Array.getElem_toList]
      exact hk)

theorem keyAt_inj {n : ℕ} : ∀ (b : List ℕ) {t u : Array ℕ}, (∀ x ∈ b, t[x]! < n) →
    (∀ x ∈ b, u[x]! < n) → keyAt n b t = keyAt n b u → ∀ x ∈ b, t[x]! = u[x]!
  | [], _, _, _, _, _, x, hx => absurd hx List.not_mem_nil
  | y :: b, t, u, ht, hu, h, x, hx => by
    have hty := ht y List.mem_cons_self
    have huy := hu y List.mem_cons_self
    have h' : t[y]! + n * keyAt n b t = u[y]! + n * keyAt n b u := h
    have h1 : t[y]! = u[y]! := by
      have := congrArg (· % n) h'
      simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hty, Nat.mod_eq_of_lt huy] at this
      exact this
    have h2 : keyAt n b t = keyAt n b u := by
      rw [h1] at h'
      exact Nat.eq_of_mul_eq_mul_left (lt_of_le_of_lt (Nat.zero_le _) hty) (Nat.add_left_cancel h')
    rcases List.mem_cons.1 hx with rfl | hx'
    · exact h1
    · exact keyAt_inj b (fun z hz => ht z (List.mem_cons_of_mem _ hz))
        (fun z hz => hu z (List.mem_cons_of_mem _ hz)) h2 x hx'

theorem lab_size : ctiLab.size = 1024 := by rw [ctiLab, Fi22CtiT.lab_eq, unpack_size]

theorem nxt_size : ctiNxt.size = 10240 := by rw [ctiNxt, Fi22CtiT.nxt_eq, unpack_size]

theorem cid_size : ctiCids.size = 1024 := by rw [ctiCids, Fi22CtiT.cid_eq, unpack_size]

theorem zi_size : ctiZi.size = 1024 := by rw [ctiZi, Fi22CtiT.zi_eq, unpack_size]

theorem EE_elt_size (htext : fi22Cent3510Text = Fi22E2065.textP) {i : ℕ} (hi : i < 1024) :
    EE[i]!.size = 3510 := by
  rw [E_eq htext, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn, Array.size_ofFn]

theorem EE_eq_mulTree (htext : fi22Cent3510Text = Fi22E2065.textP) :
    EE = mulTree 3510 ctiQArr ctiPar ctiLab := by
  rw [E_eq htext]
  exact (CFSG.KS.MulTree.mulTree_eq (gs := 10) (fun _ hk => ctiQArr_get htext hk)
    (fun _ hk x hx => pq_lt (by omega) hx) par_size (by norm_num)
    (fun i hi h0 => ⟨par_get hi, rows_PA i hi h0⟩)
    (fun i hi h0 => ⟨lab_get hi, rows_LA i hi h0⟩)).symm

theorem EE_inj (htext : fi22Cent3510Text = Fi22E2065.textP) :
    ∀ i < EE.size, ∀ j < EE.size, EE[i]! = EE[j]! → i = j :=
  inj_of_keysOK (keys_ok htext)

theorem search_eq
    (htext : fi22Cent3510Text = Fi22E2065.textP) :
    closureSearch 3510 ctiQArr 1100 = (EE, ctiPar, ctiLab, ctiNxt) := by
  have hs := E_size htext
  refine closureSearch_eq_of (fn := NX) (fp := PA) (fl := LA) (closure_ok htext)
    (fun i hi => EE_elt_size htext (by omega)) (EE_inj htext) (by omega)
    (by rw [par_size, hs]) (by rw [lab_size, hs]) (by rw [nxt_size, hs, ctiQArr_size])
    (fun i hi => par_get (by omega)) (fun i hi => lab_get (by omega))
    (fun t ht => nxt_get (by rw [hs, ctiQArr_size] at ht; omega)) ?_
  rw [ctiQArr_size, hs]
  exact Fi22CtiB.bfs

theorem ZI_lt
    (htext : fi22Cent3510Text = Fi22E2065.textP) {i : ℕ} (hi : i < 1024) : ZI i < 1024 := by
  rw [← zi_get hi]
  exact (coset_ok htext hi).2.1

theorem cosets_eq
    (htext : fi22Cent3510Text = Fi22E2065.textP) :
    ctiCosets EE ctiZ = (ctiCids, ctiReps, ctiZi) := by
  have hs := E_size htext
  refine ctiCosets_eq (M := 1024) (R := 512) hs (by rw [← hs]; exact EE_inj htext) zi_size
    (fun i hi => ?_) (fun i hi => ?_) cid_size reps_size (fun c hc => ?_) (fun c hc => ?_)
    (fun i hi => ?_) (fun i hi => (coset_ok htext hi).2.2.2.1)
  · obtain ⟨-, hz, he, -, -⟩ := coset_ok htext hi
    exact ⟨hz, arr_eq_of_eqA (EE_elt_size htext hz) (compA_size _ _ _) he⟩
  · have h := allN_spec Fi22CtiB.ziRows i hi
    unfold Fi22CtiB.ziRow at h
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
    have hzl := ZI_lt htext hi
    rw [zi_get hi, zi_get hzl]
    refine ⟨Nat.eq_of_beq_eq_true h1, fun e => ?_⟩
    rw [e, Nat.beq_refl] at h2
    exact Bool.noConfusion h2
  · obtain ⟨h1, h2⟩ := reps_ok c hc
    refine ⟨h1, h2, ?_⟩
    have h := allN_spec Fi22CtiB.repRows c hc
    rw [reps_get hc] at h1 ⊢
    rw [zi_get h1]
    exact Nat.blt_eq ▸ h
  · have h := allN_spec Fi22CtiB.incRows c (by omega)
    rw [reps_get (by omega), reps_get hc]
    exact Nat.blt_eq ▸ h
  · obtain ⟨hc, -⟩ := coset_ok htext hi
    refine ⟨hc, ?_⟩
    have h := allN_spec Fi22CtiB.cidRows i hi
    rw [cid_get hi] at hc ⊢
    rw [reps_get hc, zi_get hi]
    rcases (bOr_iff _ _).1 h with h | h
    · exact Or.inl (Nat.eq_of_beq_eq_true h)
    · exact Or.inr (Nat.eq_of_beq_eq_true h)

theorem conj_size (g gi a : Array ℕ) : (conjArr 3510 g gi a).size = 3510 := compA_size _ _ _

theorem pis_eq
    (htext : fi22Cent3510Text = Fi22E2065.textP) :
    ((List.range 9).toArray.map fun k => ctiPi EE ctiCids ctiReps (ctiG k) (ctiGi k)) =
      ctiS5.extract 0 9 := by
  have hs := E_size htext
  refine Array.ext (by rw [Array.size_map, pis_count]; simp) fun k h1 h2 => ?_
  have hk : k < 9 := by simpa using h1
  simp only [Array.getElem_map, List.getElem_toArray, List.getElem_range]
  rw [← getElem!_pos (ctiS5.extract 0 9) k h2]
  refine ctiPi_eq (EE_inj htext) (by rw [pis_size hk, reps_size]) fun c hc => ?_
  have hc' : c < 512 := by rw [reps_size] at hc; exact hc
  obtain ⟨hlt, hin⟩ := pi_ok htext hk hc'
  obtain ⟨hr, hrc⟩ := reps_ok _ hlt
  unfold ctiInCoset at hin
  rcases Bool.or_eq_true_iff.1 hin with h | h
  · exact ⟨_, by rw [hs]; exact hr,
      (arr_eq_of_eqA (conj_size _ _ _) (EE_elt_size htext hr) h).symm, hrc⟩
  · obtain ⟨-, hz, he, hcz, -⟩ := coset_ok htext hr
    refine ⟨_, by rw [hs]; exact hz, ?_, by rw [hcz, hrc]⟩
    rw [arr_eq_of_eqA (EE_elt_size htext hz) (compA_size _ _ _) he]
    exact (arr_eq_of_eqA (conj_size _ _ _) (compA_size _ _ _) h).symm

@[expose] def B5 : List (Fin 512) := [18, 32, 2]

theorem B5_nodup : B5.Nodup := by decide

theorem B5_val : (B5.map Fin.val).toArray = ctiB5 := rfl

@[expose] noncomputable def Q5 : RawSchreierDatum 512 :=
  RawSchreierDatum.ofArrays 512 (by norm_num) ctiS5 9 (by rw [image_ok.1]; norm_num) B5 B5_nodup
    ctiW5

theorem chainArr : ChainArrays Q5 (ctiS5.extract 0 9) ctiS5 ctiB5 ctiW5 := by
  rw [← B5_val]
  exact chainArrays_ofArrays (chainCheckFacts image_ok.2.1).strong_inv

@[expose] noncomputable def PiP (k : ℕ) : Equiv.Perm (Fin 512) :=
  permOfArr 512 (ctiS5.extract 0 9)[k]!

theorem rep_PiP : ∀ k < (ctiS5.extract 0 9).size, Rep 512 (ctiS5.extract 0 9)[k]! (PiP k) := by
  intro k hk
  have hk' : k < 9 := by rw [pis_count] at hk; exact hk
  have e : (ctiS5.extract 0 9)[k]! = ctiS5[k]! := by
    rw [getElem!_pos _ k hk, getElem!_pos ctiS5 k (by rw [image_ok.1]; omega)]
    simp only [Array.getElem_extract, Nat.zero_add]
  rw [PiP, e]
  exact (rep_permOfArr ((chainCheckFacts image_ok.2.1).strong_inv k
    (by rw [image_ok.1]; omega))).1

theorem Q5_eq : Q5.originalSubgroup = gensClosure (ctiS5.extract 0 9) PiP := by
  unfold RawSchreierDatum.originalSubgroup gensClosure
  congr 1
  ext g
  change g ∈ Q5.original.toList ↔ _
  rw [Q5, RawSchreierDatum.mem_ofArrays_original, pis_count]
  refine exists_congr fun k => and_congr_right fun hk => ?_
  have e : (ctiS5.extract 0 9)[k]! = ctiS5[k]! := by
    rw [getElem!_pos _ k (by rw [pis_count]; exact hk),
      getElem!_pos ctiS5 k (by rw [image_ok.1]; omega)]
    simp only [Array.getElem_extract, Nat.zero_add]
  rw [PiP, e]

theorem card_pis : Nat.card (gensClosure (ctiS5.extract 0 9) PiP) = 51840 := by
  rw [← Q5_eq, card_originalSubgroup_of_chainOK chainArr (by norm_num) image_ok.2.1, image_ok.2.2]

theorem sep5 {X Y : Equiv.Perm (Fin 512)} (hX : X ∈ gensClosure (ctiS5.extract 0 9) PiP)
    (hY : Y ∈ gensClosure (ctiS5.extract 0 9) PiP)
    (h : ∀ x ∈ ([18, 32, 2] : List ℕ), ∀ hx : x < 512, X ⟨x, hx⟩ = Y ⟨x, hx⟩) : X = Y := by
  have hQ := (validSchreier_of_chainOK chainArr (by norm_num) image_ok.2.1).1
  have hG : Y⁻¹ * X ∈ Q5.originalSubgroup := by
    rw [Q5_eq]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hY) hX
  have h1 := RawSchreierDatum.eq_one_of_fixes_base Q5 hQ hG fun i => ?_
  · rw [mul_eq_one_iff_eq_inv] at h1
    exact (inv_injective h1).symm
  · have hv := chainArr.base_val i
    have hi : (i : ℕ) < 3 := i.2
    obtain ⟨b, hb⟩ : ∃ b, Q5.base.get i = b := ⟨_, rfl⟩
    rw [hb] at hv ⊢
    have hbm : (b : ℕ) ∈ ([18, 32, 2] : List ℕ) := by
      rw [hv]
      obtain ⟨i, hi'⟩ := i
      change i < 3 at hi'
      interval_cases i <;> simp [ctiB5]
    rw [Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq]
    exact h b hbm b.2

theorem image_eq : ctiImageOK (ctiS5.extract 0 9) (closureSearch 512 (ctiS5.extract 0 9) 60000).1
    (closureSearch 512 (ctiS5.extract 0 9) 60000).2.1
    (closureSearch 512 (ctiS5.extract 0 9) 60000).2.2.1
    (closureSearch 512 (ctiS5.extract 0 9) 60000).2.2.2 = true := by
  have hb : Nat.card (gensClosure (ctiS5.extract 0 9) PiP) ≤ 60000 := by rw [card_pis]; norm_num
  obtain ⟨hok, hsz, hinj⟩ := closureSearch_spec rep_PiP hb
  have hcard := closureSearch_size rep_PiP hb
  rw [card_pis] at hcard
  set E5 := (closureSearch 512 (ctiS5.extract 0 9) 60000).1 with hE5
  unfold ctiImageOK
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨hok, hcard⟩, keysOK_of_nodup ?_⟩
  have hrec := exists_rep_mem_closure rep_PiP hok
  rw [List.nodup_iff_injective_get]
  intro i j hij
  have hi : (i : ℕ) < E5.size := by simpa using i.2
  have hj : (j : ℕ) < E5.size := by simpa using j.2
  simp only [List.get_eq_getElem, List.getElem_map, Array.getElem_toList] at hij
  rw [← getElem!_pos E5 _ hi, ← getElem!_pos E5 _ hj] at hij
  obtain ⟨X, hX, hXr⟩ := hrec i hi
  obtain ⟨Y, hY, hYr⟩ := hrec j hj
  have hpt := keyAt_inj _ (fun x hx => hXr.lt (by simp at hx; omega))
    (fun x hx => hYr.lt (by simp at hx; omega)) hij
  have hXY : X = Y := sep5 hX hY fun x hx hx' => Fin.ext (by
    rw [← hXr.apply hx', ← hYr.apply hx']
    exact hpt x hx)
  rw [hXY] at hXr
  exact Fin.ext (hinj i hi j hj (arr_eq_of_rep (hsz i hi) (hsz j hj) hXr hYr))

theorem checks_of
    (htext : fi22Cent3510Text = Fi22E2065.textP) : ctiChecks = true := by
  have h1 := search_eq htext
  have h2 := cosets_eq htext
  have h3 := pis_eq htext
  unfold ctiChecks
  simp only [h1]
  simp only [h2]
  simp only [h3]
  rw [Bool.and_eq_true]
  have hq := qok htext
  rw [← EE_eq_mulTree htext] at hq
  exact ⟨hq, image_eq⟩

open CFSG CFSG.Sporadic CFSG.Sporadic.FischerOddCore CFSG.Monster.B.Co2.Native in
open CFSG.Certificates.Native CFSG.Monster.B.Fischer CFSG.Sporadic.FischerOddCore.Native in
theorem certificate2064_of
    (htext : fi22Cent3510Text = Fi22E2065.textP) : ctiChecks = true :=
  checks_of htext

end CertificateChecks.KernelSpor.Fi22CtiG

end
