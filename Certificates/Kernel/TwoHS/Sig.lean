module

public import Certificates.Kernel.TwoHS.HYOps
public import Certificates.Kernel.TwoHS.WKVal
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S9Check
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Spor.PackFld

#kc_repo #kc_decls CFSG.KD.TwoHS "Certificates/Kernel/TwoHS/data/sig.txt" 274462 3969451038543877080

public section

set_option maxRecDepth 400000
set_option Elab.async false

namespace CFSG.KD.TwoHS

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.MulH CFSG.EvenSporadicStandard.TwoHS
open CFSG.Sporadic.Recognition.HSMultiplier

@[expose] noncomputable def SG (i : Fin 6) : Nat := WK (sigWords.getD i.val [])

@[expose] noncomputable def SGI (i : Fin 6) : Nat := WKI (sigWords.getD i.val [])

theorem sigP0 : Nat.beq (wfC L (sigWords.getD 0 []) idK) SigV0 = true := by quickRfl
theorem sigP1 : Nat.beq (wfC L (sigWords.getD 1 []) idK) SigV1 = true := by quickRfl
theorem sigP2 : Nat.beq (wfC L (sigWords.getD 2 []) idK) SigV2 = true := by quickRfl
theorem sigP3 : Nat.beq (wfC L (sigWords.getD 3 []) idK) SigV3 = true := by quickRfl
theorem sigP4 : Nat.beq (wfC L (sigWords.getD 4 []) idK) SigV4 = true := by quickRfl
theorem sigP5 : Nat.beq (wfC L (sigWords.getD 5 []) idK) SigV5 = true := by quickRfl

theorem sigWK {wd : List Nat} {v : Nat} (h : Nat.beq (wfC L wd idK) v = true) : WK wd = v := by
  have e := Nat.eq_of_beq_eq_true h
  rw [← wfoldK_eq_C] at e
  exact e

@[expose] noncomputable def SGV (i : Fin 6) : Nat := [SigV0, SigV1, SigV2, SigV3, SigV4, SigV5].getD i.val idK

theorem SG_V : SG = SGV := by
  funext i
  unfold SG SGV
  match i with
  | ⟨0, _⟩ => exact sigWK (wd := sigWords.getD 0 []) (v := SigV0) sigP0
  | ⟨1, _⟩ => exact sigWK (wd := sigWords.getD 1 []) (v := SigV1) sigP1
  | ⟨2, _⟩ => exact sigWK (wd := sigWords.getD 2 []) (v := SigV2) sigP2
  | ⟨3, _⟩ => exact sigWK (wd := sigWords.getD 3 []) (v := SigV3) sigP3
  | ⟨4, _⟩ => exact sigWK (wd := sigWords.getD 4 []) (v := SigV4) sigP4
  | ⟨5, _⟩ => exact sigWK (wd := sigWords.getD 5 []) (v := SigV5) sigP5

theorem sig_pc_of_permOK {n w p r : Nat} (hp : canonK n w (mask w) (n * w) p = true)
    (hI : canonK n w (mask w) (n * w) (pidn n w) = true)
    (h : CFSG.KC.Enum.permOK n w (mask w) (n * w) p r = true) :
    pcomp n w (mask w) r p = pidn n w := by
  obtain ⟨hn, hw, -, -⟩ := CFSG.KS.PF.canon_facts hp
  obtain ⟨-, -, hi0, -⟩ := CFSG.KS.PF.canon_facts hI
  have hw0 := CFSG.KS.PF.w_pos hw
  unfold CFSG.KC.Enum.permOK at h
  simp only [bAnd_iff] at h
  obtain ⟨-, -, ha⟩ := h
  refine CFSG.KS.PF.eq_of_fields hw0 (CFSG.KS.PF.pcomp_shr _ _ (by omega) hw0) hi0 fun i hi => ?_
  have e := allN_spec ha i hi
  rw [CFSG.KS.PEnum.strictB_app'] at e
  simp only [bAnd_iff, Nat.beq_eq] at e
  rw [CFSG.KS.PF.pg_pcomp (by omega) hi, e.2]
  exact (CFSG.KS.PF.pg_pidn hn hw hi).symm

theorem sig_permOK_of_pc {n w p r : Nat} (hp : canonK n w (mask w) (n * w) p = true)
    (hr : canonK n w (mask w) (n * w) r = true) (h : pcomp n w (mask w) r p = pidn n w) :
    CFSG.KC.Enum.permOK n w (mask w) (n * w) p r = true := by
  obtain ⟨hn, hw, h0, hlt⟩ := CFSG.KS.PF.canon_facts hp
  obtain ⟨-, -, hr0, -⟩ := CFSG.KS.PF.canon_facts hr
  unfold CFSG.KC.Enum.permOK
  simp only [bAnd_iff]
  refine ⟨by simpa using h0, by simpa using hr0, CFSG.KS.PackFld.allN_of_forall fun i hi => ?_⟩
  rw [CFSG.KS.PEnum.strictB_app']
  simp only [bAnd_iff, Nat.blt_eq, Nat.beq_eq]
  refine ⟨hlt i hi, ?_⟩
  rw [← CFSG.KS.PF.pg_pcomp (by omega) hi, h]
  exact CFSG.KS.PF.pg_pidn hn hw hi

theorem sig_pc_of_inv {p r : Nat} (hp : Cn p)
    (h : invEqK 11200 14 (mask 14) (11200 * 14) p r = true) : pc r p = idK :=
  sig_pc_of_permOK hp cId h

theorem sig_inv_of_pc {p r : Nat} (hp : Cn p) (hr : Cn r) (h : pc r p = idK) :
    invEqK 11200 14 (mask 14) (11200 * 14) p r = true :=
  sig_permOK_of_pc hp hr h

theorem sig_L_sq {l : Nat} (h1 : 1 ≤ l) (h6 : l ≤ 6) : pc (L l) (L l) = idK :=
  sig_pc_of_inv (L_cn h1 h6) (hy (j := l - 1) (by omega)).2

theorem sig_WK_rev : ∀ wd : List Nat, (∀ l ∈ wd, 1 ≤ l ∧ l ≤ 6) → pc (WK wd) (WKI wd) = idK
  | [], _ => pc_idK_left cId
  | a :: w, hw => by
    have ha := hw a (List.mem_cons_self ..)
    have hS : ∀ l ∈ w, Cn (L l) := fun l hl =>
      L_cn (hw l (List.mem_cons_of_mem _ hl)).1 (hw l (List.mem_cons_of_mem _ hl)).2
    have hR : ∀ l ∈ w.reverse, Cn (L l) := fun l hl => hS l (List.mem_reverse.1 hl)
    have cA := L_cn ha.1 ha.2
    have cR : Cn (WK w.reverse) := wfoldK_cn w.reverse hR _ cId
    have ih := sig_WK_rev w fun l hl => hw l (List.mem_cons_of_mem _ hl)
    have e1 : WK (a :: w) = pc (L a) (WK w) := by
      unfold WK
      rw [CFSG.KS.MulH.wfoldK_cons]
      change wfoldK 11200 14 (mask 14) L w (pc idK (L a)) = _
      rw [pc_idK_left cA]
      exact wfoldK_pc w hS _ cA
    have e2 : WKI (a :: w) = pc (WK w.reverse) (L a) := by
      unfold WKI WK
      rw [List.reverse_cons, wfoldK_append, CFSG.KS.MulH.wfoldK_cons]
      rfl
    unfold WKI at ih
    rw [e1, e2, pc_assoc (wkPc_cn cR cA), ← pc_assoc cA, ih, pc_idK_left cA]
    exact sig_L_sq ha.1 ha.2

theorem sigLetRange (i : Fin 6) : ∀ l ∈ sigWords.getD i.val [], 1 ≤ l ∧ l ≤ 6 := by
  intro l hl
  have h := List.all_eq_true.1 (wkLettersOK_getD wkSigWords_letters i.val) l hl
  simpa using h

theorem SG_cn (i : Fin 6) : Cn (SG i) := WK_cn (wkLettersOK_getD wkSigWords_letters i.val)

theorem SGI_cn (i : Fin 6) : Cn (SGI i) :=
  wfoldK_cn _ (fun l hl => L_cn (sigLetRange i l (List.mem_reverse.1 hl)).1
    (sigLetRange i l (List.mem_reverse.1 hl)).2) _ cId

theorem SGI_SG (i : Fin 6) : pc (SGI i) (SG i) = idK := by
  have h := sig_WK_rev (sigWords.getD i.val []).reverse fun l hl =>
    sigLetRange i l (List.mem_reverse.1 hl)
  unfold WKI at h
  rw [List.reverse_reverse] at h
  exact h

@[expose] noncomputable def pcC (p q : Nat) : Nat := pcompC 11200 14 (mask 14) p q

theorem pc_pcC (p q : Nat) : pc p q = pcC p q := pc_eq_C p q

theorem sigS0 : Nat.beq (pcC (SGV ⟨0, by decide⟩) (SGV ⟨0, by decide⟩)) idK = true := by quickRfl
theorem sigS1 : Nat.beq (pcC (SGV ⟨1, by decide⟩) (SGV ⟨1, by decide⟩)) idK = true := by quickRfl
theorem sigS2 : Nat.beq (pcC (SGV ⟨2, by decide⟩) (SGV ⟨2, by decide⟩)) idK = true := by quickRfl
theorem sigS3 : Nat.beq (pcC (SGV ⟨3, by decide⟩) (SGV ⟨3, by decide⟩)) idK = true := by quickRfl
theorem sigS4 : Nat.beq (pcC (SGV ⟨4, by decide⟩) (SGV ⟨4, by decide⟩)) idK = true := by quickRfl
theorem sigS5 : Nat.beq (pcC (SGV ⟨5, by decide⟩) (SGV ⟨5, by decide⟩)) idK = true := by quickRfl

theorem SGV_sq (i : Fin 6) : pc (SGV i) (SGV i) = idK := by
  rw [pc_pcC]
  apply Nat.eq_of_beq_eq_true
  match i with
  | ⟨0, _⟩ => exact sigS0
  | ⟨1, _⟩ => exact sigS1
  | ⟨2, _⟩ => exact sigS2
  | ⟨3, _⟩ => exact sigS3
  | ⟨4, _⟩ => exact sigS4
  | ⟨5, _⟩ => exact sigS5

theorem SGV_cn (i : Fin 6) : Cn (SGV i) := by
  rw [← SG_V]
  exact SG_cn i

theorem SGI_V : SGI = SGV := by
  funext i
  have h := SGI_SG i
  rw [SG_V] at h
  calc SGI i = pc (SGI i) idK := (pc_idK_right (SGI_cn i)).symm
    _ = pc (SGI i) (pc (SGV i) (SGV i)) := by rw [SGV_sq i]
    _ = pc (pc (SGI i) (SGV i)) (SGV i) := (pc_assoc (SGV_cn i)).symm
    _ = SGV i := by rw [h, pc_idK_left (SGV_cn i)]

@[expose] noncomputable def SGWS (l : Nat) : Nat :=
  [SigV0, SigV1, SigV2, SigV3, SigV4, SigV5].getD (l - 1) idK

theorem SGW_S : SGW = SGWS := by
  funext l
  unfold SGW SGWS
  generalize l - 1 = k
  match k with
  | 0 => exact sigWK (wd := sigWords.getD 0 []) (v := SigV0) sigP0
  | 1 => exact sigWK (wd := sigWords.getD 1 []) (v := SigV1) sigP1
  | 2 => exact sigWK (wd := sigWords.getD 2 []) (v := SigV2) sigP2
  | 3 => exact sigWK (wd := sigWords.getD 3 []) (v := SigV3) sigP3
  | 4 => exact sigWK (wd := sigWords.getD 4 []) (v := SigV4) sigP4
  | 5 => exact sigWK (wd := sigWords.getD 5 []) (v := SigV5) sigP5
  | k + 6 =>
    rw [List.getD_eq_default _ _ (by simp [sigWords]), List.getD_eq_default _ _ (by simp)]
    rfl

theorem WK_sigWord_S (w : List Nat) : WK (sigWord w) = wfC SGWS w idK := by
  rw [WK_sigWord, wfoldK_eq_C, SGW_S]

theorem sig_inv : (List.finRange 6).all (fun i =>
    invEqK 11200 14 (mask 14) (11200 * 14) (SG i) (SGI i)) = true := by
  rw [List.all_eq_true]
  intro i _
  exact sig_inv_of_pc (SG_cn i) (SGI_cn i) (SGI_SG i)

theorem sig_z : (List.finRange 6).all (fun i => Nat.beq (pcC (SG i) SigZ) (pcC SigZ (SG i))) = true := by
  rewrite [SG_V]
  quickRfl

@[expose] noncomputable def EVC (G GI : Fin 6 → Nat) (wd : List (Fin 6 × Bool)) : Nat :=
  wd.foldl (fun acc l => pcC acc (cond l.2 (G l.1) (GI l.1))) idK

theorem EVK_C : EVK = EVC := by
  funext G GI wd
  unfold EVK EVC
  simp only [pc_pcC]

@[expose] noncomputable def sigRelZ (r : List (Fin 6 × Bool)) : Bool :=
  Nat.beq (EVC SGV SGV r) idK || Nat.beq (EVC SGV SGV r) SigZ

theorem sig_all_idx {rs : List (List (Fin 6 × Bool))} {f : List (Fin 6 × Bool) → Bool} {n : Nat}
    (hn : rs.length = n) (h : ∀ k, k < n → f (rs.getD k []) = true) : rs.all f = true := by
  rw [List.all_eq_true]
  intro r hr
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hr
  have e := h k (hn ▸ hk)
  rwa [List.getD_eq_getElem _ _ hk] at e

theorem sigC_sq (i : Fin 6) : sigRelZ [(i, true), (i, true)] = true := by
  unfold sigRelZ EVC
  simp only [List.foldl_cons, List.foldl_nil, Bool.cond_true, ← pc_pcC]
  rw [pc_idK_left (SGV_cn i), SGV_sq i, Nat.beq_refl, Bool.true_or]

theorem sigC_sq' (k : Nat) (hk : k < 6)
    (h : hsCoxeter.getD k [] = [(⟨k, hk⟩, true), (⟨k, hk⟩, true)]) :
    sigRelZ (hsCoxeter.getD k []) = true := by
  rw [h]
  exact sigC_sq ⟨k, hk⟩

theorem sigC0 : sigRelZ (hsCoxeter.getD 0 []) = true := sigC_sq' 0 (by decide) rfl
theorem sigC1 : sigRelZ (hsCoxeter.getD 1 []) = true := sigC_sq' 1 (by decide) rfl
theorem sigC2 : sigRelZ (hsCoxeter.getD 2 []) = true := sigC_sq' 2 (by decide) rfl
theorem sigC3 : sigRelZ (hsCoxeter.getD 3 []) = true := sigC_sq' 3 (by decide) rfl
theorem sigC4 : sigRelZ (hsCoxeter.getD 4 []) = true := sigC_sq' 4 (by decide) rfl
theorem sigC5 : sigRelZ (hsCoxeter.getD 5 []) = true := sigC_sq' 5 (by decide) rfl
theorem sigC6 : sigRelZ (hsCoxeter.getD 6 []) = true := by quickRfl
theorem sigC7 : sigRelZ (hsCoxeter.getD 7 []) = true := by quickRfl
theorem sigC8 : sigRelZ (hsCoxeter.getD 8 []) = true := by quickRfl
theorem sigC9 : sigRelZ (hsCoxeter.getD 9 []) = true := by quickRfl
theorem sigC10 : sigRelZ (hsCoxeter.getD 10 []) = true := by quickRfl
theorem sigC11 : sigRelZ (hsCoxeter.getD 11 []) = true := by quickRfl
theorem sigC12 : sigRelZ (hsCoxeter.getD 12 []) = true := by quickRfl
theorem sigC13 : sigRelZ (hsCoxeter.getD 13 []) = true := by quickRfl
theorem sigC14 : sigRelZ (hsCoxeter.getD 14 []) = true := by quickRfl
theorem sigC15 : sigRelZ (hsCoxeter.getD 15 []) = true := by quickRfl
theorem sigC16 : sigRelZ (hsCoxeter.getD 16 []) = true := by quickRfl
theorem sigC17 : sigRelZ (hsCoxeter.getD 17 []) = true := by quickRfl
theorem sigC18 : sigRelZ (hsCoxeter.getD 18 []) = true := by quickRfl
theorem sigC19 : sigRelZ (hsCoxeter.getD 19 []) = true := by quickRfl
theorem sigC20 : sigRelZ (hsCoxeter.getD 20 []) = true := by quickRfl
theorem sigX0 : sigRelZ (hsExtra.getD 0 []) = true := by quickRfl
theorem sigX1 : sigRelZ (hsExtra.getD 1 []) = true := by quickRfl
theorem sigX2 : sigRelZ (hsExtra.getD 2 []) = true := by quickRfl
theorem sigX3 : sigRelZ (hsExtra.getD 3 []) = true := by quickRfl
theorem sigX4 : sigRelZ (hsExtra.getD 4 []) = true := by quickRfl

theorem sig_cox_z : hsCoxeter.all (fun r =>
    Nat.beq (EVK SG SGI r) idK || Nat.beq (EVK SG SGI r) SigZ) = true := by
  rewrite [SG_V, SGI_V, EVK_C]
  change hsCoxeter.all sigRelZ = true
  refine sig_all_idx (n := 21) (by decide) fun k hk => ?_
  match k, hk with
  | 0, _ => exact sigC0
  | 1, _ => exact sigC1
  | 2, _ => exact sigC2
  | 3, _ => exact sigC3
  | 4, _ => exact sigC4
  | 5, _ => exact sigC5
  | 6, _ => exact sigC6
  | 7, _ => exact sigC7
  | 8, _ => exact sigC8
  | 9, _ => exact sigC9
  | 10, _ => exact sigC10
  | 11, _ => exact sigC11
  | 12, _ => exact sigC12
  | 13, _ => exact sigC13
  | 14, _ => exact sigC14
  | 15, _ => exact sigC15
  | 16, _ => exact sigC16
  | 17, _ => exact sigC17
  | 18, _ => exact sigC18
  | 19, _ => exact sigC19
  | 20, _ => exact sigC20
  | k + 21, h => exact absurd h (by omega)

theorem sig_extra_z : hsExtra.all (fun r =>
    Nat.beq (EVK SG SGI r) idK || Nat.beq (EVK SG SGI r) SigZ) = true := by
  rewrite [SG_V, SGI_V, EVK_C]
  change hsExtra.all sigRelZ = true
  refine sig_all_idx (n := 5) (by decide) fun k hk => ?_
  match k, hk with
  | 0, _ => exact sigX0
  | 1, _ => exact sigX1
  | 2, _ => exact sigX2
  | 3, _ => exact sigX3
  | 4, _ => exact sigX4
  | k + 5, h => exact absurd h (by omega)

theorem sig_comm_z {x e : Nat} (hx : Cn x) (he : (Nat.beq e idK || Nat.beq e SigZ) = true)
    (hz : Nat.beq (pc x SigZ) (pc SigZ x) = true) : Nat.beq (pc x e) (pc e x) = true := by
  rcases Bool.or_eq_true_iff.1 he with h | h
  · rw [Nat.eq_of_beq_eq_true h, pc_idK_right hx, pc_idK_left hx]
    exact Nat.beq_refl x
  · rw [Nat.eq_of_beq_eq_true h]
    exact hz

theorem sig_rels_z {rs : List (List (Fin 6 × Bool))}
    (h : rs.all (fun r => Nat.beq (EVK SG SGI r) idK || Nat.beq (EVK SG SGI r) SigZ) = true) :
    rs.all (fun r => (List.finRange 6).all fun i =>
      Nat.beq (pc (SG i) (EVK SG SGI r)) (pc (EVK SG SGI r) (SG i))) = true := by
  rw [List.all_eq_true]
  intro r hr
  rw [List.all_eq_true]
  intro i _
  have hz := List.all_eq_true.1 sig_z i (List.mem_finRange i)
  rw [← pc_pcC, ← pc_pcC] at hz
  exact sig_comm_z (WK_cn (wkLettersOK_getD wkSigWords_letters i.val)) (List.all_eq_true.1 h r hr) hz

theorem sig_rels_cox : hsCoxeter.all (fun r => (List.finRange 6).all fun i =>
    Nat.beq (pc (SG i) (EVK SG SGI r)) (pc (EVK SG SGI r) (SG i))) = true :=
  sig_rels_z sig_cox_z

theorem sig_rels_extra : hsExtra.all (fun r => (List.finRange 6).all fun i =>
    Nat.beq (pc (SG i) (EVK SG SGI r)) (pc (EVK SG SGI r) (SG i))) = true :=
  sig_rels_z sig_extra_z

theorem sigK0 : Nat.beq (EVC SGV SGV (hsCommWord ⟨0, by decide⟩)) (SGV ⟨0, by decide⟩) = true := by
  quickRfl
theorem sigK1 : Nat.beq (EVC SGV SGV (hsCommWord ⟨1, by decide⟩)) (SGV ⟨1, by decide⟩) = true := by
  quickRfl
theorem sigK2 : Nat.beq (EVC SGV SGV (hsCommWord ⟨2, by decide⟩)) (SGV ⟨2, by decide⟩) = true := by
  quickRfl
theorem sigK3 : Nat.beq (EVC SGV SGV (hsCommWord ⟨3, by decide⟩)) (SGV ⟨3, by decide⟩) = true := by
  quickRfl
theorem sigK4 : Nat.beq (EVC SGV SGV (hsCommWord ⟨4, by decide⟩)) (SGV ⟨4, by decide⟩) = true := by
  quickRfl
theorem sigK5 : Nat.beq (EVC SGV SGV (hsCommWord ⟨5, by decide⟩)) (SGV ⟨5, by decide⟩) = true := by
  quickRfl

theorem sig_comm :(List.finRange 6).all (fun i =>
    Nat.beq (EVK SG SGI (hsCommWord i)) (SG i)) = true := by
  rewrite [SG_V, SGI_V, EVK_C]
  rw [List.all_eq_true]
  intro i _
  match i with
  | ⟨0, _⟩ => exact sigK0
  | ⟨1, _⟩ => exact sigK1
  | ⟨2, _⟩ => exact sigK2
  | ⟨3, _⟩ => exact sigK3
  | ⟨4, _⟩ => exact sigK4
  | ⟨5, _⟩ => exact sigK5

theorem sig_sq0 : Nat.beq (WK (sigWord (sigWords.getD 0 []))) (HY.F 0) = true := by
  rewrite [WK_sigWord_S]
  quickRfl
theorem sig_sq1 : Nat.beq (WK (sigWord (sigWords.getD 1 []))) (HY.F 1) = true := by
  rewrite [WK_sigWord_S]
  quickRfl
theorem sig_sq2 : Nat.beq (WK (sigWord (sigWords.getD 2 []))) (HY.F 2) = true := by
  rewrite [WK_sigWord_S]
  quickRfl
theorem sig_sq3 : Nat.beq (WK (sigWord (sigWords.getD 3 []))) (HY.F 3) = true := by
  rewrite [WK_sigWord_S]
  quickRfl
theorem sig_sq4 : Nat.beq (WK (sigWord (sigWords.getD 4 []))) (HY.F 4) = true := by
  rewrite [WK_sigWord_S]
  quickRfl
theorem sig_sq5 : Nat.beq (WK (sigWord (sigWords.getD 5 []))) (HY.F 5) = true := by
  rewrite [WK_sigWord_S]
  quickRfl

theorem sig_fix : (fx (WK outerWord) != fx (WK (sigWord outerWord))) = true := by
  rewrite [WK_sigWord_S]
  quickRfl

end CFSG.KD.TwoHS

end
