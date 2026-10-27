module

public import Certificates.Kernel.Fi23S.Letters
public import Certificates.Kernel.Fi23K.Iso
import Certificates.Kernel.Fi23S.Small
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi23S

open CFSG.KC.Enum CFSG.KC.Fi23K CFSG.KC.Fi23S CFSG.KD.Fi23K CFSG.KD.Fi23S CFSG.KS.Raw.Orb
  CFSG.KS.TBfs CFSG.KS.PC CFSG.Sporadic.Fi23.Native CFSG.Sporadic.Th.Native CFSG.Perm.Native

noncomputable abbrev SL : Array Table := sylLetters (chainLetters orbLit)

theorem invK_ok : invK LS 31671 42 = true := by
  unfold invK
  rw [allN_iff]
  intro j hj
  change j < 21 at hj
  rw [allN_iff]
  intro x hx
  rw [strictB_eq, bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true, Nat.blt_eq, Nat.blt_eq,
    Nat.beq_eq]
  have e0 : Nat.mul 2 j = 2 * j := rfl
  have e1 : Nat.succ (Nat.mul 2 j) = 2 * j + 1 := rfl
  rw [e1, e0]
  exact ⟨LS_lt (by omega) hx, LS_lt (by omega) hx, (LS_inv hj hx).1⟩

theorem tree_spec {i : Nat} (hi : i < 2) :
    tbfsHdK 31671 (BS i) (CNTS i) (TTS i 0) (TTS i 1) (TTS i 2) (TTS i 3) = true ∧
      ∀ k < CNTS i, tbfsPtK 31671 (CNTS i) (lvK LS BS 42 i).length LS (lvAt LS BS 42 i)
        (TTS i 0) (TTS i 1) (TTS i 2) (TTS i 3) (TTS i 4) k = true := by
  interval_cases i
  · refine ⟨hdS0, fun k hk => ?_⟩
    have h := trS0
    unfold trS lvS at h
    exact sl_spec h k (Nat.zero_le _) (by change k < 512 at hk; omega) hk
  · refine ⟨hdS1, fun k hk => ?_⟩
    have h := trS1
    unfold trS lvS at h
    exact sl_spec h k (Nat.zero_le _) (by change k < 512 at hk; omega) hk

theorem syl_hyp : ChainHyp 31671 42 2 SL sylBase chainQ (sylQb ()) LS BS QS BS CNTS
    (fun i => TTS i 0) (fun i => TTS i 1) (fun i => TTS i 2) (fun i => TTS i 3)
    (fun i => TTS i 4) where
  letters := ⟨syl_TR.1, fun l hl x hx => ((syl_TR.2 l hl).2 x hx).1⟩
  inv := ⟨rfl, invK_ok⟩
  base := ⟨rfl, fun i hi => by interval_cases i <;> exact ⟨rfl, by decide⟩⟩
  chk := ⟨rfl, by decide, rfl, fun i hi => by interval_cases i <;> exact ⟨rfl, by decide, rfl⟩⟩
  tree := fun i hi => tree_spec hi

theorem schSl_spec {i lo len : Nat} (h : schS i lo len = true) :
    ∀ k, lo ≤ k → k < lo + len → k < CNTS i → ∀ t < (lvK LS BS 42 i).length,
      schK LS (fun i => TTS i 0) (fun i => TTS i 1) (fun i => TTS i 2) (fun i => TTS i 3) CNTS BS
        QS 2 i (lvAt LS BS 42 i t) k = true := by
  intro k h1 h2 h3 t ht
  unfold schS schSlK at h
  rw [strictB_eq] at h
  have h' := allN_iff.1 h (k - lo) (by omega)
  rw [strictB_eq] at h'
  have e : Nat.add lo (k - lo) = k := by
    change lo + (k - lo) = k
    omega
  rw [e, bIf_eq, if_pos (Nat.blt_eq.mpr h3)] at h'
  exact allN_iff.1 h' t ht

theorem sch_all : ∀ i < 2, ∀ k < CNTS i, ∀ t < (lvK LS BS 42 i).length,
    schK LS (fun i => TTS i 0) (fun i => TTS i 1) (fun i => TTS i 2) (fun i => TTS i 3) CNTS BS
      QS 2 i (lvAt LS BS 42 i t) k = true := by
  intro i hi k hk t ht
  have hk' : k < 512 := hk
  have s0 : schS 0 0 128 = true := schF0
  have s1 : schS 0 128 128 = true := schF1
  have s2 : schS 0 256 128 = true := schF2
  have s3 : schS 0 384 128 = true := schF3
  have s4 : schS 1 0 512 = true := schS1
  interval_cases i
  · rcases (by omega : k < 128 ∨ (128 ≤ k ∧ k < 256) ∨ (256 ≤ k ∧ k < 384) ∨ 384 ≤ k) with
      h | h | h | h
    · exact schSl_spec s0 k (by omega) (by omega) hk t ht
    · exact schSl_spec s1 k (by omega) (by omega) hk t ht
    · exact schSl_spec s2 k (by omega) (by omega) hk t ht
    · exact schSl_spec s3 k (by omega) (by omega) hk t ht
  · exact schSl_spec s4 k (by omega) (by omega) hk t ht

theorem term_ok : termK LS BS 42 2 QS = true := termS_ok

theorem syl_chain : chainTrees 31671 SL sylBase =
      Array.ofFn (n := 2) (fun i => tbfsRec 31671 (CNTS i.val) (TTS i.val 0) (TTS i.val 1)
        (TTS i.val 2) (TTS i.val 3)) ∧
    ∀ chunks, chainOK 31671 SL sylBase chainQ (sylQb ()) (chainTrees 31671 SL sylBase) chunks =
      true := by
  have h := pchainK_sound syl_hyp sch_all term_ok
  exact h

theorem chain_act {l : Nat} (hl : l < 24) {x : Nat} (hx : x < 31671) :
    actN (sig 31671 (chainLetters orbLit) l) x = LL l x :=
  actN_sig chain_hyp hl hx

theorem prod_act : ∀ (w : List Int), (∀ z ∈ w, z.toNat < 24) → ∀ x < 31671,
    actN ((w.map fun z => sig 31671 (chainLetters orbLit) z.toNat).prod) x =
      w.foldr (fun z y => LL z.toNat y) x
  | [], _, x, _ => actN_one x
  | z :: w, h, x, hx => by
    rw [List.map_cons, List.prod_cons, actN_mul, chain_act (h z List.mem_cons_self) (actN_lt _ hx),
      prod_act w (fun y hy => h y (List.mem_cons_of_mem z hy)) x hx, List.foldr_cons]

theorem perm_eq_of_act {p q : Equiv.Perm (Fin 31671)} (h : ∀ x < 31671, actN p x = actN q x) :
    p = q := by
  ext y
  rw [← actN_fin, ← actN_fin, h y y.isLt]

theorem prod_mem (w : List Int) (hw : ∀ z ∈ w, z.toNat < 24) :
    (w.map fun z => sig 31671 (chainLetters orbLit) z.toNat).prod ∈ T23 := by
  refine Subgroup.list_prod_mem _ fun p hp => ?_
  obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hp
  exact sig_mem ⟨z.toNat, hw z hz⟩

theorem sig_T23 {l : Nat} (hl : l < 42) : sig 31671 SL l ∈ T23 := by
  obtain ⟨j, hj, rfl | rfl⟩ : ∃ j, j < 21 ∧ (l = 2 * j ∨ l = 2 * j + 1) := ⟨l / 2, by omega, by omega⟩
  · have e : sig 31671 SL (2 * j) =
        ((sylWords ())[j]!.map fun z => sig 31671 (chainLetters orbLit) z.toNat).prod :=
      perm_eq_of_act fun x hx => by
        rw [actN_sig syl_hyp hl hx, prod_act _ (fun z hz => (sylWords_lt j hj z hz).2) x hx,
          foldr_LL, ← SW_eq j hj]
        exact (sylJ_pt hx hj).1
    rw [e]
    exact prod_mem _ fun z hz => (sylWords_lt j hj z hz).2
  · have e : sig 31671 SL (2 * j + 1) = (sig 31671 SL (2 * j))⁻¹ :=
      perm_eq_of_act fun x hx => by
        rw [actN_sig syl_hyp hl hx, actN_sig_inv syl_hyp (by omega) hx]
        congr 1
        unfold invL
        rw [if_pos (by omega)]
    have h0 : sig 31671 SL (2 * j) ∈ T23 := by
      have e0 : sig 31671 SL (2 * j) =
          ((sylWords ())[j]!.map fun z => sig 31671 (chainLetters orbLit) z.toNat).prod :=
        perm_eq_of_act fun x hx => by
          rw [actN_sig syl_hyp (by omega) hx, prod_act _ (fun z hz => (sylWords_lt j hj z hz).2) x hx,
            foldr_LL, ← SW_eq j hj]
          exact (sylJ_pt hx hj).1
      rw [e0]
      exact prod_mem _ fun z hz => (sylWords_lt j hj z hz).2
    rw [e]
    exact Subgroup.inv_mem _ h0

theorem tw_T23 {i : Nat} (hi : i < 2) : ∀ k < CNTS i,
    twL 31671 SL (fun i => TTS i 2) (fun i => TTS i 3) i k ∈ T23 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rw [twL, tw_eq]
    split_ifs with hc
    · exact Subgroup.mul_mem _ (sig_T23 (mem_lvK.1 (lab_mem syl_hyp hi hk hc.1)).1)
        (ih _ hc.2 (by change k < 512 at hk; change _ < 512; omega))
    · exact Subgroup.one_mem _

end CertificateChecks.KernelFi23S

end
