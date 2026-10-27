module

public import Certificates.Kernel.Fi23BD0.ChkDefs
public import Certificates.Kernel.Fi23K.Letters
import Certificates.Kernel.Fi23BD0.Check
import Certificates.Kernel.Sporadic.Fi23Br.Rels
import CFSG.Certificates.Kernel.Spor.RelTR
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi23BD0

open CFSG.KC.Enum CFSG.KC.Fi23K CFSG.KC.Fi23R CFSG.KD.Fi23K CFSG.KD.Fi23BD0 CFSG.KS.Raw.Orb
  CFSG.KS.TW CFSG.Sporadic.Th.Native CFSG.Sporadic.Fi23.Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23Native
  CFSG.LocalAnalysis.GLTheoremA.H1017.BabyTwoBD0Native

theorem applyW_eq : ∀ w : List Nat, (∀ l ∈ w, l < 24) → ∀ p < 31671,
    applyW (chainLetters orbLit) w p = wv G (rW w) p ∧ wv G (rW w) p < 31671
  | [], _, p, hp => ⟨rfl, hp⟩
  | l :: w, h, p, hp => by
    obtain ⟨e1, e2⟩ := applyW_eq w (fun z hz => h z (List.mem_cons_of_mem l hz)) p hp
    have hL := (CFSG.KD.Fi23K.letters_TR.2 l (h l List.mem_cons_self)).2 _ e2
    have a1 : applyW (chainLetters orbLit) (l :: w) p =
        ap (chainLetters orbLit)[l]! (applyW (chainLetters orbLit) w p) := by
      unfold applyW
      rw [List.foldr_cons]
    have a2 : wv G (rW (l :: w)) p = LL l (wv G (rW w) p) := by
      unfold rW
      rw [List.map_cons, wv_cons]
      rfl
    rw [a1, a2, e1]
    exact hL

theorem applyWPow_eq {w : List Nat} (hw : ∀ l ∈ w, l < 24) : ∀ n, ∀ p < 31671,
    applyWPow (chainLetters orbLit) w n p = wv G (powW n (rW w)) p ∧
      wv G (powW n (rW w)) p < 31671
  | 0, p, hp => ⟨rfl, hp⟩
  | n + 1, p, hp => by
    obtain ⟨e1, e2⟩ := applyWPow_eq hw n p hp
    obtain ⟨f1, f2⟩ := applyW_eq w hw _ e2
    have a1 : applyWPow (chainLetters orbLit) w (n + 1) p =
        applyW (chainLetters orbLit) w (applyWPow (chainLetters orbLit) w n p) := rfl
    have a2 : powW (n + 1) (rW w) = rW w ++ powW n (rW w) := rfl
    rw [a1, a2, wv_append, e1]
    exact ⟨f1, f2⟩

theorem regZ_eq {z : Int} (h : z.natAbs ≤ 2 ∧ z ≠ 0) : regZ z = rZ z := by
  have hz : z = 1 ∨ z = -1 ∨ z = 2 ∨ z = -2 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;> decide

theorem imgTab_TR {k : Nat} (hk : ∀ z ∈ CFSG.KD.BrFi23.IT.W.toArray[k]!, z.natAbs ≤ 2 ∧ z ≠ 0) :
    TR 31671 (imgTab orbLit k) (wv G ((CFSG.KD.BrFi23.IT.W.toArray[k]!).map rZ)) := by
  have e : imgTab orbLit k =
      wordT 31671 (genTables orbLit) (CFSG.KD.BrFi23.IT.W.toArray[k]!) := by
    unfold imgTab
    rw [CertificateChecks.KernelSpor.Fi23Rels.img_eq]
  rw [e]
  have h := wordT_TR (by norm_num) (G := fun z => tb G (regZ z))
    (CFSG.KD.BrFi23.IT.W.toArray[k]!) fun z hz => genTables_TR (hk z hz).1 (hk z hz).2
  have hm : (CFSG.KD.BrFi23.IT.W.toArray[k]!).map rZ =
      (CFSG.KD.BrFi23.IT.W.toArray[k]!).map regZ :=
    List.map_congr_left fun z hz => (regZ_eq (hk z hz)).symm
  rw [hm]
  refine tr_congr h fun x _ => ?_
  exact foldr_regZ _ x

theorem t3_TR :
    TR 31671 (t3Tabs orbLit (chainLetters orbLit))[0]! (wv G t3W) := by
  have e : (t3Tabs orbLit (chainLetters orbLit))[0]! =
      compT 31671 (imgTab orbLit 2) (imgTab orbLit 3) := by
    rw [t3Tabs.eq_1, List.getElem!_toArray, List.getElem!_cons_zero]
  rw [e]
  have h2 := imgTab_TR (k := 2) (by decide +kernel)
  have h3 := imgTab_TR (k := 3) (by decide +kernel)
  refine tr_congr (CFSG.KS.RelTR.compT_TR h2 h3) fun x _ => ?_
  unfold t3W
  rw [wv_append]

theorem bD0_ok : bD0CheckL orbLit (chainLetters orbLit) = true := by
  have hK := bD0K_ok
  unfold bD0K bD0KW yImg at hK
  simp only [Bool.and_eq_true] at hK
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hK
  have hw : ∀ i < 4, ∀ l ∈ bD0Words[i]!, l < 24 := by decide
  have hc : ∀ l ∈ bD0Conj, l < 24 := by decide
  have hpts : ∀ k < 2, kleinPts[k]! < 31671 := by decide
  have aw := fun i (hi : i < 4) => applyW_eq _ (hw i hi)
  have pw := fun i (hi : i < 4) => applyWPow_eq (hw i hi)
  have hT := t3_TR
  unfold bD0CheckL
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · refine allIn_iff.2 fun i hi => allIn_iff.2 fun j hj => allIn_iff.2 fun t ht => ?_
    have h := allN_iff.1 (allN_iff.1 (allN_iff.1 h1 i hi) j hj) t ht
    have ht' : t < 31671 := by omega
    rw [(aw j hj t ht').1, (aw i hi t ht').1, (aw i hi _ (aw j hj t ht').2).1,
      (aw j hj _ (aw i hi t ht').2).1]
    simp only [beq_iff_eq, Nat.beq_eq] at h ⊢
    exact h
  · refine allIn_iff.2 fun i hi => allIn_iff.2 fun t ht => ?_
    have h := allN_iff.1 (allN_iff.1 h2 i hi) t ht
    rw [(pw i hi 3 t (by omega)).1]
    simp only [beq_iff_eq, Nat.beq_eq] at h ⊢
    exact h
  · refine allIn_iff.2 fun i hi => allIn_iff.2 fun k hk => ?_
    have h := allN_iff.1 (allN_iff.1 h3 i hi) k hk
    rw [(aw i hi _ (hpts k hk)).1]
    simp only [beq_iff_eq, Nat.beq_eq] at h ⊢
    exact h
  · refine allIn_iff.2 fun a ha => allIn_iff.2 fun b hb => allIn_iff.2 fun c hc' =>
      allIn_iff.2 fun e he => ?_
    have h := allN_iff.1 (allN_iff.1 (allN_iff.1 (allN_iff.1 h4 a ha) b hb) c hc') e he
    have hI : (allIn 0 6 fun t => bD0Img (chainLetters orbLit) a b c e t == t) =
        allN 6 fun t => Nat.beq (wv G (powW a (rW bD0Words[0]!)) (wv G (powW b (rW bD0Words[1]!))
          (wv G (powW c (rW bD0Words[2]!)) (wv G (powW e (rW bD0Words[3]!)) t)))) t := by
      rw [Bool.eq_iff_iff, allIn_iff, allN_iff]
      refine forall₂_congr fun t ht => ?_
      have ht' : t < 31671 := by omega
      have p3 := pw 3 (by norm_num) e t ht'
      have p2 := pw 2 (by norm_num) c _ p3.2
      have p1 := pw 1 (by norm_num) b _ p2.2
      have p0 := pw 0 (by norm_num) a _ p1.2
      unfold bD0Img
      rw [p3.1, p2.1, p1.1, p0.1, beq_iff_eq, Nat.beq_eq]
    rw [hI]
    simp only [Bool.or_eq_true, beq_iff_eq, Nat.beq_eq] at h ⊢
    exact h
  · refine allIn_iff.2 fun t ht => ?_
    have h := allN_iff.1 h5 t ht
    have ht' : t < 31671 := by omega
    have c1 := applyW_eq _ hc t ht'
    have y0 := aw 0 (by norm_num) t ht'
    have c2 := applyW_eq _ hc _ y0.2
    rw [y0.1, c1.1, c2.1, (hT.2 _ c1.2).1]
    simp only [beq_iff_eq, Nat.beq_eq] at h ⊢
    exact h

end CertificateChecks.KernelFi23BD0

end
