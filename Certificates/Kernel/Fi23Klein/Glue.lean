module

public import Certificates.Kernel.Fi23Klein.ChkDefs
public import Certificates.Kernel.Fi23C.Group
public import Certificates.Kernel.Fi23R.Sound
import Certificates.Kernel.Fi23Klein.Check
import CFSG.Certificates.Kernel.Spor.RelTR
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi23Klein

open CFSG.KC.Enum CFSG.KC.Fi23K CFSG.KC.Fi23R CFSG.KD.Fi23K CFSG.KD.Fi23Klein CFSG.KS.Raw.Orb
  CFSG.KS.TW CFSG.Sporadic.Th.Native CFSG.Sporadic.Fi23.Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Native

theorem qLettersT_TR : ∀ w : List Nat, (∀ l ∈ w, l < 24) →
    TR 31671 (qLettersT (chainLetters orbLit) w) (wv G (rW w))
  | [], _ => by
    have e : qLettersT (chainLetters orbLit) [] = idT 31671 := by
      unfold qLettersT
      rw [List.foldr_nil]
    rw [e]
    exact idT_TR (by norm_num)
  | l :: w, h => by
    have hL := CFSG.KD.Fi23K.letters_TR.2 l (h l List.mem_cons_self)
    have hW := qLettersT_TR w fun z hz => h z (List.mem_cons_of_mem l hz)
    have e1 : qLettersT (chainLetters orbLit) (l :: w) =
        compT 31671 (chainLetters orbLit)[l]! (qLettersT (chainLetters orbLit) w) := by
      unfold qLettersT
      rw [List.foldr_cons]
    have e2 : wv G (rW (l :: w)) = fun x => LL l (wv G (rW w) x) := by
      funext x
      unfold rW
      rw [List.map_cons, wv_cons]
      rfl
    rw [e1, e2]
    exact CFSG.KS.RelTR.compT_TR hL hW

theorem powT_TR' {P : Table} {w : List Nat} (h : TR 31671 P (wv G w)) :
    ∀ e, TR 31671 (powT 31671 e P) (wv G (powW e w))
  | 0 => idT_TR (by norm_num)
  | e + 1 => by
    have e0 : powW (e + 1) w = w ++ powW e w := rfl
    have e1 : wv G (powW (e + 1) w) = fun x => wv G w (wv G (powW e w) x) := by
      funext x
      rw [e0, wv_append]
    rw [e1]
    exact CFSG.KS.RelTR.compT_TR h (powT_TR' h e)

theorem fix_eq {T : Table} {w : List Nat} (h : TR 31671 T (wv G w)) {p : Nat} (hp : p < 31671) :
    (ap T p == p) = fxV w p := by
  unfold fxV
  rw [(h.2 p hp).1, Bool.eq_iff_iff, beq_iff_eq, Nat.beq_eq]

theorem baseFixed_eq {T : Table} {w : List Nat} (h : TR 31671 T (wv G w)) :
    baseFixed T = baseV w := by
  unfold baseFixed baseV
  rw [Bool.eq_iff_iff, allIn_iff, allN_iff]
  exact forall₂_congr fun t ht => by rw [fix_eq h (by omega)]

theorem all_fix_eq {T : Table} {w : List Nat} (h : TR 31671 T (wv G w)) {fx : List Nat}
    (hfx : ∀ p ∈ fx, p < 31671) : (fx.all fun p => ap T p == p) = fx.all (fxV w) := by
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  exact forall₂_congr fun p hp => by rw [fix_eq h (hfx p hp)]

theorem klein_ok : kleinOK orbLit = true := by
  have hK := kleinK_ok
  unfold kleinK at hK
  simp only [Bool.and_eq_true] at hK
  obtain ⟨⟨h1, h2⟩, h3⟩ := hK
  have hpts : ∀ i < 3, kleinPts[i]! < 31671 := by decide
  have hw : ∀ k < 5, ∀ l ∈ kleinWords[k]!, l < 24 := by decide
  have hfx : ∀ k < 5, ∀ p ∈ kleinFix[k]!, p < 31671 := by decide
  have hz : ∀ l ∈ kleinZ, l < 24 := by decide
  have hsz : (chainLetters orbLit).size = 24 := CFSG.KD.Fi23K.letters_TR.1
  have htr : ∀ k < 31671, ∀ m < 31671, treeAct orbLit.par orbLit.lab orbLit.alpha orbLit.beta
      (dTable orbLit) (genTables orbLit (-2)) k m = tA G k m := fun k hk m hm =>
    CertificateChecks.KernelFi23R.tAf_treeAct
      (fun _ hm => CertificateChecks.KernelFi23C.dTable_ap hm)
      (fun _ hm => CertificateChecks.KernelFi23C.bi_ap hm) 200 k hk (dep_pt hk).1 m hm
  unfold kleinOK kleinCheckL
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨?_, rfl⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · refine allIn_iff.2 fun i hi => allIn_iff.2 fun j hj => ?_
    have h := allN_iff.1 (allN_iff.1 h1 i hi) j hj
    rw [htr _ (hpts i hi) _ (hpts j hj)]
    simp only [Bool.or_eq_true, beq_iff_eq, Nat.beq_eq] at h ⊢
    exact h
  · rw [hsz]
    simp [kleinWords]
  · refine allIn_iff.2 fun k hk => ?_
    have h := allN_iff.1 h2 k hk
    unfold yK at h
    have hY := qLettersT_TR _ (hw k hk)
    rw [baseFixed_eq (powT_TR' hY _), baseFixed_eq hY, all_fix_eq hY (hfx k hk)]
    exact h
  · rw [hsz]
    decide
  · refine allIn_iff.2 fun i hi => ?_
    rw [fix_eq (qLettersT_TR _ hz) (hpts i hi)]
    exact allN_iff.1 h3 i hi

end CertificateChecks.KernelFi23Klein

end
